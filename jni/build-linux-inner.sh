#!/usr/bin/env bash

set -euo pipefail

WORK=/work
OUT=/output
BUILD=/tmp/build
LOGS=/tmp/logs
LOCK="$WORK/sources.lock"

die() { echo "ERROR: $*" >&2; exit 1; }

run_logged() {
  local name="$1"; shift
  mkdir -p "$LOGS"
  if ! "$@" >"$LOGS/$name.log" 2>&1; then
    echo "FAILED: $* (last lines of $LOGS/$name.log):" >&2
    tail -n 40 "$LOGS/$name.log" >&2
    exit 1
  fi
}

lock_value() {
  local want_name="$1" want_kind="$2" name kind value path
  while read -r name kind value path; do
    case "$name" in ''|'#'*) continue ;; esac
    if [ "$name" = "$want_name" ] && [ "$kind" = "$want_kind" ]; then
      echo "$value"
      return 0
    fi
  done < "$LOCK"
}

verify_sources() {
  local solver="$1" name kind value path have found=0
  while read -r name kind value path; do
    case "$name" in ''|'#'*) continue ;; esac
    [ "$name" = "$solver" ] || continue
    found=1
    case "$kind" in
      sha256)
        [ -f "$BUILD/$path" ] || die "$solver: expected fetched file $path is missing"
        have="$(sha256sum "$BUILD/$path" | cut -d' ' -f1)"
        if [ "$have" != "$value" ]; then
          die "$solver: $path has sha256 $have but sources.lock pins $value (upstream changed, or a bad download)"
        fi
        echo "  $solver: $path matches pinned sha256"
        ;;
      git)
        [ -d "$BUILD/$path/.git" ] || die "$solver: expected git checkout at $path is missing"
        have="$(git -C "$BUILD/$path" rev-parse HEAD)"
        if [ "$have" != "$value" ]; then
          git -C "$BUILD/$path" checkout --quiet --detach "$value" \
            || die "$solver: cannot check out pinned commit $value in $path"
          echo "  $solver: upstream HEAD was ${have:0:8}; pinned checkout to ${value:0:8}"
        else
          echo "  $solver: $path already at pinned commit ${value:0:8}"
        fi
        ;;
      *) die "sources.lock: unknown kind '$kind' for $name" ;;
    esac
  done < "$LOCK"
  [ "$found" = 1 ] || die "sources.lock has no entry for $solver"
}

install_wget_shim() {
  local shim_dir="$1"
  mkdir -p "$shim_dir"
  cat > "$shim_dir/wget" <<'SHIM'
#!/usr/bin/env bash
url=""; dir="."
args=("$@")
for ((i = 0; i < ${#args[@]}; i++)); do
  case "${args[$i]}" in
    http://*|https://*) url="${args[$i]}" ;;
    --directory-prefix) dir="${args[$((i + 1))]}" ;;
    --directory-prefix=*) dir="${args[$i]#*=}" ;;
  esac
done
name="$(basename "$url")"
root="${WORK:-/work}"
want="$(awk -v n="$name" '$2 == "sha256" && $4 ~ ("/" n "$") { print $3 }' "$root/sources.lock")"
vend="$root/vendor/$name"
if [ -n "$url" ] && [ -f "$vend" ]; then
  have="$(sha256sum "$vend" | cut -d' ' -f1)"
  if [ -z "$want" ] || [ "$want" != "$have" ]; then
    echo "wget shim: ERROR: vendored $name does not match sources.lock; refusing to fall back to the network" >&2
    exit 1
  fi
  echo "wget shim: using vendored copy of $name (sha256 verified)" >&2
  cp "$vend" "$dir/$name"
  exit 0
fi
/usr/bin/wget "$@" || exit $?
if [ -n "$url" ] && [ -n "$want" ]; then
  have="$(sha256sum "$dir/$name" | cut -d' ' -f1)"
  if [ "$have" != "$want" ]; then
    echo "wget shim: ERROR: downloaded $name has sha256 $have but sources.lock pins $want" >&2
    rm -f "$dir/$name"
    exit 1
  fi
  echo "wget shim: downloaded $name matches the pinned sha256" >&2
fi
SHIM
  chmod +x "$shim_dir/wget"
}

check_tools() {
  local t missing=""
  for t in gcc g++ make patch wget unzip curl git python3 javac bzip2; do
    command -v "$t" >/dev/null 2>&1 || missing="$missing $t"
  done
  [ -z "$missing" ] || die "missing tools in this image:$missing (run build-linux.sh, which builds docker/Dockerfile.builder)"
}

prepare_waf() {
  local want have
  want="$(lock_value waf sha256)"
  [ -n "$want" ] || die "sources.lock has no waf entry"
  if [ -f "$WORK/waf" ] && [ "$(sha256sum "$WORK/waf" | cut -d' ' -f1)" = "$want" ]; then
    cp "$WORK/waf" /tmp/waf
  else
    run_logged waf-download curl -fsSL https://waf.io/waf-2.0.24 -o /tmp/waf
  fi
  have="$(sha256sum /tmp/waf | cut -d' ' -f1)"
  [ "$have" = "$want" ] || die "waf has sha256 $have but sources.lock pins $want"
  chmod +x /tmp/waf
}

build_solver() {
  local solver="$1" sos so
  echo ""
  echo "=== $solver ($ARCH) ==="
  rm -rf "$BUILD/$solver"
  cp -a "$WORK/$solver" "$BUILD/$solver"
  rm -rf "$BUILD/$solver/build" "$BUILD/$solver"/.lock-waf* "$BUILD/$solver"/.waf3-*

  cd "$BUILD/$solver"
  run_logged "$solver-configure" python3 /tmp/waf configure
  cd "$BUILD"
  verify_sources "$solver"
  cd "$BUILD/$solver"
  run_logged "$solver-build" python3 /tmp/waf build -j "$(nproc)"

  sos=()
  while IFS= read -r so; do sos+=("$so"); done < <(find build -name '*.so' -type f)
  [ "${#sos[@]}" -eq 1 ] || die "$solver: expected exactly one .so under build/, found ${#sos[@]}"
  cp "${sos[0]}" "$OUT/"
  python3 "$WORK/check-native-lib.py" --arch "$ARCH" --max-glibc "$GLIBC_MAX" "$OUT/$(basename "${sos[0]}")" \
    || die "$solver: portability check failed"
  cd "$BUILD"
}

write_manifest() {
  local m="$OUT/MANIFEST.txt" f
  {
    echo "native solver libraries for linux-$ARCH"
    echo "built (UTC):      $(date -u +%Y-%m-%dT%H:%M:%SZ)"
    echo "pardinus commit:  ${PARDINUS_COMMIT:-unknown} (tracked files: ${PARDINUS_TREE:-unknown})"
    echo "base image:       ${BASE_IMAGE:-unknown}"
    echo "builder image:    ${BUILDER_IMAGE:-unknown}"
    echo "build OS:         $(. /etc/os-release && echo "$PRETTY_NAME"), glibc $(ldd --version | head -n1 | awk '{print $NF}')"
    echo "extra c/c++ flags: ${EXTRA_FLAGS:-none}"
    echo "verifier sha256:  $(sha256sum "$WORK/check-native-lib.py" | cut -d' ' -f1)"
    echo "compiler:         $(g++ --version | head -n1)"
    echo "jdk:              $(javac -version 2>&1)"
    echo "toolchain pkgs:   $(dpkg-query -W -f='${Package}=${Version} ' gcc g++ binutils libc6 wget git 2>/dev/null)"
    echo "waf sha256:       $(lock_value waf sha256)"
    echo "glibc ceiling:    $GLIBC_MAX"
    echo ""
    echo "pinned sources (sources.lock):"
    grep -v -e '^#' -e '^$' "$LOCK" | sed 's/^/  /'
    echo ""
    echo "libraries (sha256, bytes, name):"
    for f in "$OUT"/*.so; do
      echo "  $(sha256sum "$f" | cut -d' ' -f1)  $(stat -c %s "$f")  $(basename "$f")"
    done
  } > "$m"
}

main() {
  : "${ARCH:?ARCH is required}" "${SOLVERS:?SOLVERS is required}"
  GLIBC_MAX="${GLIBC_MAX:-2.31}"

  [ "$(uname -m)" = "$ARCH" ] \
    || die "container reports CPU $(uname -m) but ARCH=$ARCH was requested (is --platform being honored?)"

  check_tools

  JAVA_HOME="$(dirname "$(dirname "$(readlink -f "$(command -v javac)")")")"
  export JAVA_HOME

  EXTRA_FLAGS=""
  if [ "$ARCH" = "aarch64" ]; then
    EXTRA_FLAGS="-fsigned-char"
    export CFLAGS="$EXTRA_FLAGS" CXXFLAGS="$EXTRA_FLAGS"
  fi

  mkdir -p "$BUILD" "$OUT"
  rm -f "$OUT"/*.so "$OUT/MANIFEST.txt"
  prepare_waf
  install_wget_shim /tmp/shim
  export PATH="/tmp/shim:$PATH"

  local solver
  for solver in $SOLVERS; do
    build_solver "$solver"
  done

  write_manifest
  [ -n "${HOST_UID:-}" ] && chown -R "$HOST_UID:${HOST_GID:-$HOST_UID}" "$OUT" || true

  echo ""
  echo "=== all builds complete: linux-$ARCH ==="
  ls -l "$OUT"
}

if [ "${BASH_SOURCE[0]}" = "$0" ]; then
  main "$@"
fi
