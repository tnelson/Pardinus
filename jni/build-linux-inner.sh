#!/usr/bin/env bash

set -euo pipefail

WORK=/work
OUT=/output
BUILD=/tmp/build
LOGS=/tmp/logs
LOCK="$WORK/sources.lock"

# Load shared helpers
SCRIPT_DIR="$WORK"
. "$WORK/lib-common.sh"

check_tools() {
  local t missing=""
  for t in gcc g++ make patch wget unzip curl git python3 javac bzip2; do
    command -v "$t" >/dev/null 2>&1 || missing="$missing $t"
  done
  [ -z "$missing" ] || die "missing tools in this image:$missing (run build-linux.sh, which builds docker/Dockerfile.builder)"
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
  verify_sources "$solver" "$BUILD"
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
  prepare_waf /tmp/waf
  install_wget_shim /tmp/shim
  export PARDINUS_JNI_DIR="$WORK"
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
