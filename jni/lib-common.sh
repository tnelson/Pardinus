#!/usr/bin/env bash

die() { echo "ERROR: $*" >&2; exit 1; }

sha256_of_file() {
  if command -v sha256sum >/dev/null 2>&1; then
    sha256sum "$1" | cut -d' ' -f1
  else
    shasum -a 256 "$1" | cut -d' ' -f1
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
  local solver="$1" root="$2" name kind value path have found=0
  while read -r name kind value path; do
    case "$name" in ''|'#'*) continue ;; esac
    [ "$name" = "$solver" ] || continue
    found=1
    case "$kind" in
      sha256)
        [ -f "$root/$path" ] || die "$solver: expected fetched file $path is missing"
        have="$(sha256_of_file "$root/$path")"
        if [ "$have" != "$value" ]; then
          die "$solver: $path has sha256 $have but sources.lock pins $value (upstream changed, or a bad download)"
        fi
        echo "  $solver: $path matches pinned sha256"
        ;;
      git)
        [ -d "$root/$path/.git" ] || die "$solver: expected git checkout at $path is missing"
        have="$(git -C "$root/$path" rev-parse HEAD)"
        if [ "$have" != "$value" ]; then
          git -C "$root/$path" checkout --quiet --detach "$value" \
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
sha256_of() {
  if command -v sha256sum >/dev/null 2>&1; then
    sha256sum "$1" | cut -d' ' -f1
  else
    shasum -a 256 "$1" | cut -d' ' -f1
  fi
}
url=""; dir="."
args=("$@")
for ((i = 0; i < ${#args[@]}; i++)); do
  case "${args[$i]}" in
    http://*|https://*) url="${args[$i]}" ;;
    --directory-prefix) dir="${args[$((i + 1))]}" ;;
    --directory-prefix=*) dir="${args[$i]#*=}" ;;
  esac
done
[ -n "$url" ] || { echo "wget shim: no URL given" >&2; exit 2; }
name="$(basename "$url")"
root="${PARDINUS_JNI_DIR:?PARDINUS_JNI_DIR must point at the jni directory}"
want="$(awk -v n="$name" '$2 == "sha256" && $4 ~ ("/" n "$") { print $3 }' "$root/sources.lock")"
vend="$root/vendor/$name"
if [ -f "$vend" ]; then
  have="$(sha256_of "$vend")"
  if [ -z "$want" ] || [ "$want" != "$have" ]; then
    echo "wget shim: ERROR: vendored $name does not match sources.lock; refusing to fall back to the network" >&2
    exit 1
  fi
  echo "wget shim: using vendored copy of $name (sha256 verified)" >&2
  cp "$vend" "$dir/$name"
  exit 0
fi
curl -fsSL --retry 3 -o "$dir/$name" "$url" || exit $?
if [ -n "$want" ]; then
  have="$(sha256_of "$dir/$name")"
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

prepare_waf() {
  local dest="$1" want
  want="$(lock_value waf sha256)"
  [ -n "$want" ] || die "sources.lock has no waf entry"
  if [ -f "$SCRIPT_DIR/waf" ] && [ "$(sha256_of_file "$SCRIPT_DIR/waf")" = "$want" ]; then
    cp "$SCRIPT_DIR/waf" "$dest"
  else
    curl -fsSL --retry 3 -o "$dest" https://waf.io/waf-2.0.24 || die "could not download waf"
  fi
  [ "$(sha256_of_file "$dest")" = "$want" ] || die "waf does not match the sha256 pinned in sources.lock"
  chmod +x "$dest"
}

run_logged() {
  local name="$1"; shift
  mkdir -p "$LOGS"
  if ! "$@" >"$LOGS/$name.log" 2>&1; then
    echo "FAILED: $* (last lines of $LOGS/$name.log):" >&2
    tail -n 40 "$LOGS/$name.log" >&2
    exit 1
  fi
}
