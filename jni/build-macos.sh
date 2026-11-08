#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
LOCK="$SCRIPT_DIR/sources.lock"
. "$SCRIPT_DIR/lib-common.sh"

ALL_SOLVERS="minisat minisatp glucose lingeling"
MIN_OS="${MIN_OS:-12.0}"
ARCHS="x86_64 arm64"
SOLVERS=""
INSTALL_TO=""
DRY_RUN=0

usage() {
  cat <<'EOF'
Usage: build-macos.sh [--min-os VERSION] [--archs LIST] [--install-to DIR] [--dry-run] [SOLVER ...]

Builds universal macOS JNI solver libraries natively (no Docker) into output/macos/.

  --min-os VERSION  oldest macOS the libraries must run on (default 12.0; ARM Macs need 11.0 or later).
  --archs LIST      comma separated CPUs to build and combine (default x86_64,arm64).
  SOLVER ...        any of: minisat minisatp glucose lingeling   (minisatp builds libminisatprover)
                    Default: all four.
  --install-to DIR  after a successful build, copy the libraries and MANIFEST.txt into DIR.
  --dry-run         print what would run, without running it (works on any OS).

Needs a Mac with the Xcode command line tools and a JDK (JAVA_HOME, or the system default).
EOF
}

while [ $# -gt 0 ]; do
  case "$1" in
    --min-os) [ $# -ge 2 ] || die "--min-os needs a value"; MIN_OS="$2"; shift 2 ;;
    --archs) [ $# -ge 2 ] || die "--archs needs a value"; ARCHS="$(echo "$2" | tr ',' ' ')"; shift 2 ;;
    --install-to) [ $# -ge 2 ] || die "--install-to needs a directory"; INSTALL_TO="$2"; shift 2 ;;
    --dry-run) DRY_RUN=1; shift ;;
    -h|--help) usage; exit 0 ;;
    -*) die "unknown option: $1 (try --help)" ;;
    *)
      case " $ALL_SOLVERS " in
        *" $1 "*) SOLVERS="$SOLVERS $1"; shift ;;
        *) die "unknown solver '$1' (known: $ALL_SOLVERS)" ;;
      esac ;;
  esac
done

[ -n "$SOLVERS" ] || SOLVERS="$ALL_SOLVERS"
SOLVERS="$(echo $SOLVERS | tr ' ' '\n' | awk '!seen[$0]++' | tr '\n' ' ')"
SOLVERS="${SOLVERS% }"

for a in $ARCHS; do
  case "$a" in x86_64|arm64) ;; *) die "unknown architecture '$a' (use x86_64 or arm64)" ;; esac
done
echo "$MIN_OS" | grep -Eq '^[0-9]+(\.[0-9]+){0,2}$' || die "--min-os must look like 12.0, got '$MIN_OS'"

for required in lib-common.sh check-macho-lib.py sources.lock; do
  [ -f "$SCRIPT_DIR/$required" ] || die "missing $SCRIPT_DIR/$required"
done

lib_name_for() {
  case "$1" in
    minisat) echo libminisat ;;
    minisatp) echo libminisatprover ;;
    glucose) echo libglucose ;;
    lingeling) echo liblingeling ;;
  esac
}

arch_flags() { echo "-arch $1 -mmacosx-version-min=$MIN_OS"; }
link_flags() { echo "$(arch_flags "$1") -Wl,-dead_strip_dylibs -Wl,-install_name,@rpath/$2.dylib"; }

OUT="$SCRIPT_DIR/output/macos"

if [ "$DRY_RUN" = 1 ]; then
  echo "== dry run (nothing is executed): macOS build into $OUT"
  echo "   minimum macOS: $MIN_OS   CPUs: $ARCHS   solvers: $SOLVERS"
  echo "   export MACOSX_DEPLOYMENT_TARGET=$MIN_OS"
  for solver in $SOLVERS; do
    lib="$(lib_name_for "$solver")"
    for a in $ARCHS; do
      echo "   [$solver/$a] CFLAGS=CXXFLAGS=\"$(arch_flags "$a")\" LINKFLAGS=\"$(link_flags "$a" "$lib")\""
      echo "   [$solver/$a] python3 waf configure; verify pinned sources; python3 waf build"
    done
    echo "   [$solver] lipo -create $(for a in $ARCHS; do printf '%s ' "<$a/$lib.dylib>"; done)-output $OUT/$lib.dylib"
  done
  echo "   python3 check-macho-lib.py --archs $(echo $ARCHS | tr ' ' ',') --max-min-os $MIN_OS $OUT/*.dylib"
  echo "   write $OUT/MANIFEST.txt${INSTALL_TO:+; copy libraries and manifest to $INSTALL_TO}"
  exit 0
fi

[ "$(uname -s)" = "Darwin" ] || die "this script builds macOS libraries and must run on a Mac (use --dry-run to preview)"
missing=""
for tool in clang lipo python3 git patch tar unzip curl make xcrun; do
  command -v "$tool" >/dev/null 2>&1 || missing="$missing $tool"
done
[ -z "$missing" ] || die "missing tools:$missing (install the Xcode command line tools: xcode-select --install)"
if [ -z "${JAVA_HOME:-}" ]; then
  JAVA_HOME="$(/usr/libexec/java_home 2>/dev/null)" || die "no JDK found; install one or set JAVA_HOME"
fi
export JAVA_HOME
[ -f "$JAVA_HOME/include/jni.h" ] || die "JAVA_HOME ($JAVA_HOME) has no include/jni.h; a full JDK is required, not a JRE"

SCRATCH="$(mktemp -d "${TMPDIR:-/tmp}/pardinus-macos.XXXXXX")"
LOGS="$SCRATCH/logs"
trap 'rc=$?; if [ $rc -ne 0 ]; then echo "build failed; work files kept in $SCRATCH" >&2; else rm -rf "$SCRATCH"; fi' EXIT

prepare_waf "$SCRATCH/waf"
install_wget_shim "$SCRATCH/shim"
export PATH="$SCRATCH/shim:$PATH"
export PARDINUS_JNI_DIR="$SCRIPT_DIR"
export MACOSX_DEPLOYMENT_TARGET="$MIN_OS"
JOBS="$(sysctl -n hw.ncpu)"

rm -rf "$OUT"
mkdir -p "$OUT"

build_slice() {
  local solver="$1" arch="$2" lib="$3" work="$SCRATCH/$arch" found
  mkdir -p "$work"
  rm -rf "$work/$solver"
  cp -R "$SCRIPT_DIR/$solver" "$work/$solver"
  rm -rf "$work/$solver/build" "$work/$solver"/.lock-waf* "$work/$solver"/.waf3-*

  export CFLAGS="$(arch_flags "$arch")" CXXFLAGS="$(arch_flags "$arch")" LINKFLAGS="$(link_flags "$arch" "$lib")"
  ( cd "$work/$solver" && run_logged "$solver-$arch-configure" python3 "$SCRATCH/waf" configure )
  verify_sources "$solver" "$work"
  ( cd "$work/$solver" && run_logged "$solver-$arch-build" python3 "$SCRATCH/waf" build -j "$JOBS" )

  found="$(find "$work/$solver/build" -name '*.dylib' -type f)"
  [ "$(echo "$found" | grep -c .)" -eq 1 ] || die "$solver/$arch: expected exactly one .dylib under build/, found: ${found:-none}"
  mkdir -p "$SCRATCH/slices/$arch"
  cp "$found" "$SCRATCH/slices/$arch/$lib.dylib"
}

for solver in $SOLVERS; do
  lib="$(lib_name_for "$solver")"
  echo ""
  echo "=== $solver ($ARCHS) ==="
  inputs=""
  for arch in $ARCHS; do
    echo "  building $arch slice"
    build_slice "$solver" "$arch" "$lib"
    inputs="$inputs $SCRATCH/slices/$arch/$lib.dylib"
  done
  lipo -create $inputs -output "$OUT/$lib.dylib"
  python3 "$SCRIPT_DIR/check-macho-lib.py" --archs "$(echo $ARCHS | tr ' ' ',')" --max-min-os "$MIN_OS" "$OUT/$lib.dylib" \
    || die "$solver: portability check failed"
done

if command -v codesign >/dev/null 2>&1; then
  for f in "$OUT"/*.dylib; do
    if lipo -archs "$f" | tr ' ' '\n' | grep -qx arm64; then
      lipo -thin arm64 "$f" -output "$SCRATCH/arm64-slice.dylib"
      codesign --verify "$SCRATCH/arm64-slice.dylib" || die "$(basename "$f"): the arm64 slice has an invalid code signature"
    fi
  done
fi

PARDINUS_COMMIT="$(git -C "$SCRIPT_DIR" rev-parse HEAD 2>/dev/null || echo unknown)"
PARDINUS_TREE=clean
git -C "$SCRIPT_DIR" diff --quiet HEAD 2>/dev/null || PARDINUS_TREE=dirty
{
  echo "native solver libraries for macos"
  echo "built (UTC):        $(date -u +%Y-%m-%dT%H:%M:%SZ)"
  echo "pardinus commit:    $PARDINUS_COMMIT (tracked files: $PARDINUS_TREE)"
  echo "build host:         $(sw_vers -productName) $(sw_vers -productVersion), $(uname -m)"
  echo "xcode:              $(xcodebuild -version 2>/dev/null | tr '\n' ' ')"
  echo "compiler:           $(clang --version | head -n1)"
  echo "sdk:                $(xcrun --show-sdk-version) ($(xcrun --show-sdk-path))"
  echo "jdk:                $("$JAVA_HOME/bin/javac" -version 2>&1)"
  echo "deployment target:  macOS $MIN_OS"
  echo "cpus:               $ARCHS"
  echo "link flags:         -Wl,-dead_strip_dylibs -Wl,-install_name,@rpath/<library>.dylib"
  echo "verifier sha256:    $(sha256_of_file "$SCRIPT_DIR/check-macho-lib.py")"
  echo "waf sha256:         $(lock_value waf sha256)"
  echo ""
  echo "pinned sources (sources.lock):"
  grep -v -e '^#' -e '^$' "$LOCK" | sed 's/^/  /'
  echo ""
  echo "libraries (sha256, bytes, name):"
  for f in "$OUT"/*.dylib; do
    echo "  $(sha256_of_file "$f")  $(wc -c < "$f" | tr -d ' ')  $(basename "$f")"
  done
} > "$OUT/MANIFEST.txt"

echo ""
echo "=== all builds complete: macos ==="
ls -l "$OUT"

if [ -n "$INSTALL_TO" ]; then
  mkdir -p "$INSTALL_TO"
  cp "$OUT"/*.dylib "$OUT/MANIFEST.txt" "$INSTALL_TO/"
  echo "installed into $INSTALL_TO"
fi
