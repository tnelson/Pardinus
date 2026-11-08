#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
MIN_OS="${MIN_OS:-12.0}"

die() { echo "error: $*" >&2; exit 1; }

usage() {
  cat <<'EOF'
Usage: test-macos.sh --classpath PATH [--classpath PATH ...] [--arch arm64|x86_64] [--libs DIR] [--dry-run]

Tests the macOS libraries on this Mac with a real JVM: checks each library's structure
(check-macho-lib.py), then loads each solver and solves small satisfiable and unsatisfiable
formulas, and gets an unsat core from the proof-logging solver (NativeSolverTest.java).

  --classpath PATH  Java classes to test against: a directory of compiled Pardinus classes
                    (for example ../target/classes after `mvn compile`) or a jar, plus any
                    dependency jars. Repeatable.
  --arch CPU        which slice to run: arm64 or x86_64. Default: this Mac's CPU. Running the
                    other one needs Rosetta and a JDK that has that CPU (set JAVA_HOME to it).
  --libs DIR        libraries to test. Default: output/macos/.
  --dry-run         print what would run.
EOF
}

abs_path() {
  if [ -d "$1" ]; then (cd "$1" && pwd)
  elif [ -f "$1" ]; then echo "$(cd "$(dirname "$1")" && pwd)/$(basename "$1")"
  else die "path does not exist: $1"
  fi
}

ARCH=""
LIBS=""
CP_ARGS=()
DRY_RUN=0
while [ $# -gt 0 ]; do
  case "$1" in
    --classpath) [ $# -ge 2 ] || die "--classpath needs a value"; CP_ARGS+=("$2"); shift 2 ;;
    --libs) [ $# -ge 2 ] || die "--libs needs a directory"; LIBS="$2"; shift 2 ;;
    --arch)
      [ $# -ge 2 ] || die "--arch needs a value"
      case "$2" in
        arm64|aarch64) ARCH="arm64" ;;
        x86_64|amd64) ARCH="x86_64" ;;
        *) die "unknown architecture '$2' (use arm64 or x86_64)" ;;
      esac
      shift 2 ;;
    --dry-run) DRY_RUN=1; shift ;;
    -h|--help) usage; exit 0 ;;
    *) die "unknown argument: $1 (try --help)" ;;
  esac
done

[ "${#CP_ARGS[@]}" -ge 1 ] || die "at least one --classpath is required (try --help)"
[ -n "$LIBS" ] || LIBS="$SCRIPT_DIR/output/macos"
if [ -d "$LIBS" ]; then
  LIBS="$(abs_path "$LIBS")"
elif [ "$DRY_RUN" = 0 ]; then
  die "no libraries directory at $LIBS (build first with build-macos.sh, or pass --libs)"
fi

HOST="$(uname -m)"
[ -n "$ARCH" ] || { [ "$HOST" = "x86_64" ] && ARCH="x86_64" || ARCH="arm64"; }
RUN_PREFIX=""
HOST_NAME="$HOST"
[ "$HOST" = "aarch64" ] && HOST_NAME="arm64"
[ "$ARCH" = "$HOST_NAME" ] || RUN_PREFIX="arch -$ARCH"

CP=""
for entry in "${CP_ARGS[@]}"; do
  abs="$(abs_path "$entry")"
  if [ -d "$abs" ]; then CP="$CP:$abs:$abs/*"; else CP="$CP:$abs"; fi
done
CP="${CP#:}"

JAVA_BIN="java"
JAVAC_BIN="javac"
if [ -n "${JAVA_HOME:-}" ]; then JAVA_BIN="$JAVA_HOME/bin/java"; JAVAC_BIN="$JAVA_HOME/bin/javac"; fi

CLASS_DIR="${TMPDIR:-/tmp}/pardinus-macos-test-classes"

if [ "$DRY_RUN" = 1 ]; then
  echo "== dry run: testing macOS $ARCH slice of the libraries in $LIBS"
  echo "   python3 check-macho-lib.py --archs x86_64,arm64 --max-min-os $MIN_OS $LIBS/*.dylib"
  echo "   $JAVAC_BIN -cp \"$CP\" -d $CLASS_DIR NativeSolverTest.java"
  echo "   ${RUN_PREFIX:+$RUN_PREFIX }$JAVA_BIN -Djava.library.path=$LIBS -cp \"$CP:$CLASS_DIR\" NativeSolverTest"
  exit 0
fi

[ "$(uname -s)" = "Darwin" ] || die "this script tests macOS libraries and must run on a Mac"
ls "$LIBS"/*.dylib >/dev/null 2>&1 || die "no .dylib files in $LIBS"

echo "=== structure checks (check-macho-lib.py) ==="
python3 "$SCRIPT_DIR/check-macho-lib.py" --archs x86_64,arm64 --max-min-os "$MIN_OS" "$LIBS"/*.dylib

echo ""
echo "=== JVM solve tests, $ARCH slice (kodkod SATFactory) ==="
rm -rf "$CLASS_DIR"
mkdir -p "$CLASS_DIR"
"$JAVAC_BIN" -cp "$CP" -d "$CLASS_DIR" "$SCRIPT_DIR/NativeSolverTest.java"
$RUN_PREFIX "$JAVA_BIN" -Djava.library.path="$LIBS" -cp "$CP:$CLASS_DIR" NativeSolverTest

echo ""
echo "=== ALL CHECKS PASSED ==="
