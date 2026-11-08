#!/usr/bin/env bash

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
GLIBC_MAX="${GLIBC_MAX:-2.31}"

die() { echo "error: $*" >&2; exit 1; }

usage() {
  cat <<'EOF'
Usage: test-linux.sh --classpath PATH [--classpath PATH ...] [--arch ARCH] [--libs DIR] [--dry-run] [--shell]

  --classpath PATH  Java classes to test against: a directory of compiled Pardinus classes
                    (for example ../target/classes after `mvn compile`) or a jar, plus any
                    dependency jars. Repeatable.
  --arch ARCH       x86_64 (alias amd64) or aarch64 (alias arm64). Default: this machine.
  --libs DIR        libraries to test. Default: output/linux-<arch>/ (output of build-linux.sh).
  --dry-run         print the docker command without running it.
  --shell           open a shell in the test container.
EOF
}

abs_path() {
  if [ -d "$1" ]; then
    (cd "$1" && pwd)
  elif [ -f "$1" ]; then
    echo "$(cd "$(dirname "$1")" && pwd)/$(basename "$1")"
  else
    die "path does not exist: $1"
  fi
}

ARCH=""
LIBS=""
CP_ARGS=()
DRY_RUN=0
SHELL_MODE=0
while [ $# -gt 0 ]; do
  case "$1" in
    --classpath) [ $# -ge 2 ] || die "--classpath needs a value"; CP_ARGS+=("$2"); shift 2 ;;
    --libs) [ $# -ge 2 ] || die "--libs needs a directory"; LIBS="$2"; shift 2 ;;
    --arch)
      [ $# -ge 2 ] || die "--arch needs a value"
      case "$2" in
        x86_64|amd64) ARCH="x86_64" ;;
        aarch64|arm64) ARCH="aarch64" ;;
        *) die "unknown architecture '$2' (use x86_64 or aarch64)" ;;
      esac
      shift 2 ;;
    --dry-run) DRY_RUN=1; shift ;;
    --shell) SHELL_MODE=1; shift ;;
    -h|--help) usage; exit 0 ;;
    *) die "unknown argument: $1 (try --help)" ;;
  esac
done

if [ -z "$ARCH" ]; then
  case "$(uname -m)" in
    x86_64|amd64) ARCH="x86_64" ;;
    aarch64|arm64) ARCH="aarch64" ;;
    *) die "cannot infer an architecture; pass --arch" ;;
  esac
fi
case "$ARCH" in
  x86_64) PLATFORM="linux/amd64" ;;
  aarch64) PLATFORM="linux/arm64" ;;
esac

[ "${#CP_ARGS[@]}" -ge 1 ] || die "at least one --classpath is required (try --help)"
[ -n "$LIBS" ] || LIBS="$SCRIPT_DIR/output/linux-$ARCH"
[ -d "$LIBS" ] || die "no libraries directory at $LIBS (build first with build-linux.sh, or pass --libs)"
LIBS="$(abs_path "$LIBS")"

MOUNTS=()
CP=""
i=0
for entry in "${CP_ARGS[@]}"; do
  abs="$(abs_path "$entry")"
  if [ -d "$abs" ]; then
    MOUNTS+=(-v "$abs:/cp/$i:ro")
    CP="$CP:/cp/$i:/cp/$i/*"
  else
    MOUNTS+=(-v "$abs:/cp/$i.jar:ro")
    CP="$CP:/cp/$i.jar"
  fi
  i=$((i + 1))
done
CP="${CP#:}"

if [ "$DRY_RUN" = 0 ]; then
  command -v docker >/dev/null 2>&1 || die "docker is not installed or not on PATH"
  docker info >/dev/null 2>&1 || die "the docker daemon is not reachable (is Docker running?)"
fi

IMAGE_ARGS=(--image-tag --arch "$ARCH")
[ "$DRY_RUN" = 1 ] && IMAGE_ARGS+=(--dry-run)
TAG="$("$SCRIPT_DIR/build-linux.sh" "${IMAGE_ARGS[@]}")"

if [ "$SHELL_MODE" = 1 ]; then
  CMD=(docker run --rm -it --platform "$PLATFORM"
       -v "$SCRIPT_DIR:/work:ro" -v "$LIBS:/libs:ro" "${MOUNTS[@]}" -w /tmp
       -e "ARCH=$ARCH" -e "GLIBC_MAX=$GLIBC_MAX" -e "CLASSPATH_IN=$CP" "$TAG" bash)
else
  CMD=(docker run --rm --platform "$PLATFORM"
       -v "$SCRIPT_DIR:/work:ro" -v "$LIBS:/libs:ro" "${MOUNTS[@]}" -w /tmp
       -e "ARCH=$ARCH" -e "GLIBC_MAX=$GLIBC_MAX" -e "CLASSPATH_IN=$CP"
       "$TAG" bash /work/test-linux-inner.sh)
fi

echo "== testing linux-$ARCH libraries in $LIBS (image $TAG)"
if [ "$DRY_RUN" = 1 ]; then
  printf '   '; printf '%q ' "${CMD[@]}"; echo
  exit 0
fi
"${CMD[@]}"
