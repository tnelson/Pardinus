#!/usr/bin/env bash

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
LOCK="$SCRIPT_DIR/sources.lock"
BASE_IMAGE="${BASE_IMAGE:-ubuntu:22.04@sha256:076e7bf82319619f28dd0aa9c02ab34b055ad37100395b4f49a2ffba04fb5e11}"
ALL_SOLVERS="minisat minisatp glucose lingeling"

. "$SCRIPT_DIR/lib-common.sh"

usage() {
  cat <<'EOF'
Usage: build-windows.sh [--arch ARCH] [--install-to DIR] [--rebuild-image] [--dry-run] [--shell] [SOLVER ...]

Cross-compiles Windows JNI solver libraries (.dll) inside Docker, on any Linux, macOS or Windows
machine that runs Docker. Nothing needs to run on Windows to build.

  --arch ARCH       x86_64 (alias amd64), arm64 (alias aarch64), or all.
                    Default: all. This names the Windows CPU the libraries are for; it does not
                    have to match the CPU of the machine doing the build.
  SOLVER ...        any of: minisat minisatp glucose lingeling   (minisatp builds minisatprover.dll)
                    Default: all four.
  --install-to DIR  after a successful single-arch build, copy the libraries and MANIFEST.txt
                    into DIR (any directory you like; it is created if needed).
  --rebuild-image   rebuild the builder image from scratch (no cache).
  --dry-run         print the docker commands without running them.
  --shell           open a shell in the build container instead of building (for debugging).

Environment: BASE_IMAGE (default: ubuntu:22.04 pinned by digest).
Output: output/windows-<arch>/*.dll and MANIFEST.txt
EOF
}

normalize_arch() {
  case "$1" in
    x86_64|amd64) echo "x86_64" ;;
    arm64|aarch64) echo "arm64" ;;
    all) echo "x86_64 arm64" ;;
    *) die "unknown architecture '$1' (use x86_64, arm64, or all)" ;;
  esac
}

ARCHES=""
SOLVERS=""
INSTALL_TO=""
DRY_RUN=0
SHELL_MODE=0
REBUILD_IMAGE=0

while [ $# -gt 0 ]; do
  case "$1" in
    --arch)
      [ $# -ge 2 ] || die "--arch needs a value"
      ARCHES="$ARCHES $(normalize_arch "$2")"
      shift 2 ;;
    --install-to)
      [ $# -ge 2 ] || die "--install-to needs a directory"
      INSTALL_TO="$2"
      shift 2 ;;
    --dry-run) DRY_RUN=1; shift ;;
    --rebuild-image) REBUILD_IMAGE=1; shift ;;
    --shell) SHELL_MODE=1; shift ;;
    -h|--help) usage; exit 0 ;;
    -*) die "unknown option: $1 (try --help)" ;;
    *)
      case " $ALL_SOLVERS " in
        *" $1 "*) SOLVERS="$SOLVERS $1"; shift ;;
        *) die "unknown solver '$1' (known: $ALL_SOLVERS)" ;;
      esac ;;
  esac
done

[ -n "$ARCHES" ] || ARCHES="x86_64 arm64"
[ -n "$SOLVERS" ] || SOLVERS="$ALL_SOLVERS"
ARCHES="$(echo $ARCHES | tr ' ' '\n' | awk '!seen[$0]++' | tr '\n' ' ')"
SOLVERS="$(echo $SOLVERS | tr ' ' '\n' | awk '!seen[$0]++' | tr '\n' ' ')"
ARCHES="${ARCHES% }"
SOLVERS="${SOLVERS% }"

if [ -n "$INSTALL_TO" ] && [ "$(echo $ARCHES | wc -w | tr -d ' ')" -ne 1 ]; then
  die "--install-to works with exactly one architecture"
fi

if [ "$DRY_RUN" = 0 ]; then
  command -v docker >/dev/null 2>&1 || die "docker is not installed or not on PATH"
  docker info >/dev/null 2>&1 || die "the docker daemon is not reachable (is Docker running?)"
fi

for required in build-windows-inner.sh check-pe-lib.py lib-common.sh sources.lock docker/Dockerfile.windows windows/compat/zlib.h; do
  [ -f "$SCRIPT_DIR/$required" ] || die "missing $SCRIPT_DIR/$required"
done

case "$(uname -m)" in
  x86_64|amd64) HOST_KEY=x86_64; PLATFORM=linux/amd64 ;;
  aarch64|arm64) HOST_KEY=aarch64; PLATFORM=linux/arm64 ;;
  *) die "cannot infer this machine's CPU from '$(uname -m)'" ;;
esac

TOOLCHAIN_SHA256="$(lock_value "llvm-mingw-$HOST_KEY" sha256)"
[ -n "$TOOLCHAIN_SHA256" ] || die "sources.lock has no llvm-mingw-$HOST_KEY entry"
TOOLCHAIN_FILE="$(awk -v n="llvm-mingw-$HOST_KEY" '$1 == n && $2 == "sha256" { print $4 }' "$LOCK")"
TOOLCHAIN_VERSION="$(echo "$TOOLCHAIN_FILE" | sed -E 's/^llvm-mingw-([0-9]+)-.*/\1/')"
TOOLCHAIN_URL="https://github.com/mstorsjo/llvm-mingw/releases/download/$TOOLCHAIN_VERSION/$TOOLCHAIN_FILE"

sha256_stdin() {
  if command -v sha256sum >/dev/null 2>&1; then sha256sum | cut -d' ' -f1; else shasum -a 256 | cut -d' ' -f1; fi
}

IMAGE_HASH="$( (cat "$SCRIPT_DIR/docker/Dockerfile.windows"; echo "$BASE_IMAGE"; echo "$TOOLCHAIN_SHA256") | sha256_stdin | cut -c1-12 )"
TAG="pardinus-windows-builder:$IMAGE_HASH-$HOST_KEY"

PARDINUS_COMMIT="$(git -C "$SCRIPT_DIR" rev-parse HEAD 2>/dev/null || echo unknown)"
PARDINUS_TREE=clean
git -C "$SCRIPT_DIR" diff --quiet HEAD 2>/dev/null || PARDINUS_TREE=dirty

NOCACHE=""
[ "$REBUILD_IMAGE" = 1 ] && NOCACHE="--no-cache"
BUILD_CMD=(docker build ${NOCACHE:+"$NOCACHE"} --platform "$PLATFORM" --build-arg "BASE_IMAGE=$BASE_IMAGE"
           --build-arg "TOOLCHAIN_URL=$TOOLCHAIN_URL" --build-arg "TOOLCHAIN_SHA256=$TOOLCHAIN_SHA256"
           -t "$TAG" -f "$SCRIPT_DIR/docker/Dockerfile.windows" "$SCRIPT_DIR/docker")

build_one() {
  local arch="$1" out cmd
  out="$SCRIPT_DIR/output/windows-$arch"

  if [ "$SHELL_MODE" = 1 ]; then
    cmd=(docker run --rm -it --platform "$PLATFORM"
         -v "$SCRIPT_DIR:/work:ro" -v "$out:/output" -w /work
         -e "TARGET=$arch" -e "SOLVERS=${SOLVERS# }"
         "$TAG" bash)
  else
    cmd=(docker run --rm --platform "$PLATFORM"
         -v "$SCRIPT_DIR:/work:ro" -v "$out:/output" -w /work
         -e "TARGET=$arch" -e "SOLVERS=${SOLVERS# }"
         -e "PARDINUS_COMMIT=$PARDINUS_COMMIT" -e "PARDINUS_TREE=$PARDINUS_TREE"
         -e "BASE_IMAGE=$BASE_IMAGE" -e "BUILDER_IMAGE=$TAG"
         -e "HOST_UID=$(id -u)" -e "HOST_GID=$(id -g)"
         "$TAG" bash /work/build-windows-inner.sh)
  fi

  echo "== windows-$arch: builder image $TAG ($PLATFORM), solvers:${SOLVERS# }"
  if [ "$DRY_RUN" = 1 ]; then
    echo "   (build the image if it does not exist; always with --rebuild-image)"
    printf '   '; printf '%q ' "${BUILD_CMD[@]}"; echo
    printf '   '; printf '%q ' "${cmd[@]}"; echo
    return 0
  fi

  if [ "$REBUILD_IMAGE" = 1 ] || ! docker image inspect "$TAG" >/dev/null 2>&1; then
    echo "== building builder image $TAG (once; later runs reuse it)"
    "${BUILD_CMD[@]}"
  fi

  mkdir -p "$out"
  "${cmd[@]}"

  if [ "$SHELL_MODE" = 0 ]; then
    echo "== windows-$arch: output in $out"
    ls -l "$out"
    if [ -n "$INSTALL_TO" ]; then
      mkdir -p "$INSTALL_TO"
      cp "$out"/*.dll "$out/MANIFEST.txt" "$INSTALL_TO/"
      echo "== installed into $INSTALL_TO"
    fi
  fi
}

for arch in $ARCHES; do
  build_one "$arch"
done
