#!/usr/bin/env bash

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
BASE_IMAGE="${BASE_IMAGE:-ubuntu:20.04@sha256:8feb4d8ca5354def3d8fce243717141ce31e2c428701f6682bd2fafe15388214}"
GLIBC_MAX="${GLIBC_MAX:-2.31}"
ALL_SOLVERS="minisat minisatp glucose lingeling"

die() { echo "error: $*" >&2; exit 1; }

usage() {
  cat <<'EOF'
Usage: build-linux.sh [--arch ARCH] [--install-to DIR] [--rebuild-image] [--dry-run] [--shell]
                      [--image-tag] [SOLVER ...]

  --arch ARCH       x86_64 (alias amd64), aarch64 (alias arm64), or all.
                    Default: this machine's CPU.
  SOLVER ...        any of: minisat minisatp glucose lingeling   (minisatp builds libminisatprover)
                    Default: all four.
  --install-to DIR  after a successful single-arch build, copy the libraries and MANIFEST.txt
                    into DIR (any directory you like; it is created if needed).
  --rebuild-image   rebuild the builder image from scratch (no cache), e.g. to pick up newer
                    package versions. Otherwise an existing image for this Dockerfile is reused.
  --dry-run         print the docker commands without running them.
  --shell           open a shell in the build container instead of building (for debugging).
  --image-tag       print the builder image's tag for --arch (building the image first if it does
                    not exist) and exit. Used by test-linux.sh so both use the same image.

Environment: BASE_IMAGE (default: ubuntu:20.04 pinned by digest), GLIBC_MAX (default 2.31).
Output: output/linux-<arch>/lib*.so and MANIFEST.txt
EOF
}

normalize_arch() {
  case "$1" in
    x86_64|amd64) echo "x86_64" ;;
    aarch64|arm64) echo "aarch64" ;;
    all) echo "x86_64 aarch64" ;;
    *) die "unknown architecture '$1' (use x86_64, aarch64, or all)" ;;
  esac
}

platform_for() {
  case "$1" in
    x86_64) echo "linux/amd64" ;;
    aarch64) echo "linux/arm64" ;;
    *) die "no docker platform for '$1'" ;;
  esac
}

host_arch() {
  case "$(uname -m)" in
    x86_64|amd64) echo "x86_64" ;;
    aarch64|arm64) echo "aarch64" ;;
    *) die "cannot infer an architecture from '$(uname -m)'; pass --arch" ;;
  esac
}

ARCHES=""
SOLVERS=""
INSTALL_TO=""
DRY_RUN=0
SHELL_MODE=0
REBUILD_IMAGE=0
IMAGE_TAG_MODE=0

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
    --image-tag) IMAGE_TAG_MODE=1; shift ;;
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

[ -n "$ARCHES" ] || ARCHES="$(host_arch)"
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

for required in build-linux-inner.sh check-native-lib.py sources.lock docker/Dockerfile.builder; do
  [ -f "$SCRIPT_DIR/$required" ] || die "missing $SCRIPT_DIR/$required"
done

sha256_stdin() {
  if command -v sha256sum >/dev/null 2>&1; then sha256sum | cut -d' ' -f1; else shasum -a 256 | cut -d' ' -f1; fi
}

builder_tag() {
  local h
  h="$( (cat "$SCRIPT_DIR/docker/Dockerfile.builder"; echo "$BASE_IMAGE") | sha256_stdin | cut -c1-12 )"
  echo "pardinus-native-builder:$h-$1"
}

set_build_cmd() {
  local platform="$1" tag="$2" nocache=""
  [ "$REBUILD_IMAGE" = 1 ] && nocache="--no-cache"
  BUILD_CMD=(docker build ${nocache:+"$nocache"} --platform "$platform" --build-arg "BASE_IMAGE=$BASE_IMAGE"
             -t "$tag" -f "$SCRIPT_DIR/docker/Dockerfile.builder" "$SCRIPT_DIR/docker")
}

PARDINUS_COMMIT="$(git -C "$SCRIPT_DIR" rev-parse HEAD 2>/dev/null || echo unknown)"
PARDINUS_TREE=clean
git -C "$SCRIPT_DIR" diff --quiet HEAD 2>/dev/null || PARDINUS_TREE=dirty

build_one() {
  local arch="$1" platform out tag
  platform="$(platform_for "$arch")"
  out="$SCRIPT_DIR/output/linux-$arch"
  tag="$(builder_tag "$arch")"

  set_build_cmd "$platform" "$tag"
  local build_cmd=("${BUILD_CMD[@]}")

  local cmd
  if [ "$SHELL_MODE" = 1 ]; then
    cmd=(docker run --rm -it --platform "$platform"
         -v "$SCRIPT_DIR:/work:ro" -v "$out:/output" -w /work
         -e "ARCH=$arch" -e "SOLVERS=${SOLVERS# }" -e "GLIBC_MAX=$GLIBC_MAX"
         "$tag" bash)
  else
    cmd=(docker run --rm --platform "$platform"
         -v "$SCRIPT_DIR:/work:ro" -v "$out:/output" -w /work
         -e "ARCH=$arch" -e "SOLVERS=${SOLVERS# }" -e "GLIBC_MAX=$GLIBC_MAX"
         -e "PARDINUS_COMMIT=$PARDINUS_COMMIT" -e "PARDINUS_TREE=$PARDINUS_TREE"
         -e "BASE_IMAGE=$BASE_IMAGE" -e "BUILDER_IMAGE=$tag"
         -e "HOST_UID=$(id -u)" -e "HOST_GID=$(id -g)"
         "$tag" bash /work/build-linux-inner.sh)
  fi

  echo "== linux-$arch: builder image $tag ($platform), solvers:${SOLVERS% }"
  if [ "$DRY_RUN" = 1 ]; then
    echo "   (build the image if it does not exist; always with --rebuild-image)"
    printf '   '; printf '%q ' "${build_cmd[@]}"; echo
    printf '   '; printf '%q ' "${cmd[@]}"; echo
    return 0
  fi

  if [ "$REBUILD_IMAGE" = 1 ] || ! docker image inspect "$tag" >/dev/null 2>&1; then
    echo "== building builder image $tag (once; later runs reuse it)"
    "${build_cmd[@]}"
  fi

  mkdir -p "$out"
  "${cmd[@]}"

  if [ "$SHELL_MODE" = 0 ]; then
    echo "== linux-$arch: output in $out"
    ls -l "$out"
    if [ -n "$INSTALL_TO" ]; then
      mkdir -p "$INSTALL_TO"
      cp "$out"/*.so "$out/MANIFEST.txt" "$INSTALL_TO/"
      echo "== installed into $INSTALL_TO"
    fi
  fi
}

if [ "$IMAGE_TAG_MODE" = 1 ]; then
  [ "$(echo $ARCHES | wc -w | tr -d ' ')" -eq 1 ] || die "--image-tag works with exactly one architecture"
  arch="$ARCHES"
  platform="$(platform_for "$arch")"
  tag="$(builder_tag "$arch")"
  if [ "$DRY_RUN" = 0 ] && { [ "$REBUILD_IMAGE" = 1 ] || ! docker image inspect "$tag" >/dev/null 2>&1; }; then
    set_build_cmd "$platform" "$tag"
    echo "== building builder image $tag (once; later runs reuse it)" >&2
    "${BUILD_CMD[@]}" >&2
  fi
  echo "$tag"
  exit 0
fi

for arch in $ARCHES; do
  build_one "$arch"
done
