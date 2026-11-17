#!/usr/bin/env bash
# This script only works on MacOS. It builds all native libraries for Forge (except the 
# outdated 32-bit ones), installs them and a Kodkod JAR file into Forge, and then runs 
# Forge's native-library test suite (for MacOS only).
# It requires Docker to be running (with x86_64 emulation), Xcode, JDK, Maven, Racket.

# Step 1: cd to the jni folder inside Pardinus
# ./build-all-macos.sh <forge repo location>

set -euo pipefail

# There are some common helpers that all the build scripts share.
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
. "$SCRIPT_DIR/lib-common.sh"

# Resolve paths to Forge, Pardinus, etc.
FORGE="${1:?usage: build-all-macos.sh FORGE_DIR}"
[ -d "$FORGE/forge/pardinus-cli/jar/native" ] || die "$FORGE does not look like a Forge repo"
FORGE="$(cd "$FORGE" && pwd)"
JAR="$FORGE/forge/pardinus-cli/jar"
NATIVE="$JAR/native"

PARDINUS="$(cd "$SCRIPT_DIR/.." && pwd)"
if [ -n "$(git -C "$PARDINUS" status --porcelain --untracked-files=no)" ]; then
  echo "WARNING: Pardinus has uncommitted changes; the MANIFESTs will record a modified tree." >&2
fi

step() { echo; echo "=== $* ==="; }

# Build native libraries
cd "$SCRIPT_DIR"
for arch in x86_64 aarch64; do
  step "linux-$arch"
  ./build-linux.sh --arch "$arch" --install-to "$NATIVE/linux-$arch"
done
for arch in x86_64 arm64; do
  step "windows-$arch"
  ./build-windows.sh --arch "$arch" --install-to "$NATIVE/windows-$arch"
done
step "macos"
./build-macos.sh --install-to "$NATIVE/macos"

# Build Kodkod JAR file
step "kodkod.jar"
racket "$FORGE/forge/pardinus-cli/install-pardinus-jar.rkt" "$PARDINUS"

CP=(--classpath "$JAR/kodkod.jar")
for j in "$JAR"/org.sat4j.*.jar; do CP+=(--classpath "$j"); done
for arch in x86_64 aarch64; do
  step "test linux-$arch"
  ./test-linux.sh --arch "$arch" --libs "$NATIVE/linux-$arch" "${CP[@]}"
done

# Test (MacOS and Linux only. Other platforms are run in CI.)
step "test macos"
./test-macos.sh --libs "$NATIVE/macos" "${CP[@]}"
bash "$NATIVE/test-native.sh" --dir macos

step "done"