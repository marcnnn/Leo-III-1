#!/usr/bin/env bash
# Builds Leo-III from this source tree in user space and installs a launcher at
# $PREFIX/leo3/bin/leo3 (default PREFIX=~/tools). No root needed: a Temurin JDK
# and the sbt launcher are downloaded into $PREFIX if missing.
#
# Run on the build host from the repository root (or pass it as $1):
#   scripts/leo3_build.sh [repo_root]
#
# The source tree carries local changes (e.g. --instantiate-sets), so the
# official v1.8.x release jars are not used. picosat (contrib/picosat-965.tar.gz)
# is no longer referenced by the sources or the Makefile and is not built.
set -euo pipefail

REPO=$(cd "${1:-.}" && pwd)
PREFIX=${PREFIX:-$HOME/tools}
JDK_VERSION=${JDK_VERSION:-21}
SBT_VERSION=${SBT_VERSION:-1.13.0}

case "$(uname -m)" in
  aarch64 | arm64) ARCH=aarch64 ;;
  x86_64) ARCH=x64 ;;
  *) echo "unsupported arch $(uname -m)" >&2; exit 1 ;;
esac

mkdir -p "$PREFIX"

if [ ! -x "$PREFIX/jdk/bin/java" ]; then
  echo "== installing Temurin JDK $JDK_VERSION ($ARCH) into $PREFIX/jdk"
  tmp=$(mktemp -d)
  curl -fsSL -o "$tmp/jdk.tgz" \
    "https://api.adoptium.net/v3/binary/latest/$JDK_VERSION/ga/linux/$ARCH/jdk/hotspot/normal/eclipse"
  mkdir -p "$PREFIX/jdk"
  tar -xzf "$tmp/jdk.tgz" -C "$PREFIX/jdk" --strip-components=1
  rm -rf "$tmp"
fi
export JAVA_HOME="$PREFIX/jdk"
export PATH="$JAVA_HOME/bin:$PATH"

if [ ! -x "$PREFIX/sbt/bin/sbt" ]; then
  echo "== installing sbt $SBT_VERSION into $PREFIX/sbt"
  tmp=$(mktemp -d)
  curl -fsSL -o "$tmp/sbt.tgz" \
    "https://github.com/sbt/sbt/releases/download/v$SBT_VERSION/sbt-$SBT_VERSION.tgz"
  tar -xzf "$tmp/sbt.tgz" -C "$PREFIX"
  rm -rf "$tmp"
fi
export PATH="$PREFIX/sbt/bin:$PATH"

# Build in a private copy so the checkout stays clean.
SRC="$PREFIX/leo3/src"
mkdir -p "$SRC"
rsync -a --delete --exclude target --exclude bin --exclude astraea --exclude benchmarks \
  "$REPO/build.sbt" "$REPO/Makefile" "$REPO/project" "$REPO/src" "$SRC/"

echo "== sbt assembly"
(cd "$SRC" && sbt -batch assembly)

JAR=$(ls "$SRC"/target/scala-3.*/leo3-*.jar | head -1)
mkdir -p "$PREFIX/leo3/bin"
cp "$JAR" "$PREFIX/leo3/bin/leo3.jar"

# Same JVM flags as src/main/resources/scripts/exec_dummy; $LEO3_JAVA_ARGS adds more.
cat > "$PREFIX/leo3/bin/leo3" <<EOF
#!/bin/sh
exec "$JAVA_HOME/bin/java" \$LEO3_JAVA_ARGS -Xss32m -Xmx1g -jar "$PREFIX/leo3/bin/leo3.jar" "\$@"
EOF
chmod +x "$PREFIX/leo3/bin/leo3"

git -C "$REPO" rev-parse HEAD > "$PREFIX/leo3/SOURCE_COMMIT" 2>/dev/null || true
"$PREFIX/leo3/bin/leo3" --version || true
echo "== installed $PREFIX/leo3/bin/leo3"
