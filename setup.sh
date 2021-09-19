#!/bin/sh

case "$(uname)" in
    "Darwin") platform="osx-10.14.6"; ext="dylib";;
    "Linux") platform="ubuntu-16.04"; ext="so";;
    *) echo 'not supported system: $(uname)'; exit;;
esac

mkdir -p ./lib

echo "#### Z3..."
z3=z3-4.8.8-x64-${platform}
curl -sSLO "https://github.com/Z3Prover/z3/releases/download/z3-4.8.8/${z3}.zip"
unzip "${z3}.zip" > /dev/null
cp ${z3}/bin/libz3*.${ext} .
cp "${z3}/bin/com.microsoft.z3.jar" ./lib
echo "#### Z3 done"

echo "#### scala-smtlib..."
git clone git@github.com:regb/scala-smtlib > /dev/null
cd scala-smtlib
sbt package
cp target/scala-2.13/scala-smtlib*.jar ../lib
cd ..
echo "#### scala-smtlib done"

read -p "try to build? (y/N)" yn; case "$yn" in [nN]*) exit;; esac
sbt assembly
read -p "try to solve one? (y/N)" yn; case "$yn" in [nN]*) exit;; esac
java -jar target/scala-2.13/*.jar constraints/bench/deleteall.smt2 preimage
