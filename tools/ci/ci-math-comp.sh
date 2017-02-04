#!/bin/bash

# Proof of concept contrib build script.

set -xe

export PATH=`pwd`/bin:$PATH

git clone --depth 3 https://github.com/math-comp/math-comp.git

pushd math-comp/mathcomp

# odd_order takes too much time for travis.
sed -i.bak '/odd_order/d' Make
make -j ${NJOBS}

popd
