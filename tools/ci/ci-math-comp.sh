#!/bin/bash

# $0 is not the safest way, but...
ci_dir="$(dirname "$0")"
source ${ci_dir}/ci-common.sh

git clone --depth 3 https://github.com/math-comp/math-comp.git

# odd_order takes too much time for travis.
( cd math-comp/mathcomp && sed -i.bak '/odd_order/d' Make && make -j ${NJOBS} )

