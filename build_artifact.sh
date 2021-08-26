#!/bin/bash

set -e

REV=`git rev-parse --short HEAD`
BUILD=${1:-build-$REV}

# build ptx_inline.cu
mkdir -p $BUILD

# assumes we're running in ROCetta
make -C .. semantics-compiler/exec_semantics/ptx_executable_semantics_xir.py ptx-xir/src/utils.py

cp ../semantics-compiler/exec_semantics/ptx_executable_semantics_xir.py $BUILD/ptx_executable_semantics_xir.py.orig
src/rewrite.py $BUILD/ptx_executable_semantics_xir.py.orig $BUILD/ptx_executable_semantics_xir.py c

# syntax-checking is integrated

make $BUILD/c TARGET=$BUILD
make c TARGET=$BUILD

make $BUILD/smt2 TARGET=$BUILD
make smt2 TARGET=$BUILD

# build artifact
tar jcvf build.tar.bz2 $BUILD
