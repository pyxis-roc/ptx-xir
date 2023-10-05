#!/bin/bash

# SPDX-FileCopyrightText: 2021 University of Rochester
#
# SPDX-License-Identifier: LGPL-3.0-or-later

set -e

REV=`git rev-parse --short HEAD`
BUILD=${1:-build-$REV}

# build ptx_inline.cu
mkdir -p $BUILD

# assumes we're running in ROCetta
make -C .. semantics-compiler/exec_semantics/ptx_executable_semantics_xir.py
# ptx-xir/src/utils.py

make legacy SCDIR=../semantics-compiler TARGET=$BUILD

# syntax-checking is integrated

make c smt2 TARGET=$BUILD

# TODO: test cases

# build artifact
tar jcvf build.tar.bz2 $BUILD
