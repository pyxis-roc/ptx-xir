# ptx-xir

![build status](https://github.com/pyxis-roc/ptx-xir/actions/workflows/build.yml/badge.svg)

ptx-xir contains the XIR definitions for the PTX ISA. It also contains
the associated runtime libraries for C and SMT2.

For legacy reasons, the PTX XIR repository depends on the
`semantics-compiler` repository.

## Pre-requisites

This package requires the ROCetta `xlatir` and `gpusemtest` packages.

## Obtain legacy code

In the `ptx-xir` directory, create a build directory:

```
mkdir build
make legacy SCDIR=../semantics-compiler TARGET=build
```
Adjust the path `SCDIR` if needed.

## Generating the C semantics

To obtain the C semantics run:

```
make c TARGET=build
```

The C translations of the XIR semantics will be available in `build/c`

## Generating the SMT2 semantics

To obtain the SMT2 semantics run:

```
make smt2 TARGET=build
```

The SMT2 translations of the XIR semantics will be available in
`build/smt2`

## Generating test harnesses

The generated semantics can be tested using the `ptx-semantics-tests`
(i.e. `simple_test_runner.py`) framework. To generate test harnesses
for testing, run:

```
make c-tests smt2-tests TARGET=build
```

This will deposit the test harnesses in `../ptx-semantics-tests/v6.5/c` and
`../ptx-semantics-tests/v6.5/ptx-smt2` for C and SMT2 respectively.

You can then run these tests in the usual way using `simple_test_runner.py`.
