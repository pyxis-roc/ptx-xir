#pragma once
#include <math.h>

#ifndef PYCPARSER /* pycparser doesn't handle _Generic */
#define FTZ(X) _Generic((X), \
						float: FTZf,			\
						double: FTZd)(X)

#define SAT(X) _Generic((X), \
						float: SATf,			\
						double: SATd)(X)

#define SATURATE(X) _Generic((X), \
							 float: SATf,		\
							 double: SATd)(X)

#define FMA(X, Y, Z) _Generic((X),				\
							  float: fmaf,		\
							  double: fma)(X, Y, Z)

#endif

static inline float FTZf(float x) {
  if(fpclassify(x) == FP_SUBNORMAL) {
	return copysignf(0.0, x);
  }

  return x;
}

static inline float FTZd(double x) {
  if(fpclassify(x) == FP_SUBNORMAL) {
	return copysign(0.0, x);
  }

  return x;
}

#include "ptxc_utils_template.h"

/* note: add_sat_s32 is not a separate operator because of overflow */
