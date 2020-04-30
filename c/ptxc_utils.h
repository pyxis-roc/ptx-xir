#pragma once
#include <math.h>

#ifndef PYCPARSER /* pycparser doesn't handle _Generic */
#define FTZ(X) _Generic((X), \
						float: FTZf,			\
						double: FTZd)(X)

#define SAT(X) _Generic((X), \
						float: SATf,			\
						double: SATd)(X)

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

static inline float SATf(float x) {
  if(isnan(x)) return 0.0;

  if(x < 0.0)
	return 0.0;
  else if (x > 1.0)
	return 1.0;
  else
	return x;
}

static inline double SATd(double x) {
  if(isnan(x)) return 0.0;

  if(x < 0.0)
	return 0.0;
  else if (x > 1.0)
	return 1.0;
  else
	return x;
}

/* note: add_sat_s32 is not a separate operator because of overflow */
