#pragma once
#include <math.h>
#include <fenv.h>

#ifndef PYCPARSER /* pycparser doesn't handle _Generic */
#define FTZ(X) _Generic((X), \
						float: FTZf,			\
						double: FTZd)(X)

#define SAT(X) _Generic((X), \
						float: SATf,			\
						double: SATd)(X)

#define FMA(X, Y, Z) _Generic((X),				\
							  float: fmaf,		\
							  double: fma)(X, Y, Z)

#define SQRT(X) _Generic((X),				\
						 float: sqrtf,		\
						 double: sqrt)(X)

#define extract_24(X) _Generic((X),								\
							   uint32_t: extract_24_unsigned,	\
							   int32_t: extract_24_signed)(X)


#endif

#define RCP(X) (1.0 / (X))

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

static inline uint32_t extract_24_unsigned(uint32_t x) {
  return x & 0xffffff;
}

static inline uint32_t extract_24_signed(int32_t x) {
  uint32_t xx = x;
  xx = x & 0xffffff;
  if(xx & 0x800000) xx |= 0xff000000;

  return xx;
}

#include "ptxc_utils_template.h"

int32_t ADD_SATURATE_s32(int32_t x, int32_t y) {
  /* see Dietz et al., ICSE 2012 */

  if(x > 0 && y > 0 && x > INT32_MAX - y)
	return INT32_MAX;

  if(x < 0 && y < 0 && x < INT32_MIN - y)
	return INT32_MIN;

  return x + y;
}

int32_t SUB_SATURATE_s32(int32_t x, int32_t y) {
  if(x < 0 && y > 0 && x < INT32_MIN + y) {
	return INT32_MIN;
  }

  if(x > 0 && y < 0 && x > INT32_MAX + y) {
	return INT32_MAX;
  }

  // both same sign or no overflow detected
  return x - y;
}
