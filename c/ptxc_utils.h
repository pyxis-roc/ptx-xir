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

#define MAXVALUE(x) _Generic((x), \
							 int16_t: INT16_MAX,	\
							 uint16_t: UINT16_MAX,	\
							 int32_t: INT32_MAX,	\
							 uint32_t: UINT32_MAX,	\
							 int64_t: INT64_MAX,	\
							 uint64_t: UINT64_MAX)

#endif

#define RCP(X) (1.0 / (X))

typedef uint16_t bitstring16_t;
typedef uint32_t bitstring32_t;
typedef uint64_t bitstring64_t;
typedef uint32_t BIT_T;

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

static inline uint8_t ReadByte(uint8_t control, uint64_t value, uint8_t pos) {
  uint8_t byte = 0;
  byte = (value >> ((control & 0x7) * 8)) & 0xff;
  if(control & 0x8) {
	if(byte & 0x80)
	  return 0xff;
	else
	  return 0x0;
  } else {
	return byte;
  }
}
