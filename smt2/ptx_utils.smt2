; (set-logic QF_FPBV)

(define-fun copysign_f32 ((x Float32) (y Float32)) Float32
  (ite (and (fp.isPositive y) (fp.isPositive x)) x (fp.neg x)))

(define-fun FTZ_f32 ((x Float32)) Float32
  (ite (fp.isSubnormal x) (copysign_f32 (_ +zero 8 24) x) x))


(define-fun copysign_f64 ((x Float64) (y Float64)) Float64
  (ite (and (fp.isPositive y) (fp.isPositive x)) x (fp.neg x)))

(define-fun FTZ_f64 ((x Float64)) Float64
  (ite (fp.isSubnormal x) (copysign_f64 (_ +zero 11 53) x) x))

; TODO: consider generating this from XIR?

(define-fun SATURATE_f32 ((x Float32)) Float32
  (let ( (zero_f32 (_ +zero 8 24)) )
	(let ( (one_f32 ((_ to_fp_unsigned 8 24) roundNearestTiesToEven #x00000001)) )
	  (ite (fp.isNaN x)
		   zero_f32
		   (ite (fp.lt x zero_f32)
				zero_f32
				(ite (fp.gt x one_f32) one_f32 x))))))

(define-fun SATURATE_f64 ((x Float64)) Float64
  (let ( (zero_f64 (_ +zero 11 53)) )
	(let ( (one_f64 ((_ to_fp_unsigned 11 53) roundNearestTiesToEven #x0000000000000001)) )
	  (ite (fp.isNaN x)
		   zero_f64
		   (ite (fp.lt x zero_f64) zero_f64
				(ite (fp.gt x one_f64) one_f64 x))))))

(define-fun abs_s16 ((x s16)) s16
  (ite (bvslt x #x0000) (bvneg x) x))   ; note for -INT16_MIN, this returns INT16_MIN

(define-fun abs_s32 ((x s32)) s32
  (ite (bvslt x #x00000000) (bvneg x) x))

(define-fun abs_s64 ((x s64)) s64
  (ite (bvslt x #x0000000000000000) (bvneg x) x))

(define-fun ADD_SATURATE_s32 ((x s32) (y s32)) s32
  (let ((INT32_MAX #x7fffffff) (INT32_MIN #x80000000) (INT32_ZERO #x00000000))
	(ite (and (bvsgt x INT32_ZERO) (bvsgt y INT32_ZERO) (bvsgt x (bvsub INT32_MAX y)))
		 INT32_MAX
		 (ite (and (bvslt x INT32_ZERO) (bvslt y INT32_ZERO) (bvslt x (bvsub INT32_MIN y)))
			  INT32_MIN
			  (bvadd x y)))))

(define-fun SUB_SATURATE_s32 ((x s32) (y s32)) s32
  (let ((INT32_MAX #x7fffffff) (INT32_MIN #x80000000) (INT32_ZERO #x00000000))
	(ite (and (bvslt x INT32_ZERO) (bvsgt y INT32_ZERO) (bvslt x (bvadd INT32_MIN y)))
		 INT32_MIN
		 (ite (and (bvsgt x INT32_ZERO) (bvslt y INT32_ZERO) (bvsgt x (bvadd INT32_MAX y)))
			  INT32_MAX
			  (bvsub x y)))))
