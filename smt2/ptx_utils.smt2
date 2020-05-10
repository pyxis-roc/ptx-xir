; (set-logic QF_FPBV)

(define-fun copysign_f32 ((x Float32) (y Float32)) Float32
  (ite (and (fp.isPositive y) (fp.isPositive x)) x (fp.neg x)))

(define-fun FTZ_f32 ((x Float32)) Float32
  (ite (fp.isSubnormal x) (copysign_f32 (_ +zero 8 24) x) x))


(define-fun copysign_f64 ((x Float64) (y Float64)) Float64
  (ite (and (fp.isPositive y) (fp.isPositive x)) x (fp.neg x)))

(define-fun FTZ_f64 ((x Float64)) Float64
  (ite (fp.isSubnormal x) (copysign_f64 (_ +zero 11 53) x) x))

; TODO: evaluate generating this from XIR

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
