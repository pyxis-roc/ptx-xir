; (set-logic QF_FPBV)

(define-fun copysign_f32 ((x Float32) (y Float32)) Float32
  (ite (and (fp.isPositive y) (fp.isPositive x)) x (fp.neg x)))

(define-fun FTZ_f32 ((x Float32)) Float32
  (ite (fp.isSubnormal x) (copysign_f32 (_ +zero 8 24) x) x))


(define-fun copysign_f64 ((x Float64) (y Float64)) Float64
  (ite (and (fp.isPositive y) (fp.isPositive x)) x (fp.neg x)))

(define-fun FTZ_f64 ((x Float64)) Float64
  (ite (fp.isSubnormal x) (copysign_f64 (_ +zero 11 53) x) x))
