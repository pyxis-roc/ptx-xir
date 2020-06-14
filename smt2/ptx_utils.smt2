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


(define-fun MUL24_u32 ((x u32) (y u32)) u64
  (let ((x64 ((_ zero_extend 40) ((_ extract 23 0) x)))
		(y64 ((_ zero_extend 40) ((_ extract 23 0) y))))
	(bvmul x64 y64)))

(define-fun MUL24_s32 ((x s32) (y s32)) s64
  (let ((x64 ((_ sign_extend 40) ((_ extract 23 0) x)))
		(y64 ((_ sign_extend 40) ((_ extract 23 0) y))))
	(bvmul x64 y64)))

(define-fun MULWIDE_u16 ((x u16) (y u16)) u32
  (let ((xw ((_ zero_extend 16) x))
		(yw ((_ zero_extend 16) y)))
	(bvmul xw yw)))

(define-fun MULWIDE_u32 ((x u32) (y u32)) u64
  (let ((xw ((_ zero_extend 32) x))
		(yw ((_ zero_extend 32) y)))
	(bvmul xw yw)))

(define-fun MULWIDE_u64 ((x u64) (y u64)) u128
  (let ((xw ((_ zero_extend 64) x))
		(yw ((_ zero_extend 64) y)))
	(bvmul xw yw)))

(define-fun MULWIDE_s16 ((x s16) (y s16)) s32
  (let ((xw ((_ sign_extend 16) x))
		(yw ((_ sign_extend 16) y)))
	(bvmul xw yw)))

(define-fun MULWIDE_s32 ((x s32) (y s32)) s64
  (let ((xw ((_ sign_extend 32) x))
		(yw ((_ sign_extend 32) y)))
	(bvmul xw yw)))

(define-fun MULWIDE_s64 ((x s64) (y s64)) s128
  (let ((xw ((_ sign_extend 64) x))
		(yw ((_ sign_extend 64) y)))
	(bvmul xw yw)))

(define-fun ADD_CARRY_u32 ((a u32) (b u32) (cf b1)) u32_carry
  (let ((bvmax #xffffffff))
	(mk-pair (bvadd (bvadd a b)
					((_ zero_extend 31) cf))
			 (ite (or (bvugt a (bvsub bvmax b))
					  (and (= cf #b1) (= bvmax (bvadd a b))))
				  #b1 #b0
				  ))))

(define-fun SUB_CARRY_u32 ((a u32) (b u32) (cf b1)) u32_carry
  (mk-pair (bvsub a (bvadd b ((_ zero_extend 31) cf)))
		   (ite (or (bvugt b a)
					(and (= cf #b1) (= a b)))
				#b1 #b0
				)))

(define-fun na_extractAndZeroExt_4 ((x b32) (pos u8)) b32
  ((_ zero_extend 24)
   (ite (= pos #x00)
		((_ extract 7 0) x)
		 (ite (= pos #x01)
			  ((_ extract 15 8) x)
			  (ite (= pos #x02)
				   ((_ extract 23 16) x)
				   ((_ extract 31 24) x))))))

(define-fun na_extractAndSignExt_4 ((x b32) (pos u8)) b32
  ((_ sign_extend 24)
   (ite (= pos #x00)
		((_ extract 7 0) x)
		 (ite (= pos #x01)
			  ((_ extract 15 8) x)
			  (ite (= pos #x02)
				   ((_ extract 23 16) x)
				   ((_ extract 31 24) x))))))

(define-fun na_extractAndZeroExt_2 ((x b32) (pos u8)) b32
  ((_ zero_extend 16)
   (ite (= pos #x00)
		((_ extract 15 0) x)
		((_ extract 31 16) x))))

(define-fun na_extractAndSignExt_2 ((x b32) (pos u8)) b32
  ((_ sign_extend 16)
   (ite (= pos #x00)
		((_ extract 15 0) x)
		((_ extract 31 16) x))))

(define-fun ReadByte ((control u32) (value u64) (pos u32)) u32 ; pos is not used for ReadByte
	(let ( (bitpos (bvshl ((_ zero_extend 32) (bvand control #x00000007)) #x0000000000000003)) )
	  (let ( (byte (bvand (bvlshr value bitpos) #x00000000000000ff)) )
		((_ zero_extend 24)
		 (ite (= (bvand control #x00000008) #x00000008)
			  ((_ repeat 8) ((_ extract 7 7) byte))
			  ((_ extract 7 0) byte)
			  )
		 ))))

; machine-specific
;(define-fun MACHINE_SPECIFIC_execute_rem_divide_by_zero_unsigned_u16 ((x u16)) u16 x)
; these need to be implemented

(define-fun log2_f32 ((x f32)) f32 x)
(define-fun log2_f64 ((x f64)) f64 x)
(define-fun sqrt_round_f32 ((m RoundingMode) (x f32)) f32 x)
(define-fun sqrt_round_f64 ((m RoundingMode) (x f64)) f64 x)
(define-fun sqrt_f32 ((x f32)) f32 x)
(define-fun sqrt_f64 ((x f64)) f64 x)

(define-fun sin_f32 ((x f32)) f32 x)
(define-fun sin_f64 ((x f64)) f64 x)

(define-fun cos_f32 ((x f32)) f32 x)
(define-fun cos_f64 ((x f64)) f64 x)

(define-fun pow_f32 ((x f32) (y f32)) f32 x)
(define-fun pow_f64 ((x f64) (y f32)) f64 x)
