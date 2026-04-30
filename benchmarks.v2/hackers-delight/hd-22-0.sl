; Compute parity.

(set-logic BV)

(define-fun hd22 ((x (_ BitVec 32))) (_ BitVec 32)
    (bvand (bvlshr (bvmul (bvand (bvxor (bvxor (bvlshr x #x00000001) x) (bvlshr (bvxor (bvlshr x #x00000001) x)
    #x00000002)) #x11111111) #x11111111) #x0000001c) #x00000001)
)

(synth-fun f ((x (_ BitVec 32))) (_ BitVec 32)
    ((Start (_ BitVec 32) (
						 (bvlshr Start #x0000001c)
						 (bvmul Start Start)
						 (bvlshr Start #x00000001)
						 (bvlshr Start #x00000002)
						 (bvand Start Start)
						 (bvxor Start Start)
                         x
                         #x00000001
                         #x11111111
                         (ite StartBool Start Start)))

                         (StartBool Bool
                         ((= Start Start)
                         ))))

(declare-var x (_ BitVec 32))
(constraint (= (hd22 x) (f x)))
(check-synth)

