; Compute parity.

(set-logic BV)

(define-fun hd22 ((x (_ BitVec 64))) (_ BitVec 64)
(bvand (bvlshr (bvmul (bvand (bvxor (bvxor (bvlshr x #x0000000000000001) x) (bvlshr (bvxor (bvlshr x #x0000000000000001) x)
#x0000000000000002)) #x1111111111111111) #x1111111111111111) #x000000000000001c) #x0000000000000001))

(synth-fun f ((x (_ BitVec 64))) (_ BitVec 64)
    ((Start (_ BitVec 64) ((bvnot Start)
						 (bvxor Start Start)
						 (bvand Start Start)
						 (bvor Start Start)
						 (bvadd Start Start)
						 (bvmul Start Start)
						 (bvlshr Start Start)
						 (bvshl Start Start)
                         x
                         #x0000000000000001
                         #x0000000000000002
                         #x000000000000001c
                         #x1111111111111111
                         (ite StartBool Start Start)))

                         (StartBool Bool
                         ((= Start Start)
                         ))))

(declare-var x (_ BitVec 64))
(constraint (= (hd22 x) (f x)))
(check-synth)

