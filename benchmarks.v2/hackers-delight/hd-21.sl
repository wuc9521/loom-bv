; Cycling through 3 values a, b, c.

(set-logic BV)

(define-fun hd21 ((x (_ BitVec 64)) (a (_ BitVec 64)) (b (_ BitVec 64)) (c (_ BitVec 64))) (_ BitVec 64)
(ite (= x a) b (ite (= x b) c a)))

(synth-fun f ((x (_ BitVec 64)) (a (_ BitVec 64)) (b (_ BitVec 64)) (c (_ BitVec 64))) (_ BitVec 64)
		   
((Start (_ BitVec 64)
((bvnot Start)
(bvxor Start Start)
(bvand Start Start)
(bvor Start Start)
(bvneg Start)
(bvadd Start Start)
(bvmul Start Start)
(bvudiv Start Start)
(bvurem Start Start)
(bvlshr Start Start)
(bvashr Start Start)
(bvshl Start Start)
(bvsdiv Start Start)
(bvsrem Start Start)
(bvsub Start Start)
x
a
b
c
(ite StartBool Start Start)))
(StartBool Bool
((= Start Start)))))

(declare-var x (_ BitVec 64))
(declare-var a (_ BitVec 64))
(declare-var b (_ BitVec 64))
(declare-var c (_ BitVec 64))

(constraint (= (hd21 x a b c) (f x a b c)))
(check-synth)

