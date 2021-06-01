(declare-rel itp (Int Int Int Int))
(declare-var x Int)
(declare-var k Int)
(declare-var c Int)
(declare-var n Int)
(declare-var x1 Int)
(declare-var k1 Int)
(declare-var c1 Int)
(declare-var n1 Int)

(declare-rel fail ())

(rule (=> (and (>= n 0) (= c 0) (= k 0) (= x 0)) (itp x k c n)))

(rule (=>
    (and
	(itp x k c n)
    (<= c (- n 1))
    (= c1 (+ c 1))
    (= x1 (ite (= 0 (mod k 2)) (+ x 1) x))
	(= k1 (+ x c))
    )
    (itp x1 k1 c1 n)
  )
)


(rule (=> (and (itp x k c n) (>= c n) (not (= x n))) fail))

(query fail :print-certificate true)
