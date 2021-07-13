(declare-rel inv (Int Int Int Int))
(declare-var x0 Int)
(declare-var x1 Int)
(declare-var y0 Int)
(declare-var y1 Int)
(declare-var z0 Int)
(declare-var z1 Int)
(declare-var break Int)


(declare-rel fail ())

(rule (=> (and (= x1 0) )
          (inv x1 y1 z1 break)))

(rule (=>
    (and
        (inv x0 y0 z0 break)
        (= y1 (ite (>= x 5) (+ y0 1) y0))
        (= x1 (ite (>= x 5) x0 (+ x0 1)))
        (= z1 (ite (<= y 5)  (+ z0 1) z0))


    )
    (inv x1 y1 z0 break)
  )
)

(rule (=> (and (inv  x1 y1 z1 break) (= y1 0) (not (= x1 0))) fail))

(query fail :print-certificate true)
