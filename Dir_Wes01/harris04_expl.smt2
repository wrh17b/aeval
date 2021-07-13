(declare-rel inv (Int Int))
(declare-var x0 Int)
(declare-var x1 Int)
(declare-var y0 Int)
(declare-var y1 Int)


(declare-rel fail ())

(rule (=> (and (= x1 0) )
          (inv x1 y1 )))

(rule (=>
    (and
        (inv x0 y0 )
        (= x1 (ite (= (mod y0 2) 0)  x0 (+ x0 1)))
        (= y1 (ite (= (mod y0 2) 0) (div (- y0 1) 2) (div y0 2)))
    )
    (inv x1 y1 )
  )
)

(rule (=> (and (inv  x1 y1 ) (= y1 0) (not (= x1 0))) fail))

(query fail :print-certificate true)
