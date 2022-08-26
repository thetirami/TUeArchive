(declare-const curr Int)         ; the number of vertice
(declare-const prev Int)         ; the number of vertice
(declare-fun v (Int) Int)

(assert
    (and
        (= curr 2)
        (= prev 1)
        (= (v prev) 3)
        (= (v curr) (+ (v prev) 1))
    )
)

(check-sat)
(get-model)