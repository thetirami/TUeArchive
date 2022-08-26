(declare-const a Int)

(assert
    (and
        (ite (= 2 1) (= a 1) (= a 2))
    )
)

(check-sat)
(get-model)
