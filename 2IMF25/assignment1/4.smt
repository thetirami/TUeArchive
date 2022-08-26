(declare-fun a (Int) Int)
(declare-fun b (Int) Int)
(declare-fun c (Int) Bool)
(declare-const n Int)

(assert
    (and
        (= (a 0) 1)
        (= (b 0) 1)
        (forall ((i Int))
        (=> (and (<= 1 i) (<= i 10))
            (ite (c i) (and (= (a i) (+ (a (- i 1)) (* 2 (b (- i 1))))) (= (b i) (+ (b (- i 1)) i))) (and (= (b i) (+ (a (- i 1)) (b (- i 1)))) (= (a i) (+ (a (- i 1)) i))))
        ))
        (= n 10)
        (= (b 10) (+ 600 n))
    )
)
(check-sat)
(get-model)

;   sat: 1, 2, 3, 4, 8, 10
; unsat: 5, 6, 7, 9