(declare-const v_num Int)         ; the number of vertice
(declare-fun e (Int Int) Bool)  ; e(i, j) linked or not, i < j
(declare-fun v (Int Int) Int)   ; v(i, j) = k means vertex i is chosen k time(s), after checking edge j
(declare-fun r (Int Int) Bool)  ; choose edge (i, j) as result

(assert
    (and
        ; use e to describe the graph
        (= v_num 5)

        (= (e 1 2) true)
        (= (e 1 3) true)
        (= (e 1 4) true)
        (= (e 1 5) true)
        (= (e 2 3) true)
        (= (e 2 4) true)
        (= (e 2 5) true)
        (= (e 3 4) true)
        (= (e 3 5) true)
        (= (e 4 5) true)
    )
)

(assert
    (and
        (forall ((i Int))
        (=> (and (<= 1 i) (<= i v_num))
            (= (v i 0) 0)
        ))
    )
)

; v(i, k) = m  检查完边 k 后，点 i 被访问的次数是 m
(assert
    (and
        (forall ((j Int) (k Int))
        (=> (and (<= 1 j) (<= j v_num) (< j k) (<= k v_num))
            ; curr (+ (div (* (- (* 2 v_num) j) (- j 1)) 2) (- k j))
            ; prev (- (+ (div (* (- (* 2 v_num) j) (- j 1)) 2) (- k j)) 1)
            ; index of this edge is (2*v_num - j)*(j - 1)/2 + (k - j)
            (ite (and (= (e j k) true) (= (r j k) true)) (and
                ; have this edge and use this edge
                (= (v j (+ (div (* (- (* 2 v_num) j) (- j 1)) 2) (- k j))) (+ (v j (- (+ (div (* (- (* 2 v_num) j) (- j 1)) 2) (- k j)) 1)) 1))
                (= (v k (+ (div (* (- (* 2 v_num) j) (- j 1)) 2) (- k j))) (+ (v k (- (+ (div (* (- (* 2 v_num) j) (- j 1)) 2) (- k j)) 1)) 1))
                (forall ((n Int))
                (=> (and (<= 1 n) (<= n v_num) (not (= n j)) (not (= n k)))
                    (= (v n (+ (div (* (- (* 2 v_num) j) (- j 1)) 2) (- k j))) (v n (- (+ (div (* (- (* 2 v_num) j) (- j 1)) 2) (- k j)) 1)))
                ))
            ) (and
                ; do not have this edge / do not use this edge
                (forall ((n Int))
                (=> (and (<= 1 n) (<= n v_num))
                    (= (v n (+ (div (* (- (* 2 v_num) j) (- j 1)) 2) (- k j))) (v n (- (+ (div (* (- (* 2 v_num) j) (- j 1)) 2) (- k j)) 1)))
                ))
            ))
        ))
    )
)

(assert
    (and
        (forall ((n Int))
        (=> (and (<= 1 n) (<= n v_num))
            (= (v n (div (* v_num (- v_num 1)) 2)) 2)
        ))
    )
)

(check-sat)
(get-model)