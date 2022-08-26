(declare-fun dish (Int Int) Int)    ; when i, whether house j has dish
(declare-fun pos (Int Int) Int)     ; when i, person j is in pos(i, j)
(declare-fun num (Int Int Int) Int) ; when i, person j and person k meeting times

(assert
    (and
        ; dish(i, j) = 0 or 1
        (forall ((i Int) (j Int))
        (=> (and (<= 1 i) (<= i 5) (<= 1 j) (<= j 5))
            (or (= (dish i j) 0) (= (dish i j) 1))
        ))

        ; for each row and column, there are two and only two.
        (= (+ (dish 1 1) (dish 1 2) (dish 1 3) (dish 1 4) (dish 1 5)) 2)
        (= (+ (dish 2 1) (dish 2 2) (dish 2 3) (dish 2 4) (dish 2 5)) 2)
        (= (+ (dish 3 1) (dish 3 2) (dish 3 3) (dish 3 4) (dish 3 5)) 2)
        (= (+ (dish 4 1) (dish 4 2) (dish 4 3) (dish 4 4) (dish 4 5)) 2)
        (= (+ (dish 5 1) (dish 5 2) (dish 5 3) (dish 5 4) (dish 5 5)) 2)
        (= (+ (dish 1 1) (dish 2 1) (dish 3 1) (dish 4 1) (dish 5 1)) 2)
        (= (+ (dish 1 2) (dish 2 2) (dish 3 2) (dish 4 2) (dish 5 2)) 2)
        (= (+ (dish 1 3) (dish 2 3) (dish 3 3) (dish 4 3) (dish 5 3)) 2)
        (= (+ (dish 1 4) (dish 2 4) (dish 3 4) (dish 4 4) (dish 5 4)) 2)
        (= (+ (dish 1 5) (dish 2 5) (dish 3 5) (dish 4 5) (dish 5 5)) 2)
    )
)

(define-fun assign (
    (a1 Int)(a2 Int)(a3 Int)(a4 Int)(a5 Int)(a6 Int)(tar1 Int)(tar2 Int)) Bool
    (or
        (and (= a1 a2) (= a2 a3) (= a1 tar1) (= a4 a5) (= a5 a6) (= a4 tar2))
        (and (= a1 a2) (= a2 a4) (= a1 tar1) (= a3 a5) (= a5 a6) (= a3 tar2))
        (and (= a1 a2) (= a2 a5) (= a1 tar1) (= a3 a4) (= a4 a6) (= a3 tar2))
        (and (= a1 a2) (= a2 a6) (= a1 tar1) (= a3 a4) (= a4 a5) (= a3 tar2))
        (and (= a1 a3) (= a3 a4) (= a1 tar1) (= a2 a5) (= a5 a6) (= a2 tar2))
        (and (= a1 a3) (= a3 a5) (= a1 tar1) (= a2 a4) (= a4 a6) (= a2 tar2))
        (and (= a1 a3) (= a3 a6) (= a1 tar1) (= a2 a4) (= a4 a5) (= a2 tar2))
        (and (= a1 a4) (= a4 a5) (= a1 tar1) (= a2 a3) (= a3 a6) (= a2 tar2))
        (and (= a1 a4) (= a4 a6) (= a1 tar1) (= a2 a3) (= a3 a5) (= a2 tar2))
        (and (= a1 a5) (= a5 a6) (= a1 tar1) (= a2 a3) (= a3 a4) (= a2 tar2))

        (and (= a1 a2) (= a2 a3) (= a1 tar2) (= a4 a5) (= a5 a6) (= a4 tar1))
        (and (= a1 a2) (= a2 a4) (= a1 tar2) (= a3 a5) (= a5 a6) (= a3 tar1))
        (and (= a1 a2) (= a2 a5) (= a1 tar2) (= a3 a4) (= a4 a6) (= a3 tar1))
        (and (= a1 a2) (= a2 a6) (= a1 tar2) (= a3 a4) (= a4 a5) (= a3 tar1))
        (and (= a1 a3) (= a3 a4) (= a1 tar2) (= a2 a5) (= a5 a6) (= a2 tar1))
        (and (= a1 a3) (= a3 a5) (= a1 tar2) (= a2 a4) (= a4 a6) (= a2 tar1))
        (and (= a1 a3) (= a3 a6) (= a1 tar2) (= a2 a4) (= a4 a5) (= a2 tar1))
        (and (= a1 a4) (= a4 a5) (= a1 tar2) (= a2 a3) (= a3 a6) (= a2 tar1))
        (and (= a1 a4) (= a4 a6) (= a1 tar2) (= a2 a3) (= a3 a5) (= a2 tar1))
        (and (= a1 a5) (= a5 a6) (= a1 tar2) (= a2 a3) (= a3 a4) (= a2 tar1))
    )
)

(assert
    (and
        ; 1 <= pos(i, j) <= 5
        (forall ((i Int) (j Int))
        (=> (and (<= 1 i) (<= i 5) (<= 1 j) (<= j 10))
            (and (<= 1 (pos i j)) (<= (pos i j) 5))
        ))

        ; if dish(i, j) = 0, pos(i, k) != j
        (forall ((i Int) (j Int) (k Int))
        (=> (and (<= 1 i) (<= i 5) (<= 1 j) (<= j 5) (<= 1 k) (<= k 10))
            (implies (= (dish i j) 0) (and
                (not (= (pos i k) j))
            ))
        ))

        ; if dish(i, j) = 1, pos(i, 2j-1) and pos(i, 2j) = j, other pos=j or not
        (forall ((i Int))
        (=> (and (<= 1 i) (<= i 5))
            (and
                (implies (and (= (dish i 1) 1) (= (dish i 2) 1)) (and
                    (= (pos i 1) 1)
                    (= (pos i 2) 1)
                    (= (pos i 3) 2)
                    (= (pos i 4) 2)
                    (assign (pos i 5) (pos i 6) (pos i 7) (pos i 8) (pos i 9) (pos i 10) 1 2)
                ))
                (implies (and (= (dish i 1) 1) (= (dish i 3) 1)) (and
                    (= (pos i 1) 1)
                    (= (pos i 2) 1)
                    (= (pos i 5) 3)
                    (= (pos i 6) 3)
                    (assign (pos i 3) (pos i 4) (pos i 7) (pos i 8) (pos i 9) (pos i 10) 1 3)
                ))
                (implies (and (= (dish i 1) 1) (= (dish i 4) 1)) (and
                    (= (pos i 1) 1)
                    (= (pos i 2) 1)
                    (= (pos i 7) 4)
                    (= (pos i 8) 4)
                    (assign (pos i 3) (pos i 4) (pos i 5) (pos i 6) (pos i 9) (pos i 10) 1 4)
                ))
                (implies (and (= (dish i 1) 1) (= (dish i 5) 1)) (and
                    (= (pos i 1) 1)
                    (= (pos i 2) 1)
                    (= (pos i 9) 5)
                    (= (pos i 10) 5)
                    (assign (pos i 5) (pos i 6) (pos i 7) (pos i 8) (pos i 3) (pos i 4) 1 5)
                ))
                (implies (and (= (dish i 2) 1) (= (dish i 3) 1)) (and
                    (= (pos i 3) 2)
                    (= (pos i 4) 2)
                    (= (pos i 5) 3)
                    (= (pos i 6) 3)
                    (assign (pos i 1) (pos i 2) (pos i 7) (pos i 8) (pos i 9) (pos i 10) 2 3)
                ))
                (implies (and (= (dish i 2) 1) (= (dish i 4) 1)) (and
                    (= (pos i 3) 2)
                    (= (pos i 4) 2)
                    (= (pos i 7) 4)
                    (= (pos i 8) 4)
                    (assign (pos i 1) (pos i 2) (pos i 5) (pos i 6) (pos i 9) (pos i 10) 2 4)
                ))
                (implies (and (= (dish i 2) 1) (= (dish i 5) 1)) (and
                    (= (pos i 3) 2)
                    (= (pos i 4) 2)
                    (= (pos i 9) 5)
                    (= (pos i 10) 5)
                    (assign (pos i 1) (pos i 2) (pos i 7) (pos i 8) (pos i 5) (pos i 6) 2 5)
                ))
                (implies (and (= (dish i 3) 1) (= (dish i 4) 1)) (and
                    (= (pos i 5) 3)
                    (= (pos i 6) 3)
                    (= (pos i 7) 4)
                    (= (pos i 8) 4)
                    (assign (pos i 1) (pos i 2) (pos i 3) (pos i 4) (pos i 9) (pos i 10) 3 4)
                ))
                (implies (and (= (dish i 3) 1) (= (dish i 5) 1)) (and
                    (= (pos i 5) 3)
                    (= (pos i 6) 3)
                    (= (pos i 9) 5)
                    (= (pos i 10) 5)
                    (assign (pos i 1) (pos i 2) (pos i 3) (pos i 4) (pos i 7) (pos i 8) 3 5)
                ))
                (implies (and (= (dish i 4) 1) (= (dish i 5) 1)) (and
                    (= (pos i 7) 4)
                    (= (pos i 8) 4)
                    (= (pos i 9) 5)
                    (= (pos i 10) 5)
                    (assign (pos i 1) (pos i 2) (pos i 3) (pos i 4) (pos i 5) (pos i 6) 4 5)
                ))
            )
        ))
    )
)

(assert
    (and
        (forall ((j Int) (k Int))
        (=> (and (<= 1 j) (<= j 10) (< j k) (<= k 10))
            (and
                (ite (= (pos 1 j) (pos 1 k)) (= (num 1 j k) 1) (= (num 1 j k) 0))
                (ite (= (pos 2 j) (pos 2 k)) (= (num 2 j k) (+ (num 1 j k) 1)) (= (num 2 j k) (num 1 j k)))
                (ite (= (pos 3 j) (pos 3 k)) (= (num 3 j k) (+ (num 2 j k) 1)) (= (num 3 j k) (num 2 j k)))
                (ite (= (pos 4 j) (pos 4 k)) (= (num 4 j k) (+ (num 3 j k) 1)) (= (num 4 j k) (num 3 j k)))
                (ite (= (pos 5 j) (pos 5 k)) (= (num 5 j k) (+ (num 4 j k) 1)) (= (num 5 j k) (num 4 j k)))
            )
        ))
    )
)

(assert
    (and
        (forall ((j Int) (k Int))
        (=> (and (<= 1 j) (<= j 10) (< j k) (<= k 10))
            (<= (num 5 j k) 4)
        ))

        ; A
        (forall ((j Int) (k Int))
        (=> (and (<= 1 j) (<= j 10) (< j k) (<= k 10))
            (>= (num 5 j k) 1)
        ))

        ; B
        ;(forall ((j Int) (k Int))
        ;(=> (and (<= 1 j) (<= j 10) (< j k) (<= k 10))
        ;    (<= (num 5 j k) 3)
        ;))

        ; C
        ;(forall ((j Int) (k Int))
        ;(=> (and (or (= j 1)(= j 3)(= j 5)(= j 7)(= j 9)) (= k (+ j 1)))
        ;    (= (num 5 j k) 2)
        ;))

        ; D one can only go to one place once if he/she is not the owner
        (forall ((t1 Int) (t2 Int) (j Int) (k Int))
        (=> (<= 1 t1) (<= t1 5) (<= 1 t2) (<= t2 5) (not (= t1 t2)) (<= 1 j) (<= j 5) (<= 1 k) (<= k 10) (not (= k (* 2 j))) (not (= k (- (* 2 j) 1)))
            (implies (and (= (dish t1 j) 1) (= (dish t2 j) 1)) (not (= (pos t1 k) (pos t2 k))))
        ))
    )
)

(check-sat)
(get-model)
