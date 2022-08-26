(declare-fun a (Int) Int)
(declare-fun b (Int) Int)
(declare-fun c (Int) Int)
(declare-fun t (Int) Int)
(declare-fun l (Int) Int)
(declare-fun d (Int) Int) ;number of packages of food drop down

;max capacitor of the truck
(declare-const max Int)
(declare-const rounds Int)

;S = 0, A = 1, B = 2, C = 3
(assert (and (= max 300) (= (l 1) 0)(= (t 1) max)(= rounds 21)(= (a 1) 40)(= (b 1) 30)(= (c 1) 145)))
;(assert (and (= (a 1) 40) (= (b 1) 30)(= (c 1) 145)(>= (t 1) 0)(>= (d 1) 0)(<= (a 1) 120)(<= (b 1) 120)(<= (c 1) 200)(<= (t 1) max)) )


(assert
    (and
        (forall ((i Int))
            (=> (and (<= 2 i) (<= i rounds))
                (and (>= (a i) 0) (>= (b i) 0)(>= (c i) 0)(>= (t i) 0) (>= (d i) 0) (<= (a i) 120) (<= (b i) 120)(<= (c i) 200)(<= (t i) max))
            )
        )
    )
)

;S = 0, A = 1, B = 2, C = 3
;l1 = current location, l2 = next location
;a1 = A before, a2 = A after
;b1 = B before, b2 = B after
;c1 = C before, c2 = c after
;t1 = truck before, t2 = truck after
;d = food drop down
(define-fun deliver (
    (l1 Int)(l2 Int)(a1 Int)(a2 Int)(b1 Int)(b2 Int)(c1 Int)(c2 Int)(t1 Int)(t2 Int)(d Int)) Bool
    (or
       (and (= l1 0) (= l2 1) (= a2 (+ (- a1 29) d)) (= b2 (- b1 29)) (= c2 (- c1 29)) (= t2 (- t1 d)) (>= a1 29) (>= b1 29) (>= c1 29))
       (and (= l1 0) (= l2 2) (= a2 (- a1 21)) (= b2 (+ (- b1 21) d)) (= c2 (- c1 21)) (= t2 (- t1 d)) (>= a1 21) (>= b1 21) (>= c1 21))
       (and (= l1 1) (= l2 0) (= a2 (- a1 29)) (= b2 (- b1 29)) (= c2 (- c1 29)) (<= t2 max) (>= a1 29) (>= b1 29) (>= c1 29))
       (and (= l1 1) (= l2 2) (= a2 (- a1 17)) (= b2 (+ (- b1 17) d)) (= c2 (- c1 17)) (= t2 (- t1 d)) (>= a1 17) (>= b1 17) (>= c1 17))
       (and (= l1 1) (= l2 3) (= a2 (- a1 32)) (= b2 (- b1 32)) (= c2 (+ (- c1 32) d)) (= t2 (- t1 d)) (>= a1 32) (>= b1 32) (>= c1 32))
       (and (= l1 2) (= l2 0) (= a2 (- a1 21)) (= b2 (- b1 21)) (= c2 (- c1 21)) (<= t2 max) (>= a1 21) (>= b1 21) (>= c1 21))
       (and (= l1 2) (= l2 1) (= a2 (+ (- a1 17) d)) (= b2 (- b1 17)) (= c2 (- c1 17)) (= t2 (- t1 d)) (>= a1 17) (>= b1 17) (>= c1 17))
       (and (= l1 2) (= l2 3) (= a2 (- a1 37)) (= b2 (- b1 37)) (= c2 (+ (- c1 37) d)) (= t2 (- t1 d)) (>= a1 37) (>= b1 37) (>= c1 37))
       (and (= l1 3) (= l2 1) (= a2 (+ (- a1 32) d)) (= b2 (- b1 32)) (= c2 (- c1 32)) (= t2 (- t1 d)) (>= a1 32) (>= b1 32) (>= c1 32))
       (and (= l1 3) (= l2 2) (= a2 (- a1 37)) (= b2 (+ (- b1 37) d)) (= c2 (- c1 37)) (= t2 (- t1 d)) (>= a1 37) (>= b1 37) (>= c1 37))
    )
)

;(assert (= (deliver (l 1)(l 2)(a 1)(a 2)(b 1)(b 2)(c 1)(c 2)(t 1)(t 2) (d 1)) true ))


(assert
    (forall ((i Int))
    (=> (and (<= 1 i) (<= i rounds))
        (= (deliver (l i) (l (+ i 1)) (a i) (a (+ i 1)) (b i) (b (+ i 1)) (c i) (c (+ i 1)) (t i) (t (+ i 1)) (d i))  true )
    ))
)

(check-sat)
;(get-model)