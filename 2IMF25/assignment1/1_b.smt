(declare-fun num_c (Int) Int) ; the number of cheese pallets on trucks
(declare-fun num_b (Int) Int) ; the number of beer pallets on trucks
(declare-fun num_w (Int) Int) ; the number of wine pallets on trucks
(declare-fun num_s (Int) Int) ; the number of soft drink pallets on trucks
(declare-fun num_p (Int) Int) ; the number of potato chips pallets on trucks

(assert
    (and
        ; number of pallets should be \ge 0
        (>= (num_c 1) 0)
        (>= (num_c 2) 0)
        (>= (num_c 3) 0)
        (>= (num_c 4) 0)
        (>= (num_c 5) 0)
        (>= (num_c 6) 0)
        (>= (num_b 1) 0)
        (>= (num_b 2) 0)
        (>= (num_b 3) 0)
        (>= (num_b 4) 0)
        (>= (num_b 5) 0)
        (>= (num_b 6) 0)
        (>= (num_w 1) 0)
        (>= (num_w 2) 0)
        (>= (num_w 3) 0)
        (>= (num_w 4) 0)
        (>= (num_w 5) 0)
        (>= (num_w 6) 0)
        (>= (num_s 1) 0)
        (>= (num_s 2) 0)
        (>= (num_s 3) 0)
        (>= (num_s 4) 0)
        (>= (num_s 5) 0)
        (>= (num_s 6) 0)
        (>= (num_p 1) 0)
        (>= (num_p 2) 0)
        (>= (num_p 3) 0)
        (>= (num_p 4) 0)
        (>= (num_p 5) 0)
        (>= (num_p 6) 0)
        ; capacity \le
        (<= (+ (* 700 (num_c 1)) (* 1300 (num_b 1)) (* 1000 (num_w 1)) (* 1500 (num_s 1)) (* 100 (num_p 1))) 8500)
        (<= (+ (* 700 (num_c 2)) (* 1300 (num_b 2)) (* 1000 (num_w 2)) (* 1500 (num_s 2)) (* 100 (num_p 2))) 8500)
        (<= (+ (* 700 (num_c 3)) (* 1300 (num_b 3)) (* 1000 (num_w 3)) (* 1500 (num_s 3)) (* 100 (num_p 3))) 8500)
        (<= (+ (* 700 (num_c 4)) (* 1300 (num_b 4)) (* 1000 (num_w 4)) (* 1500 (num_s 4)) (* 100 (num_p 4))) 8500)
        (<= (+ (* 700 (num_c 5)) (* 1300 (num_b 5)) (* 1000 (num_w 5)) (* 1500 (num_s 5)) (* 100 (num_p 5))) 8500)
        (<= (+ (* 700 (num_c 6)) (* 1300 (num_b 6)) (* 1000 (num_w 6)) (* 1500 (num_s 6)) (* 100 (num_p 6))) 8500)
        ; let truck 1 and truck 2 cannot carry beer and wine
        (= (num_b 1) 0)
        (= (num_b 2) 0)
        (= (num_w 1) 0)
        (= (num_w 2) 0)
        ; every truck carrys at most 8 pallets
        (<= (+ (num_c 1) (num_b 1) (num_w 1) (num_s 1) (num_p 1)) 8)
        (<= (+ (num_c 2) (num_b 2) (num_w 2) (num_s 2) (num_p 2)) 8)
        (<= (+ (num_c 3) (num_b 3) (num_w 3) (num_s 3) (num_p 3)) 8)
        (<= (+ (num_c 4) (num_b 4) (num_w 4) (num_s 4) (num_p 4)) 8)
        (<= (+ (num_c 5) (num_b 5) (num_w 5) (num_s 5) (num_p 5)) 8)
        (<= (+ (num_c 6) (num_b 6) (num_w 6) (num_s 6) (num_p 6)) 8)
        ; cheese, wine, soft drink and potato chips are all carried
        (= (+ (num_c 1) (num_c 2) (num_c 3) (num_c 4) (num_c 5) (num_c 6)) 4)
        (= (+ (num_w 1) (num_w 2) (num_w 3) (num_w 4) (num_w 5) (num_w 6)) 8)
        (= (+ (num_s 1) (num_s 2) (num_s 3) (num_s 4) (num_s 5) (num_s 6)) 10)
        (= (+ (num_p 1) (num_p 2) (num_p 3) (num_p 4) (num_p 5) (num_p 6)) 5)
        ; every truck contains at most 2 pallets of soft drinks
        (<= (num_s 1) 2)
        (<= (num_s 2) 2)
        (<= (num_s 3) 2)
        (<= (num_s 4) 2)
        (<= (num_s 5) 2)
        (<= (num_s 6) 2)
    )
)
; maximize the number of pallets of beer
(maximize (+ (num_b 1) (num_b 2) (num_b 3) (num_b 4) (num_b 5) (num_b 6)))

(check-sat)
(get-model)

; 12
; c: 4 0 0 0 0 0
; b: 0 0 3 4 5 0
; w: 0 0 3 0 0 5
; s: 2 2 1 2 1 2
; p: 2 0 1 2 0 0