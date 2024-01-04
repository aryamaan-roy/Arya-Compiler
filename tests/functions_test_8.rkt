(define (f1 [x : Integer] [y : Integer] [z : Integer]) : Integer
  (if
    (not
     (and
      (and
       (or (< x z) (>= 5 y)) (< 10 x)) #t)) (+ 5 (- 6 (- 7))) (+ 6 9)))


(define (f2 [a : Integer] [b : Integer]) : Integer
  (let ([x 1])
    (let ([y (f1 5 6 8)])
      (let ([z (if (if (not (< x 1))
                       (not (eq? x 0))
                       (eq? x (f1 4 5 6)))
                   (not (eq? y 2))
                   (not (eq? y 10)))])
        (if z (+ 2 a) (+ b (f1 7 7 7)))))))


(f2 4 6)