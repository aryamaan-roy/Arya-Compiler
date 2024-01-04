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

(define (f3 [x : Integer] [y : Integer]) : Integer  (+ x y))
(define (f4 [x : Integer] [y : Integer] [z : Boolean]) : Integer
  (if (not (and (and (or (<
                          (if
                           (if (> x y)
                               (eq? 0 0)
                               (eq? 0 1)
                               )
                           (+ 0 (f3 (f2 6 7) (f1 8 7 4)))
                           2
                           )
                          4) (>= 5 6)) (< 10 12)) z)) (+ 5 (- (f3 (f1 7 8 9) 6) (- y))) (+ x 9)))

(f4 (f3 4 2) (f2 7 8) #t)