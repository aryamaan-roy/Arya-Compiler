(define (f1 [x : Integer] [y : Integer]) : Integer
  (if (not (and (and (or (<
                          (if
                           (if (> x y)
                               (eq? 0 0)
                               (eq? 0 1)
                               )
                           (+ 0 3)
                           2
                           )
                          4) (>= 5 6)) (< 10 12)) #t)) (+ 5 (- 6 (- y))) (+ x 9)))


(define (f2 [a : Integer] [b : Integer]) : Integer
  (let ([x 1])
    (let ([y (f1 5 6)])
      (let ([z (if (if (not (< x 1))
                       (not (eq? x 0))
                       (eq? x 2))
                   (not (eq? y 2))
                   (not (eq? y 10)))])
        (if z (+ 2 a) (+ b (f1 7 7)))))))


(f2 36 12)