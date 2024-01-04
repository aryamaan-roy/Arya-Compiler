(define (f2 [x : Integer] [y : Integer]) : Integer (f1 (+ x 4) (+ 8 y)))
(define (f1 [x : Integer] [y : Integer]) : Integer (if (not (and (and (or (<
                        (if
                            (if (> x y)
                                (eq? 0 0)
                                (eq? 0 1)
                             )
                            (+ 0 3)
                            2
                         )
                        4) (>= 5 6)) (< 10 12)) #t)) (+ 5 (- 6 (- y))) (+ x 9)))
(f2 36 12)