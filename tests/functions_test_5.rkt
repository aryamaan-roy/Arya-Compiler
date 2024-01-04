(define (f1 [y : Integer]) : Integer (if (not (and (and (or (< y 4) (>= 5 y)) (< y 12)) #t)) (+ 5 (- 6 (- 7))) (+ 6 9)))
(define (f2 [x : Integer]) : Integer (if (and (not (let ([ x (if (< 3 4) (+ 1 2) (+ 3 4))]) (if (< x 5) #t
                                                           (not
                                                             (if (and (eq? 1 2) (eq? 0 0))
                                                                 #t
                                                                 #f
                                                              )
                                                            )
                                                           ))) #t) (+ 3 (+
                                                                         (let ([y
                                                                                (if (eq? 2 (f1 2))
                                                                                    (let ([x 3]) (+ x 2))
                                                                                    2
                                                                                 )
                                                                               ])
                                                                           (+ y
                                                                              (if (not (eq? (computeInt #f) 2))
                                                                                  2
                                                                                  3
                                                                               )
                                                                           )
                                                                          )
                                                                         (- 6))) (+ 3 2)))

(define (computeInt [z : Boolean]) : Integer (let ([x (and #t z)]) (if x (let ([x 5]) x) (let ([x 13]) x))))
(f2 (computeInt #f))