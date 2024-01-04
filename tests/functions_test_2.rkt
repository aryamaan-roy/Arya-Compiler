(define (f1 [x : Integer] [y : Integer]) : Integer (if (and (not (let ([ x (if (< x y) (+ 1 2) (+ x 4))]) (if (< x 5) #t
                                                           (not
                                                             (if (and (eq? 2 2) (eq? 0 0))
                                                                 #t
                                                                 #f
                                                              )
                                                            )
                                                           ))) #t) (+ 3 (+ 2 (- 6))) (+ 1 y)))
(f1 4 6)