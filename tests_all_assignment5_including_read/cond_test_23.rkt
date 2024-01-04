(if (and (not (let ([ x (if (< 3 4) (+ 1 2) (+ 3 4))]) (if (< x 5) #t
                                                           (not
                                                             (if (and (eq? 2 2) (eq? 0 0))
                                                                 #t
                                                                 #f
                                                              )
                                                            )
                                                           ))) #t) (+ 3 (+ 2 (- 6))) (+ 1 2))