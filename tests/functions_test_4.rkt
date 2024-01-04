(define (f1 [y : Integer]) : Integer (if (not (and (and (or (< y 4) (>= 5 y)) (< y 12)) #t)) (+ 5 (- 6 (- 7))) (+ 6 9)))
(define (computeInt [z : Boolean]) : Integer (let ([x (and #t z)]) (if x (let ([x 5]) x) (let ([x 13]) x))))
(f1 (computeInt #f))