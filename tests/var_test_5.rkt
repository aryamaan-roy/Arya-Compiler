(let ([x
       (let ([x 0]) (- x 5))
       ]) (+ x
             (let ([x 6]) x)
             ))
