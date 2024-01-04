(let
    ([x
      (let
          ([y (+ 8 (- 4 (read)))])
        (+ y (- 10))
       )
      ])
  (+ (read) (let
          ([z (+ x (read))])
              (- z (+ x (- 4)))
            )
     )
  )