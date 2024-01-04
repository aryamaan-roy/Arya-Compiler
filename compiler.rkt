
#lang racket
(require racket/set racket/stream)
(require graph)
(require racket/dict)
(require racket/fixnum)
(require "interp-Lint.rkt")
(require "interp-Lvar.rkt")
(require "interp-Cvar.rkt")
(require "type-check-Lvar.rkt")
(require "type-check-Cvar.rkt")


(require "interp-Lif.rkt")
(require "interp-Cif.rkt")
(require "type-check-Lif.rkt")
(require "type-check-Cif.rkt")

(require "interp-Lfun.rkt")
(require "interp-Cfun.rkt")
(require "type-check-Lfun.rkt")
(require "type-check-Cfun.rkt")
(require "interp-Lfun-prime.rkt")

(require "utilities.rkt")
(require "interp.rkt")
(require "graph-printing.rkt")
(require "priority_queue.rkt")
(require "multigraph.rkt")
(provide (all-defined-out))


;; Shrink pass for L_if


(define (shrink p)
  (define (shrink-inner inner_p)
    (match inner_p
      [(Bool b) (Bool b)]
      [(Int x) (Int x)]
      [(Var x) (Var x)]
      [(Let x e body) (Let x (shrink-inner e) (shrink-inner body))]
      [(If cnd thn els) (If (shrink-inner cnd) (shrink-inner thn) (shrink-inner els))]
      [(Prim 'and (list e1 e2))
       (If (shrink-inner e1) (shrink-inner e2) (Bool #f))]
      [(Prim 'or (list e1 e2)) (If (shrink-inner e1) (Bool #t) (shrink-inner e2))]
      [(Prim op es) (Prim op (for/list ([e es]) (shrink-inner e)))]
      [(Apply var lst) (Apply var (for/list ([i (in-list lst)]) (shrink-inner i)))]
      [(Def var lst type info exp) (Def var lst type info (shrink-inner exp))]
      [else (error "error in shrink, match not found" inner_p)]
      ))      
  (match p
    [(ProgramDefsExp '() defs ins)
     (define new_main (Def 'main '() 'Integer '() ins))
     (ProgramDefs '()
                  (for/list ([i (in-list (append defs (list new_main)))])
                    (match i
                      [(Def name vars ret_type info body) (Def name vars ret_type info (shrink-inner body))])))]))
     

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; uniquify : R1 -> R1
(define (uniquify p)
  (define (uniquify-inner env e)
    (match e
      [(Bool b) (Bool b)]
      [(Var x) (Var (dict-ref env x))]
      [(Int n) (Int n)]
      [(Let x e body)
       (let ([new-env (dict-set env x (gensym "x"))])
         (define uniquified_variable (dict-ref new-env x) )
         (define uniquified_expression (uniquify-inner env e))
         (define uniquified_body (uniquify-inner new-env body))
         (Let uniquified_variable uniquified_expression uniquified_body)
         )]
      [(If cnd thn els) (If (uniquify-inner env cnd) (uniquify-inner env thn) (uniquify-inner env els))]
      [(Prim op es) (Prim op (for/list ([e es]) (uniquify-inner env e)))]
      [(Apply var lst) (Apply var (for/list ([i (in-list lst)]) (uniquify-inner env i)))]
      [(Def var lst type info ins)
       (define new_lst '())
       (for ([i (in-list lst)])
         (define curr_var (gensym "x"))
         (set! new_lst (append new_lst (list (cons curr_var (cdr i)))))
         (set! env (dict-set env (car i) curr_var)))
       (Def var new_lst type info (uniquify-inner env ins))]
      ))
  (match p
    [(ProgramDefs info defs) (ProgramDefs info (for/list ([i (in-list defs)]) (uniquify-inner '() i)))]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(define (reveal_functions p)
  (define (reveal_functions_inner ins)
    (match ins
      [(Var x) (Var x)]
      [(Int n) (Int n)]
      [(Bool b) (Bool b)]
      [(Let x e body) (Let (reveal_functions_inner x) (reveal_functions_inner e) (reveal_functions_inner body))]
      [(If cnd thn els) (If (reveal_functions_inner cnd) (reveal_functions_inner thn) (reveal_functions_inner els))]
      [(Prim op es) (Prim op (for/list ([i (in-list es)]) (reveal_functions_inner i)))]
      [(Def var lst type info exp) (Def var lst type info (reveal_functions_inner exp))]
      [(Apply (Var f) lst)
       (Apply (FunRef f (length lst)) (for/list ([i (in-list lst)]) (reveal_functions_inner i)))
       ]
      [else ins]
      ))
  (match p
    [(ProgramDefs info defs) (ProgramDefs info (for/list ([i (in-list defs)]) (reveal_functions_inner i)))]))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (is-atm? p)
  (match p
    [(Int n) #t]
    [(Var x) #t]
    [(Bool b) #t]
    [(Prim 'read '()) #t]
    [(Let x e body) (and (is-atm? x) (is-atm? e) (is-atm? body))]
    [(Prim 'not (list e1)) (or (Int? e1) (Var? e1) (and (Let? e1) (is-atm? e1)))]
    [(Prim 'op (list e1 e2)) (and (or (Int? e1) (Var? e1) (and (Let? e1) (is-atm? e1))) (or (Int? e2) (Var? e2) (and (Let? e2) (is-atm? e2))))]
    [(Apply var lst)
     (define curr_and_here (is-atm? var))
     (for/list ([i (in-list lst)]) (set! curr_and_here (and curr_and_here (is-atm? i))))
     curr_and_here
     ]
    [(FunRef f len_lst) #f]
    [else #f]
    ))


(define (rco-atm env p)
  (if (is-atm? p) p
      (match p
        [(Int n) (Return (Int n))]
        [(Var x) (Return (Var x))]
        [(Bool b) (Return (Bool b))]
        [(Prim 'read '()) (Return p)]
        [(If cnd thn els) (If (rco-exp env cnd) (rco-exp env thn) (rco-exp env els))]
        [(Let x e body)
         (define new-exp
           (if (is-atm? e) e (rco-atm env e)))
         (define new-body
           (if (is-atm? body) body (rco-atm env body)))
         (Let x new-exp new-body)]
        [(Prim op (list e1 e2))
         (if (and (is-atm? e1) (is-atm? e2))
             ;p
             (let ([var-here (gensym "hemlu")] [var-here-2 (gensym "hemlu")]) (Let var-here e1 (Let var-here-2 e2 (Prim op (list (Var var-here) (Var var-here-2))))))
             (if (or (is-atm? e1) (is-atm? e2))
                 (if (is-atm? e1)
                     (let ([var-here (gensym "hemlu")] [var-here-2 (gensym "hemlu")]) (Let var-here e1 (Let var-here-2 (rco-atm env e2) (Prim op (list (Var var-here) (Var var-here-2))))))
                     (let ([var-here (gensym "hemlu")] [var-here-2 (gensym "hemlu")]) (Let var-here (rco-atm env e1) (Let var-here-2 e2 (Prim op (list (Var var-here) (Var var-here-2))))))
                     )                 
                 (let ([var-here (gensym "ans")] [var-here-2 (gensym "ans")]) (Let var-here (rco-exp env e1) (Let var-here-2 (rco-exp env e2) (Prim op (list (Var var-here) (Var var-here-2))))
                                                                                   ))))]
        [(Prim '- (list e1)) (rco-exp '() (Prim '- (list (Int 0) e1)))]
        [(Prim 'not (list e1))
         (if (is-atm? e1)
             p
             (let ([var-here (gensym "hemlu")]) (Let var-here (rco-atm env e1) (Prim 'not (list (Var var-here))))))]
        [(FunRef f len_lst) p]
        [(Apply (FunRef f l) lst) (define new_var (gensym "hemlu"))
                                  (Let new_var (FunRef f l) (rco-exp env (Apply (Var new_var) lst)))]
        [(Apply (Var x) lst)
         (define curr_flag #f)
         (define new_var 0)
         (define first_non_atomic -1)
         (define new_args '())
         (if (is-atm? p)
             p
             (begin               
               (set! new_args
                     (for/list ([i (in-list lst)])
                       (if (or (is-atm? i) curr_flag)
                           i
                           (begin
                             (set! curr_flag #t)
                             (set! first_non_atomic i)
                             (set! new_var (gensym "hemlu"))
                             (Var new_var)))))
               (if (equal? new_var 0)
                   p
                   (Let new_var (rco-atm env first_non_atomic) (rco-atm env (Apply (Var x) new_args)))))
             )
         ]             
        [else p]
        )))

(define (rco-exp env p)
  (match p
    [(Int n) p]
    [(Var x) p]
    [(Bool b) (Bool b)]
    [(Let x e body) (Let x (rco-exp env e) (rco-exp env body))]
    [(Prim op es) (rco-atm env p)]
    [(If cnd thn els) (If (rco-exp env cnd) (rco-exp env thn) (rco-exp env els))]
    [(FunRef f len_lst) (FunRef f len_lst)]
    [(Apply var lst) (rco-atm env p)]
     ))

(define (remove-complex-opera* p)
  (match p
    [(ProgramDefs info defs) (ProgramDefs info (for/list ([i (in-list defs)])
                                                 (match i
                                                   [(Def func a b c ins) (Def func a b c (rco-exp '() ins))]                                                  
                                                   )))]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; explicate-control : R1 -> C0

(define basic-blocks `())

(define (create_block tail)
  (match tail
    [(Goto label) (Goto label)]
    [else
     (let ([label (gensym 'block)]) (set! basic-blocks (cons (cons label tail) basic-blocks))
       (Goto label))]))

(define (explicate_pred cnd thn els)
  (define label_thn (create_block thn))
  (define label_els (create_block els))
  (match cnd
    [(Var x) (IfStmt (Prim 'eq? (list (Var x) (Bool #t))) label_thn label_els)]
    [(Bool b) (IfStmt (Prim 'eq? (list (Bool b) (Bool #t))) label_thn label_els)]
    ;[(Bool b) (if b thn els)]
    [(Let x rhs body)
     (explicate-assign rhs x (explicate_pred body label_thn label_els))]
    [(Prim 'not (list e)) (IfStmt (Prim 'eq? (list e (Bool #f))) label_thn label_els)]
    [(Prim op es)
     ; #:when (or (eq? op 'eq?) (eq? op '<))
                (IfStmt (Prim op es) label_thn label_els)]
    [(If cnd^ thn^ els^)
     (define cont_thn label_thn)
     (define cont_els label_els)
     (define cont_thn^ (explicate_pred thn^ cont_thn cont_els))
     (define cont_els^ (explicate_pred els^ cont_thn cont_els))
     (explicate_pred cnd^ cont_thn^ cont_els^)
     ]
    [(Apply f lst)
     (define new_var (gensym "hemlu"))
     (define cont_here (IfStmt (Prim 'eq? (list (Var new_var) (Bool #t))) label_thn label_els))
     (explicate_pred cnd new_var cont_here)
     ] 
    [else (error "explicate_pred unhandled case" cnd)]))


(define (explicate-assign e x cont)
  (match e
    [(Var y) (Seq (Assign (Var x) (Var y) ) cont)]
    [(Int n) (Seq (Assign (Var x) (Int n)) cont)]
    [(Bool b) (Seq (Assign (Var x) (Bool b)) cont)]
    [(FunRef f l) (Seq (Assign (Var x) (FunRef f l)) cont)]
    [(Let y rhs body) (define new-body (explicate-assign body x cont))
                      (explicate-assign rhs y new-body)]
    [(Prim op es) (Seq (Assign (Var x) (Prim op es)) cont)]
    [(If cnd thn els)
     (define cont_block (create_block cont))
     (define new-thn (explicate-assign thn x cont_block))
     (define new-els (explicate-assign els x cont_block))
     (explicate_pred cnd new-thn new-els)]
    [(Apply f lst) (Seq (Assign (Var x) (Call f lst)) cont)]
    [else (error "explicate_assign unhandled case" e)]))

(define (explicate-tail e)
  (match e
    [(Var x) (Return (Var x))]
    [(Int n) (Return (Int n))]
    [(Bool b) (Return (Bool b))]
    [(Let x rhs body) (define new-body (explicate-tail body))
                      (explicate-assign rhs x new-body)]
    [(Prim op es) (Return (Prim op es))]
    [(If cnd thn els) (define new-thn (explicate-tail thn))
                      (define new-els (explicate-tail els))
                      (explicate_pred cnd new-thn new-els)]
    [(Apply f lst) (TailCall f lst)]
    [else (error "explicate_tail unhandled case" e)]))



(define (explicate-control p)
  (set! basic-blocks '())
  (define (tidy-func body)
    (define output
      (for/list ([i (in-list body)])
        (set! basic-blocks '())
        (match i
          [(Def name vars ret_type info ins)
           (Def name vars ret_type info
                (cons
                 (cons
                  (string->symbol (string-append (symbol->string name) "start"))
                  (explicate-tail ins)) basic-blocks))])))
    output    
    )
  (match p
    [(ProgramDefs info defs) (ProgramDefs info (tidy-func defs))]))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; The following is the code for select-instructions

(define (figure-it-out p)
  (match p
    [(Int p) (Imm p)]
    [(Var p) (Var p)]
    [(Bool #t) (Imm 1)]
    [(Bool #f) (Imm 0)]
    [else (error "error in figure-it-out")]))

(define (get-cc-flag p)
  (match p
    [(Prim 'eq? (list e1 e2)) 'e]
    [(Prim '< (list e1 e2)) 'l]
    [(Prim '<= (list e1 e2)) 'le]
    [(Prim '> (list e1 e2)) 'g]
    [(Prim '>= (list e1 e2)) 'ge]))

(define (select-inner-func-2 lst p label)
  (define concluding_label (string->symbol (string-append (symbol->string label) "conclusion")))
  (define push_caller_saved
    (list (Instr 'pushq (list (Reg 'rax)))
          (Instr 'pushq (list (Reg 'rcx)))
          (Instr 'pushq (list (Reg 'rdx)))
          (Instr 'pushq (list (Reg 'rsi)))
          (Instr 'pushq (list (Reg 'rdi)))
          (Instr 'pushq (list (Reg 'r8)))
          (Instr 'pushq (list (Reg 'r9)))
          (Instr 'pushq (list (Reg 'r10)))
          (Instr 'pushq (list (Reg 'r11)))))

  (define pop_caller_saved
    (list (Instr 'popq (list (Reg 'r11)))
          (Instr 'popq (list (Reg 'r10)))
          (Instr 'popq (list (Reg 'r9)))
          (Instr 'popq (list (Reg 'r8)))
          (Instr 'popq (list (Reg 'rdi)))
          (Instr 'popq (list (Reg 'rsi)))
          (Instr 'popq (list (Reg 'rdx)))
          (Instr 'popq (list (Reg 'rcx)))
          (Instr 'popq (list (Reg 'rax)))))
  (define lst_arg_passing (list (Reg 'rdi) (Reg 'rsi) (Reg 'rdx) (Reg 'rcx) (Reg 'r8) (Reg 'r9)))
  (match p
    [(Assign x body)
     (append lst (match body
                   [(Int e1) (list (Instr 'movq (list (Imm e1) x)))]
                   [(Var y) (list (Instr 'movq (list (Var y) x)))]
                   [(Bool #t) (list (Instr 'movq (list (Imm 1) x)))]
                   [(Bool #f) (list (Instr 'movq (list (Imm 0) x)))]
                   [(Prim '+ (list e1 e2))
                    (list (Instr 'movq (list (figure-it-out e1) x )) (Instr 'addq (list (figure-it-out e2) x ))
                          )]
                   [(Prim '- (list e1 e2))
                    (list (Instr 'movq (list (figure-it-out e1) x )) (Instr 'subq (list (figure-it-out e2) x ))
                          )]
                   [(Prim '- (list e1))
                    (if (Var? e1)
                        (list (Instr 'negq (list e1)) (Instr 'movq (list e1 x)))
                        (list (Instr 'movq (list (Imm (Int-value e1)) x)) (Instr 'negq (list x)) )
                        )
                    ]
                   [(Prim 'read '()) (list (Callq 'read_int 0) (Instr 'movq (list (Reg 'rax) x)))]
                   [(Prim 'not (list e1))
                    (if (eq? x e1) (list (Instr 'xorq (list (Imm 1) (figure-it-out e1))))
                        (list (Instr 'movq (list (figure-it-out e1) x)) (Instr 'xorq (list (Imm 1) x))))
                    ]
                   [(Prim op (list e1 e2))
                    (list
                     (Instr 'cmpq (list (figure-it-out e2) (figure-it-out e1)))
                     (Instr 'set (list (get-cc-flag body) (ByteReg 'al)))
                     (Instr 'movzbq (list (ByteReg 'al) x)))]
                   [(FunRef l i) (list (Instr 'leaq (list (Global l) (Reg 'rax)))
                                       (Instr 'movq (list (Reg 'rax) x)))]
                   [(Call e1 lst)
                    (define temp_lst '())
                    (define count 0)                    
                    (set! temp_lst (append temp_lst push_caller_saved))
                    (for ([e2 (in-list lst)])
                      (set! temp_lst (append temp_lst (list (Instr 'movq (list (figure-it-out e2) (list-ref lst_arg_passing count))))))
                      ;(set! temp_lst (append temp_lst (list (Instr 'movq (list (list-ref lst_arg_passing count) (figure-it-out e2))))))
                      (set! count (+ count 1)))
                    (set! temp_lst (append temp_lst (list (IndirectCallq e1 (length lst)) (Instr 'movq (list (Reg 'rax) x)))))
                    (set! temp_lst (append temp_lst pop_caller_saved))
                    temp_lst
                    ]                   
                   [else (error "Error in select instructions func 2, match not found" body)]
                   ))]
    [(Var x) (append lst (list (Instr 'movq (list (Var x) (Reg 'rax))) (Jmp concluding_label)))]
    [(Int x) (append lst (list (Instr 'movq (list (Imm x) (Reg 'rax))) (Jmp concluding_label)))]
    [(Prim '+ (list e1 e2))
     (append lst (list (Instr 'movq (list (figure-it-out e1) (Reg 'rax ))) (Instr 'addq (list (figure-it-out e2) (Reg 'rax) ))
                       (Jmp concluding_label)))]
    [(Prim '- (list e1 e2))
     (append lst (list (Instr 'movq (list (figure-it-out e1) (Reg 'rax) )) (Instr 'subq (list (figure-it-out e2) (Reg 'rax) ))
                       (Jmp concluding_label)))]
    [(Prim '- (list e1))
     (if (Var? e1)
         (append lst (list (Instr 'negq (list e1)) (Instr 'movq (list e1 (Reg 'rax))) (Jmp concluding_label)))
         (append lst (list (Instr 'movq (list (Imm (Int-value e1)) (Reg 'rax))) (Instr 'negq (list (Reg 'rax))) (Jmp concluding_label) ))
         )
     ]
    [(Prim 'read '()) (append lst (list (Callq 'read_int 0) (Jmp concluding_label)))]
    [else (error "Error in select instructions func 2, outer match not found" p)]
    ))

(define (extract-label p)
  (match p
    [(Goto label) label]))

(define (select-inner-func lst body label)
  (define lst_arg_passing (list (Reg 'rdi) (Reg 'rsi) (Reg 'rdx) (Reg 'rcx) (Reg 'r8) (Reg 'r9)))
  (match body
    [(Seq assign_t second_seq) (append lst (select-inner-func-2 lst assign_t label) (select-inner-func lst second_seq label))]
    [(Return body) (append lst (select-inner-func-2 lst body label))]
    [(Goto label) (append lst (list (Jmp label)))]
    [(IfStmt cnd thn els)
     (match cnd
       [(Prim op (list e1 e2)) (append lst (list (Instr 'cmpq (list (figure-it-out e2) (figure-it-out e1))) (JmpIf (get-cc-flag cnd) (extract-label thn)) (Jmp (extract-label els)))) ]
       )]
    [(TailCall f lst)
     (define temp_lst '())
     (define count 0)
     (for ([e2 (in-list lst)])
       (set! temp_lst (append temp_lst (list (Instr 'movq (list (figure-it-out e2) (list-ref lst_arg_passing count))))))
       (set! count (+ count 1)))
     (set! temp_lst (append temp_lst (list (TailJmp f (length lst)))))
     temp_lst
     ]
    [else (error "Error in select ins func1, match not found" body)]
    ))


(define (select-instructions-helper-for-func p)
  (define lst_here '())
  (match p
    [(Def label lst1 type info lst2)
     (for ([b (in-list lst2)])
       (set! lst_here (dict-set lst_here (car b) (Block '() (select-inner-func '() (cdr b) label))))
       )
;     (Def label '() type (dict-set info 'num-params (length lst1)) lst_here)]))
     (Def label lst1 type (dict-set info 'num-params (length lst1)) lst_here)]))

(define (select-instructions-helper-add-argReg-to-var p)
  (define lst_arg_passing (list (Reg 'rdi) (Reg 'rsi) (Reg 'rdx) (Reg 'rcx) (Reg 'r8) (Reg 'r9)))
  (match p
    [(Def label lst1 type info lst2)
     (define lst_arg_reg_used (take lst_arg_passing (length lst1)))
     (define itr -1)
     (define new_lst (for/list ([i (in-list lst_arg_reg_used)]) (set! itr (+ itr 1)) (Instr 'movq (list i (Var (car (list-ref lst1 itr)))))))
     (define itr2 0)
     (define new_def_lst
       (for/list ([i (in-list lst2)])
         (if (equal? (car i) (string->symbol (string-append (symbol->string label) "start")))
         ;(if (equal? itr2 0)
             (begin
               (set! itr2 (+ itr2 1))
               (cons (car i) 
                     (match (cdr i)
                       [(Block info body) (Block info (append new_lst body))])))
             i
             )))
       
     (Def label '() type info new_def_lst)]))

(define (select-instructions p)
  (define final-body '())
  (match p
    [(ProgramDefs info body)
     (for ([b (in-list body)])       
       (set! final-body (append final-body (list (select-instructions-helper-add-argReg-to-var (select-instructions-helper-for-func b))))))
     (X86Program info final-body)
     ]
    )
  )



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(define (inner_live_3 ins lst label)
  (define concluding_label (string->symbol (string-append (symbol->string label) "conclusion")))
  (define caller_s (set (Reg 'rax) (Reg 'rcx) (Reg 'rdx) (Reg 'rsi) (Reg 'rdi) (Reg 'r8) (Reg 'r9) (Reg 'r10) (Reg 'r11)))
  (define arg_passing (list (Reg 'rdi) (Reg 'rsi) (Reg 'rdx) (Reg 'rcx) (Reg 'r8) (Reg 'r9)))
  (define set_last (list-ref lst (- (length lst) 1)))
  (match ins
    [(Instr 'pushq (list e1)) (append lst (list (set-union set_last (set e1))))]
    [(Instr 'popq (list e1)) (append lst (list (set-subtract set_last (set e1))))]
    [(Instr 'movq (list (Imm e1) e2)) (if (set-member? set_last e2)
                                    (let ([set_here (set-union (set-subtract set_last (set e2)) )]) (append lst (list set_here)))
                                    lst)]
    [(Instr 'addq (list (Imm e1) e2)) (append lst (list (set-union set_last (set e2))))]
    [(Instr 'subq (list (Imm e1) e2)) (append lst (list (set-union set_last (set e2))))]
    [(Instr 'negq (list (Imm e1))) lst]
    [(Instr 'xorq (list (Imm e1) e2))
     (append lst (list (set-union set_last (set e2))))
     ]
    [(Instr 'movq (list e1 e2))
     (if (set-member? set_last e2)
         (let ([set_here (set-union (set-subtract set_last (set e2)) (set e1))]) (append lst (list set_here)))
         (append lst (list (set-union set_last (set e1)))))]
    
    [(Instr 'addq (list e1 e2)) (append lst (list (set-union set_last (set e1 e2))))]
    [(Instr 'subq (list e1 e2)) (append lst (list (set-union set_last (set e1 e2))))]
    [(Instr 'negq (list e1)) (append lst (list (set-union set_last (set e1))))]    
    [(Instr 'xorq (list e1 e2))
     (append lst (list (set-union set_last (set e1 e2))))
     ]
    [(Instr 'cmpq (list (Imm e1) (Imm e2)))
     (append lst (list set_last))]
    [(Instr 'cmpq (list (Imm e1) e2))
     (append lst (list (set-union set_last (set e2))))]
    [(Instr 'cmpq (list e1 (Imm e2)))
     (append lst (list (set-union set_last (set e1 ))))]
    [(Instr 'cmpq (list e1 e2))
     (append lst (list (set-union set_last (set e1 e2))))]
    [(Instr 'set (list cc e1))
     (if (set-member? set_last (Reg 'rax))
         (let ([set_here (set-subtract set_last (set (Reg 'rax)))]) (append lst (list set_here)))
         (append lst (list set_last)))
     ]
    [(Instr 'movzbq (list e1 e2))
     (if (set-member? set_last e2)
         (let ([set_here (set-union (set-subtract set_last (set e2)) (set (Reg 'rax)))]) (append lst (list set_here)))
         (append lst (list (set-union set_last (set (Reg 'rax))))))
     ]
    ;[(Jmp 'conclusion) (append lst (list (set-union set_last (set (Reg 'rax) (Reg 'rsp)))))]
    [(Jmp concluding_label) (append lst (list (set-union set_last (set (Reg 'rax) (Reg 'rsp)))))]
    [(JmpIf cc label) (append lst (list set_last))]
    [(Jmp label) (append lst (list set_last))]
    [(Callq 'read_int e1) (append lst (list (set-subtract set_last caller_s)))]
    [(IndirectCallq reg int)
     (define arg_pass_reg_here (take arg_passing int))
     (define set_here_read_regs (list->set (append arg_pass_reg_here (list reg))))
     (append lst (list (set-union (set-subtract set_last caller_s) set_here_read_regs)))]

    [(TailJmp arg int)
     ;(define arg_pass_reg_here (take arg_passing int))
     (define arg_pass_reg_here arg_passing)
     (define set_here_read_regs (list->set (append arg_pass_reg_here (list arg))))
     (append lst (list (set-union set_last set_here_read_regs)))]
    [(Instr 'leaq (list label reg))
     (append lst (list (set-subtract set_last (set reg))))]
    [else (error "Match not found in inner_live_3," ins)]
    ;[else (append lst (list (set-union (set 'nahi) set_last)))]
    ))
  
(define (inner_live_2 starting_lst body label)
  ;; We need to make a list of sets, initally list will have 1 set ie/ {phie}
  (for ([e (in-list (reverse body))]) (set! starting_lst (inner_live_3 e starting_lst label)))
  starting_lst
)

(define global_liveliness '())


(define (inner_live label starting_lst body)
  (match body
    [(Block info inner_body)
     (define output (inner_live_2 starting_lst inner_body label))
     (set! global_liveliness (dict-set global_liveliness label (car (reverse output))))
     (Block (dict-set info 'liveness output) inner_body)]))
  

(define (uncover_live p)
  (set! global_liveliness '())
  ;(define my-multig (make-multigraph '()))
  (define (append-to-multig g n1 n2 label)
    (define concluding_label (string->symbol (string-append (symbol->string label) "conclusion")))
    (match n2
      [(Block info body)
       (for ([e (in-list body)])
         (match e
           [(Goto label)
            (add-vertex! g n1)
            (add-vertex! g label)
            (add-directed-edge! g n1 label)]
           [(Jmp label)
            (add-vertex! g n1)
            (add-vertex! g label)
            (add-directed-edge! g n1 label)]
           [(JmpIf cc label)
            (add-vertex! g n1)
            (add-vertex! g label)
            (add-directed-edge! g n1 label)]
           [(TailJmp arg int)
            (add-vertex! g n1)
            (add-vertex! g concluding_label)
            (add-directed-edge! g n1 concluding_label)]
           [else null]
           ))]
      ))
  (define (uncover-live-helper p)
    (set! global_liveliness '())
    (define my-multig (make-multigraph '()))
    (match p
      [(Def label '() type info body)
       (for ([e (in-list body)]) (append-to-multig my-multig (car e) (cdr e) label))
       (set! my-multig (transpose my-multig))
       
       (define cfg (tsort my-multig))
       ;(define new_multig 
       (set! my-multig (transpose my-multig))
       ;(define new_cfg (tsort my-multig))
       (define itr 0)
       (define final-body '())
       (define my_set (set))
       (define starting_lst (list my_set))
       (define curr_neigh '())
       (define output 0)
       (define concluding_label (string->symbol (string-append (symbol->string label) "conclusion")))
       (for ([e (in-list cfg)])
         (if (eq? itr 0)
             (set! itr (+ itr 1))
             (begin
               (set! curr_neigh (get-neighbors my-multig e))
               (set! my_set (set))
               (for ([n (in-list curr_neigh)])
                 (if (eq? n concluding_label)
                     (set! my_set (set))
                     (set! my_set (set-union my_set (dict-ref global_liveliness n))))
                 )
             
               (set! output (inner_live e (list my_set) (dict-ref body e)))
               (set! final-body (dict-set final-body e output))
               )))
       (Def label '() type info final-body)]))

  (match p
    [(X86Program info lst_defs)
     (X86Program info (for/list ([i (in-list lst_defs)]) (uncover-live-helper i)))]))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Build Interference

(define (inner_build_interference3 curr_instr prev_set next_set grph)
  (define set_1 next_set)
  (match curr_instr
    [(Instr 'cmpq (list e1 e2)) grph]
    [(Instr op (list (Imm e1) e2))
     (for ([v1 (in-set set_1)])
       (if (equal? v1 e2) null
       (add-edge! grph v1 e2)))
     grph]
    [(Instr 'movq (list e1 e2))
     (match e2 [(Imm x) (error "second wala")] [else 0])
     (for ([v1 (in-set set_1)])
       (if (or (equal? v1 e1) (equal? v1 e2))
           ; then
           null
           ; else
           (add-edge! grph v1 e2)
           ) 
       )
     grph
     ]
    [(Instr 'movzbq (list e1 e2))
     (match e2 [(Imm x) (error "third wala")] [else 0])
     (for ([v1 (in-set set_1)])
       (if (or (equal? v1 (Reg 'rax)) (equal? v1 e2))
           ; then
           null
           ; else
           (add-edge! grph v1 e2)
           ) 
       )
     grph
     ]
    
    [(Instr 'set (list cc e))
     (for ([v1 (in-set set_1)])
       (if (equal? v1 (Reg 'rax)) null
       (add-edge! grph v1 (Reg 'rax))))
     grph]
    [(Instr op (list e1 e2))
     (match e2 [(Imm x) (error "fourth wala")] [else 0])
     (for ([v1 (in-set set_1)])
       (if (equal? v1 e2) null
           (add-edge! grph v1 e2)))
     grph]
    [(Instr op (list e1))
     (match e1 [(Imm x) (error "fifth wala")] [else 0])
     (for ([v1 (in-set set_1)])
       (if (equal? v1 e1) null
           (add-edge! grph v1 e1)))
     grph
     ]
    [(IndirectCallq arg int) grph]
    [(Instr 'leaq (list label reg))
     (for ([v1 (in-set set_1)])
       (if (equal? v1 (Reg 'rax)) null
       (add-edge! grph v1 (Reg 'rax))))
     grph]
    [else grph]
    ))
           

(define (inner_build_interference2 myg lst_set lst_instr)
  ;(define myg (undirected-graph (list (list (Reg 'rax) (Reg 'rsp)))))
  (define itr 0)
  (define len_lst_set (length lst_set))
  (for ([e (in-list lst_instr)])
    (if (< (+ itr 1) len_lst_set)
        (begin
          (set! myg (inner_build_interference3 e (list-ref lst_set itr) (list-ref lst_set (+ itr 1)) myg))
          (set! itr (+ itr 1)))
        null))
  myg
  )

(define (inner_build_interference p)
  (define myg (undirected-graph (list (list (Reg 'rax) (Reg 'rsp)))))
  (for ([n_block (in-list p)])
    (match (cdr n_block)
      [(Block info body)
       (set! myg (inner_build_interference2 myg (reverse (dict-ref info 'liveness )) body))]))
  myg
  )
  

(define (build_interference p)
  (match p
    [(X86Program info lst_def)
     (X86Program info
                 (for/list ([i (in-list lst_def)])
                   (match i
                     [(Def label '() type info lst_blocks)
                      (Def label '() type (dict-set info 'conflicts (inner_build_interference lst_blocks)) lst_blocks)])))]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Graph Coloring


(struct pq_node (Vertex Set))

(define (pq_cmp node_1 node_2)
  (define l1 (set-count (pq_node-Set node_1)))
  (define l2 (set-count (pq_node-Set node_2)))
  (if (> l1 l2)
      #t
      #f)
  )

(define (get_lowest_positive node_here set_here)
  ; This is the OG list
  (define register_lst (list (Reg 'rcx) (Reg 'rdx) (Reg 'rsi) (Reg 'rdi) (Reg 'r8) (Reg 'r9) (Reg 'r10) (Reg 'rbx) (Reg 'r12) (Reg 'r13) (Reg 'r14)))
  ;(define register_lst (list (list (Reg 'r10) (Reg 'rbx) (Reg 'r12) (Reg 'r13) (Reg 'r14) (Reg 'rcx) (Reg 'rdx) (Reg 'rsi) (Reg 'rdi) (Reg 'r8) (Reg 'r9))))
  (set! set_here (sort (set->list set_here) <))

  ;(if (equal? node_here (Var 'hemlu172334))
  ;    (println set_here)
  ;    null)
  
  (define (get_lowest_positive_var node_here set_here)
    (define output 0)
    (define flag 1)
    (for ([e (in-range 50)])
      (if (set-member? set_here e)
          null
          (if (equal? flag 1)
              (begin (set! output e) (set! flag 0))
              (set! flag 0)
              )))
    output)
  (define (get_lowest_positive_reg node_here set_here reg_lst)
    (define reg_number 0)
    (define flag #t)
    (for ([i (in-list reg_lst)])
      (if (and (equal? node_here i) flag)
          (begin
            (set! flag #f))
          (if (equal? flag #t)
              (set! reg_number (+ reg_number 1))
              null)))
    reg_number)

  (define exists #f)
  (for ([i (in-list register_lst)])
    (if (equal? i node_here)
        (set! exists #t)
        null))
  (define output 0)
  (if (equal? exists #t)
      (set! output (get_lowest_positive_reg node_here set_here register_lst))
      (set! output (get_lowest_positive_var node_here set_here)))
  output)

  

(define (color-graph grph lst_vertices)
  (define register_lst (list (Reg 'rcx) (Reg 'rdx) (Reg 'rsi) (Reg 'rdi) (Reg 'r8) (Reg 'r9) (Reg 'r10) (Reg 'rbx) (Reg 'r12) (Reg 'r13) (Reg 'r14)))
  
  (define mypq (make-pqueue pq_cmp))

  (set! lst_vertices (remove (Reg 'rax) lst_vertices))
  (set! lst_vertices (remove (Reg 'rsp) lst_vertices))

  (define vertex_to_handle
    (for/list ([e (in-list lst_vertices)])
      (cons e (pqueue-push! mypq (pq_node e (set) )))))
  
  (define vertex_to_register `())
  (set! vertex_to_register (dict-set vertex_to_register (Reg 'rax) -1))
  (set! vertex_to_register (dict-set vertex_to_register (Reg 'rsp) -2))
  
  (define neigh_rax (get-neighbors grph (Reg 'rax)))
  (set! neigh_rax (remove (Reg 'rsp) neigh_rax))
  (for ([e (in-list neigh_rax) ])
    (define handle_here (dict-ref vertex_to_handle e))
    (set-node-key! handle_here (pq_node e (set -1)))
    (pqueue-decrease-key! mypq handle_here)
    )
  
  (define neigh_rsp (get-neighbors grph (Reg 'rsp)))
  (set! neigh_rsp (remove (Reg 'rax) neigh_rsp))
  (for ([e (in-list neigh_rsp) ])
    (define handle_here (dict-ref vertex_to_handle e))
    (set-node-key! handle_here (pq_node e (set-union (pq_node-Set (node-key handle_here)) (set -2))))
    (pqueue-decrease-key! mypq handle_here)
    )

  (remove-vertex! grph (Reg 'rax))
  (remove-vertex! grph (Reg 'rsp))

  (define (halla_bol grph reg vertex_to_handle reg_lst)
    (define neigh (get-neighbors grph reg))
    ;(if (equal? reg (Reg 'rsi))
    ;    (println neigh)
    ;    null)
    (define col_here 0)
      (define flag #f)
      (for ([i (in-list reg_lst)])
        (cond
          [(equal? flag #t) null]
          [(equal? i reg) (set! flag #t)]
          [else (set! col_here (+ 1 col_here))]))

    (for ([e (in-list neigh)])
      (define handle_here (dict-ref vertex_to_handle e))
      
      (set-node-key! handle_here (pq_node e (set-union (pq_node-Set (node-key handle_here)) (set col_here))))
      (pqueue-decrease-key! mypq handle_here)
        ;(remove-vertex! grph reg)
      ))

  (for ([i (in-list lst_vertices)])
    (if (Reg? i)
        (halla_bol grph i vertex_to_handle register_lst)
        null))
  
      

  
  
  (for ([index (in-range (length lst_vertices))])
    (define highest_struct (pqueue-pop! mypq))
    ;(println (pq_node-Vertex highest_struct))
    (define curr_color (get_lowest_positive (pq_node-Vertex highest_struct) (pq_node-Set highest_struct)))
    (for ([v (in-list (get-neighbors grph (pq_node-Vertex highest_struct)))])
         (define handle_here (dict-ref vertex_to_handle v))
          (set-node-key! handle_here (pq_node v (set-union (pq_node-Set (node-key handle_here)) (set curr_color))))
           (pqueue-decrease-key! mypq handle_here))
    (set! vertex_to_register (dict-set vertex_to_register (pq_node-Vertex highest_struct) curr_color))
    (remove-vertex! grph (pq_node-Vertex highest_struct))
    )
  vertex_to_register  
  )

(define (outer_color_graph p)
  (match p
    [(X86Program info body)
     (X86Program info
                 (for/list ([i (in-list body)])
                   (match i
                     [(Def label '() type info lst_blocks)
                      (define grph (dict-ref info 'conflicts))
                      (define lst_vertices (get-vertices (dict-ref info 'conflicts)))
                      (Def label '() type (dict-set info 'graph_colors (color-graph grph lst_vertices)) lst_blocks)])))]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Assign Homes Task

(define (assign-stack internal_list x)
  (match x
    [(Imm y) x]
    [(Var y) (define new_y 'timepass)
             (for ([e (in-list internal_list)])
               (if (equal? (car e) (Var y))
                   (set! new_y (cdr e))
                   null))
             (if (Reg? new_y)
                 new_y
                 (Deref 'rbp new_y))
             ]
    [else x]))

(define (internal-assign-homes-2 internal_list body)
  (match body
    [(Instr op (list l1 l2)) (Instr op (list (assign-stack internal_list l1) (assign-stack internal_list l2)))]
    [(Instr op (list l1)) (Instr op (list (assign-stack internal_list l1)))]
    [(TailJmp arg int) (TailJmp (assign-stack internal_list arg) int)]
    [(IndirectCallq arg int) (IndirectCallq (assign-stack internal_list arg) int)]
    [else body]))

(define (internal-assign-homes internal_list body)
  (define new-body '())
  (for ([b (in-list body)])
    (set! new-body (dict-set new-body (car b)
              (match (cdr b)
                [(Block info ins) (Block info (for/list ([curr_ins (in-list ins)]) (internal-assign-homes-2 internal_list curr_ins)))]))))
  new-body
  )

(define (callee_size p)
  (define lst_mapping_callee `())
  (set! lst_mapping_callee (dict-set lst_mapping_callee -2 8))
  (set! lst_mapping_callee (dict-set lst_mapping_callee -1 0))
  (set! lst_mapping_callee (dict-set lst_mapping_callee 0 0))
  (set! lst_mapping_callee (dict-set lst_mapping_callee 1 0))
  (set! lst_mapping_callee (dict-set lst_mapping_callee 2 0))
  (set! lst_mapping_callee (dict-set lst_mapping_callee 3 0))
  (set! lst_mapping_callee (dict-set lst_mapping_callee 4 0))
  (set! lst_mapping_callee (dict-set lst_mapping_callee 5 0))
  (set! lst_mapping_callee (dict-set lst_mapping_callee 6 0))
  (set! lst_mapping_callee (dict-set lst_mapping_callee 7 8))
  (set! lst_mapping_callee (dict-set lst_mapping_callee 8 8))
  (set! lst_mapping_callee (dict-set lst_mapping_callee 9 8))
  (set! lst_mapping_callee (dict-set lst_mapping_callee 10 8))
  (define count 0)

  (define graph_colors_here
    (match p
      [(Def label '() type info lst_blocks) (define graph_colors_here (dict-ref info 'graph_colors)) graph_colors_here]
;      [(X86Program info body) (define graph_colors_here (dict-ref info 'graph_colors))
;                              graph_colors_here]
      ))
  
  (for ([e (in-list graph_colors_here)])
    (if (and (not (equal? (cdr e) -1)) (not (equal? (cdr e) -2)) (< (cdr e) 11))
        (set! count (+ count (dict-ref lst_mapping_callee (cdr e))))
        null))
  (set! count (align count 16))
  count
  )
                          

(define (allocate-registers p)
  (define new_program (outer_color_graph p))
  ;(define count (callee_size new_program))
  (define register_lst (list (Reg 'rcx) (Reg 'rdx) (Reg 'rsi) (Reg 'rdi) (Reg 'r8) (Reg 'r9) (Reg 'r10) (Reg 'rbx) (Reg 'r12) (Reg 'r13) (Reg 'r14)))

  (match new_program
    [(X86Program info lst_defs)
     (X86Program info
                 (for/list ([i (in-list lst_defs)])
                   (match i
                     [(Def label '() type info lst_blocks)
                      (define count (callee_size i))
                      (define graph_colors (dict-ref info 'graph_colors))
                      (set! graph_colors (remove (cons (Reg 'rax) -1) graph_colors))
                      (set! graph_colors (remove (cons (Reg 'rsp) -2) graph_colors))
                      (define internal_list
                        (for/list ([hemlu graph_colors])
                          (if (< (cdr hemlu) 11)
                              (cons (car hemlu) (list-ref register_lst (cdr hemlu)))
                              (begin
                                (set! count (- count 8))
                                (cons (car hemlu) count)
                                ))))
                      (Def label '() type info (internal-assign-homes internal_list lst_blocks))])))]))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define global-lst '())


(define (internal-patch-instructions-2 lst x label)
  (define new_conc_2 (string->symbol (string-append (symbol->string label) "conclusion2")))
  (match x
    ;; added now
    [(TailJmp arg int)
     (if (equal? arg (Reg 'rax))
         (begin
           ;(set! global-lst (append global-lst (list x)))
           (set! dict_for_tailJmp_reg (dict-set dict_for_tailJmp_reg label arg))
           (set! global-lst (append global-lst (list (Jmp new_conc_2))))
           x)
         (begin
;           (set! global-lst (append global-lst (list (Instr 'movq (list arg (Reg 'rax))) (TailJmp (Reg 'rax) int))))
           (set! dict_for_tailJmp_reg (dict-set dict_for_tailJmp_reg label arg))
           (set! global-lst (append global-lst (list (Instr 'movq (list arg (Reg 'rax))) (Jmp new_conc_2))))
           x
           ))]
    
    [(Instr 'leaq (list e1 e2))
     (if (Reg? e2)
         (begin
           (set! global-lst (append global-lst (list x)))
           x)
         (begin
           (set! global-lst (append global-lst (list (Instr 'leaq (list e1 (Reg 'rax))) (Instr 'movq (list (Reg 'rax) e2)))))
           x
           ))]         
         
    [(Instr 'movzbq (list (Reg x) (Deref reg2 int2)))
         (set! global-lst (append global-lst
                                  (list (Instr 'movzbq (list (Reg x) ((Reg 'rax))))
                                        (Instr 'movq (list (Reg 'rax) (Deref reg2 int2))))))
     x
     ]
    [(Instr 'cmpq (list e1 (Imm e2)))
     (set! global-lst (append global-lst
                                  (list (Instr 'movq (list (Imm e2) (Reg 'rax)))
                                        (Instr 'cmpq (list e1 (Reg 'rax))))))
     x
     ]
         
    [(Instr 'movq (list (Deref reg1 int1) (Deref reg2 int2)))
     (if (equal? (Deref reg1 int1) (Deref reg2 int2)) null
         (set! global-lst (append global-lst
                              (list (Instr 'movq (list (Deref reg1 int1) (Reg 'rax)))
                                    (Instr 'movq (list (Reg 'rax) (Deref reg2 int2))))))) 
     x
     ]
    [(Instr com (list (Deref reg1 int1) (Deref reg2 int2)))
     (set! global-lst (append global-lst
                              (list (Instr 'movq (list (Deref reg1 int1) (Reg 'rax)))
                                    (Instr com (list (Reg 'rax) (Deref reg2 int2)))))) x]
    [(Instr 'movq (list e1 e2))
     (if (equal? e1 e2) null
         (set! global-lst (append global-lst (list x)))) 
     x
     ]
    [else (set! global-lst (append global-lst (list x))) x])) 

(define (internal-patch-instructions lst body label)
  (set! global-lst '())
  (match body
    [(Block e1 e2)
     (for/list ([e (in-list e2)]) (internal-patch-instructions-2 lst e label))
     (Block e1 global-lst)])
  )

(define (get-block body label)
  (set! global-lst '())
  (define output-body '())
  (for ([b (in-list body)])
    (set! output-body (dict-set output-body (car b) (internal-patch-instructions '() (cdr b) label))))
  output-body)


(define dict_for_tailJmp_reg '())


(define (patch-instructions p)
  (set! dict_for_tailJmp_reg '())
  (set! global-lst '())
  (define count 0)
  (set! global-lst empty)
  (match p
    [(X86Program info lst_def)
     (X86Program info
                 (for/list ([curr_func (in-list lst_def)])
                   (match curr_func
                     [(Def label '() type info lst_blocks)
                      (Def label '() type info (get-block lst_blocks label))])))]
    ;[(X86Program info body) (X86Program info (get-block body))]
    ))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (concluding_block set_output stack_size)
  (define my-list '())
  (if (equal? stack_size 0)
      null
      (set! my-list (append my-list (list (Instr 'addq (list (Imm stack_size) (Reg 'rsp)))))))
  (for ([e (in-list (reverse set_output))])
    (set! my-list (append my-list (list e))))
  (set! my-list (append my-list (list (Instr 'popq (list (Reg 'rbp))) (Retq))))
  (Block '() my-list))

(define (concluding_block2 set_output stack_size function_name)
  (define my-list '())
  (if (equal? stack_size 0)
      null
      (set! my-list (append my-list (list (Instr 'addq (list (Imm stack_size) (Reg 'rsp)))))))
  (for ([e (in-list (reverse set_output))])
    (set! my-list (append my-list (list e))))
  (set! my-list
        (append my-list
                (list
                 (Instr 'popq (list (Reg 'rbp)))
                 (if (equal? (dict-has-key? dict_for_tailJmp_reg function_name) #t)
                     ;(IndirectJmp (dict-ref dict_for_tailJmp_reg function_name))
                     (IndirectJmp (Reg 'rax))
                     (Retq))
                 )))
  (Block '() my-list))


(define (main_block info graph_colors_here lst_mapping_callee stack_size func_label)
  (define register_lst (list (Reg 'rcx) (Reg 'rdx) (Reg 'rsi) (Reg 'rdi) (Reg 'r8) (Reg 'r9) (Reg 'r10) (Reg 'rbx) (Reg 'r12) (Reg 'r13) (Reg 'r14)))
  (define lst_ins_main (list
                        (Instr 'pushq (list (Reg 'rbp)))
                        (Instr 'movq (list (Reg 'rsp) (Reg 'rbp)))
                        ))
  (define set_unique_push_ins (set))
  
  (for ([e (in-list graph_colors_here)])
    (if (and (< (cdr e) 11) (equal? (dict-ref lst_mapping_callee (cdr e)) 8) (not (equal? (cdr e) -1)) (not (equal? (cdr e) -2)))
        (begin
          (set! set_unique_push_ins (set-union set_unique_push_ins (set (Instr 'pushq (list (list-ref register_lst (cdr e))))))))
        null
        )
    )
  (define set_output (set->list set_unique_push_ins))
  (set! lst_ins_main (append lst_ins_main set_output))
  (if (equal? stack_size 0)
      null
      (set! lst_ins_main (append lst_ins_main (list (Instr 'subq (list (Imm stack_size) (Reg 'rsp)))))))  
  (set! lst_ins_main
        (append lst_ins_main
                (list (Jmp (string->symbol (string-append (symbol->string func_label) "start"))))))
  (cons set_output (Block '() lst_ins_main)))


(define (get-stack-size graph_colors_here lst_mapping p)
  (define total_spilled 0)
  (define total_callee 0)
  (for ([e (in-list graph_colors_here)])
    (if (> (cdr e) 10)
        (set! total_spilled (+ total_spilled 8))
        (set! total_callee (+ total_callee (dict-ref lst_mapping (cdr e))))))
  (define size (- (align (+ total_spilled total_callee) 16) total_callee));
  size)


(define (prelude-and-conclusion p)
  (define lst_mapping_callee `())
  (set! lst_mapping_callee (dict-set lst_mapping_callee -2 8))
  (set! lst_mapping_callee (dict-set lst_mapping_callee -1 0))
  (set! lst_mapping_callee (dict-set lst_mapping_callee 0 0))
  (set! lst_mapping_callee (dict-set lst_mapping_callee 1 0))
  (set! lst_mapping_callee (dict-set lst_mapping_callee 2 0))
  (set! lst_mapping_callee (dict-set lst_mapping_callee 3 0))
  (set! lst_mapping_callee (dict-set lst_mapping_callee 4 0))
  (set! lst_mapping_callee (dict-set lst_mapping_callee 5 0))
  (set! lst_mapping_callee (dict-set lst_mapping_callee 6 0))
  (set! lst_mapping_callee (dict-set lst_mapping_callee 7 8))
  (set! lst_mapping_callee (dict-set lst_mapping_callee 8 8))
  (set! lst_mapping_callee (dict-set lst_mapping_callee 9 8))
  (set! lst_mapping_callee (dict-set lst_mapping_callee 10 8))
  

  (define (prelude-and-conclude-helper lst_mapping p)
    (match p
      [(Def label '() type info lst_blocks)
       (define graph_colors_here (dict-ref info 'graph_colors))
       (define size (get-stack-size graph_colors_here lst_mapping p))
       (define output_main (main_block info graph_colors_here lst_mapping_callee size label))
       ;(Def label '() type info
       (append lst_blocks
               (list
                (cons label (cdr output_main))
                (cons (string->symbol (string-append (symbol->string label) "conclusion")) (concluding_block (car output_main) size))
                (cons (string->symbol (string-append (symbol->string label) "conclusion2")) (concluding_block2 (car output_main) size label))
                ))
       ]))

  (match p
    [(X86Program info lst_defs)
     (define new_lst '())
     (for ([i (in-list lst_defs)]) (set! new_lst (append new_lst (prelude-and-conclude-helper lst_mapping_callee i))))
     (X86Program info new_lst)]))

#|
  (match p
    [(X86Program info body)
     (define graph_colors_here (dict-ref info 'graph_colors))
     (define size (get-stack-size graph_colors_here lst_mapping_callee p))
     (define output_main (main_block info graph_colors_here lst_mapping_callee size))
     (X86Program info (append body (list (cons 'main (cdr output_main))
                                         (cons 'conclusion (concluding_block (car output_main ) size))
                                         )))]))

|#


(define output_build (build_interference (X86Program
 '()
 (list
  (Def
   'lesser
   '()
   'Integer
   '((locals-types
      (x172325 . Integer)
      (x172324 . Integer)
      (hemlu172333 . Integer)
      (hemlu172332 . Integer))
     (num-params . 2))
   (list
    (cons
     'block172335
     (Block
      (list
       (list
        'liveness
        (set)
        (set (Reg 'rax) (Reg 'rsp))
        (set (Var 'x172324) (Reg 'rsp))))
      (list
       (Instr 'movq (list (Var 'x172324) (Reg 'rax)))
       (Jmp 'lesserconclusion))))
    (cons
     'block172336
     (Block
      (list
       (list
        'liveness
        (set)
        (set (Reg 'rax) (Reg 'rsp))
        (set (Var 'x172325) (Reg 'rsp))))
      (list
       (Instr 'movq (list (Var 'x172325) (Reg 'rax)))
       (Jmp 'lesserconclusion))))
    (cons
     'lesserstart
     (Block
      (list
       (list
        'liveness
        (set (Var 'x172324) (Var 'x172325) (Reg 'rsp))
        (set (Reg 'rax) (Var 'x172324) (Var 'x172325) (Reg 'rsp))
        (set (Reg 'rax) (Var 'x172324) (Var 'x172325) (Reg 'rsp))
        (set
         (Reg 'rax)
         (Var 'hemlu172332)
         (Var 'hemlu172333)
         (Var 'x172324)
         (Var 'x172325)
         (Reg 'rsp))
        (set
         (Reg 'rax)
         (Var 'hemlu172332)
         (Var 'x172324)
         (Var 'x172325)
         (Reg 'rsp))
        (set (Reg 'rax) (Var 'x172324) (Var 'x172325) (Reg 'rsp))
        (set (Reg 'rax) (Reg 'rsi) (Var 'x172324) (Reg 'rsp))
        (set (Reg 'rax) (Reg 'rdi) (Reg 'rsi) (Reg 'rsp))))
      (list
       (Instr 'movq (list (Reg 'rdi) (Var 'x172324)))
       (Instr 'movq (list (Reg 'rsi) (Var 'x172325)))
       (Instr 'movq (list (Var 'x172324) (Var 'hemlu172332)))
       (Instr 'movq (list (Var 'x172325) (Var 'hemlu172333)))
       (Instr 'cmpq (list (Var 'hemlu172333) (Var 'hemlu172332)))
       (JmpIf 'l 'block172335)
       (Jmp 'block172336))))))
  (Def
   'main
   '()
   'Integer
   '((locals-types
      (hemlu172334 Integer Integer -> Integer)
      (x172327 . Integer)
      (x172326 . Integer))
     (num-params . 0))
   (list
    (cons
     'mainstart
     (Block
      (list
       (list
        'liveness
        (set)
        (set
         (Reg 'rdx)
         (Reg 'r8)
         (Reg 'r9)
         (Reg 'rdi)
         (Reg 'rcx)
         (Reg 'rsi)
         (Var 'hemlu172334))
        (set
         (Reg 'rdx)
         (Var 'hemlu172334)
         (Var 'x172327)
         (Reg 'r8)
         (Reg 'r9)
         (Reg 'rdi)
         (Reg 'rcx))
        (set
         (Reg 'rcx)
         (Reg 'rdx)
         (Var 'hemlu172334)
         (Var 'x172326)
         (Var 'x172327)
         (Reg 'r8)
         (Reg 'r9))
        (set
         (Reg 'rax)
         (Reg 'rcx)
         (Reg 'rdx)
         (Var 'x172326)
         (Var 'x172327)
         (Reg 'r8)
         (Reg 'r9))
        (set
         (Reg 'rcx)
         (Reg 'rdx)
         (Var 'x172326)
         (Var 'x172327)
         (Reg 'r8)
         (Reg 'r9))
        (set (Reg 'rcx) (Reg 'rdx) (Var 'x172326) (Reg 'r8) (Reg 'r9))
        (set (Reg 'rcx) (Reg 'rdx) (Reg 'r8) (Reg 'r9))))
      (list
       (Instr 'movq (list (Imm 42) (Var 'x172326)))
       (Instr 'movq (list (Imm 56) (Var 'x172327)))
       (Instr 'leaq (list (Global 'lesser) (Reg 'rax)))
       (Instr 'movq (list (Reg 'rax) (Var 'hemlu172334)))
       (Instr 'movq (list (Var 'x172326) (Reg 'rdi)))
       (Instr 'movq (list (Var 'x172327) (Reg 'rsi)))
       (TailJmp (Var 'hemlu172334) 2))))))))))



(define (hehehehe tt)
  (match tt
    [(X86Program info lst_def)
     (for ([i lst_def])
       (match i
         [(Def 'main a b c d) (print-graph (dict-ref c 'conflicts))]
         [else null]))]))

;(hehehehe output_build)

;(allocate-registers output_build)






;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Define the compiler passes to be used by interp-tests and the grader
;; Note that your compiler file (the file that defines the passes)
;; must be named "compiler.rkt"
(define compiler-passes
  `( 
     ;; Uncomment the following passes as you finish them.
     ("shrink", shrink, interp-Lfun, type-check-Lfun)
     ("uniquify" ,uniquify ,interp-Lfun ,type-check-Lfun)
     ("reveal", reveal_functions, interp-Lfun-prime, type-check-Lfun)
     ("remove complex opera*" ,remove-complex-opera* ,interp-Lfun-prime ,type-check-Lfun)
     ("explicate control" ,explicate-control ,interp-Cfun ,type-check-Cfun)
     ("instruction selection", select-instructions, #f)
     ("uncover_live", uncover_live, #f)
     ("build_interference", build_interference, #f)
     ("allocate_registers", allocate-registers, #f)
     ("patch instructions" ,patch-instructions, #f)     
     ("prelude and conclusion",prelude-and-conclusion,#f)
     ))






