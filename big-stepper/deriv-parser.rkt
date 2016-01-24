#lang racket/base
(require (for-syntax racket/base)
         racket/promise
         syntax/stx
         parser-tools/lex
         macro-debugger/model/yacc-ext
         macro-debugger/model/yacc-interrupted
         "deriv.rkt"
         "deriv-tokens.rkt")
(provide parse-derivation
         trace
         trace*)

(define (deriv-error ok? name value start end)
  (if ok?
      (error 'derivation-parser
             "error on token #~a: <~s, ~s>"
             start name value)
      (error 'derivation-parser "bad token #~a" start)))

;; PARSER

(define-production-splitter production/I values values)

(define-syntax (productions/I stx)
  (syntax-case stx ()
    [(productions/I def ...)
     #'(begin (production/I def) ...)]))

(define parse-derivation
  (parser
   (options (start Start)
            (src-pos)
            (tokens basic-tokens)
            (end EOF)
            #| (debug "/tmp/DEBUG-PARSER.txt") |#
            (error deriv-error))

   ;; tokens
   (skipped-token-values
    next next-group EOF IMPOSSIBLE weight
    eval-top syntax-error eval-expr return
    expr:variable expr:quote expr:let* expr:lambda expr:app expr:fix
    expr:S-sample expr:N-sample expr:observe-sample expr:fail expr:mem
    expr:if if-true if-false 
    apply-function apply:primop apply:closure apply:fixed apply:memoized
    memo-miss
    )

    ;; Entry point
   (productions
    (Start
     [(eval-top EE) $2]
     [(eval-top EE/Interrupted) $2]))

   (productions/I

    (EE
     [(eval-expr (? EE/Inner) return)
      (node:eval (car $1) (cdr $1) $2 $3 #f)])
    (EEs
     (#:skipped null)
     [() null]
     [(next (? EE) (? EEs)) (cons $2 $3)])

    (EE/Inner
     [(expr:variable !)
      (deriv:variable $2)]
     [(expr:quote)
      (deriv:quote)]
     [(expr:let* (? EEs) next-group (? EE))
      (deriv:let* $2 $4)]
     [(expr:lambda)
      (deriv:lambda)]
     [(expr:app (? EE) next-group (? EEs) (? ApplyFunction))
      (deriv:app $2 $4 $5)]
     [(expr:fix (? EE) !)
      (deriv:fix $2 $3)]
     [(expr:if (? EE) (? EE))
      (deriv:if $2 $3)]
     [(expr:S-sample (? EE) ! DoSample)
      (deriv:S-sample $2 $3 $4)]
     [(expr:N-sample (? EE) ! DoSample)
      (deriv:N-sample $2 $3 $4)]
     [(expr:observe-sample (? EE) (? EE) ! weight)
      (deriv:observe-sample $2 $3 $4 $5)]
     [(expr:fail !)
      (deriv:fail $2)]
     [(expr:mem (? EE) !)
      (deriv:mem $2 $3)]
     [(!!)
      (deriv:error $1)])

    (ApplyFunction
     [(apply-function (? ApplyFunction/Inner) return)
      (node:apply (car $1) (cdr $1) $2 $3)])

    (ApplyFunction/Inner
     [(apply:primop !)
      (apply:primop $2)]
     [(apply:closure ! (? EE))
      (apply:closure $2 $3)]
     [(apply:fixed (? ApplyFunction) (? ApplyFunction))
      (apply:fixed $2 $3)]
     [(apply:memoized)
      (apply:mem-hit)]
     [(apply:memoized memo-miss (? ApplyFunction))
      (apply:mem-miss $3)]
     [(!!)
      (apply:error $1)])

    (DoSample
     [() #f])

    )))

;; ============================================================

;; trace : Expr (Expr -> Value) -> Deriv
(define (trace e eval)
  (let-values ([(result events derivp) (trace* e eval)])
    (force derivp)))

;; trace* : Expr (Expr -> Value) -> Value/Exn (list-of Event) (promise-of Deriv)
(define (trace* e eval)
  (let-values ([(result events) (trace/events e eval)])
    (values result
            events
            (delay (parse-derivation (events->token-generator events))))))

;; trace/events : Expr (Expr -> Value) -> Value/Exn (list-of Event)
(define (trace/events e eval)
  (define events null)
  (define (add! x y)
    (set! events (cons (cons x y) events)))
  (parameterize ((current-emit-listener add!))
    (let ([result
           (with-handlers ([(lambda (exn) #t)
                            (lambda (exn)
                              (add! 'syntax-error exn)
                              exn)])
             (eval e))])
      (add! 'EOF #f)
      (values result (reverse events)))))

;; events->token-generator : (list-of Event) -> (-> Token)
(define (events->token-generator events)
  (let ([pos 1])
    (lambda ()
      (define sig+val (car events))
      ;; (eprintf " -- ~s\n" sig+val)
      (set! events (cdr events))
      (let* ([sig (car sig+val)]
             [val (cdr sig+val)]
             [t (tokenize sig val pos)])
        (when #f; (trace-verbose?)
          (printf "~s: ~s\n" pos
                  (token-name (position-token-token t))))
        (set! pos (add1 pos))
        t))))
