#lang racket/base
(require parser-tools/lex)
(provide (all-defined-out))

(define current-emit-listener (make-parameter void))

(define-tokens basic-tokens
  (eval-top
   next
   next-group
   EOF
   IMPOSSIBLE           ; in error-handling clauses that have no NoError counterpart
   weight               ; Real
   memo-miss

   syntax-error         ; Exn;;  AAARRGH! hard-coded in :(

   eval-expr            ; (cons Expr Env)
   return               ; Value

   apply-function       ; (cons Function (listof Value))

   expr:variable
   expr:quote
   expr:let*
   expr:lambda
   expr:app
   expr:fix
   expr:if
   if-true
   if-false
   expr:S-sample
   expr:N-sample
   expr:observe-sample
   expr:fail
   expr:mem

   apply:primop
   apply:closure
   apply:fixed
   apply:memoized
   ))

;; ** Signals to tokens

(define signal-mapping
  ;; (symbol token-constructor)
  `([eval-top                           ,token-eval-top]
    [next                               ,token-next]
    [next-group                         ,token-next-group]
    [EOF                                ,token-EOF]
    [IMPOSSIBLE                         ,token-IMPOSSIBLE]
    [memo-miss                          ,token-memo-miss]

    [syntax-error                       ,token-syntax-error]

    [eval-expr                          ,token-eval-expr]
    [return                             ,token-return]

    [apply-function                     ,token-apply-function]

    [expr:variable                      ,token-expr:variable]
    [expr:quote                         ,token-expr:quote]
    [expr:let*                          ,token-expr:let*]
    [expr:lambda                        ,token-expr:lambda]
    [expr:app                           ,token-expr:app]
    [expr:fix                           ,token-expr:fix]
    [expr:if                            ,token-expr:if]
    [if-true                            ,token-if-true]
    [if-false                           ,token-if-false]
    [expr:S-sample                      ,token-expr:S-sample]
    [expr:N-sample                      ,token-expr:N-sample]
    [expr:observe-sample                ,token-expr:observe-sample]
    [expr:fail                          ,token-expr:fail]
    [expr:mem                           ,token-expr:mem]

    [apply:primop                       ,token-apply:primop]
    [apply:closure                      ,token-apply:closure]
    [apply:fixed                        ,token-apply:fixed]
    [apply:memoized                     ,token-apply:memoized]

    [weight                             ,token-weight]
    ))

(define (tokenize sig val pos)
  (cond [(assv sig signal-mapping)
         => (lambda (entry) (make-position-token ((cadr entry) val) pos pos))]
        [else
         (error 'tokenize "bad signal: ~s" sig)]))
