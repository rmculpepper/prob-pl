#lang racket/base
(require racket/class
         (rename-in racket/match [match-define defmatch])
         racket/gui
         framework
         mrlib/hierlist
         "deriv.rkt"
         "stepper-base.rkt")
(provide (all-defined-out))

;; show-deriv : Deriv -> Frame
(define (show-deriv d)
  (define f (new frame% (label "Debugger")))
  (define t (new text%))
  (send t set-styles-sticky #f)
  (define dv (new deriv-view% (t t)))
  (define hp (new panel:horizontal-dragable% (parent f)))
  (define h (make-deriv-view d hp dv))
  (define ec (new editor-canvas% (editor t) (parent hp)))
  (send f show #t)
  f)

;; make-deriv-view : Deriv Container -> Hierlist
(define (make-deriv-view d parent dv)
  (define (on-select item)
    (send dv show (and item (send item user-data))))
  (define h (new hierlist% (parent parent) (select-callback on-select)))
  (add:deriv d h)
  h)

(define hierlist%
  (class hierarchical-list%
    (init-field [select-callback void])
    (super-new)
    (define/override (on-select i)
      (select-callback i))
    ))

;; add:* returns true if deriv is ok, false if interrupted

;; add:deriv : Deriv HierlistContainer -> Boolean
(define (add:deriv d parent)
  (match d
    [(node:eval expr env inner result)
     (define view (send parent new-list))
     (send view user-data d)
     (send view open)
     (add:inner expr env inner result view)]
    [#f
     (eprintf "add:deriv: bad ~e" d)
     #f]))

;; add:inner : ... -> Boolean
(define (add:inner expr env inner result view)
  (define (label s) (send (send view get-editor) insert s) #t)
  (define (recur d) (add:deriv d view))
  (match inner
    [(deriv:variable ?1)
     (label "variable")]
    [(deriv:quote)
     (label "constant")]
    [(deriv:let* rhss body)
     (label "let*")
     (and (andmap recur rhss) (recur body))]
    [(deriv:lambda)
     (label "lambda")]
    [(deriv:app op args apply)
     (label "application")
     (and (recur op) (andmap recur args) (add:apply apply view))]
    [(deriv:fix arg ?1)
     (label "fix")
     (and (recur arg) (add:exn ?1 view))]
    [(deriv:if test branch)
     (label "if")
     (and (recur test) (recur branch))]
    [(deriv:S-sample inner ?1 sample)
     (label "S-sample")
     (and (recur inner) (add:exn ?1 view))]
    [(deriv:N-sample inner ?1 sample)
     (label "N-sample")
     (and (recur inner) (add:exn ?1 view))]
    [(deriv:observe-sample dist value ?1 weight)
     (label "observe-sample")
     (and (recur dist) (recur value) (add:exn ?1 view))]
    [(deriv:fail ?1)
     (label "fail")
     (add:exn ?1 view)]
    [(deriv:mem fun ?1)
     (label "mem")
     (and (recur fun) (add:exn ?1 view))]
    [(deriv:error exn)
     (label "error")]))

(define (add:exn maybe-exn view)
  (not maybe-exn))

(define (add:apply a parent)
  (match a
    [(node:apply fun args inner result)
     (define view (send parent new-list))
     (send view user-data a)
     (send view open)
     (add:apply* inner view)]))

(define (add:apply* a view)
  (define (label s) (send (send view get-editor) insert s) #t)
  (match a
    [(apply:primop ?1)
     (label "primop")
     (add:exn ?1 view)]
    [(apply:closure ?1 body)
     (label "closure")
     (and (add:exn ?1 view) (add:deriv body view))]
    [(apply:fixed self apply)
     (label "fixed")
     (and (add:apply self view) (add:apply apply view))]
    [(apply:mem-hit)
     (label "memoized (hit)")]
    [(apply:mem-miss apply)
     (label "memoized (miss)")
     (add:apply apply view)]
    [(apply:error exn)
     (label "error")]))

;; ============================================================

#|
;; A Display is (listof DisplayLine)
;; A DisplayLine is (listof DisplayElem)
;; A DisplayLine is one of
;; - String
;; - (display:string String Styles)
;; - (display:expr Sexpr Abbrev)
;; - (display:env Sexpr Abbrev)
;; - (display:value Sexpr Abbrev)
;;     -- represents (optionally abbrev'able) {expr, env, value} respectively
;; - (display:rule String/#f)
;;     -- represents a horizontal rule w/ optional label
;; An Abbrev is either Symbol or #f
(struct display:string (text style) #:transparent)
(struct display:env (sexpr abbrev) #:transparent)
(struct display:expr (sexpr abbrev) #:transparent)
(struct display:expr (sexpr abbrev) #:transparent)
(struct display:rule (label) #:transparent)

;; TODO: pretty-typeset by abbreviating when necessary
|#

;; ============================================================

(define deriv-view%
  (class object%
    (init-field t)
    (super-new)

    (define/public (show d)
      (send t erase)
      (when d (show-deriv d)))

    ;; show-* returns #f if okay, String for error
    (define/public (show-deriv d)
      (match d
        [(node:eval expr env inner result)
         (define table (make-hash))
         (define env-sexpr (env->sexpr env))
         (hash-set! table env-sexpr "ρ")
         (show-inner expr env inner result table)
         (insert "--------------------------------------------------\n")
         (show-judgment env expr result table)
         (show-table table)]
        [#f
         (insertf "bad deriv:\n~e" d)
         #f]))

    (define/public (show-judgment env expr result table)
      (insert/abbrev (env->sexpr env) table)
      (insert ", ")
      (insert/abbrev (expr->sexpr expr) table)
      (insert " ⇓ ")
      (cond [(exn? result)
             (insert (exn-message result) #:style error-sd)]
            [else (insert/abbrev (value->sexpr result) table)])
      (insert "\n"))

    (define/public (insert/abbrev sexpr table)
      (cond [(hash-ref table sexpr #f)
             => (lambda (abbrev) (insert abbrev #:style meta-code-sd))]
            [else
             (insertf "~s" sexpr #:style code-sd)]))

    (define/public (show-table table)
      (define abbrev+sexpr-list
        (sort (for/list ([(s a) (in-hash table)]) (cons a s))
              string<?
              #:key car))
      (unless (empty? abbrev+sexpr-list)
        (insert "\n")
        (for ([abbrev+sexpr abbrev+sexpr-list])
          (defmatch (cons abbrev sexpr) abbrev+sexpr)
          (insert abbrev #:style meta-code-sd)
          (insert " = ")
          (insertf "~s\n" sexpr #:style code-sd))))

    (define/public (render-expr expr)
      (format "~s" (expr->sexpr expr)))

    (define/public (render-env env)
      (string-append
       "{"
       (string-join
        (for/list ([binding (in-list env)])
          (match binding
            [(cons var value)
             (format "~a ↦ ~a" var (render-value value))]))
        ", ")
       "}"))

    (define/public (render-value v)
      (format "~s" (value->sexpr v)))

    (define/public (show-inner expr env inner result table)
      (match inner
        [(deriv:variable ?1)
         (insert/rule "variable")]
        [(deriv:quote)
         (insert/rule "constant")]
        [(deriv:let* rhss body)
         (insert/rule "let*")]
        [(deriv:lambda)
         (insert/rule "lambda")]
        [(deriv:app op args apply)
         (insert/rule "application")]
        [(deriv:fix arg ?1)
         (insert/rule "fix")]
        [(deriv:if test branch)
         (insert/rule "if")]
        [(deriv:S-sample inner ?1 sample)
         (insert/rule "S-sample")]
        [(deriv:N-sample inner ?1 sample)
         (insert/rule "N-sample")]
        [(deriv:observe-sample dist value ?1 weight)
         (insert/rule "observe-sample")]
        [(deriv:fail ?1)
         (insert/rule "fail")]
        [(deriv:mem fun ?1)
         (insert/rule "mem")]
        [(deriv:error exn)
         (insert/rule "error")]))

    (define/public (insert/rule s)
      (insert/style (string-append "[" s "]\n\n") (list rule-sd)))

    (define/private (insert/style s style)
      (define a (send t last-position))
      (send t insert s)
      (define b (send t last-position))
      (for ([sd (if (list? style) style (list style))])
        (send t change-style sd a b #f)))
    (define/private (insert s #:style [styles null])
      (insert/style s null))
    (define/private (insertf #:style [styles null] fmt . args)
      (insert/style (apply format fmt args) styles))

    #|
    (define (view-apply a parent)
      (match a
        [(node:apply fun args inner result)
         (define view (send parent new-list))
         (send view user-data a)
         (send view open)
         (add:apply* inner view)]))
    (define (add:apply* a view)
      (define (label s) (send (send view get-editor) insert s) #t)
      (match a
        [(apply:primop ?1)
         (label "primop")]
        [(apply:closure ?1 body)
         (label "closure")
         (and (add:exn ?1 view) (add:deriv body view))]
        [(apply:fixed self apply)
         (label "fixed")
         (and (add:apply self view) (add:apply apply view))]
        [(apply:mem-hit)
     (label "memoized (hit)")]
    [(apply:mem-miss apply)
     (label "memoized (miss)")
     (add:apply apply view)]
    [(apply:error exn)
     (label "error")]))
    |#
    ))

(define-syntax-rule (style-delta [command arg ...] ...)
  (let ([sd (make-object style-delta%)])
    (cond [(eq? 'command 'color)
           (send sd set-delta-foreground (car (list arg ...)))]
          [else
           (send sd set-delta 'command arg ...)])
    ...
    sd))

(define rule-sd (style-delta [change-bold] [color "blue"]))
(define error-sd (style-delta [change-italic] [color "red"]))
(define code-sd (style-delta [change-family 'modern]))
(define meta-code-sd (style-delta [change-family 'modern] [change-italic]))
