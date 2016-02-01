#lang racket/base
(require racket/class
         racket/pretty
         (rename-in racket/match [match-define defmatch])
         racket/gui
         framework
         mrlib/hierlist
         macro-debugger/syntax-browser/hrule-snip
         "deriv.rkt"
         "stepper-base.rkt")
(provide (all-defined-out))

;; show-deriv : Deriv -> Frame
(define (show-deriv d)
  (define f (new frame% (label "Debugger") (height 600) (width 800)))
  (define t (new text%))
  (send t set-styles-sticky #f)
  (define dv (new deriv-view% (t t)))
  (define hp (new panel:horizontal-dragable% (parent f)))
  (define h (make-deriv-view d hp dv))
  (define ec (new editor-canvas% (editor t) (parent hp)))
  (send hp set-percentages '(1/3 2/3))
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
    [(node:eval expr env inner result _weight)
     (cond [(trivial-deriv? inner)
            ;; Skip trivial nodes
            #t]
           [else
            (define view (send parent new-list))
            (send view user-data d)
            (send view open)
            (add:inner expr env inner result view)])]
    [#f
     (eprintf "add:deriv: bad ~e" d)
     #f]))

;; trivial-deriv? : Inner -> Boolean
(define (trivial-deriv? inner) (eq? (classify-deriv inner) 'trivial))

;; leaf-deriv? : Inner -> Boolean

;; classify-deriv : Inner -> (U 'trivial 'leaf 'compound)
(define (classify-deriv inner)
  (match inner
    [(deriv:quote) 'trivial]
    [(deriv:variable #f) 'trivial]
    [(deriv:lambda) 'trivial]
    [_ 'compound]))

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
      (when d (show-node d)))

    (define/public (show-node d)
      (match d
        [(node:eval expr env inner result weight)
         (define table (make-hash))
         (define env-sexpr (env->sexpr env))
         ;; (hash-set! table env-sexpr "ρ")
         (show-inner expr env inner result table)
         (insert (new hrule-snip%) #:style hrule-sd)
         (insert "\n")
         (show-judgment env expr result weight table)
         (show-table table)]
        [(node:apply fun args inner result)
         (show-apply inner)
         (insert (new hrule-snip%) #:style hrule-sd)
         (insert "\n")
         (show-apply-judgment fun args result)]
        [#f
         (insertf "bad deriv:\n~e" d)
         #f]))

    (define/public (show-judgment env expr result weight table)
      (insert/abbrev (env->sexpr env) table)
      (insert ",\n" #:style meta-sd)
      ;; (insert/abbrev (expr->sexpr expr) table)
      (insert (render-expr expr) #:style code-sd)
      (insert "\n ⇓\n" #:style meta-sd)
      (cond [(exn? result)
             (insert (exn-message result) #:style error-sd)]
            [else (insert/abbrev (value->sexpr result) table)])
      (insert ",\n" #:style meta-sd)
      (insertf "~s" weight #:style code-sd)
      (insert "\n"))

    (define/public (show-apply-judgment fun args result)
      (insert "apply function\n" #:style meta-sd)
      (insert (render-value fun) #:style code-sd)
      (insert "\nto arguments\n" #:style meta-sd)
      (for ([arg args])
        (insert (render-value arg) #:style code-sd)
        (insert "\n"))
      (insert "\n ⇓\n" #:style meta-sd)
      (cond [(exn? result)
             (insert (exn-message result) #:style error-sd)]
            [else (insert (render-value result) #:style code-sd)])
      (insert "\n"))

    (define/public (summary-apply a)
      (define table '#hash())
      (match a
        [(node:apply fun args inner result)
         (insert "apply " #:style meta-sd)
         (insert/abbrev (value->sexpr fun) table #:limit 20)
         (insert " to " #:style meta-sd)
         (insert/abbrev (value->sexpr args) table #:limit 20)
         (insert "  ⇓  " #:style meta-sd)
         (cond [(exn? result)
                (insert (exn-message result) #:style error-sd)]
               [else (insert/abbrev (value->sexpr result) table #:limit 30)])
         (insert "\n")]
        [_ (void)]))

    (define/public (summary-judgment d table)
      (match d
        [(node:eval expr env inner result weight)
         (insert/abbrev (env->sexpr env) table #:limit 20)
         (insert ", " #:style meta-sd)
         (insert/abbrev (expr->sexpr expr) table #:limit 50)
         (insert "  ⇓  " #:style meta-sd)
         (cond [(exn? result)
                (insert (exn-message result) #:style error-sd)]
               [else (insert/abbrev (value->sexpr result) table #:limit 30)])
         (insert ", " #:style meta-sd)
         (insertf "~s" weight #:style code-sd)
         (insert "\n")]
        [#f (void)]))

    (define/public (insert/abbrev sexpr table
                                  #:insert [insert-abbrev #f]
                                  #:limit [limit +inf.0])
      (cond [(hash-ref table sexpr #f)
             => (lambda (abbrev) (insert abbrev #:style meta-code-sd))]
            [else
             (define s (format "~s" sexpr))
             (cond [(and insert-abbrev (> (length s) limit))
                    (hash-set! table sexpr insert-abbrev)
                    (insert insert-abbrev #:style meta-code-sd)]
                   [else
                    (insert (~a s #:max-width limit #:limit-marker "̣...")
                            #:style code-sd)])]))

    (define/public (show-table table)
      (define abbrev+sexpr-list
        (sort (for/list ([(s a) (in-hash table)]) (cons a s))
              string<?
              #:key car))
      (unless (empty? abbrev+sexpr-list)
        (insert "\nwhere:\n")
        (for ([abbrev+sexpr abbrev+sexpr-list])
          (defmatch (cons abbrev sexpr) abbrev+sexpr)
          (insert abbrev #:style meta-code-sd)
          (insert " = " #:style meta-sd)
          ;; (define t* (new text%))
          ;; (define s (new resizable-editor-snip% (inner-editor t*)))
          ;; (send t* insert (format "~s" sexpr))
          ;; (insert s)
          (insertf "~s\n" sexpr #:style code-sd))))

    (define/public (render-expr expr)
      (pretty-format (expr->sexpr expr) 60 #:mode 'write))

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
      (pretty-format (value->sexpr v) 60 #:mode 'write))

    (define (show-apply inner)
      (define (summary d) (summary-judgment d '#hash()))
      (match inner
        [(apply:primop ?1)
         (insert/rule "primop")
         (summary-exn ?1)]
        [(apply:closure ?1 body)
         (insert/rule "closure")
         (summary-exn ?1)
         (summary body)]
        [(apply:fixed self apply)
         (insert/rule "fixed")
         (summary-apply self)
         (summary-apply apply)]
        [(apply:mem-hit)
         (insert/rule "memoized (hit)")]
        [(apply:mem-miss apply)
         (insert/rule "memoized (miss)")
         (summary-apply apply)]
        [(apply:error exn)
         (insert/rule "error")
         (summary-exn exn)]))

    (define/public (show-inner expr env inner result table)
      (define (summary d) (summary-judgment d table))
      (match inner
        [(deriv:variable ?1)
         (insert/rule "variable")
         (summary-exn ?1)]
        [(deriv:quote)
         (insert/rule "constant")]
        [(deriv:let* rhss body)
         (insert/rule "let*")
         (for ([rhs rhss])
           (summary rhs))
         (summary body)]
        [(deriv:lambda)
         (insert/rule "lambda")]
        [(deriv:app op args apply)
         (insert/rule "application")
         (summary op)
         (for ([arg args]) (summary arg))
         ;; FIXME: apply
         ]
        [(deriv:fix arg ?1)
         (insert/rule "fix")
         (summary arg)
         (summary-exn ?1)]
        [(deriv:if test branch)
         (insert/rule "if")
         (summary test)
         (summary branch)]
        [(deriv:S-sample inner ?1 sample)
         (insert/rule "S-sample")
         (summary inner)
         (summary-exn ?1)
         ;; sample?
         ]
        [(deriv:N-sample inner ?1 sample)
         (insert/rule "N-sample")
         (summary inner)
         (summary-exn ?1)
         ;; sample?
         ]
        [(deriv:observe-sample dist value ?1 weight)
         (insert/rule "observe-sample")
         (summary dist)
         (summary value)
         (summary-exn ?1)
         ;; weight?
         ]
        [(deriv:fail ?1)
         (insert/rule "fail")
         (summary-exn ?1)]
        [(deriv:mem fun ?1)
         (insert/rule "mem")
         (summary fun)
         (summary-exn ?1)]
        [(deriv:error exn)
         (insert/rule "error")
         (summary-exn exn)]
        ))

    (define/public (summary-exn e)
      (when (exn? e)
        (insert (exn-message e) #:style error-sd)))

    (define/public (insert/rule s)
      (insert/style (string-append "[" s "]\n\n") (list rule-sd)))

    (define/private (insert/style s style)
      (define a (send t last-position))
      (send t insert s)
      (define b (send t last-position))
      (for ([sd (if (list? style) style (list style))])
        (send t change-style sd a b #f)))
    (define/private (insert s #:style [styles null])
      (insert/style s styles))
    (define/private (insertf #:style [styles null] fmt . args)
      (insert/style (apply format fmt args) styles))
    ))


;; ============================================================

;; resizable-editor-snip%
(define resizable-editor-snip%
  (class* editor-snip% ()
    (init-field (inner-editor (new text%)))
    (inherit get-flags set-flags)
    (super-new (editor inner-editor))
    (set-flags (append '(handles-events handles-all-mouse-events) (get-flags)))

    (define/public (get-inner-editor) inner-editor)

    (define was-dragging? #f)

    (define/override (on-event dc x y edx edy event)
      (define (call-super) (super on-event dc x y edx edy event))
      (define TARGET-W 4)
      (define TARGET-H 4)
      (define mx (send event get-x))
      (define my (send event get-y))
      (define sxb (box 0))
      (define syb (box 0))
      (define owner (send (send this get-admin) get-editor))
      (send owner get-snip-location this sxb syb #f)
      (define sx1 (unbox sxb))
      (define sy1 (unbox syb))
      (send owner get-snip-location this sxb syb #t)
      (define sx2 (unbox sxb))
      (define sy2 (unbox syb))
      (eprintf "event ~s,~s ~s,~s ~s ~a\n" x y edx edy
               (send event get-event-type)
               (if (send event dragging?) "dragging" ""))
      (eprintf "  mouse at ~s,~s\n" mx my)
      (eprintf "  snip top-left ~s,~s bottom-right ~s,~s\n"
               sx1 sy1 sx2 sy2)
      (eprintf "  size min ~s,~s max ~s,~s\n"
               (send this get-min-width) (send this get-min-height)
               (send this get-max-width) (send this get-max-height))
      (cond [(and (eq? (send event get-event-type) 'left-down)
                  (<= (max sx1 #;(- sx2 TARGET-W)) mx sx2)
                  (<= (max sy1 #;(- sy2 TARGET-H)) my sy2))
             (set! was-dragging? #t)
             (call-super)]
            [(eq? (send event get-event-type) 'leave)
             (set! was-dragging? #f)
             (call-super)]
            [(and was-dragging?
                  (eq? (send event get-event-type) 'left-up))
             (send this resize (- mx sx1) (- my sy1))
             (void)]
            [else (call-super)]))
    ))

#|
;; clicky-snip%
(define clicky-snip%
  (class* editor-snip% ()
    (init-field [open-style '(border)]
                [closed-style '(tight-text-fit)])
    (inherit set-margin
             set-inset
             set-snipclass
             set-tight-text-fit
             show-border
             get-admin)

    (define -outer (new text%))
    (super-new (editor -outer) (with-border? #f))
    (set-margin 2 2 2 2)
    (set-inset 2 2 2 2)
    ;;(set-margin 3 0 0 0)
    ;;(set-inset 1 0 0 0)
    ;;(set-margin 0 0 0 0)
    ;;(set-inset 0 0 0 0)

    (define/public (closed-contents) null)
    (define/public (open-contents) null)

    (define open? #f)

    (define/public (refresh-contents)
      (with-unlock -outer
        (send -outer erase)
        (do-style (if open? open-style closed-style))
        (outer:insert (if open? (hide-icon) (show-icon))
                      style:hyper
                      (if open?
                          (lambda _
                            (set! open? #f)
                            (refresh-contents))
                          (lambda _
                            (set! open? #t)
                            (refresh-contents))))
        (for-each (lambda (s) (outer:insert s))
                  (if open? (open-contents) (closed-contents)))
        (send -outer change-style top-aligned 0 (send -outer last-position))))

    (define/private (do-style style)
      (show-border (memq 'border style))
      (set-tight-text-fit (memq 'tight-text-fit style)))

    (define/private outer:insert
      (case-lambda
       [(obj)
        (if (styled? obj)
            (outer:insert (styled-contents obj)
                          (styled-style obj)
                          (styled-clickback obj))
            (outer:insert obj style:normal))]
       [(text style)
        (outer:insert text style #f)]
       [(text style clickback)
        (let ([start (send -outer last-position)])
          (send -outer insert text)
          (let ([end (send -outer last-position)])
            (send -outer change-style style start end #f)
            (when clickback
                  (send -outer set-clickback start end clickback))))]))

    (send -outer hide-caret #t)
    (send -outer lock #t)
    (refresh-contents)
    ))

(define (show-icon)
  (make-object image-snip%
    (collection-file-path "turn-up.png" "icons")))
(define (hide-icon)
  (make-object image-snip%
    (collection-file-path "turn-down.png" "icons")))
|#

;; ============================================================

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
(define meta-sd (style-delta [change-family 'modern] [color "blue"]
                             [change-bold] [change-bigger 2]))
(define hrule-sd (style-delta [change-size 4]))