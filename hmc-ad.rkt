#lang racket/base
(require (rename-in racket/match [match-define defmatch])
         racket/list
         gamble
         "base.rkt"
         "trace-mh.rkt")
(provide (all-defined-out))

;; A SensVar is a Symbol.
(define (gensvar) (string->symbol (symbol->string (gensym 'sens))))

;; A SensStore is Hash[ TraceVar => Real ]
;; Maps trace variables to sensitivities.
;; The special variable 'likelihood represents the likelihood.

(define (sensitivity tvar)
  (hash-ref (current-senstore) tvar 0))
(define (set-sensitivity! tvar r)
  (hash-set! (current-senstore) tvar r))
(define (add-sensitivity! tvar r)
  (hash-set! (current-senstore) tvar (+ r (sensitivity tvar))))

;; current-tstore

;; current-senstore
(define current-senstore (make-parameter (make-hash)))

;; reverse-mode-AD : Trace -> Void
(define (reverse-mode-AD trace)
  (parameterize ((current-senstore (make-hash)))
    (set-sensitivity! 'likelihood 1)
    (for ([ts (reverse trace)])
      (reverse-mode-AD-statement ts))
    (current-senstore)))

(define (reverse-mode-AD-statement ts)
  (match ts
    [(ts:primop var (primop opname) args)
     (reverse-mode-AD-primop var opname args)]
    [(ts:sample var dist-e value-e)
     (reverse-mode-AD-sample var dist-e value-e)]))

(define (reverse-mode-AD-primop dest-var opname args)
  (match* [opname args]
    [['+ (list e1 e2)]
     (for ([src-var (filter symbol? (list e1 e2))])
       (add-sensitivity! src-var (* (sensitivity dest-var) 1)))]
    [['* (list e1 e2)]
     (for ([src-var (list e1 e2)]
           [other-arg (list e2 e1)]
           #:when (symbol? src-var))
       (add-sensitivity! src-var (* (sensitivity dest-var)
                                    (eval-trace-expr other-arg (current-tstore)))))]
    ))

(define (reverse-mode-AD-sample dest-var dist-e value-e)
  (let* ([dist (eval-trace-expr dist-e (current-tstore))]
         [nparams (dist-param-count dist)]
         [value (eval-trace-expr value-e (current-tstore))])
    (when (symbol? value-e)
      (add-sensitivity! value-e
                        (* (sensitivity 'likelihood)
                           (apply dist-Denergy dist value 1 (make-list nparams 0)))))
    (match dist-e
      [(t:dist dist-name args)
       (for ([arg args]
             [i  (in-naturals)]
             #:when (symbol? arg))
         (add-sensitivity! arg
                           (* (sensitivity 'likelihood)
                              (apply dist-Denergy dist value 0 (one-high nparams i)))))]
      [_ (void)])))

;; Returns list of N elements where only the element at index K is set.
(define (one-high n k)
  (for/list ([i n]) (if (= i k) 1 0)))

;; ----

;; PStore = Hash[ TraceVar => Real ]
;; For each position variable xi that has a corresponding momentum
;; variable pi, pstore(xi) = pi.

(define (leapfrog trace L delta xvars xstore_0)
  (define Ugradient_0
    (parameterize ((current-tstore xstore_0))
      (reverse-mode-AD trace)))
  (define pstore_0
    (for/hash ([xvar xvars])
      (values xvar (dist-sample (normal-dist 0 1)))))
  (define-values (xstore_L pstore_L Ugradient_L)
    (for/fold ([xstore_t xstore_0] [pstore_t pstore_0] [Ugradient_t Ugradient_0])
              ([ti (in-range L)])
      (leapfrog-step trace delta xstore_t pstore_t Ugradient_t)))
  (list xstore_L
        (- (total-energy xvars xstore_0 pstore_L)
           (total-energy xvars xstore_L pstore_L))))

(define (total-energy xvars xstore pstore)
  (+ (for/sum ([(xvar p) (in-hash pstore)]) (* 1/2 p p))
     ...))


(define (leapfrog-step trace delta xstore_t pstore_t Ugradient_t)
  ;; pstore_td stores p(t+delta/2)
  (define pstore_td
    (for/hash ([(xvari pi) (in-hash pstore_t)])
      (values xvari (- pi (* 1/2 delta (hash-ref Ugradient_t xvari))))))
  ;; xstore_tdd stores x(t+delta)
  (define xstore_tdd
    (hash-copy
     (for/hash ([(xvari pi) (in-hash pstore_td)])
       (values xvari (+ (hash-ref xstore_t xvari) pi)))))
  (void (exec-trace trace xstore_tdd))
  (define Ugradient_tdd
    (parameterize ((current-tstore xstore_tdd))
      (reverse-mode-AD trace xstore_tdd)))
  ;; pstore_tdd stores p(t+delta)
  (define pstore_tdd
    (for/hash ([(xvari pi) (in-hash pstore_td)])
      (values xvari (- pi (* 1/2 delta (hash-ref Ugradient_tdd xvari))))))
  (values xstore_tdd pstore_tdd Ugradient_tdd))


;; ----

(define trace1
  (list (ts:sample 'tv2 (t:quote (uniform-dist 0 1)) 'tv1)
        (ts:primop 'tv3 (primop '*) (list 'tv2 (t:quote 2)))
        (ts:primop 'tv4 (primop '+) (list 'tv3 (t:quote -1)))
        (ts:sample 'tv5 (t:dist 'normal-dist (list 'tv4 (t:quote 1))) (t:quote 0.3))))

(define tstore1 (make-hash '((tv1 . 0.7))))
(current-tstore tstore1)

(exec-trace trace1 tstore1)
