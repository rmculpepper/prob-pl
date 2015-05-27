#lang racket/base
(require (rename-in racket/match [match-define defmatch])
         racket/list
         gamble
         "base.rkt"
         "trace-mh.rkt")
(provide (all-defined-out))

;; TODO
;; - common sampler code?
;; - logspace
;; - partial momentum preservation across steps?
;;   (makes showing intermediate leapfrog steps easy)
;; - do AD as Trace -> Trace transformation

;; A SensStore is Hash[ TraceVar => Real ]
;; Maps trace variables to sensitivities.
;; The special variable 'Uenergy represents the Uenergy (negative log likelihood).

(define (sensitivity tvar)
  (hash-ref (current-senstore) tvar 0))
(define (set-sensitivity! tvar r)
  (hash-set! (current-senstore) tvar r))
(define (add-sensitivity! tvar r)
  (hash-set! (current-senstore) tvar (+ r (sensitivity tvar))))

;; current-tstore

;; current-senstore
(define current-senstore (make-parameter (make-hash)))

;; AD/Uenergy : Trace -> SensStore
(define (AD/Uenergy trace)
  (AD trace (hash 'Uenergy 1)))

;; AD : Trace SensStore -> SensStore
(define (AD trace init-sens)
  (parameterize ((current-senstore (hash-copy init-sens)))
    (AD-trace trace)
    (current-senstore)))

;; AD-trace : Trace -> Void
(define (AD-trace trace)
  (for ([ts (reverse trace)])
    (AD-statement ts)))

;; AD-statement : TraceStatement -> Void
(define (AD-statement ts)
  (match ts
    [(ts:primop var (primop opname) args)
     (AD-primop var opname args)]
    [(ts:sample var dist-e value-e)
     (AD-sample var dist-e value-e)]))

;; AD-primop : TraceVar Symbol (Listof TraceExpr) -> Void
(define (AD-primop dest-var opname args)
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

;; AD-sample : TraceVar TraceExpr TraceExpr -> Void
(define (AD-sample dest-var dist-e value-e)
  (let* ([dist (eval-trace-expr dist-e (current-tstore))]
         [nparams (dist-param-count dist)]
         [value (eval-trace-expr value-e (current-tstore))])
    (when (symbol? value-e)
      (add-sensitivity! value-e (sensitivity dest-var))
      (add-sensitivity! value-e
                        (* (sensitivity 'Uenergy)
                           (apply dist-Denergy dist value 1 (make-list nparams 0)))))
    (match dist-e
      [(t:dist dist-name args)
       (for ([arg args]
             [i  (in-naturals)]
             #:when (symbol? arg))
         (add-sensitivity! arg
                           (* (sensitivity 'Uenergy)
                              (apply dist-Denergy dist value 0 (one-high nparams i)))))]
      [_ (void)])))

;; Returns list of N elements where only the element at index K is set.
(define (one-high n k)
  (for/list ([i n]) (if (= i k) 1 0)))

;; ----

;; PStore = Hash[ TraceVar => Real ]
;; For each position variable xi that has a corresponding momentum
;; variable pi, pstore(xi) = pi.

;; leapfrog : Trace PosInt PosReal (Listof Symbol) TraceStore
;;         -> (list TraceStore Real)
;; Returns final state and log-threshold for acceptance.
(define (leapfrog trace L delta xvars xstore_0)
  (define Uenergy_0 (- (exec-trace trace xstore_0)))
  (define Ugradient_0
    (parameterize ((current-tstore xstore_0))
      (AD/Uenergy trace)))
  ;; Want E[Kenergy_0] to be 1, ie independent of number of RVs
  ;; E[Kenergy_0] = E[sum{i≤k} N(0,σ²)²] = kσ², so set σ = sqrt(1/k)
  (define p-dist (normal-dist 0 (sqrt (/ (length xvars)))))
  (define pstore_0
    (for/hash ([xvar xvars])
      (values xvar (dist-sample p-dist))))
  (define-values (xstore_L pstore_L Uenergy_L Ugradient_L)
    (for/fold ([xstore_t xstore_0] [pstore_t pstore_0]
               [Uenergy_t Uenergy_0] [Ugradient_t Ugradient_0])
              ([ti (in-range L)])
      (when #f (print-leapfrog-state ti xstore_t pstore_t Uenergy_t Ugradient_t))
      (vprintf 'hmc "energy_~a = ~s + ~s = ~s\n" ti
               Uenergy_t (Kenergy pstore_t) (+ Uenergy_t (Kenergy pstore_t)))
      (leapfrog-step trace delta xstore_t pstore_t Ugradient_t)))
  (when #f (print-leapfrog-state L xstore_L pstore_L Uenergy_L Ugradient_L))
  (vprintf 'hmc "energy_L = ~s + ~s = ~s\n"
           Uenergy_L (Kenergy pstore_L) (+ Uenergy_L (Kenergy pstore_L)))
  (vprintf 'hmc "distance moved = ~s\n"
           (distance xstore_0 xstore_L))
  (list xstore_L
        (- (+ Uenergy_0 (Kenergy pstore_0))
           (+ Uenergy_L (Kenergy pstore_L)))))

(define (print-leapfrog-state step xstore pstore Uenergy Ugradient)
  (printf "\nstep ~s:\n" step)
  (printf "  xstore = ~s\n" xstore)
  (printf "  pstore = ~s\n" pstore)
  (printf "  Uenergy = ~s\n" Uenergy)
  (printf "  Ugradient = ~s\n" Ugradient))

(define (distance xstore1 xstore2)
  (sqrt
   (for/sum ([(k v1) (in-hash xstore1)])
     (define v2 (hash-ref xstore2 k))
     (* (- v1 v2) (- v1 v2)))))


;; Kenergy : PStore -> Real
(define (Kenergy pstore)
  (for/sum ([(xvar p) (in-hash pstore)]) (* 1/2 p p)))

;; leapfrog-step : Trace PosReal TraceStore PStore SensStore
;;              -> (values TraceStore PStore Real SensStore)
(define (leapfrog-step trace delta xstore_t pstore_t Ugradient_t)
  ;; pstore_td stores p(t+delta/2)
  (define pstore_td
    (for/hash ([(xvari pi) (in-hash pstore_t)])
      (values xvari (- pi (* 1/2 delta (hash-ref Ugradient_t xvari))))))
  (when #f (printf "  pstore' = ~s\n" pstore_td))
  ;; xstore_tdd stores x(t+delta)
  (define xstore_tdd
    (hash-copy
     (for/hash ([(xvari pi) (in-hash pstore_td)])
       (values xvari (+ (hash-ref xstore_t xvari) (* delta pi))))))
  (when #f (printf "  xstore'' = ~s\n" xstore_tdd))
  (define Uenergy_tdd (- (exec-trace trace xstore_tdd)))
  (define Ugradient_tdd
    (parameterize ((current-tstore xstore_tdd))
      (AD/Uenergy trace)))
  ;; pstore_tdd stores p(t+delta)
  (define pstore_tdd
    (for/hash ([(xvari pi) (in-hash pstore_td)])
      (values xvari (- pi (* 1/2 delta (hash-ref Ugradient_tdd xvari))))))
  (when #f (printf "  pstore'' = ~s\n" pstore_tdd))
  (values xstore_tdd pstore_tdd Uenergy_tdd Ugradient_tdd))


;; ----

#|
(define trace0
  ;; X ~ (uniform 0 1)
  ;; Y ~ (normal (- (* 2 X) 1) 1)
  ;; observe Y = 0.3
  (list (ts:sample 'tv2 (t:quote (uniform-dist 0 1)) 'tv1)
        (ts:primop 'tv3 (primop '*) (list 'tv2 (t:quote 2)))
        (ts:primop 'tv4 (primop '+) (list 'tv3 (t:quote -1)))
        (ts:sample 'tv5 (t:dist 'normal-dist (list 'tv4 (t:quote 1))) (t:quote 0.3))))

(define trace1
  ;; X ~ (normal 0 1)
  ;; Y ~ (normal (- (* 2 X) 1) 1)
  ;; observe Y = 0.3
  (list (ts:sample 'tv2 (t:quote (normal-dist 0 1)) 'tv1)
        (ts:primop 'tv3 (primop '*) (list 'tv2 (t:quote 2)))
        (ts:primop 'tv4 (primop '+) (list 'tv3 (t:quote -1)))
        (ts:sample 'tv5 (t:dist 'normal-dist (list 'tv4 (t:quote 1))) (t:quote 0.3))))

(define tstore1 (make-hash '((tv1 . 0.7))))
(exec-trace trace1 tstore1)
(parameterize ((current-tstore tstore1))
  (AD/Uenergy trace1))
|#

#|
(define trace2
  (list (ts:primop 'y (primop '*) (list (t:quote 2) 'x))
        (ts:sample 'z (t:quote (normal-dist 0 1)) 'y)))
(define tstore2 (make-hash '((x . 0.2))))
(exec-trace trace2 tstore2)

(current-tstore tstore2)
(AD trace2 (hash 'y 1))
(AD/Unenergy trace2)
|#

#|
(define trace-circ
  ;; observe X*X + Y*Y ~= 1
  (list (ts:sample 'x (t:quote (uniform-dist -2 2)) 'Xin)
        (ts:sample 'y (t:quote (uniform-dist -2 2)) 'Yin)
        (ts:primop 'x^2 (primop '*) (list 'x 'x))
        (ts:primop 'y^2 (primop '*) (list 'y 'y))
        (ts:primop 'rad^2 (primop '+) (list 'x^2 'y^2))
        (ts:sample '_o (t:dist 'normal-dist (list 'rad^2 (t:quote 0.3))) (t:quote 1))))

(define tstore-circ (make-hash '((Xin . 1) (Yin . 0))))
(exec-trace trace-circ tstore-circ)
|#
