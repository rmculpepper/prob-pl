#lang racket/base
(require (rename-in racket/match [match-define defmatch])
         racket/class
         gamble
         "base.rkt"
         "lightweight-mh.rkt")
(provide (all-defined-out))

;; ============================================================
;; MH Sampling

(define (mh-samples expr n #:verbose? [verbose? #f])
  (define s (new sampler% (expr expr) (verbose? verbose?)))
  (for/list ([i n]) (send s sample)))

;; ------------------------------------------------------------

(define sampler%
  (class object%
    (init-field expr
                ;; proposal-method : (U 'resample 'drift)
                [proposal-method 'resample]
                [verbose? #f])
    (super-new)

    (field [prev-result #f]        ;; Value
           [prev-likelihood #f]    ;; Real
           [prev-db #f]            ;; DB

           [accept-count 0]        ;; Nat
           [sample-count 0])       ;; Nat

    ;; Initialize
    (let loop ()
      ;; (eprintf "Trying to initialize\n")
      (match (eval-top expr '#hash())
        [(list result likelihood db)
         (cond [(> likelihood -inf.0)
                (set! prev-result result)
                (set! prev-likelihood likelihood)
                (set! prev-db db)]
               [else (loop)])]))
    ;; For simplicity, just raise an error if no random choices.
    (when (zero? (hash-count prev-db))
      (error 'mh "program is deterministic"))
    ;; (eprintf "Initialized\n")

    (define/public (sample)
      (define key-to-change (list-ref (hash-keys prev-db) (random (hash-count prev-db))))
      (set! sample-count (add1 sample-count))
      (sample-S key-to-change))

    (define/public (sample-S key-to-change)
      (defmatch (entry _ dist value) (hash-ref prev-db key-to-change))
      (defmatch (cons value* proposal-factor) (propose dist value))
      (define modified-prev-db (hash-copy prev-db))
      (hash-set! modified-prev-db key-to-change (entry #t dist value*))
      (defmatch (list new-result new-likelihood new-db)
        (eval-top expr modified-prev-db))
      ;; accept-threshold = (Qbackward / Qforward) * (Pnew / Pprev)
      (define accept-threshold
        (+ proposal-factor
           (- (log (hash-count prev-db)) (log (hash-count new-db)))
           (- new-likelihood prev-likelihood)
           (for/sum ([(key old-entry) (in-hash prev-db)]
                     #:when (hash-has-key? new-db key))
             (define new-entry (hash-ref new-db key))
             ;; ASSERT: except for key-to-change,
             ;;   (entry-value new-entry) = (entry-value old-entry)
             (- (dist-pdf (entry-dist new-entry) (entry-value new-entry) #t)
                (dist-pdf (entry-dist old-entry) (entry-value old-entry) #t)))))
      (cond [(< (log (random)) accept-threshold)
             (accept-S new-result new-likelihood new-db)
             new-result]
            [else
             (reject-S)
             prev-result]))

    (define/public (accept-S new-result new-likelihood new-db)
      (set! accept-count (add1 accept-count))
      (set! prev-result new-result)
      (set! prev-likelihood new-likelihood)
      (set! prev-db new-db))

    (define/public (reject-S)
      (void))

    (define/public (vprintf fmt . args)
      (when verbose? (apply eprintf fmt args)))

    ;; propose : Dist Value -> (cons Value Real)
    ;; Returns new value and Q(x'->x)/Q(x->x') ratio (ie, Reverse/Forward)
    (define/public (propose dist value)
      (case proposal-method
        [(resample) (propose/resample dist value)]
        [(drift) (propose/drift dist value)]
        [else (error 'propose "unknown proposal method: ~e" proposal-method)]))

    (define/public (propose/drift dist value)
      (defmatch (cons value* logfactor) (dist-drift dist value 0.5))
      (cons value* logfactor))

    (define/public (propose/resample dist value)
      (define value* (dist-sample dist))
      (cons value* (- (dist-pdf dist value #t) (dist-pdf dist value* #t))))
    ))

;; ============================================================

(define (samples->mean samples)
  (/ (apply + samples) (length samples)))

(module+ test
  (printf "p-cd: want 9.5, got: ~s\n"
          (samples->mean (mh-samples p-cd 1000)))
  (printf "p-geometric: got ~s\n"
          (mh-samples p-geometric 10))
  (printf "p-mem: got ~s\n"
          (mh-samples p-mem 3))
  (printf "p-mem2: got ~s\n"
          (mh-samples p-mem 3))
  (printf "p-match: got ~s\n"
          (mh-samples p-match 10)))
