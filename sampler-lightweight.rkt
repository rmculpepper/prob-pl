;; Copyright (c) 2016 Ryan Culpepper
;; Released under the terms of the 2-clause BSD license.
;; See the file COPYRIGHT for details.

#lang racket/base
(require (rename-in racket/match [match-define defmatch])
         racket/class
         gamble
         "base.rkt"
         "lightweight-db.rkt"
         "lightweight-mh.rkt")
(provide (all-defined-out))

;; ============================================================
;; MH Sampling

(define (mh-samples expr n)
  (define s (new sampler% (expr expr)))
  (for/list ([i n]) (send s sample)))

;; ------------------------------------------------------------

(define sampler%
  (class object%
    (init-field expr
                ;; proposal-method : (U 'resample 'drift)
                [proposal-method 'resample])
    (super-new)

    (field [prev-result #f]        ;; Value
           [prev-likelihood #f]    ;; Real
           [prev-db #f]            ;; DB

           [accept-count 0]        ;; Nat
           [sample-count 0])       ;; Nat

    ;; Initialize
    (let loop ()
      (vprintf 'init "Trying to initialize\n")
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
    (vprintf 'init "Initialized\n")

    (define/public (sample)
      (define key-to-change (list-ref (hash-keys prev-db) (random (hash-count prev-db))))
      (set! sample-count (add1 sample-count))
      (vprintf 'mh "-- Starting sample #~s\n" sample-count)
      (sample-S key-to-change))

    (define/public (sample-S key-to-change)
      (defmatch (entry _ dist value) (hash-ref prev-db key-to-change))
      (defmatch (cons value* l-R/F) (propose dist value))
      (define modified-prev-db (hash-set prev-db key-to-change (entry #t dist value*)))
      (defmatch (list new-result new-likelihood new-db)
        (eval-top expr modified-prev-db))
      (define threshold
        (accept-threshold l-R/F prev-db prev-likelihood new-db new-likelihood))
      (vprintf 'mh-ratio "Accept ratio (log) = ~s\n" threshold)
      (cond [(< (log (random)) threshold)
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
      (vprintf 'mh-reject "Rejected\n")
      (void))

    ;; propose : Dist Value -> (cons Value Real)
    ;; Returns new value and Q(x'->x)/Q(x->x') ratio (ie, Reverse/Forward)
    (define/public (propose dist value)
      (case proposal-method
        [(resample) (propose/resample dist value)]
        [(drift) (propose/drift dist value)]
        [else (error 'propose "unknown proposal method: ~e" proposal-method)]))

    (define/public (propose/drift dist value)
      (defmatch (cons value* logfactor) (dist-drift1 dist value 0.5))
      (cons value* logfactor))

    (define/public (propose/resample dist value)
      (define value* (dist-sample dist))
      (cons value* (- (dist-pdf dist value #t) (dist-pdf dist value* #t))))
    ))

;; ============================================================

(module+ test
  (printf "p-cd: want 9.5, got: ~s\n"
          (samples->mean (list->vector (map (lambda (x) (cons x 1)) (mh-samples p-cd 1000)))))
  (printf "p-geometric: got ~s\n"
          (mh-samples p-geometric 10))
  (printf "p-mem: got ~s\n"
          (mh-samples p-mem 3))
  (printf "p-mem2: got ~s\n"
          (mh-samples p-mem 3))
  (printf "p-match: got ~s\n"
          (mh-samples p-match 10)))
