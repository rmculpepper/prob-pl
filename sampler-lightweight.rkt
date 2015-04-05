#lang racket/base
(require (rename-in racket/match [match-define defmatch])
         gamble
         "base.rkt"
         "lightweight-mh.rkt")
(provide (all-defined-out))

;; ============================================================
;; MH Sampling

(define (mh-samples e n)
  (define results '())

  (define-values (prev-result prev-likelihood prev-db)
    (let loop ()
      (match (eval-top e '#hash())
        [(list result likelihood db)
         (cond [(> likelihood 0)
                (values result likelihood db)]
               [else (loop)])])))

  (for ([i n])
    (define modified-last-db (hash-copy prev-db))
    (define proposal-factor (propose! modified-last-db))
    (defmatch (list new-result new-likelihood new-db)
      (eval-top e modified-last-db))
    (define accept-threshold
      ;; (Qbackward / Qforward) * (Pnew / Pprev)
      (* proposal-factor
         (/ (hash-count prev-db) (hash-count new-db))
         (/ new-likelihood prev-likelihood)
         (for/product ([(key old-entry) (in-hash prev-db)]
                       #:when (hash-has-key? new-db key))
           (define new-entry (hash-ref new-db key))
           ;; ASSERT: (entry-value new-entry) = (entry-value old-entry)
           (/ (dist-pdf (entry-dist new-entry) (entry-value new-entry))
              (dist-pdf (entry-dist old-entry) (entry-value old-entry))))))
    (cond [(< (random) accept-threshold)
           (set! results (cons new-result results))
           (set! prev-result new-result)
           (set! prev-likelihood new-likelihood)
           (set! prev-db new-db)]
          [else
           (set! results (cons prev-result results))]))
  (reverse results))

;; propose! : DB -> Real
(define (propose! db)
  (define size (hash-count db))
  (when (zero? size) (error 'propose! "program is deterministic"))
  (define i (random size))
  (define key-to-change (list-ref (hash-keys db) i))
  (defmatch (entry structural? dist value) (hash-ref db key-to-change))
  (defmatch (cons value* logfactor) (dist-drift dist value 0.5))
  (hash-set! db key-to-change (entry structural? dist value*))
  (exp logfactor))

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
