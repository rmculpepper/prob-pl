#lang racket/base
(require (rename-in racket/match [match-define defmatch])
         racket/class
         gamble
         "base.rkt"
         "lightweight-mh.rkt"
         "trace-mh.rkt")
(provide (all-defined-out)
         (all-from-out "base.rkt")
         (all-from-out "lightweight-mh.rkt")
         (all-from-out "trace-mh.rkt"))

;; ============================================================
;; MH Sampler -- combining classic eval and tracing

(define (mh-samples expr n #:verbose? [verbose? #f])
  (define s (new sampler% (expr expr) (verbose? verbose?)))
  (for/list ([i n]) (send s sample)))

;; ------------------------------------------------------------

(define sampler%
  (class object%
    (init-field expr
                [verbose? #f])
    (super-new)

    (field [prev-result #f]
           [prev-likelihood #f]
           [prev-db #f]
           [db-needs-update? #f]

           [prev-trace #f]
           [prev-result-te #f]
           [prev-tmapping #f]
           [prev-tstore #f])

    ;; Initialize
    (let loop ()
      (match (eval-top expr '#hash())
        [(list result likelihood db)
         (cond [(> likelihood 0)
                (set! prev-result result)
                (set! prev-likelihood likelihood)
                (set! prev-db db)]
               [else (loop)])]))
    (when (zero? (hash-count prev-db))
      (error 'mh "program is deterministic"))

    (define/public (sample)
      (define key-to-change (list-ref (hash-keys prev-db) (random (hash-count prev-db))))
      (cond [(entry-structural? (hash-ref prev-db key-to-change))
             (sample-S key-to-change)]
            [else
             (sample-N key-to-change)]))

    (define/public (sample-S key-to-change)
      (when db-needs-update?
        (vprintf "S: updating db\n")
        (db-add-tstore! prev-db prev-tmapping prev-tstore)
        ;; Rerun to get up-to-date likelihood
        (defmatch (list new-result new-likelihood new-db)
          (eval-top expr prev-db))
        (unless (equal? new-result prev-result)
          (error 'sample-S "result changed\n  from: ~v\n  to: ~v" prev-result new-result))
        (unless (equal? new-db prev-db)
          (error 'sample-S "db changed\n  from: ~v\n  to: ~v" prev-db new-db))
        (set! prev-likelihood new-likelihood)
        (set! db-needs-update? #f))
      (defmatch (entry #t dist value) (hash-ref prev-db key-to-change))
      (defmatch (cons value* proposal-factor) (propose dist value))
      (define modified-prev-db (hash-copy prev-db))
      (hash-set! modified-prev-db key-to-change (entry #t dist value*))
      (defmatch (list new-result new-likelihood new-db)
        (eval-top expr modified-prev-db))
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
             (set! prev-result new-result)
             (set! prev-likelihood new-likelihood)
             (set! prev-db new-db)
             (set! prev-trace #f)
             (set! prev-result-te #f)
             (set! prev-tmapping #f)
             (set! prev-tstore #f)
             new-result]
            [else
             prev-result]))

    (define/public (sample-N key-to-change)
      (cond [prev-trace
             (vprintf "N: reusing trace\n")]
            [else
             (vprintf "N: tracing\n")
             (defmatch (list result-te tmapping tstore trace) (trace-top expr prev-db))
             (set! prev-trace trace)
             (set! prev-result-te result-te)
             (set! prev-tmapping tmapping)
             (set! prev-tstore tstore)])
      (defmatch (list #f dist-te value-te)
        (hash-ref prev-tmapping key-to-change))
      (define dist (eval-trace-expr dist-te prev-tstore))
      (define value (eval-trace-expr value-te prev-tstore))
      (define current-tstore (hash-copy prev-tstore))
      (define prev-l (exec-trace prev-trace current-tstore))
      (defmatch (cons value* proposal-factor) (propose dist value))
      (tstore-set! current-tstore value-te value*)
      (define current-l (exec-trace prev-trace current-tstore))
      (define result (eval-trace-expr prev-result-te current-tstore))
      (define accept-threshold
        (* 1 ;; size of db doesn't change
           proposal-factor
           (/ current-l prev-l)))
      (cond [(< (random) accept-threshold)
             (set! db-needs-update? #t)
             (set! prev-tstore current-tstore)
             (set! prev-result result)
             result]
            [else prev-result]))

    (define/public (vprintf fmt . args)
      (when verbose? (apply eprintf fmt args)))
    ))

;; propose : Dist Value -> (cons Value Real)
(define (propose dist value)
  (defmatch (cons value* logfactor) (dist-drift dist value 0.5))
  (cons value* (exp logfactor)))

;; ============================================================

(require (only-in plot plot density plot-new-window?)
         (only-in gamble/viz hist))
(provide hist
         plot-density)

(define (plot-density vals) (plot (density vals)))

(plot-new-window? #t)

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
