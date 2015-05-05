#lang racket/base
(require (rename-in racket/match [match-define defmatch])
         racket/class
         gamble
         "base.rkt"
         "lightweight-mh.rkt"
         "trace-mh.rkt"
         (only-in "sampler-lightweight.rkt" [sampler% sampler-base%]))
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
  (class sampler-base%
    (super-new)
    (inherit-field expr
                   accept-count
                   sample-count
                   prev-result
                   prev-likelihood
                   prev-db)
    (inherit propose
             vprintf)

    (field [db-needs-update? #f]   ;; Boolean
           [prev-trace #f]         ;; Trace
           [prev-result-te #f]     ;; TraceExpr
           [prev-tmapping #f]      ;; TraceMapping
           [prev-tstore #f])       ;; TraceStore

    (define/override (sample)
      (define key-to-change (list-ref (hash-keys prev-db) (random (hash-count prev-db))))
      (set! sample-count (add1 sample-count))
      (cond [(entry-structural? (hash-ref prev-db key-to-change))
             (sample-S key-to-change)]
            [else
             (sample-N key-to-change)]))

    (define/override (sample-S key-to-change)
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
      (super sample-S key-to-change))

    (define/override (accept-S new-result new-likelihood new-db)
      (super accept-S new-result new-likelihood new-db)
      (set! prev-trace #f)
      (set! prev-result-te #f)
      (set! prev-tmapping #f)
      (set! prev-tstore #f))

    (define/public (sample-N key-to-change)
      (cond [prev-trace
             (vprintf "N: reusing trace\n")]
            [else
             (vprintf "N: tracing\n")
             (defmatch (list result-te tmapping tstore trace) (trace-top expr prev-db))
             (set! prev-trace trace)
             (set! prev-result-te result-te)
             (set! prev-tmapping tmapping)
             (set! prev-tstore tstore)
             (sample-N-reset)])
      (sample-N* key-to-change))

    (define/public (sample-N* key-to-change)
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
             (accept-N result current-tstore)
             result]
            [else prev-result]))

    (define/public (accept-N result current-tstore)
      (set! accept-count (add1 accept-count))
      (set! prev-result result)
      (set! prev-tstore current-tstore)
      (set! db-needs-update? #t))

    (define/public (sample-N-reset)
      (void))
    ))

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
