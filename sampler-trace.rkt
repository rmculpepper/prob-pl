#lang racket/base
(require (rename-in racket/match [match-define defmatch])
         racket/class
         gamble
         data/order
         "base.rkt"
         "lightweight-mh.rkt"
         "trace-mh.rkt"
         "trace-slice.rkt"
         "trace-gibbs.rkt"
         "trace-hmc.rkt"
         (only-in "sampler-lightweight.rkt" [sampler% sampler-base%]))
(provide (all-defined-out)
         (all-from-out "base.rkt")
         (all-from-out "lightweight-mh.rkt")
         (all-from-out "trace-mh.rkt"))

;; ============================================================
;; MH Sampler -- combining classic eval and tracing

(define (mh-samples expr n
                    #:N-method  [method 'trace]
                    #:hmc-L     [hmc-L default-hmc-L]
                    #:hmc-delta [hmc-delta default-hmc-delta])
  (define s
    (new sampler% (expr expr) (N-method method)
         (hmc-L hmc-L) (hmc-delta hmc-delta)))
  (for/list ([i n]) (send s sample)))

(define default-hmc-L 10)
(define default-hmc-delta 0.1)

(define (make-sampler expr #:N-method [N-method 'trace])
  (new sampler% (expr expr) (N-method N-method)))

;; ------------------------------------------------------------

(define sampler%
  (class sampler-base%
    (init-field [N-method       'trace]
                [hmc-L          default-hmc-L]
                [hmc-delta      default-hmc-delta])
    (inherit-field expr
                   accept-count
                   sample-count
                   prev-result
                   prev-likelihood
                   prev-db)
    (inherit propose)
    (super-new)

    (field [db-needs-update? #f]   ;; Boolean
           [prev-trace #f]         ;; Trace
           [prev-result-te #f]     ;; TraceExpr
           [prev-tmapping #f]      ;; TraceMapping
           [prev-tstore #f]        ;; TraceStore
           [prev-slicemap #f])     ;; Hash[ TraceVar => Trace ]

    (define/public (get-trace)
      prev-trace)

    (define/public (get-structural-choices)
      (get-choices #t))

    (define/public (get-choices [structural-only? #f])
      (sort (for/list ([(addr e) (in-hash (or prev-db '#hash()))]
                       #:when (if structural-only?
                                  (entry-structural? e)
                                  #t))
              (list addr e))
            (order-<? datum-order)
            #:key car))

    (define/override (sample)
      (define key-to-change (list-ref (hash-keys prev-db) (random (hash-count prev-db))))
      (set! sample-count (add1 sample-count))
      (vprintf 'mh "-- Starting sample #~s\n" sample-count)
      (cond [(entry-structural? (hash-ref prev-db key-to-change))
             (sample-S key-to-change)]
            [else
             (sample-N key-to-change)]))

    (define/override (sample-S key-to-change)
      (when db-needs-update?
        (vprintf 'trace "S: updating db\n")
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
      (set! prev-tstore #f)
      (set! prev-slicemap #f))

    (define/public (sample-N key-to-change)
      (cond [prev-trace
             (vprintf 'trace "N: reusing trace\n")]
            [else
             (vprintf 'trace "N: tracing\n")
             (defmatch (list result-te tmapping tstore trace) (trace-top expr prev-db))
             (set! prev-trace trace)
             (set! prev-result-te result-te)
             (set! prev-tmapping tmapping)
             (set! prev-tstore tstore)
             (sample-N-reset)])
      (case N-method
        [(trace sliced-trace gibbs)
         (sample-N/single-site key-to-change)]
        [(hmc)
         (sample-N/hmc)]
        [else (error 'sample-N "unknown sampling method: ~s\n" N-method)]))

    (define/public (sample-N/single-site key-to-change)
      (defmatch (list #f dist-te value-te)
        (hash-ref prev-tmapping key-to-change))
      (define dist (eval-trace-expr dist-te prev-tstore))
      (define value (eval-trace-expr value-te prev-tstore))
      (define current-tstore (hash-copy prev-tstore))
      (defmatch (list use-trace value* proposal-factor)
        (single-site/method value-te current-tstore dist value))
      (define prev-l (exec-trace use-trace current-tstore))
      (tstore-set! current-tstore value-te value*)
      (define current-l (exec-trace use-trace current-tstore))
      (define result (eval-trace-expr prev-result-te current-tstore))
      (define accept-threshold
        (+ 0 ;; size of db doesn't change
           proposal-factor
           (- current-l prev-l)))
      (vprintf 'mh-ratio "Accept ratio (log) = ~s\n" accept-threshold)
      (cond [(< (log (random)) accept-threshold)
             (accept-N result current-tstore)
             result]
            [else
             (vprintf 'mh-reject "Rejected\n")
             prev-result]))

    ;; single-site/method : TraceExpr TraceStore Dist Value -> (list Trace Value Real)
    (define/public (single-site/method value-te current-tstore dist value)
      (case N-method
        [(trace)
         (defmatch (cons value* proposal-factor) (propose dist value))
         (list prev-trace value* proposal-factor)]
        [(sliced-trace)
         (defmatch (cons value* proposal-factor) (propose dist value))
         (list (get-sliced-trace value-te) value* proposal-factor)]
        [(gibbs)
         (define sliced-trace (get-sliced-trace value-te))
         (defmatch (list gibbs-trace cond-dist)
           (gibbs-reslice sliced-trace value-te current-tstore))
         (vprintf 'trace "N: gibbs eliminated ~s rescores\n"
                  (- (length (filter ts:sample? sliced-trace))
                     (length (filter ts:sample? gibbs-trace))))
         (vprintf 'gibbs "N: gibbs trace = \n")
         (for ([ts gibbs-trace]) (vprintf 'gibbs "    ~v\n" ts))
         (define value* (dist-sample cond-dist))
         (define proposal-factor 0)
         (list gibbs-trace value* proposal-factor)]))

    (define/public (get-sliced-trace value-te)
      (cond [(hash-ref prev-slicemap value-te #f)
             => (lambda (s)
                  (vprintf 'trace "N: reusing sliced trace\n")
                  s)]
            [else
             (vprintf 'trace "N: slicing trace wrt ~e\n" value-te)
             (define s (slice-trace prev-trace value-te))
             (hash-set! prev-slicemap value-te s)
             s]))

    (define/public (get-gibbs-trace value-te)
      (define sliced-trace (get-sliced-trace value-te))
      (defmatch (list gibbs-trace cond-dist)
        (gibbs-reslice sliced-trace value-te current-tstore))
      gibbs-trace)

    (define/public (sample-N/hmc)
      ;; We change all non-structural choices simultaneously.
      (cond [prev-trace
             (vprintf 'trace "N: reusing trace\n")]
            [else
             (vprintf 'trace "N: tracing\n")
             (defmatch (list result-te tmapping tstore trace) (trace-top expr prev-db))
             (set! prev-trace trace)
             (set! prev-result-te result-te)
             (set! prev-tmapping tmapping)
             (set! prev-tstore tstore)])
      (define N-vars
        (filter symbol? (for/list ([(_addr sdv) (in-hash prev-tmapping)]) (caddr sdv))))
      (defmatch (list current-tstore logthreshold)
        (leapfrog prev-trace hmc-L hmc-delta N-vars prev-tstore))
      (define result (eval-trace-expr prev-result-te current-tstore))
      (define accept-threshold logthreshold)
      (vprintf 'mh-ratio "Accept ratio (log) = ~s\n" accept-threshold)
      (cond [(< (log (random)) accept-threshold)
             (accept-N result current-tstore)
             result]
            [else
             (vprintf 'mh-reject "Rejected\n")
             prev-result]))

    (define/public (accept-N result current-tstore)
      (set! accept-count (add1 accept-count))
      (set! prev-result result)
      (set! prev-tstore current-tstore)
      (set! db-needs-update? #t))

    (define/public (sample-N-reset)
      (set! prev-slicemap (make-hash)))
    ))

;; ============================================================

(require (only-in plot plot density plot-new-window? points lines)
         (only-in gamble/viz hist))
(provide hist
         plot-density)

(define (plot-density vals) (plot (density vals)))

(plot-new-window? #t)

;; ============================================================

(module+ test
  (define (do-tests method [do-discrete? #t])
    (printf "** ~s\n" method)
    (printf "p-cd: want 9.5, got: ~s\n"
            (samples->mean
             (list->vector (map (lambda (x) (cons x 1))
                                (mh-samples p-cd 1000 #:N-method method)))))
    (when do-discrete?
      (printf "p-geometric: got ~s\n"
              (mh-samples p-geometric 10 #:N-method method))
      (printf "p-mem: got ~s\n"
              (mh-samples p-mem 3 #:N-method method))
      (printf "p-mem2: got ~s\n"
              (mh-samples p-mem 3 #:N-method method)))
    (printf "p-match: got ~s\n"
            (mh-samples p-match 10 #:N-method method))
    (newline))

  (do-tests 'trace)
  (do-tests 'sliced-trace)
  (do-tests 'gibbs)
  (do-tests 'hmc #f))

;; p-match is a good example for slicing

;; circle-demo for hmc
(define (circle-demo N)
  (define s (new sampler% (expr p-circle) (N-method 'hmc)))
  (define pts (for/list ([i N]) (send s sample)))
  (eprintf "accept = ~s, reject = ~s\n"
           (get-field accept-count s) (get-field reject-count s))
  (plot (list (points pts)
              (lines pts #:color "pink"))))
