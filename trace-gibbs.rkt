#lang racket/base
(require (rename-in racket/match [match-define defmatch])
         gamble
         "base.rkt"
         "lightweight-mh.rkt"
         "trace-mh.rkt")
(provide (all-defined-out))

;; ------------------------------------------------------------
;; Slicing for Gibbs sampling

;; Reslices a trace already minimized to the given variable by
;; removing rescoring operations of conjugate distributions. A
;; residual trace and closer-to-full conditional distribution are
;; returned. (The distribution might not be the full conditional
;; distribution, because the residual trace might contain
;; non-conjugate rescoring operations that could not be absorbed.)

;; gibbs-reslice : Trace TraceVar TraceStore -> (list Trace Dist)
(define (gibbs-reslice trace var tstore)
  (match trace
    [(cons (and (ts:sample dest-var dist-e var*) ts) trace-rest)
     (unless (equal? var* var)
       (error 'gibbs-reslice "internal error: ~s != ~s" var var*))
     (define dist (eval-trace-expr dist-e tstore))
     (defmatch (list trace* dist*)
       (gibbs-reslice* trace-rest dest-var tstore dist))
     (list (cons (ts:sample dest-var (t:quote dist*) var) trace*) dist*)]
    [_ (error 'gibbs-reslice "internal error: bad trace")]))

;; gibbs-reslice* : Trace TraceVar TraceStore Dist -> (list Trace Dist)
(define (gibbs-reslice* trace main-var tstore main-dist)
  (define (loop trace main-dist racc)
    (match trace
      [(cons ts trace-rest)
       (match ts
         [(ts:primop dest-var p args)
          (loop trace-rest main-dist (cons ts racc))]
         [(ts:sample dest-var dist-te value-te)
          (cond [(dist-te->dist-pattern dist-te main-var tstore)
                 => (lambda (dist-pattern)
                      ;; (eprintf "  ts = ~s\n" ts)
                      ;; (eprintf "  main-dist = ~s\n" main-dist)
                      ;; (eprintf "  dist-pattern = ~s\n" dist-pattern)
                      (define value (eval-trace-expr value-te tstore))
                      (cond [(dist-update-prior main-dist dist-pattern (vector value))
                             => (lambda (main-dist*)
                                  ;; Do not emit ts, absorbed into main-dist*
                                  ;; (eprintf "  main-dist* = ~s\n" main-dist*)
                                  (loop trace-rest main-dist* racc))]
                            [else (loop trace-rest main-dist (cons ts racc))]))]
                [else
                 (loop trace-rest main-dist (cons ts racc))])])]
      ['() (list (reverse racc) main-dist)]))
  (loop trace main-dist null))

;; dist-te->dist-pattern : TraceExpr TraceVar TraceStore -> (U DistPattern #f)
;; Returns #f or a dist-pattern suitable as an argument to dist-update-prior.
(define (dist-te->dist-pattern dist-te main-var tstore)
  (match dist-te
    [(t:dist dist-primop args)
     #:when (= 1 (length (filter (lambda (a) (equal? a main-var)) args)))
     (cons dist-primop
           (for/list ([arg args])
             (cond [(equal? arg main-var) '_]
                   [else (eval-trace-expr arg tstore)])))]
    [_ #f]))

;; dist-update-prior needs a better interface to enable staging: instead of
;;   (dist-update-prior prior '(sub-dist _ p ...) (vector v ...)) -> posterior
;; maybe replace with
;;   (dist-update-prior* 'prior-dist '(sub-dist 0)) -> (lambda (prior ps vs) posterior)
