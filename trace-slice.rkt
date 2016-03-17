;; Copyright (c) 2016 Ryan Culpepper
;; Released under the terms of the 2-clause BSD license.
;; See the file COPYRIGHT for details.

#lang racket/base
(require (rename-in racket/match [match-define defmatch])
         gamble
         "base.rkt"
         "lightweight-mh.rkt"
         "trace-mh.rkt")
(provide (all-defined-out))

;; TODO:
;; - do slice-sampling via slice

;; slice-trace : Trace TraceVar -> Trace
(define (slice-trace trace tvar)
  (slice-trace* trace (hash tvar #t)))

;; slice-trace* : Trace Hash[Tvar => #t] -> Trace
(define (slice-trace* trace rel)
  (match trace
    [(cons (and (ts:primop var primop args) ts) trace-rest)
     (cond [(any-relevant? rel args)
            (let ([rel* (hash-set rel var #t)])
              (cons ts (slice-trace* trace-rest rel*)))]
           [else (slice-trace* trace-rest rel)])]
    [(cons (and (ts:sample var dist value) ts) trace-rest)
     (cond [(relevant? rel value)
            (let ([rel* (hash-set rel var #t)])
              (cons ts (slice-trace* trace-rest rel*)))]
           [(relevant? rel dist)
            (cons ts (slice-trace* trace-rest rel))]
           [else (slice-trace* trace-rest rel)])]
    ['() '()]))

;; relevant? : Hash[TraceVar => #t] TraceExpr -> Boolean
(define (relevant? rel te)
  (match te
    [(t:quote _) #f]
    [(t:cons e1 e2) (or (relevant? rel e1) (relevant? rel e2))]
    [(t:dist _ args) (any-relevant? rel args)]
    [(? symbol? tvar) (hash-ref rel tvar #f)]))

;; any-relevant? : Hash[TraceVar => #t] (Listof TraceExpr) -> Boolean
(define (any-relevant? rel tes)
  (for/or ([te tes]) (relevant? rel te)))
