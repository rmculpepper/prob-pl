;; Copyright (c) 2016 Ryan Culpepper
;; Released under the terms of the 2-clause BSD license.
;; See the file COPYRIGHT for details.

#lang racket/base
(require racket/list
         gamble)
(provide (all-defined-out))

;; An Addr is (listof AddrFrame)
;; where AddrFrame = (U 'top 'fix CallSite (cons 'mem (Listof Value)))

;; A DB is Hash[Address => Entry]

;; An Entry is (entry Boolean Dist Value)
(struct entry (structural? dist value) #:transparent)

;; accept-threshold : Real DB Real DB Real -> Real
;; Single-site acceptance threshold.
(define (accept-threshold l-R/F old-db old-ll new-db new-ll)
  (+ l-R/F
     (- (log (exact->inexact (hash-count old-db)))
        (log (exact->inexact (hash-count new-db))))
     (- new-ll old-ll)
     (db-common-dlx old-db new-db)))

;; db-common-dlx : DB DB -> Real
;; Difference in log densities of random variables held in common.
(define (db-common-dlx old-db new-db)
  (for/sum ([(key old-entry) (in-hash old-db)]
            #:when (hash-has-key? new-db key))
    (define new-entry (hash-ref new-db key))
    ;; ASSERT: except for key-to-change, new-entry.value = old-entry.value
    (- (dist-pdf (entry-dist new-entry) (entry-value new-entry) #t)
       (dist-pdf (entry-dist old-entry) (entry-value old-entry) #t))))

;; db-merge : DB DB (Listof Addr) -> DB
;; Copies non-stale parts of old db that aren't already in new-db.
(define (db-merge new-db old-db copy-prefixes)
  (for/fold ([db new-db])
            ([(key entry) (in-hash old-db)])
    (cond [(hash-has-key? db key)
           db]
          [(for/or ([copy-prefix (in-list copy-prefixes)])
             (address-prefix? copy-prefix key))
           (hash-set db key entry)]
          [else db])))

;; address-prefix? : Addr Addr -> Boolean
(define (address-prefix? prefix addr)
  (and (<= (length prefix) (length addr))
       (equal? prefix (take-right addr (length prefix)))))
