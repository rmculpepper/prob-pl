#lang racket/base
(require racket/match
         racket/set
         (for-syntax racket/base)
         "base.rkt")
(provide (all-defined-out))

;; Alpha-conversion

(define (alpha-convert expr)
  ;; loop* : Expr (Listof (cons Symbol Symbol)) -> Expr
  (define (loop* expr rens)
    (define (loop expr [rens rens]) (loop* expr rens))
    (match expr
      [(? symbol? var)
       (cond [(assq var rens) => cdr]
             [else var])]
      [(expr:quote v) expr]
      [(expr:lambda formals body)
       (let ([formals* (freshen formals)])
         (expr:lambda formals* (loop body (append (map cons formals formals*) rens))))]
      [(expr:fix e)
       (expr:fix (loop e))]
      [(expr:app cs op args)
       (expr:app cs (loop op) (map loop args))]
      [(expr:if e1 e2 e3)
       (expr:if (loop e1) (loop e2) (loop e3))]
      [(expr:S-sample cs e)
       (expr:S-sample cs (loop e))]
      [(expr:N-sample cs e)
       (expr:N-sample cs (loop e))]
      [(expr:observe-sample e1 e2)
       (expr:observe-sample (loop e1) (loop e2))]
      [(expr:fail)
       (expr:fail)]
      [(expr:mem cs e)
       (expr:mem cs (loop e))]
      [(expr:let* vars rhss body)
       (let bindingsloop ([vars vars] [rhss rhss] [rens rens]
                          [r-vars* null] [r-rhss* null])
         (match* [vars rhss]
           [[(cons var vars) (cons rhs rhss)]
            (define var* (freshen var))
            (bindingsloop vars rhss
                          (cons (cons var var*) rens)
                          (cons var* r-vars*)
                          (cons (loop rhs rens) r-rhss*))]
           [['() '()]
            (expr:let* (reverse r-vars*) (reverse r-rhss*)
                       (loop body rens))]))]))
  (loop* expr null))

(define fresh-counter 0)

(define (freshen x)
  (set! fresh-counter (add1 fresh-counter))
  (let loop ([x x])
    (cond [(symbol? x) (string->symbol (format "~s_~s" x fresh-counter))]
          [(list? x) (map loop x)])))

;; SBA

;; An SBA-Init is hashof[(cons Key Key) => #t]
;; each entry is (cons From-Key To-Key)

;; An SBA-Inc is hashof[Key => (setof Key)]
;; also From => (setof To) order.

;; An SBA is hashof[Key => (setof Key)]
;; in To => (setof From) order.

;; A Key is one of
;; - Expr
;; - (list 'dom Nat Key)
;; - (list 'rng Key)
;; - (list 'car Key)
;; - (list 'cdr Key)

(define (sba-init expr)
  (define t (make-hash))
  (define (flow! from to)
    (hash-set! t (cons from to) #t))
  (define (loop expr)
    (match expr
      [(? symbol? var)
       (void)]
      [(expr:quote v)
       (flow! expr expr)]
      [(expr:lambda formals body)
       (loop body)
       (flow! expr expr)
       (for ([formal formals] [i (in-naturals)])
         (flow! (list 'dom i expr) formal))
       (flow! body (list 'rng expr))]
      [(expr:fix e)
       ;; ????
       (loop e)
       (flow! expr expr)
       (flow! expr (list 'dom 0 e))]
      [(expr:app cs op args)
       (loop op) (for-each loop args)
       (for ([arg args] [i (in-naturals)])
         (flow! arg (list 'dom i op)))
       (flow! (list 'rng op) expr)]
      [(expr:if e1 e2 e3)
       (loop e1) (loop e2) (loop e3)
       (flow! e2 expr)
       (flow! e3 expr)]
      [(expr:S-sample cs e)
       (loop e)]
      [(expr:N-sample cs e)
       (loop e)]
      [(expr:observe-sample e1 e2)
       (loop e1) (loop e2)]
      [(expr:fail)
       (void)]
      [(expr:mem cs e)
       (loop e)
       ;; Pretend identity
       (flow! e expr)]
      [(expr:let* vars rhss body)
       (for-each loop rhss) (loop body)
       (for ([var vars] [rhs rhss])
         (flow! rhs var))
       (flow! body expr)]))
  (loop expr)
  (for/fold ([h (hash)]) ([from+to (in-hash-keys t)])
    (sba-add h (car from+to) (cdr from+to))))

(define (sba-add h from to)
  (hash-set h from (set-add (hash-ref h from (set)) to)))

(define (sba-closure sba)
  (let ([sba* (sba-closure1 sba)])
    (if (equal? sba sba*)
        sba*
        (sba-closure sba*))))


;; (M clause ...) : SBA -> SBA
(define-syntax (M stx)
  (syntax-case stx (≤)
    [(M (p1 ≤ p2) . clauses)
     #'(lambda (sba)
         (for/fold ([sba sba]) ([(k1 _) (in-hash sba)])
           (match k1
             [p1
              ((M* (p1 ≤ p2) . clauses) sba)]
             [_ sba])))]))

;; (M* clause ...) : SBA -> SBA
(define-syntax (M* stx)
  (syntax-case stx (≤ =>)
    [(M* (p1 ≤ p2) . clauses)
     #'(lambda (sba)
         (for*/fold ([sba sba])
                    ([k2 (in-set (hash-ref sba p1 (set)))])
           (match k2
             [p2
              ((M* . clauses) sba)]
             [_ sba])))]
    [(M* => (pfrom ≤ pto))
     #'(lambda (sba) (sba-add sba pfrom pto))]))

(define sba-closure1
  (compose (M (k1 ≤ k2)               (k2 ≤ k3)               => (k1 ≤ k3))
           (M (k1 ≤ (list 'rng k2))   (k2 ≤ k3)               => (k1 ≤ (list 'rng k3)))
           (M ((list 'dom i k1) ≤ k2) (k2 ≤ k3)               => ((list 'dom k3) ≤ k2))
           (M (k1 ≤ (list 'rng k2))   ((list 'rng k2) ≤ k3)   => (k1 ≤ k3)) ;; -- redundant w/ (1) ???
           (M (k1 ≤ (list 'dom i k2)) ((list 'dom i k2) ≤ k3) => (k1 ≤ k3))))

(define (sba-final sba)
  (for*/fold ([h (hash)])
             ([(k1 k2-set) (in-hash sba)]
              [k2 (in-set k2-set)])
    (sba-add h k2 k1)))

(define (sba expr)
  (sba-final (sba-closure (sba-init expr))))

(define p-sba-test
  (parse-expr
   '(lambda (k)
     (let* ([f (lambda (x) x)])
       (k (f 1) (f 2))))))
