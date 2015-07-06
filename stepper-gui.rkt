#lang racket/base
(require racket/class
         racket/match
         racket/pretty
         "stepper-base.rkt"
         racket/gui/base
         macro-debugger/view/cursor
         macro-debugger/syntax-browser/util
         macro-debugger/syntax-browser/text
         unstable/gui/notify
         images/compile-time
         images/gui
         (for-syntax racket/base
                     images/icons/arrow images/icons/control images/logos
                     images/icons/style))
(provide (all-defined-out))

(define (make-gui-emit-step)
  (define f (new frame% (width 600) (height 400) (label "Stepper")))
  (define w (new stepper-widget% (parent f)))
  (send f show #t)
  (lambda (s) (send w add-step s)))

;; ============================================================
;; from macro-debugger/view/stepper

(define navigate-to-start-icon
  (compiled-bitmap (search-backward-icon #:color syntax-icon-color #:height (toolbar-icon-height))))
(define navigate-previous-icon
  (compiled-bitmap (step-back-icon #:color syntax-icon-color #:height (toolbar-icon-height))))
(define navigate-next-icon
  (compiled-bitmap (step-icon #:color syntax-icon-color #:height (toolbar-icon-height))))
(define navigate-to-end-icon
  (compiled-bitmap (search-forward-icon #:color syntax-icon-color #:height (toolbar-icon-height))))

;; stepper-widget%
(define stepper-widget%
  (class object%
    (init-field parent)

    (define frame (send parent get-top-level-window))
    (define eventspace (send frame get-eventspace))

    (define-syntax-rule (with-eventspace . body)
      (parameterize ((current-eventspace eventspace))
        (queue-callback (lambda () . body))))

    ;; Steps

    ;; steps : (Cursor-of Step%)
    (define steps (cursor:new null))

    ;; get-step-count : -> Nat
    (define/public (get-step-count)
      (cursor-count steps))

    ;; current-step-index : notify of number/#f
    (define-notify current-step-index (new notify-box% (value #f)))

    ;; add-step : Step% -> Void
    (define/public (add-step s)
      (with-eventspace
        (cursor:add-to-end! steps (list s))
        (refresh)))

    (define superarea (new vertical-pane% (parent parent)))
    (define area
      (new vertical-panel%
           (parent superarea)
           (enabled #f)))
    (define top-panel
      (new horizontal-panel%
           (parent area)
           (horiz-margin 5)
           (stretchable-height #f)))
    (define supernavigator
      (new horizontal-panel%
           (parent top-panel)
           (stretchable-height #f)
           (alignment '(center center))))
    (define navigator
      (new horizontal-panel%
           (parent supernavigator)
           (stretchable-width #f)
           (stretchable-height #f)
           (alignment '(left center))))
    (define extra-navigator
      (new horizontal-panel%
           (parent supernavigator)
           (stretchable-width #f)
           (stretchable-height #f)
           (alignment '(left center))
           (style '())))

    (define stepview
      (new step-view%
           (parent area)
           (widget this)))
    (define control-pane
      (new vertical-panel% (parent area) (stretchable-height #f)))

    (define nav:start
      (new button% (label (list navigate-to-start-icon "Start" 'left)) (parent navigator)
           (callback (lambda (b e) (navigate-to-start)))))
    (define nav:previous
      (new button% (label (list navigate-previous-icon "Step" 'left)) (parent navigator)
           (callback (lambda (b e) (navigate-previous)))))
    (define nav:next
      (new button% (label (list navigate-next-icon "Step" 'right)) (parent navigator)
           (callback (lambda (b e) (navigate-next)))))
    (define nav:end
      (new button% (label (list navigate-to-end-icon "End" 'right)) (parent navigator)
           (callback (lambda (b e) (navigate-to-end)))))

    (define nav:text
      (new text-field%
           (label "Step#")
           (init-value "00000")
           (parent extra-navigator)
           (stretchable-width #f)
           (stretchable-height #f)
           (callback
            (lambda (b e)
              (when (eq? (send e get-event-type) 'text-field-enter)
                (let* ([value (send b get-value)]
                       [step (string->number value)])
                  (cond [(exact-positive-integer? step)
                         (navigate-to (sub1 step))]
                        [(equal? value "end")
                         (navigate-to-end)])))))))

    (define nav:step-count
      (new message%
           (label "")
           (parent extra-navigator)
           (auto-resize #t)
           (stretchable-width #f)
           (stretchable-height #f)))
    (send nav:text set-value "")

    (listen-current-step-index
     (lambda (n)
       (send nav:text set-value
             (if (number? n) (number->string (add1 n)) ""))))

    ;; Navigation
    (define/public-final (navigate-to-start)
      (cursor:move-to-start steps)
      (update/preserve-lines-view))
    (define/public-final (navigate-to-end)
      (cursor:move-to-end steps)
      (update/preserve-lines-view))
    (define/public-final (navigate-previous)
      (cursor:move-prev steps)
      (update/preserve-lines-view))
    (define/public-final (navigate-next)
      (cursor:move-next steps)
      (update/preserve-lines-view))
    (define/public-final (navigate-to n)
      (cursor:skip-to steps n)
      (update/preserve-lines-view))

    ;; enable/disable-buttons : -> void
    (define/private (enable/disable-buttons [? #t])
      (send area enable ?)
      (cond [(send frame get-menu-bar)
             => (lambda (menu-bar) (send menu-bar enable ?))])
      (send nav:start enable (and ? (cursor:has-prev? steps)))
      (send nav:previous enable (and ? (cursor:has-prev? steps)))
      (send nav:next enable (and ? (cursor:has-next? steps)))
      (send nav:end enable (and ? (cursor:has-next? steps)))
      (send nav:text enable (and ? #t)))

    ;; Update

    ;; update/preserve-lines-view : -> void
    (define/public (update/preserve-lines-view)
      (begin
       (define start+end-lines (send stepview save-position))
       (update*)
       (send stepview restore-position start+end-lines)))

    ;; update : -> void
    ;; Updates the terms in the syntax browser to the current step
    (define/private (update)
      (begin
       (update*)))

    (define/private (update*)
      (send stepview erase-all)
      (let ([step (cursor:next steps)])
        (when step
          (send stepview show step)))
      (enable/disable-buttons #t)
      (set-current-step-index (cursor-position steps)))

    ;; --

    ;; refresh : -> void
    (define/public (refresh)
      (begin
       (let ([step-count (get-step-count)])
         (when step-count
           (send nav:step-count set-label (format "of ~s" step-count)))))
      (update/preserve-lines-view))

    ;; Initialization
    (super-new)))

;; ============================================================

(define step-view%
  (class object%
    (init-field parent widget)
    (super-new)

    (define text (new text%))
    (define canvas (new editor-canvas% (parent parent) (editor text)))

    (define/public (erase-all)
      (with-unlock text
        (send text erase)))

    (define/public (save-position)
      (define start-box (box 0))
      (define end-box (box 0))
      (send text get-visible-line-range start-box end-box)
      (cons (unbox start-box) (unbox end-box)))

    (define/public (restore-position start+end-lines)
      (send text scroll-to-position
            (send text line-start-position (car start+end-lines))
            #f
            (send text line-start-position (cdr start+end-lines))
            'start))

    ;; show : Step -> void
    (define/public (show s)
      (match s
        [(step type ctx old-expr old-extra new-expr new-extra)
         (show-state old-expr 'redex)
         (show-separator type)
         (show-state new-expr 'contractum)]))

    (define/private (show-state expr mode)
      (insert-syntax (expr->sexpr expr)
                     null ;; foci
                     mode))

    ;; show-separator : Step [...] -> void
    (define/private (show-separator type #:compact? [compact? #f])
      (add-text (if compact? "" "\n"))
      (add-text
       (make-object image-snip%
                    (collection-file-path "red-arrow.bmp" "icons")))
      (add-text "  [")
      (add-text type)
      (add-text "]\n\n"))

    ;; insert-syntax/redex
    (define/private (insert-syntax stx foci mode)
      (define foci-color
        (case mode
          [(redex) "MistyRose"]
          [(contractum) "LightCyan"]
          [else #f]))
      (insert-syntax/color stx foci foci-color))

    ;; insert-syntax/color
    (define/private (insert-syntax/color stx foci hi-color)
      (add-syntax stx
                  #:hi-colors (list hi-color)
                  #:hi-stxss (list foci)))

    ;; from syntax-browser/widget

    (define/public (add-text str)
      (with-unlock text
        (send text insert str)))

    ;; FIXME
    (define/public (add-syntax stx
                               #:hi-colors [hi-colors null]
                               #:hi-stxss [hi-stxss null])
      (define out (open-output-string))
      (pretty-write stx out)
      (add-text (get-output-string out)))

    #|
    (define/private (calculate-columns)
      (define style (code-style -text (send/i config config<%> get-syntax-font-size)))
      (define char-width (send style get-text-width (send -ecanvas get-dc)))
      (let ([admin (send -text get-admin)]
            [w-box (box 0.0)])
        (send admin get-view #f #f w-box #f)
        (sub1 (inexact->exact (floor (/ (unbox w-box) char-width))))))
    |#

    ))
