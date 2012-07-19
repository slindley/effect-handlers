;; Effect handlers in Racket
;;
;; By Ohad Kammar, Sam Lindley and Nicolas Oury
;;
;; See the draft paper:
;;
;;   http://homepages.inf.ed.ac.uk/slindley/papers/handlers.pdf
;;
;; for further details.

#lang racket

(define request-parameter-symbol (gensym 'request-parameter))
(define (parameter-requested? l)
  (and (not (empty? l)) (eq? (car l) request-parameter-symbol)))

;; operation names are useful for debugging code written using
;; the macros
(define (with-name name)
   (lambda l (error  (string-append "unhandled effect: " name))))

;; declare an operation
(define (operation [default (with-name "unnamed effect")])
  (let ([p (make-parameter default)])
    (lambda l  
      (if (parameter-requested? l) p (apply (p) l)))))

;; The code in the paper doesn't include operation names
;;
;; (define (operation
;;            [default (lambda l (error "unhandled operation"))])
;;   (let ([p (make-parameter default)]) 
;;     (lambda l (if  (parameter-requested? l) 
;;                    p 
;;                    (apply (p) l)))))

;; 
(define (parameter-for-operation operation) 
  (operation request-parameter-symbol))

;; a clause that only calls its continuation in tail position
(define (local-clause f)
  (lambda (prompt) f))

;; a clause that does not call its continuation
(define (escape-clause f)
  (lambda (prompt)
    (lambda l 
      (abort-current-continuation prompt (lambda () (apply f l))))))

;; a clause that can call its continuation arbitrarily
(define (full-clause f)
  (lambda (prompt)
    (lambda l 
      (call-with-composable-continuation 
       (lambda (k) 
         (abort-current-continuation 
          prompt  (lambda () (apply f 
                                    (lambda (x) 
                                      (install-prompt prompt (lambda () (k x)))) l)))) prompt))))

(define (install-prompt prompt computation)
  (call-with-continuation-prompt 
   (lambda () (computation)) prompt 
   (lambda (clause-thunk) (clause-thunk))))

;; 'handlerS' rather than 'handler' to avoid a clash with the macro
(struct handlerS (prompt return clauses))
(struct clause (operation function))
(define (make-handler return . clauses)
  (let ((prompt (make-continuation-prompt-tag)))
    (handlerS prompt return 
              (map (lambda (c) 
                     (clause (clause-operation c) ((clause-function c) prompt))) 
                   clauses))))

(define (install-clause clause)
  (lambda (computation)
    (lambda ()
      (parameterize ([(parameter-for-operation (clause-operation clause)) (clause-function clause)])
                   (computation)))))
  
(define (install-clauses clauses computation)
    (((foldr compose (lambda (x) x) (map install-clause clauses)) 
      computation)))

;; 'do-handle' to avoid a clash with the macro 'handle'
(define (do-handle computation handler)
  (install-prompt (handlerS-prompt handler)
   (lambda () 
     ((handlerS-return handler) (install-clauses (handlerS-clauses handler) computation)))))
 
(define (extend-handler handler cl)
  (handlerS (handlerS-prompt handler) 
            (handlerS-return handler) 
            (cons (clause (clause-operation cl) ((clause-function cl) (handlerS-prompt handler))) 
                  (handlerS-clauses handler))))

;; Macros

;; handlers
(define-syntax handler
  (syntax-rules (locally return)    
    [(handler [(return x) body ...])  (make-handler (lambda (x) body ...))]
    [(handler)  (make-handler (lambda (x) x))]
    [(handler [(op args ...) body ...] clauses ...)  
     (extend-handler 
      (handler clauses ...)
      (clause op (full-clause (lambda (args ...) body ...))))]
    [(handler [locally (op args ...) body ...] clauses ...)
     (extend-handler 
      (handler clauses ...)
      (clause op (local-clause (lambda (args ...) body ...))))]
     [(handler [escape (op args ...) body ...] clauses ...)
     (extend-handler 
      (handler clauses ...)
      (clause op (escape-clause (lambda (args ...) body ...))))]
    ))

;; handled ... with ...
(define-syntax handle
  (syntax-rules (with)
    [(handle body ... with handler)
     (do-handle (lambda () 
                  body ...) handler)]))

;; operations
(define-syntax-rule (define-operation e)
  (define e (operation (with-name (symbol->string 'e)))))

(define-syntax-rule (handle-with h body ...)
  (handle body ... with h))

(define-syntax-rule (define-handler l body ...)
  (define l (handler body ...)))
