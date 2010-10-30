(require mzlib/defmacro)

(define (debug e)
  (print e)
  (print '=)
  (print (eval e))
  (newline))

;;------------------------------------------------------------------
;; http://okmij.org/ftp/Scheme/curry-fold.txt
(define-macro (lambda-curried bindings . body)
  (define (fold-right kons knil lis1)
    (let recur ((lis lis1))
       (if (null? lis) knil
	    (let ((head (car lis)))
	      (kons head (recur (cdr lis)))))))
  (if (null? bindings) `(lambda () ,@body)
    (fold-right (lambda (arg curr-body) `(lambda (,arg) ,curr-body))
	 (cons 'begin body) bindings)))

(define (fold kons knil lis1)
  (let lp ((lis lis1) (ans knil))
    (if (null? lis) ans
      (lp (cdr lis) (kons (car lis) ans)))))

(define (rev-apply-1 arg f) (f arg))

(define (uncurry f . arglist)
  (fold rev-apply-1 f arglist))
;;------------------------------------------------------------------
;; deep uncurry

;; uncurry every funcall in an expression and curry every lambda
;; curry prefix deactivates this for a single funcall,
;; deep-curry for the whole sub-expression
;; remember to prefix every special form (e.g. if) with curry
(define-macro (deep-uncurry e)
  (letrec ((aux (lambda (x)
                  (cond ((not (list? x)) x)
                        ((= (length x) 0) x)
                        ((= (length x) 1) (list (aux (car x))))
                        ((or (equal? (car x) 'lambda)
                             (equal? (car x) 'lambda-curried))
                         (append (list 'lambda-curried (cadr x)) (map aux (cddr x)))) ;; skip lambda and bindings
                        ((equal? (car x) 'curry) (cons (cadr x) (map aux (cddr x))))  ;; skip uncurry but recurse
                        ((equal? (car x) 'cataBool) (cons (car x) (map aux (cdr x)))) ;; skip the only lazy construct
                        ((equal? (car x) 'deep-curry) (cdr x))                        ;; skip uncurry in this subexpr
                        ((equal? (car x) 'quote) x)                                   ;; don't touch quoted stuff
                        (#t (cons 'uncurry (map aux x)))))))
    (list 'eval (aux e))))

;; define with implicit deep-uncurry for the whole body
(define-macro (define-curry sig . body)
  `(define ,sig (deep-uncurry ,(cons 'curry (cons 'begin body))))) ;; curry the begin
;;------------------------------------------------------------------
;; utils
(define id
  (lambda (x) x))

(define-curry const
  (lambda (a b)
    a))

(define (foldr f z l)
  (if (null? l)
      z
      (f (car l) (foldr f z (cdr l)))))
;;------------------------------------------------------------------
;; strict booleans
;; (define-curry cataBool
;;   (lambda (f g b)
;;     (b f g)))

;; (define-curry tru
;;   (lambda (f g)
;;     f))

;; (define-curry fals
;;   (lambda (f g)
;;     g))

;; (define (reifyBool b)
;;   (uncurry b #t #f))

;; (define (reflectBool b)
;;   (if b
;;       tru
;;       fals))
;;------------------------------------------------------------------
;; lazy booleans
(define-macro (cataBool f g b)
  `(uncurry ,b (lambda () ,f) (lambda () ,g)))

(define-curry tru
  (lambda (f g)
    (f)))

(define-curry fals
  (lambda (f g)
    (g)))
;;------------------------------------------------------------------
;; pairs
(define-curry cataPair
  (lambda (f x)
    (x f)))

(define-curry pair
  (lambda (x y p)
    (p x y)))

(define-curry first
  (cataPair (lambda (x y) x)))

(define-curry second
  (cataPair (lambda (x y) y)))

(define (reifyPair p)
  (uncurry p (lambda-curried (a b) (cons a b))))

(define (reflectPair a b)
  (uncurry pair a b))
;;------------------------------------------------------------------
;; nats
(define-curry cataNat
  (lambda (s z n)
    (n s z)))

(define-curry zero
  (lambda (s z)
    z))

(define-curry succ
  (lambda (n s z)
    (s (cataNat s z n))))

(define (reifyNat n)
  (uncurry n (lambda (n) (+ 1 n)) 0))

(define (reflectNat n)
  (if (= n 0)
      zero
      (uncurry succ (reflectNat (- n 1)))))

(define-curry paraNat
  (lambda (f z n)
    (first (cataNat (lambda (y)
                      (pair (f (second y) (first y)) (succ (second y))))
                    (pair z zero)
                    n))))

(define-curry pred
  (paraNat (lambda (n k) n) zero))

;; (define hyloNat
;;   (lambda-curried (f g s p a)
;;     (uncurry cataBool (f (uncurry hyloNat f g s p (s a))) g (p a))))

;; (define anaNat
;;   (lambda-curried (n s p)
;;     (uncurry hyloNat succ zero s p n)))

(define-curry add
  (cataNat (lambda (g x)
             (succ (g x)))
           id))

(define-curry mul
  (cataNat (lambda (x b)
             (add b (x b)))
           (const zero)))

(debug '(reifyNat (uncurry add (pred (reflectNat 10)) (reflectNat 80))))
;;------------------------------------------------------------------
;; maybe
(define-curry cataMaybe
  (lambda (f z x)
    (x f z)))

(define-curry nothing
  (lambda (f z)
    z))

(define-curry just
  (lambda (x f z)
    (f x)))

(define (reflectMaybe x)
  (if (equal? x 'nothing)
      nothing
      (just x)))

(define (reifyMaybe x)
  (uncurry x id 'nothing))
;;------------------------------------------------------------------
;; lists
(define-curry cataList
  (lambda (f z l)
    (l f z)))

(define-curry nil
  (lambda (f z)
    z))

(define-curry kons
  (lambda (x xs f z)
    (f x (cataList f z xs))))

(define-curry paraList
  (lambda (f z l)
    (first (cataList (lambda (x ys)
                       (pair (f x (second ys) (first ys)) (kons x (second ys))))
                     (pair z nil)
                     l))))

;; (define hyloList
;;   (lambda-curried (f g s p a)
;;     (uncurry cataBool (f (uncurry hyloList f g s p (s a))) g (p a))))


(define-curry anaList
  (lambda (s p x)
    (cataBool (kons (first (s x)) (anaList s p (second (s x)))) nil (p x))))

(define-curry head
  (cataList const 'undefined))

(define (reifyList l)
  (uncurry l (lambda-curried (x xs) (cons x xs)) '()))

(define (reifyNatList l)
  (map reifyNat (reifyList l)))

(define (reflectList . args)
  (foldr (lambda (x xs) (uncurry kons x xs)) nil args))

(define-curry tail
  (paraList (lambda (x xs ys) xs) 'undefined))

(debug '(head (tail (reflectList 1 2 3))))

(define-curry destruct_count_p
  (cataNat (const tru) fals))

(define-curry destruct_count_s
  (paraNat (lambda (k ks)
             (pair (succ k) k))
           'undefined))

(define-curry count
  (anaList destruct_count_s destruct_count_p))

(debug '(reifyNatList (count (reflectNat 10))))
