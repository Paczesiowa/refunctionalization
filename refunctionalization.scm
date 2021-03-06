#!/usr/bin/mzscheme -f
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
;; scheme utils
(define (foldr f z l)
  (if (null? l)
      z
      (f (car l) (foldr f z (cdr l)))))
;;------------------------------------------------------------------
;; lambda utils
(define-curry id
  (lambda (x) x))

(define-curry const
  (lambda (a b)
    a))

;; TODO this is not lambda term, use fixpoint
(define-curry undefined
  (lambda (x)
    undefined))

(define-curry combine
  (lambda (f g x)
    (f (g x))))
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

;; definition
(define-macro (cataBool f g b)
  `(uncurry ,b (lambda () ,f) (lambda () ,g)))

(define-curry tru
  (lambda (f g)
    (f)))

(define-curry fals
  (lambda (f g)
    (g)))

;; projections
(define (reifyBool b)
  (cataBool #t #f b))

;; functions
(define-curry not
  (lambda (x)
    (cataBool fals tru x)))
;;------------------------------------------------------------------
;; pairs

;; definition
(define-curry cataPair
  (lambda (f x)
    (x f)))

(define-curry pair
  (lambda (x y p)
    (p x y)))

;; projections
(define (reifyPair p)
  (uncurry p (lambda-curried (a b) (cons a b))))

(define (reflectPair a b)
  (uncurry pair a b))

;; functions
(define-curry first
  (cataPair (lambda (x y) x)))

(define-curry second
  (cataPair (lambda (x y) y)))

(define-curry ><
  (lambda (f g p)
    (pair (f (first p))
             (g (second p)))))
;;------------------------------------------------------------------
;; nats

;; definition
(define-curry cataNat
  (lambda (s z n)
    (n s z)))

(define-curry zero
  (lambda (s z)
    z))

(define-curry succ
  (lambda (n s z)
    (s (cataNat s z n))))

;; projections
(define (reifyNat n)
  (uncurry n (lambda (n) (+ 1 n)) 0))

(define (reflectNat n)
  (if (= n 0)
      zero
      (uncurry succ (reflectNat (- n 1)))))

;; morphisms
(define-curry paraNat
  (lambda (f z n)
    (first (cataNat (lambda (y)
                      (pair (f (second y) (first y)) (succ (second y))))
                    (pair z zero)
                    n))))

;; functions
(define-curry pred
  (paraNat (lambda (n k) n) zero))

(define-curry add
  (cataNat (lambda (g x)
             (succ (g x)))
           id))

(define-curry mul
  (cataNat (lambda (x b)
             (add b (x b)))
           (const zero)))

(define-curry isZero
  (cataNat (const fals) tru))

(define-curry lt
  (paraNat (lambda (x w)
	     (paraNat (lambda (y u)
			(w y))
		      fals))
	   (const tru)))

;; tests
;; (debug '(reifyNat (uncurry add (pred (reflectNat 10)) (reflectNat 80))))
;; (debug '(reifyBool (uncurry lt (reflectNat 10) (reflectNat 11))))
;;------------------------------------------------------------------
;; maybe

;; definition
(define-curry cataMaybe
  (lambda (f z x)
    (x f z)))

(define-curry nothing
  (lambda (f z)
    z))

(define-curry just
  (lambda (x f z)
    (f x)))

;; projections
(define (reflectMaybe x)
  (if (equal? x 'nothing)
      nothing
      (just x)))

(define (reifyMaybe x)
  (uncurry x id 'nothing))
;;------------------------------------------------------------------
;; lists

;; definition
(define-curry cataList
  (lambda (f z l)
    (l f z)))

(define-curry nil
  (lambda (f z)
    z))

(define-curry kons
  (lambda (x xs f z)
    (f x (cataList f z xs))))

;; projections
(define (reifyList l)
  (uncurry l (lambda-curried (x xs) (cons x xs)) '()))

(define (reifyNatList l)
  (map reifyNat (reifyList l)))

(define (reifyPairNatLists p)
  (uncurry cataPair (lambda-curried (a b)
		      (cons (reifyNatList a) (reifyNatList b)))
	            p))

(define (reflectList . args)
  (foldr (lambda (x xs) (uncurry kons x xs)) nil args))

(define (reflectNatList . args)
  (eval (cons 'reflectList (map reflectNat args))))

;; morphisms
(define-curry paraList
  (lambda (f z l)
    (first (cataList (lambda (x ys)
                       (pair (f x (second ys) (first ys)) (kons x (second ys))))
                     (pair z nil)
                     l))))

(define-curry hyloList
  (lambda (f g s p a)
    (cataBool (f (>< id (hyloList f g s p) (s a)))
              g
              (p a))))

(define-curry anaList
  (hyloList (lambda (p)
              (kons (first p) (second p)))
            nil))

;; functions
(define-curry head
  (cataList const undefined))

(define-curry tail
  (paraList (lambda (x xs ys) xs) undefined))

(define-curry ++
  (lambda (xs ys)
    (cataList kons ys xs)))

(define-curry countDownFrom
  (anaList (paraNat (lambda (k ks)
		      (pair (succ k) k))
		    undefined)
	   (combine not isZero)))

(define-curry partitionR
  (lambda (p)
    (cataList (lambda (x ys)
		(cataBool (pair (kons x (first ys)) (second ys))
			  (pair (first ys) (kons x (second ys)))
			  (p x)))
	      (pair nil nil))))

(define-curry nullR
  (cataList (lambda (x ys) fals) tru))

;; tests
;; (debug '(head (tail (reflectList 1 2 3))))
;; (debug '(reifyNatList (countDownFrom (reflectNat 10))))
;; (debug '(reifyList (uncurry ++ (reflectList 1 2 3) (reflectList 4 5 6))))
;; (debug '(reifyPairNatLists (uncurry partitionR (lambda (x) (uncurry lt x (reflectNat 3)))
;; 				               (reflectNatList 5 1 2 6 5 0 5 6))))
;;------------------------------------------------------------------
;; trees

;; definition
(define-curry cataTree
  (lambda (f z l)
    (l f z)))

(define-curry leaf
  (lambda (f z)
    z))

(define-curry node
  (lambda (x l r f z)
    (f x (cataTree f z l) (cataTree f z r))))

;; morphisms
(define-curry hyloTree
  (lambda (f g s p a)
    (cataBool (f (>< id (>< (hyloTree f g s p) (hyloTree f g s p)) (s a)))
              g
              (p a))))

;;------------------------------------------------------------------
;; treeSort
(define-curry part
  (paraList (lambda (x xs ys)
	      (pair x (partitionR (lambda (y) (lt y x))
				  xs)))
	    undefined))

(define-curry flatten
  (lambda (p)
    (++ (first (second p)) (kons (first p) (second (second p))))))

(define-curry treeSort
  (hyloTree flatten nil part (combine not nullR)))

;; (debug '(reifyNatList (treeSort (reflectNatList 2 4 1 5 3))))
;;------------------------------------------------------------------
;; para-histomorphisms

;; pairPH must be 'curry'-ied inside define-curry because it's a macro
;; and macros are lazy
(define-macro (pairPH x y)
  (let ((p (gensym)))
    `(lambda (,p) (uncurry ,p (lambda () ,x) (lambda () ,y)))))

(define-curry cataPairPH
  (lambda (f x)
    (x f)))

(define-curry fstPH
  (cataPairPH (lambda (x y)
		(x))))

(define-curry sndPH
  (cataPairPH (lambda (x y)
		(y))))

(debug '(sndPH (pairPH 1 2)))

(define-curry natPH
  (lambda (z s n)
    (n z s)))

(define-curry zeroPH
  (lambda (z s)
    (curry pairPH z 'undefined)))

(define-curry succPH
  (lambda (n z s)
    ((lambda (h) (curry pairPH (s n h) h)) (natPH z s n))))

;; projections
(define (reifyNatPH n)
  (fstPH (uncurry n 0 (lambda-curried (m h) (+ 1 (fstPH h))))))

(define (reflectNatPH n)
  (if (= n 0)
      zeroPH
      (uncurry succPH (reflectNatPH (- n 1)))))

(debug '(reifyNatPH (reflectNatPH 0)))
(debug '(reifyNatPH (reflectNatPH 10)))

(define-curry listPH
  (lambda (n c l)
    (l n c)))

(define-curry nilPH
  (lambda (n c)
    (curry pairPH n 'undefined)))

(define-curry consPH
  (lambda (x xs n c)
    ((lambda (h) (curry pairPH (uncurry c x xs h) h))
     (uncurry listPH n c xs))))

;; projections
(define (reifyListPH l)
  (fstPH (uncurry l '() (lambda-curried (x xs h) (cons x (fstPH h))))))

(define (reifyNatListPH l)
  (map reifyNatPH (reifyListPH l)))

(define (reflectListPH . args)
  (foldr (lambda (x xs) (uncurry consPH x xs)) nilPH args))

(define (reflectNatListPH . args)
  (eval (cons 'reflectListPH (map reflectNatPH args))))

(debug '(reifyListPH (reflectListPH 1 2 3 4)))
(debug '(reifyListPH (reflectListPH )))
(debug '(reifyListPH nilPH))
(debug '(reifyListPH (uncurry consPH 1 nilPH)))
(debug '(reifyListPH (uncurry consPH 1 (uncurry consPH 2 (uncurry consPH 3 nilPH)))))
;; (define (reflectNatPH n)
;;   (if (= n 0)
;;       zeroPH
;;       (uncurry succPH (reflectNatPH (- n 1)))))


(define-curry isZeroPH
  (lambda (n)
    (fstPH (natPH tru (lambda (m h) fals ) n))))

(debug '(reifyBool (isZeroPH (reflectNatPH 0))))
(debug '(reifyBool (isZeroPH (reflectNatPH 10))))

(define-curry isOnePH
  (combine fstPH (natPH fals (lambda (m h) (isZeroPH m)))))

(debug '(reifyBool (isOnePH (reflectNatPH 0))))
(debug '(reifyBool (isOnePH (reflectNatPH 1))))
(debug '(reifyBool (isOnePH (reflectNatPH 10))))

(define-curry onePH
  (succPH zeroPH))

(debug '(reifyNatPH onePH))

(define-curry cataPH
  (lambda (z s n)
    (fstPH (natPH z (lambda (m h) (s (fstPH h))) n))))

(define-curry paraPH
  (lambda (z s n)
    (fstPH (natPH z (lambda (m h) (s m (fstPH h))) n))))

(define-curry plusPH
  (cataPH id (lambda (g x)
                (succPH (g x)))))

(debug '(reifyNatPH (uncurry plusPH (reflectNatPH 3) (reflectNatPH 4))))

(define-curry fibPH
  (lambda (n)
    (fstPH (natPH onePH
           (lambda-curried (m  h)
             (cataBool onePH (plusPH (fstPH h) (fstPH (sndPH h))) (isZeroPH m) ))
           n))))

(debug '(reifyNatPH (fibPH (reflectNatPH 0))))
(debug '(reifyNatPH (fibPH (reflectNatPH 1))))
(debug '(reifyNatPH (fibPH (reflectNatPH 2))))
(debug '(reifyNatPH (fibPH (reflectNatPH 5))))
(debug '(reifyNatPH (fibPH (reflectNatPH 11))))

(define-curry ltPH
  (paraPH (const tru)
	  (lambda (x w)
	    (paraPH fals
		    (lambda (y u)
		      (w y))))))


(debug '(reifyBool (uncurry ltPH (reflectNatPH 0) (reflectNatPH 0))))
(debug '(reifyBool (uncurry ltPH (reflectNatPH 0) (reflectNatPH 1))))
(debug '(reifyBool (uncurry ltPH (reflectNatPH 1) (reflectNatPH 0))))
(debug '(reifyBool (uncurry ltPH (reflectNatPH 2) (reflectNatPH 2))))

;; TODO
;; zamienic fstPH na lambda + combine

(define-curry singletonPH
  (lambda (x)
    (consPH x nilPH)))

(define-curry insertPH
  (lambda (x)
    (combine fstPH
	     (listPH (singletonPH x)
		     (lambda (y ys h)
		       (cataBool (consPH x (consPH y ys))
				 (consPH y (fstPH h))
				 (ltPH x y)))))))

(debug '(reifyNatListPH (uncurry insertPH (reflectNatPH 1) (reflectNatListPH 0 2))))

(define-curry insertSortPH
  (combine fstPH
	   (listPH nilPH (lambda (x xs h)
			   (insertPH x (fstPH h))))))

(debug '(reifyNatListPH (insertSortPH (reflectNatListPH))))
(debug '(reifyNatListPH (insertSortPH (reflectNatListPH 1))))
(debug '(reifyNatListPH (insertSortPH (reflectNatListPH 1 2))))
(debug '(reifyNatListPH (insertSortPH (reflectNatListPH 2 3 1))))
(debug '(reifyNatListPH (insertSortPH (reflectNatListPH 2 4 1 5 3))))

(define-curry nthPH
  (cataPH fstPH
	  (lambda (x)
	    (combine x sndPH))))

(debug '(uncurry nthPH (reflectNatPH 0) (pairPH 1 (pairPH 2 (pairPH 3 4)))))
(debug '(uncurry nthPH (reflectNatPH 2) (pairPH 1 (pairPH 2 (pairPH 3 4)))))


(define-curry multPH
  (cataPH (const zeroPH)
	  (lambda (x b)
	    (plusPH b (x b)))))

(debug '(reifyNatPH (uncurry multPH (reflectNatPH 3) (reflectNatPH 3))))

(define-curry predPH
  (paraPH zeroPH
	  (lambda (m h) m)))

(debug '(reifyNatPH (predPH (reflectNatPH 0))))
(debug '(reifyNatPH (predPH (reflectNatPH 10))))

(define-curry minusPH2
  (cataPH id (lambda (g x)
                (predPH (g x)))))

(define-curry minusPH
  (lambda (x y)
    (minusPH2 y x)))

(debug '(reifyNatPH (uncurry minusPH (reflectNatPH 3) (reflectNatPH 4))))
(debug '(reifyNatPH (uncurry minusPH (reflectNatPH 6) (reflectNatPH 4))))

(define-curry fooPH
  (lambda (m h)
    (paraPH (nthPH m h)
	    (lambda (i c)
	      (plusPH (multPH (nthPH i h)
			      (nthPH (minusPH m i) h))
		      c))
	    m)))

(define (appendHistory h1 h2)
  (if (equal? h1 'undefined)
      h2
      (pairPH (fstPH h1) (appendHistory (sndPH h1) h2))))

(define (reverseHistoryPH h)
  (if (equal? h 'undefined)
      'undefined
      (appendHistory (reverseHistoryPH (sndPH h))
		     (pairPH (fstPH h)
			     'undefined))))

(define (zipMult h1 h2)
  (if (equal? h1 'undefined)
      'undefined
      (pairPH (uncurry multPH (fstPH h1)
		              (fstPH h2))
	      (zipMult (sndPH h1)
		       (sndPH h2)))))

(define (sumPH h)
  (if (equal? h 'undefined)
      zeroPH
      (uncurry plusPH (fstPH h)
	              (sumPH (sndPH h)))))

(define (reifyNatHistory h)
  (if (equal? h 'undefined)
      '()
      (cons (reifyNatPH (fstPH h)) (reifyNatHistory (sndPH h)))))

(define-curry catalanPH
  (combine fstPH
	   (natPH onePH (lambda (m h)
			  (sumPH (curry zipMult h (reverseHistoryPH h)))))))

;; (define-macro (debug2 n)
;;   `(begin
;;      (print ,n)
;;      (print '=)
;;      (print (eval n))
;;      (newline)))


;; (define-curry baz
;;   (lambda (n)
;;     (cataNat (lambda (n)
;; 	       (curry debug n)
;; 	       (curry + 1 n))
;;  	     0
;; 	     n)))

;; (baz (reflectNat 5))

(debug '(reifyNatPH (catalanPH (reflectNatPH 0))))
(debug '(reifyNatPH (catalanPH (reflectNatPH 1))))
(debug '(reifyNatPH (catalanPH (reflectNatPH 10))))

(define-curry barPH
  (lambda (m n h)
    (multPH (nthPH m h)
	    (nthPH (minusPH n m)))))

(define h18
  (pairPH (reflectNatPH 1) (pairPH (reflectNatPH 1) (pairPH (reflectNatPH 2) (pairPH (reflectNatPH 5) (pairPH (reflectNatPH 14) 'undefined))))))

(debug '(reifyNatHistory h18))
(debug '(reifyNatHistory (reverseHistoryPH h18)))
(debug '(reifyNatPH (sumPH (zipMult h18 (reverseHistoryPH h18)))))


;; (debug '(reifyNatPH (uncurry fooPH (reflectNatPH 3) h18)))
;; (debug '(reifyNatPH (uncurry barPH (reflectNatPH 0)(reflectNatPH 1) h18)))
;; (debug '(reifyNatPH (uncurry nthPH (uncurry minusPH (reflectNatPH 2) (reflectNatPH 0)) h18)))
