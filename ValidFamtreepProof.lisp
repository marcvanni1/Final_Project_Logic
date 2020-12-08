(defdata person (cons symbol nat))
(defdata famTree (oneof person (list famTree person famTree)))

(personp '(Jason . 1985))  
(famTreep '(Jason . 1985))
(famTreep '((Tammy . 1969) (Jason . 1985) (Alan . 1968)))
(famTreep '((Tammy . 1969) (Jason . 1985) ((Glenn . 1930) (Alan . 1968) (Liz . 1932))))

;; getRootYear: famTree -> int
;;
(definec getRootYear (a :famTree) :nat
  (cond
   ((personp ft) (rest ft))
   ((famTreep ft) (rest (second ft)))))

;; validFamTreep: famTree -> bool
;; Return true if the given famTree is a valid famTree
(definec validFamTreep (ft :famTree) :bool
  (cond
   ((personp ft) t)
   ((famtreep ft) (and (validFamTreep (first ft))
                       (validFamTreep (third ft))
                       (< (getRootYear (first ft)) (rest (second ft)))
                       (< (getRootYear (third ft)) (rest (second ft)))))))

;; Proof:
(defthm project2 (implies (and (validFamTreep a) 
                               (validFamTreep b) 
                               (natp YoB)
                               (symbolp name))
                          (implies (and (< (getRootYear a) YoB)
                                        (< (getRootYear b) YoB))
                                   (validFamTreep (list a (cons name YoB) b)))))

;; Proof obligations
;; Contract Case
(implies (and (not (validFamTreep a))
              (not (validFamTreep b)) 
              (not (natp YoB))
              (not (symbolp name)))
         (implies (and (validFamTreep a) 
                       (validFamTreep b) 
                       (natp YoB)
                       (symbolp name))
                  (implies (and (< (getRootYear a) YoB)
                                (< (getRootYear b) YoB))
                           (validFamTreep (list a (cons name YoB) b)))))

;; Base Case
(implies (and (validFamTreep a) 
              (validFamTreep b)
              (person a)
              (person b)
              (natp YoB)
              (symbolp name))
         (implies (and (< (getRootYear a) YoB)
                       (< (getRootYear b) YoB))
                  (validFamTreep (list a (cons name YoB) b))))

;; Inductive Case
(implies (and (validFamTreep a) 
              (validFamTreep b)
              (not (personp a))
              (not (personp b))
              (natp YoB)
              (symbolp name)
              (implies
               (and 
                (< (getRootYear (first a)) YoB)
                (< (getRootYear (third a)) YoB))
                (validFamTreep (list (first a) (cons name YoB) (third a))))
			  (implies
               (and 
                (< (getRootYear (first b)) YoB)
                (< (getRootYear (third b)) YoB))
                (validFamTreep (list (first b) (cons name YoB) (third b)))))
         (implies (and (< (getRootYear a) YoB)
                       (< (getRootYear b) YoB))
                  (validFamTreep (list a (cons name YoB) b))))


;;Proof Contract Case:
Problem 1a:
(implies (and (not (validFamTreep a))
              (not (validFamTreep b)) 
              (not (natp YoB))
              (not (symbolp name)))
         (implies (and (validFamTreep a) 
                       (validFamTreep b) 
                       (natp YoB)
                       (symbolp name))
                  (implies (and (< (getRootYear a) YoB)
                                (< (getRootYear b) YoB))
                           (validFamTreep (list a (cons name YoB) b)))))

Exportation:
(implies (and (not (validFamTreep a))
              (not (validFamTreep b)) 
              (not (natp YoB))
              (not (symbolp name))
              (validFamTreep a) 
              (validFamTreep b) 
              (natp YoB)
              (symbolp name)
              (< (getRootYear a) YoB)
              (< (getRootYear b) YoB))
         (validFamTreep (list a (cons name YoB) b)))

Context:
C1. (not (validFamTreep a))
C2. (not (validFamTreep b)) 
C3. (not (natp YoB))
C4. (not (symbolp name))
C5. (validFamTreep a) 
C6. (validFamTreep b) 
C7. (natp YoB)
C8. (symbolp name)
C9. (< (getRootYear a) YoB)
C10. (< (getRootYear b) YoB)

Derived Context:
D1. nil { C1, C2, C3, C4, C5, C6, C7, C8 }

QED

;; Proof Base Case
Problem 1b:
(implies (and (validFamTreep a) 
              (validFamTreep b)
              (personp a)
              (personp b)
              (natp YoB)
              (symbolp name))
         (implies (and (< (getRootYear a) YoB)
                       (< (getRootYear b) YoB))
                  (validFamTreep (list a (cons name YoB) b))))

Exportation:
(implies (and (validFamTreep a) 
              (validFamTreep b)
              (personp a)
              (personp b)
              (natp YoB)
              (symbolp name)
              (< (getRootYear a) YoB)
              (< (getRootYear b) YoB))
         (validFamTreep (list a (cons name YoB) b)))

Context:
C1. (validFamTreep a) 
C2. (validFamTreep b)
C3. (personp a)
C4. (personp b)
C5. (natp YoB)
C6. (symbolp name)
C7. (< (getRootYear a) YoB)
C8. (< (getRootYear b) YoB)

Derived Context:
D1. (personp (cons name YoB)) { Def person }
D2. (famtreep (list a (cons name YoB) b)) { Def famtree }

Goal:
(validFamTreep (list a (cons name YoB) b))

Proof:
(validFamTreep (list a (cons name YoB) b))
= { Def validFamTreep }
(cond
 ((personp (list a (cons name YoB) b)) t)
 ((famtreep (list a (cons name YoB) b)) 
  (and 
   (validFamTreep (first (list a (cons name YoB) b)))
   (validFamTreep (third (list a (cons name YoB) b)))
   (< (getRootYear (first (list a (cons name YoB) b))) 
      (rest (second (list a (cons name YoB) b))))
   (< (getRootYear (third (list a (cons name YoB) b))) 
      (rest (second (list a (cons name YoB) b)))))))
= { if axioms, D2 }
(and 
   (validFamTreep (first (list a (cons name YoB) b)))
   (validFamTreep (third (list a (cons name YoB) b)))
   (< (getRootYear (first (list a (cons name YoB) b))) 
      (rest (second (list a (cons name YoB) b))))
   (< (getRootYear (third (list a (cons name YoB) b))) 
      (rest (second (list a (cons name YoB) b)))))
= { car-cdr axioms }
(and 
   (validFamTreep a)
   (validFamTreep b)
   (< (getRootYear a) YoB)
   (< (getRootYear b) YoB))
= { Def validFamTreep }
(and
 (cond
  ((personp a) t)
  ((famtreep a) (and (validFamTreep (first a))
                     (validFamTreep (third a))
                     (< (getRootYear (first a)) (rest (second a)))
                     (< (getRootYear (third a)) (rest (second a))))))
 (cond
  ((personp b) t)
  ((famtreep b) (and (validFamTreep (first b))
                     (validFamTreep (third b))
                     (< (getRootYear (first b)) (rest (second b)))
                     (< (getRootYear (third b)) (rest (second b))))))
 (< (getRootYear a) YoB)
 (< (getRootYear b) YoB))
= { if axioms, C3, C4 }
(and 
 t
 t
 (< (getRootYear a) YoB)
 (< (getRootYear b) YoB))
= { C7, C8 }
(and 
 t
 t
 t
 t)
= { MP, arith }
t

QED

;; Proof Inductive Case
Problem 1c:
(implies (and (validFamTreep a) 
              (validFamTreep b)
              (not (personp a))
              (not (personp b))
              (natp YoB)
              (symbolp name)
              (implies
               (and 
                (< (getRootYear (first a)) YoB)
                (< (getRootYear (third a)) YoB))
                (validFamTreep (list (first a) (cons name YoB) (third a))))
			  (implies
               (and 
                (< (getRootYear (first b)) YoB)
                (< (getRootYear (third b)) YoB))
                (validFamTreep (list (first b) (cons name YoB) (third b)))))
         (implies (and (< (getRootYear a) YoB)
                       (< (getRootYear b) YoB))
                  (validFamTreep (list a (cons name YoB) b))))

Exportation:
(implies (and (validFamTreep a) 
              (validFamTreep b)
              (not (personp a))
              (not (personp b))
              (natp YoB)
              (symbolp name)
              (implies
               (and 
                (< (getRootYear (first a)) YoB)
                (< (getRootYear (third a)) YoB))
                (validFamTreep (list (first a) (cons name YoB) (third a))))
			  (implies
               (and 
                (< (getRootYear (first b)) YoB)
                (< (getRootYear (third b)) YoB))
                (validFamTreep (list (first b) (cons name YoB) (third b))))
              (< (getRootYear a) YoB)
              (< (getRootYear b) YoB))
         (validFamTreep (list a (cons name YoB) b)))

Context:
C1. (validFamTreep a) 
C2. (validFamTreep b)
C3. (not (personp a))
C4. (not (personp b))
C5. (natp YoB)
C6. (symbolp name)
C7. (implies
		(and 
		(< (getRootYear (first a)) YoB)
        (< (getRootYear (third a)) YoB))
        (validFamTreep (list (first a) (cons name YoB) (third a))))
C8. (implies
		(and 
        (< (getRootYear (first b)) YoB)
        (< (getRootYear (third b)) YoB))
        (validFamTreep (list (first b) (cons name YoB) (third b))))
C9. (< (getRootYear a) YoB)
C10. (< (getRootYear b) YoB)

Derived Context:
D1. (personp (cons name YoB)) { Def person }
D2. (famtreep (list a (cons name YoB) b)) { Def famtree }
D3. (famtreep (first a)) { C3, Def famtree }
D4. (famtreep (third a)) { C3, Def famtree }
D5. (famtreep (first b)) { C3, Def famtree }
D6. (famtreep (third b)) { C3, Def famtree }
D7. (and 
		(validFamTreep (first a))
		(validFamTreep (third a))) { Lemma Validfamtreep-first-third, C1 }
D8. (and 
		(validFamTreep (first b))
		(validFamTreep (third b))) { Lemma Validfamtreep-first-third, C2 }

Goal:
(validFamTreep (list a (cons name YoB) b))

Proof:
(validFamTreep (list a (cons name YoB) b))
= { Def validFamTreep }
(cond
 ((personp (list a (cons name YoB) b)) t)
 ((famtreep (list a (cons name YoB) b)) 
  (and 
   (validFamTreep (first (list a (cons name YoB) b)))
   (validFamTreep (third (list a (cons name YoB) b)))
   (< (getRootYear (first (list a (cons name YoB) b))) 
      (rest (second (list a (cons name YoB) b))))
   (< (getRootYear (third (list a (cons name YoB) b))) 
      (rest (second (list a (cons name YoB) b)))))))
= { car-cdr axioms }
(and
   (validFamTreep a)
   (validFamTreep b)
   (< (getRootYear a) YoB)
   (< (getRootYear b) YoB))
= { C8, C9 }
(and 
 (validFamTreep a)
 (validFamTreep b)
 t
 t)
= { MP, Arith }
(and
 (validFamTreep a)
 (validFamTreep b))
= { Def validFamTreep }
(and
 (cond
  ((personp a) t)
  ((famtreep a) (and (validFamTreep (first a))
                     (validFamTreep (third a))
                     (< (getRootYear (first a)) (rest (second a)))
                     (< (getRootYear (third a)) (rest (second a))))))
 (cond
  ((personp b) t)
  ((famtreep b) (and (validFamTreep (first b))
                     (validFamTreep (third b))
                     (< (getRootYear (first b)) (rest (second b)))
                     (< (getRootYear (third b)) (rest (second b)))))))
= { C1, C3, C2, C4 }
(and 
 (and (validFamTreep (first a))
      (validFamTreep (third a))
      (< (getRootYear (first a)) (rest (second a)))
      (< (getRootYear (third a)) (rest (second a))))
 (and (validFamTreep (first b))
      (validFamTreep (third b))
      (< (getRootYear (first b)) (rest (second b)))
      (< (getRootYear (third b)) (rest (second b)))))
= { MP, Arith }
(and
 (validFamTreep (first a))
 (validFamTreep (third a))
 (< (getRootYear (first a)) (rest (second a)))
 (< (getRootYear (third a)) (rest (second a)))
 (validFamTreep (first b))
 (validFamTreep (third b))
 (< (getRootYear (first b)) (rest (second b)))
 (< (getRootYear (third b)) (rest (second b))))
= { Arith } ;; Double check for possibility of MP
(and
 (validFamTreep (first a))
 (validFamTreep (third a))
 (validFamTreep (first b)) 
 (validFamTreep (third b))
 (< (getRootYear (first a)) (rest (second a)))
 (< (getRootYear (third a)) (rest (second a)))
 (< (getRootYear (first b)) (rest (second b)))
 (< (getRootYear (third b)) (rest (second b))))
= { D7, D8, PL }
(and 
	t
	t
	t
	t
	(< (getRootYear (first a)) (rest (second a)))
	(< (getRootYear (third a)) (rest (second a)))
	(< (getRootYear (first b)) (rest (second b)))
	(< (getRootYear (third b)) (rest (second b))))
= { PL }
(and 
	(< (getRootYear (first a)) (rest (second a)))
	(< (getRootYear (third a)) (rest (second a)))
	(< (getRootYear (first b)) (rest (second b)))
	(< (getRootYear (third b)) (rest (second b))))
= { Lemma Root-to-Rest-Second }
(and 
	(< (getRootYear (first a)) (getRootYear a))
	(< (getRootYear (third a)) (getRootYear a))
	(< (getRootYear (first b)) (getRootYear b))
	(< (getRootYear (third b)) (getRootYear b)))
= { C9, C10, Arith }
(and 
	(< (getRootYear (first a)) YoB)
	(< (getRootYear (third a)) YoB)
	(< (getRootYear (first b)) YoB)
	(< (getRootYear (third b)) YoB))
= { C9, C10, Lemma fam-tree-root-year, MP }
(and 
	t
	t
	t
	t)
= { PL }
t
QED

Lemma fam-tree-root-year:

(implies 
	(and
	(natp YoB)
	(validFamTreep a)
	(not (personp a)))
		(implies 
			(< (getRootYear a) YoB)
				(and 
				(< (getRootYear (first a)) YoB)
				(< (getRootYear (third a)) YoB))))

Problem 2:
(implies 
	(and
	(natp YoB)
	(validFamTreep a)
	(not (personp a)))
		(implies 
			(< (getRootYear a) YoB)
				(and 
				(< (getRootYear (first a)) YoB)
				(< (getRootYear (third a)) YoB))))
					
Exportation:
(implies 
	(and
		(natp YoB)
		(validFamTreep a)
		(not (personp a))
		(< (getRootYear a) YoB))
	(and 
		(< (getRootYear (first a)) YoB)
		(< (getRootYear (third a)) YoB)))
		
Context:
C1. (natp YoB)
C2. (validFamTreep a)
C3. (not (personp a))
C4. (< (getRootYear a) YoB)

Derived Context:
D1. (famtreep a) { C2, C3 }
D2. (cond
		((personp a) t)
		((famtreep a) (and (validFamTreep (first a))
                       (validFamTreep (third a))
                       (< (getRootYear (first a)) (rest (second a)))
                       (< (getRootYear (third a)) (rest (second a)))))) { Def validFamTreep, D1 }
D3. (and 
		(validFamTreep (first a))
	    (validFamTreep (third a))
	    (< (getRootYear (first a)) (rest (second a)))
	    (< (getRootYear (third a)) (rest (second a)))) { if axioms, D2, D1 }
D4. (and 
		t
		t
		(< (getRootYear (first a)) (rest (second a)))
        (< (getRootYear (third a)) (rest (second a)))) { PL, C2, Def validFamTreep, D3 }
D5. (and 
		(< (getRootYear (first a)) (rest (second a)))
        (< (getRootYear (third a)) (rest (second a)))) { PL, D4 }
D6. (and 
		(< (getRootYear (first a)) (getRootYear a))
        (< (getRootYear (third a)) (getRootYear a))) { Lemma Root-to-Rest-Second, D5 }
D7. (and 
		(< (getRootYear (first a)) YoB)
        (< (getRootYear (third a)) YoB)) { D6, C4, Arith }
		 
Goal:
(and 
	(< (getRootYear (first a)) YoB)
	(< (getRootYear (third a)) YoB))	 

Proof:
(and 
	(< (getRootYear (first a)) YoB)
	(< (getRootYear (third a)) YoB))
= { D7 }
t
QED

Lemma Root-to-Rest-Second:
(implies
	(and (validFamTreep a)
		 (not (personp a)))
	(equal (getRootYear a)
		   (rest (second a))))
	
Problem 3:
(implies
	(and (validFamTreep a)
		 (not (personp a)))
	(equal (getRootYear a)
		   (rest (second a))))

Context:
C1. (validFamTreep a)
C2. (not (personp a))

Derived Context:
D1. (famtreep a) { C1, C2 }

Goal:
(equal 
	(getRootYear a)
	(rest (second a)))

Proof:
(getRootYear a)
= { Def getRootYear }
(cond
   ((personp a) (rest a))
   ((famTreep a) (rest (second a))))
= { D1, if axioms }
(rest (second a))
QED

Lemma Validfamtreep-first-third:
(implies
	(validFamTreep a)
	(not (personp a))
	(and
		(validFamTreep (first a))
		(validFamTreep (third a))))

Problem 4:
(implies
	(validFamTreep a)
	(not (personp a))
	(and
		(validFamTreep (first a))
		(validFamTreep (third a))))
		
Context:
C1. (validFamTreep a)
C2. (not (personp a))

Derived Context:
D1. (famtreep a) { C1, C2 }
D2. (cond
	    ((personp a) t)
	    ((famtreep a) (and (validFamTreep (first a))
		 				    (validFamTreep (third a))
		 				    (< (getRootYear (first a)) (rest (second a)))
						    (< (getRootYear (third a)) (rest (second a)))))) { C1, Def validFamTreep }
D3. (and (validFamTreep (first a))
		 (validFamTreep (third a))
		 (< (getRootYear (first a)) (rest (second a)))
		 (< (getRootYear (third a)) (rest (second a)))) { if axioms, D1 }
D4. (and (validFamTreep (first a))
		 (validFamTreep (third a))
		 t
		 t) { PL, C1, C2 }
D5. (and (validFamTreep (first a))
		 (validFamTreep (third a))) { PL }
Goal:
(and 
	(validFamTreep (first a))
	(validFamTreep (third a)))

Proof:
(and 
	(validFamTreep (first a))
	(validFamTreep (third a)))
= { D5 }
t
QED
