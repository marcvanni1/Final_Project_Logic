Marc Vanni, Kelli Therrien, Nan Chen, Yousuf Khan
(defdata person (cons symbol nat))
(defdata famTree (oneof person (list famTree person famTree)))

;; getRootYear: famTree -> int
;;
(definec getRootYear (ft :famTree) :nat
  (cond
   ((personp ft) (rest ft))
   ((famTreep ft) (rest (second ft)))))

;;-----------------------------------------------------------------------
;; Case 1: x :person
(implies (personp x) (natp (getRootYear x)))

;; Exportation:
(implies (personp x)
         (natp (getRootYear x)))

;; Context:
C1. (personp x)

;; Derived Context:
;; None

;; Goal:
(natp (getRootYear x))

;; Proof
(getRootYear x)
= {Def getRootYear}
(cond
 ((personp x) (rest x))
 ((famTreep x) (rest (second x))))
= {if-axioms, C1}
(rest x)
= {Def person}
(rest (cons symbol int))
= {cons axioms}
(nat)
(natp nat)
= {Arith}
t

QED

;;-----------------------------------------------------------------------
;; Case 2: x :famtree
(implies (and (famtreep x) (not (personp x)))
         (natp (getRootYear x)))

;; Exportation:
(implies (and (famtreep x)
              (not (personp x)))
         (natp (getRootYear x)))

;; Context:
C1. (famtreep x)
C2. (not (personp x))

;; Derived Context:
;; None

;; Goal:
(natp (getRootYear x))

;; Proof
(getRootYear x)
= {Def getRootYear}
(cond
 ((personp x) (rest x))
 ((famTreep x) (rest (second x))))
= {if-axioms, C1, C2}
(rest (second x))
= {Def famtree, C2}
(rest (second ((list famTree person famTree))))
= {cons-axioms}
(rest person)
= {Def person}
(rest (cons symbol int))
= {cons axioms}
(nat)
(natp nat)
= {Arith}
t

QED
