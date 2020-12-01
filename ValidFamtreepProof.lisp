; ****************** BEGIN INITIALIZATION FOR ACL2s MODE ****************** ;
; (Nothing to see here!  Your actual file is after this initialization code);
(make-event
 (er-progn
  (set-deferred-ttag-notes t state)
  (value '(value-triple :invisible))))

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading the CCG book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "acl2s/ccg/ccg" :uncertified-okp nil :dir :system :ttags ((:ccg)) :load-compiled-file nil);v4.0 change

;Common base theory for all modes.
#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s base theory book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "acl2s/base-theory" :dir :system :ttags :all)


#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s customizations book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "acl2s/custom" :dir :system :ttags :all)

;; guard-checking-on is in *protected-system-state-globals* so any
;; changes are reverted back to what they were if you try setting this
;; with make-event. So, in order to avoid the use of progn! and trust
;; tags (which would not have been a big deal) in custom.lisp, I
;; decided to add this here.
;; 
;; How to check (f-get-global 'guard-checking-on state)
;; (acl2::set-guard-checking :nowarn)
(acl2::set-guard-checking :all)

;Settings common to all ACL2s modes
(acl2s-common-settings)
;(acl2::xdoc acl2s::defunc) ;; 3 seconds is too much time to spare -- commenting out [2015-02-01 Sun]

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s customizations book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "acl2s/acl2s-sigs" :dir :system :ttags :all)

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem setting up ACL2s mode.") (value :invisible))

(acl2::xdoc acl2s::defunc) ; almost 3 seconds

; Non-events:
;(set-guard-checking :none)

(set-inhibit-warnings! "Invariant-risk" "theory")

(in-package "ACL2")
(redef+)
(defun print-ttag-note (val active-book-name include-bookp deferred-p state)
  (declare (xargs :stobjs state)
	   (ignore val active-book-name include-bookp deferred-p))
  state)

(defun print-deferred-ttag-notes-summary (state)
  (declare (xargs :stobjs state))
  state)

(defun notify-on-defttag (val active-book-name include-bookp state)
  (declare (xargs :stobjs state)
	   (ignore val active-book-name include-bookp))
  state)
(redef-)

(acl2::in-package "ACL2S")

; ******************* END INITIALIZATION FOR ACL2s MODE ******************* ;
;$ACL2s-SMode$;ACL2s
(defdata person (cons symbol nat))
(defdata famTree (oneof person (list famTree person famTree)))

 

(personp '(Jason . 1985))  
(famTreep '(Jason . 1985))
(famTreep '((Tammy . 1969) (Jason . 1985) (Alan . 1968)))
(famTreep '((Tammy . 1969) (Jason . 1985) ((Glenn . 1930) (Alan . 1968) (Liz . 1932))))

 

;; getRootYear: famTree -> int
;;
(definec getRootYear (ft :famTree) :nat
  (cond
   ((personp ft) (rest ft))
   ((famTreep ft) (rest (second ft)))))

 

;; validFamTreep: framTree -> bool
;; Return true if the given famTree is a valid famTree
(definec validFamTreep (ft :famTree) :bool
  (cond
   ((personp ft) t)
   ((famtreep ft) (and (validFamTreep (first ft))
                       (validFamTreep (third ft))
                       (< (getRootYear (first ft)) (rest (second ft)))
                       (< (getRootYear (third ft)) (rest (second ft)))))))

Proof:
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
                (< (getRootYear (first a)) (rest (second a)))
                (< (getRootYear (third a)) (rest (second a)))
                (< (getRootYear (first b)) (rest (second b)))
                (< (getRootYear (third b)) (rest (second b))))
               (and
                (validFamTreep (list (first a) (second a) (third a)))
                (validFamTreep (list (first b) (second b) (third b))))))
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
= { if-axioms, D2 }
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
= { if-axioms, C3, C4 }
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
                (< (getRootYear (first a)) (rest (second a)))
                (< (getRootYear (third a)) (rest (second a)))
                (< (getRootYear (first b)) (rest (second b)))
                (< (getRootYear (third b)) (rest (second b))))
               (and
                (validFamTreep (list (first a) (second a) (third a)))
                (validFamTreep (list (first b) (second b) (third b))))))
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
                (< (getRootYear (first a)) (rest (second a)))
                (< (getRootYear (third a)) (rest (second a)))
                (< (getRootYear (first b)) (rest (second b)))
                (< (getRootYear (third b)) (rest (second b))))
               (and
                (validFamTreep (list (first a) (second a) (third a)))
                (validFamTreep (list (first b) (second b) (third b)))))
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
      (< (getRootYear (first a)) (rest (second a)))
      (< (getRootYear (third a)) (rest (second a)))
      (< (getRootYear (first b)) (rest (second b)))
      (< (getRootYear (third b)) (rest (second b))))
     (and
      (validFamTreep (list (first a) (second a) (third a)))
      (validFamTreep (list (first b) (second b) (third b)))))
C8. (< (getRootYear a) YoB)
C9. (< (getRootYear b) YoB)

Derived Context:
D1. (personp (cons name YoB)) { Def person }
D2. (famtreep (list a (cons name YoB) b)) { Def famtree }
D3. (famtreep (first a)) { C3, Def famtree }
D4. (famtreep (third a)) { C3, Def famtree }
D5. (famtreep (first b)) { C3, Def famtree }
D6. (famtreep (third b)) { C3, Def famtree }

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
= { C7 }
(and
 (validFamTreep (first a))
 (validFamTreep (third a))
 (validFamTreep (first b))
 (validFamTreep (third b))
 (validFamTreep (list (first a) (second a) (third a)))
 (validFamTreep (list (first b) (second b) (third b))))
;; stuckkkkkkkkk






