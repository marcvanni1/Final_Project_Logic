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
(defdata person (cons symbol int))
(defdata famTree (oneof person (list famTree person famTree)))#|ACL2s-ToDo-Line|#


;; getRootYear: famTree -> int
;;
(definec getRootYear (ft :famTree) :int
  (cond
   ((personp ft) (rest ft))
   (t (rest (second ft)))))

;;-----------------------------------------------------------------------
;; Case 1: x :person
(implies (personp x) (intp (getRootYear x)))

;; Exportation:
(implies (personp x)
         (natp (getRootYear x)))

;; Context:
C1. (personp x)

;; Derived Context:
;; None

;; Goal:
(intp (getRootYear x))

;; Proof
(getRootYear x)
= {Def getRootYear}
(cond
 ((personp x) (rest x))
 (t (rest (second x))))
= {if-axioms, C1}
(rest x)
= {Def person}
(rest (cons symbol int))
= {cons axioms}
(int)
(intp int)
= {Arith}
t

QED

;;-----------------------------------------------------------------------
;; Case 2: x :famtree
(implies (and (famtreep x) (not (personp x)))
         (intp (getRootYear x)))

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
(intp (getRootYear x))

;; Proof
(getRootYear x)
= {Def getRootYear}
(cond
 ((personp x) (rest x))
 (t (rest (second x))))
= {if-axioms, C1, C2}
(rest (second x))
= {Def famtree, C2}
(rest (second ((list famTree person famTree))))
= {cons-axioms}
(rest person)
= {Def person}
(rest (cons symbol int))
= {cons axioms}
(int)
(intp int)
= {Arith}
t

QED