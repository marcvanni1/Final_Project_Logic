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

 (check= (getRootYear '(Jason . 1985)) 1985)
(check= (getRootYear '((Tammy . 1969) (Jason . 1985) (Alan . 1968))) 1985)
(check= (getRootYear '((Tammy . 1969) (Jason . 1985) ((Glenn . 1930) (Alan . 1968) (Liz . 1932)))) 1985)#|ACL2s-ToDo-Line|#



 
;; validFamTreep: framTree -> bool
;; Return true if the given famTree is a valid famTree
(definec validFamTreep (ft :famTree) :bool
  (cond
   ((personp ft) t)
   ((famtreep ft) (and (validFamTreep (first ft))
                       (validFamTreep (third ft))
                       (< (getRootYear (first ft)) (rest (second ft)))
                       (< (getRootYear (third ft)) (rest (second ft)))))
   (t nil)))

 

;;-----------------------------------------------------------------------------------
(validFamTreep (list '((Tammy . 1969) (Jason . 1985) (Alan . 1968))
                     (cons 'fish 2000)
                     '((Tammy . 1969) (Jason . 1985) ((Glenn . 1930)
                                                      (Alan . 1968) (Liz . 1932)))))

 

(let ((JASON '(Jason . 1985))
      (TAMMY '(Tammy . 1969))
      (ALAN '(Alan . 1968)))
  (famTreep (list TAMMY JASON ALAN)))

 

(let ((JASON '(Jason . 1985))
      (TAMMY '(Tammy . 1969))
      (ALAN '(Alan . 1968))
      (GLENN '(Glenn . 1930))
      (LIZ '(Liz . 1932)))
  (famTreep (list TAMMY JASON (list GLENN ALAN LIZ))))

 

(let ((JASON '(Jason . 1985))
      (TAMMY '(Tammy . 1969))
      (ALAN '(Alan . 1968))
      (GLENN '(Glenn . 1930))
      (LIZ '(Liz . 1932)))
  (validFamTreep (list (list TAMMY JASON ALAN)
                       (cons 'millenial 2000) 
                       (list TAMMY JASON (list GLENN ALAN LIZ)))))
;;-----------------------------------------------------------------------------------

 

(set-gag-mode nil)

 

(defthm project2 (implies (and (validFamTreep a) 
                               (validFamTreep b) 
                               (natp YoB)
                               (symbolp name))
                          (implies (and (< (getRootYear a) YoB)
                                        (< (getRootYear b) YoB))
                                   (validFamTreep (list a (cons name YoB) b)))))