; Capture an ordinary bootstrap proof window during full initialization.
; All event forms, proof flags and hints still come from initialize-acl2 NIL.
(load "init.lisp")
; SBCL loads the .lisp sources and compiles on the fly. Refuse another mode
; rather than assigning current source provenance to precompiled files.
(unless acl2::*suppress-compile-build-time*
  (error "Bootstrap capture requires direct source loading"))
(acl2::load-acl2 :load-acl2-proclaims nil)
(format t "~A~%" (acl2::acl2-snapshot-info))

(defparameter *acl2lean-target-names*
  (with-open-file (stream (or (sb-ext:posix-getenv "ACL2LEAN_BOOTSTRAP_SELECTION")
                              (error "Missing bootstrap selection")))
    (let ((*read-eval* nil))
      (read stream))))
(defvar *acl2lean-targets-seen* nil)
(defvar *acl2lean-target-active* nil)
(defvar *acl2lean-target-ended* nil)
(defvar *acl2lean-target-cited* nil)
(defvar *acl2lean-window-world* nil)

; TRACE-LOG[suppress/bootstrap-capture-print]: suppress only output outside
; the selected event window, retaining errors and every initialization proof.
(let ((original (symbol-function 'acl2::enter-boot-strap-mode)))
  (setf (symbol-function 'acl2::enter-boot-strap-mode)
        (lambda (&rest args)
          (multiple-value-prog1 (apply original args)
            (acl2::f-put-global
             'acl2::inhibit-output-lst
             (remove 'acl2::error acl2::*valid-output-names*)
             acl2::*the-live-state*)))))

; TRACE-LOG[suppress/bootstrap-capture-ld]: change only the four LD print
; settings; all inputs, redefinition settings and proof flags are preserved.
(let ((original (symbol-function 'acl2::ld-alist-raw)))
  (setf (symbol-function 'acl2::ld-alist-raw)
        (lambda (&rest args)
          (mapcar (lambda (entry)
                    (if (member (car entry)
                                '(acl2::ld-prompt acl2::ld-pre-eval-print
                                  acl2::ld-post-eval-print acl2::ld-verbose))
                        (cons (car entry) nil)
                      entry))
                  (apply original args)))))

; TRACE-LOG[infra/bootstrap-capture-window]: observe the selected contiguous
; source events in their FIRST actual logic-mode execution. Later bootstrap
; passes still run unchanged, without reopening the captured window. The original function
; receives exactly the original arguments and its values are returned intact.
(let ((original (symbol-function 'acl2::defthm-fn)))
  (setf (symbol-function 'acl2::defthm-fn)
        (lambda (name term state &rest args)
          (let ((actual-proof
                 (and (eq (acl2::default-defun-mode-from-state state) :logic)
                      (null (acl2::ld-skip-proofsp state)))))
            (when (and actual-proof (not *acl2lean-target-ended*)
                       (eq name (car *acl2lean-target-names*)))
              (when *acl2lean-target-active*
                (error "Repeated selected bootstrap proof window"))
              (setq *acl2lean-target-active* t
                    *acl2lean-window-world* (acl2::w state))
              (acl2::set-raw-proof-format-fn :structured state))
            (when *acl2lean-target-active*
              (unless (and actual-proof
                           (eq name (nth (length *acl2lean-targets-seen*)
                                         *acl2lean-target-names*)))
                (error "Unexpected event in selected bootstrap window: ~S" name)))
            (let ((results (multiple-value-list
                            (apply original name term state args))))
              (when *acl2lean-target-active*
                (unless (and (= (length results) 3) (null (car results)))
                  (error "Selected bootstrap event failed: ~S" name))
                (push name *acl2lean-targets-seen*)
                (when (eq name (car (last *acl2lean-target-names*)))
                  (setq *acl2lean-target-cited* acl2::*structured-cited-symbols*
                        *acl2lean-target-active* nil
                        *acl2lean-target-ended* t)
                  (acl2::set-raw-proof-format-fn nil state)
                  (acl2::f-put-global
                   'acl2::inhibit-output-lst
                   (remove 'acl2::error acl2::*valid-output-names*) state)))
              (values-list results))))))

(let ((completed (acl2::initialize-acl2 nil)))
  (with-open-file
      (stream (or (sb-ext:posix-getenv "ACL2LEAN_BOOTSTRAP_RESULT")
                  (error "Missing capture result path"))
              :direction :output :if-exists :error :if-does-not-exist :create)
    (write (list :initialized completed
                 :selected-events (reverse *acl2lean-targets-seen*)
                 :window-ended *acl2lean-target-ended*) :stream stream)
    (terpri stream))
  (unless (and completed *acl2lean-target-ended*
               (equal (reverse *acl2lean-targets-seen*) *acl2lean-target-names*))
    (sb-ext:exit :code 1))
  ; TRACE-LOG[emit/bootstrap-capture-end]: only a completed initialization
  ; permits the selected cited-closure snapshots and final capture marker.
  ; Resume the existing stream without resetting its collector or BEGIN marker.
  (acl2::f-put-global 'acl2::raw-proof-format :structured acl2::*the-live-state*)
  (setq acl2::*structured-cited-symbols* *acl2lean-target-cited*)
  ; Read the actual world immediately BEFORE the first selected proof.
  ; Leave CURRENT-ACL2-WORLD and its installed property cache unchanged:
  ; fgetprop must take its historical-alist path for this older world.
  ; W is scoped only for snapshot printing, after initialization's proofs.
  (let ((original-w (symbol-function 'acl2::w)))
    (unwind-protect
        (progn
          (setf (symbol-function 'acl2::w)
                (lambda (state)
                  (declare (ignore state))
                  *acl2lean-window-world*))
          (acl2::emit-ground-zero-snapshots acl2::*the-live-state*))
      (setf (symbol-function 'acl2::w) original-w)))
  (acl2::emit-capture-manifest acl2::*the-live-state*)
  (finish-output)
  (sb-ext:exit :code 0))
