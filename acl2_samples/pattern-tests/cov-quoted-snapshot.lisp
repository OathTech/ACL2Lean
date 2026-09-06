(in-package "ACL2")

; Quoted function names are data, not snapshot dependencies. The second
; quoted list also exercises the pretty printer's quote tuple.
(defthm quoted-apply-name
  (equal (car '(apply$)) 'apply$)
  :rule-classes nil)

; These literal bytes must not masquerade as capture failures or make grep
; suppress the event census as "binary file matches".
(defconst *snapshot-nul-data* (coerce (list #\H (code-char 0) (code-char 255)) 'string))
(defthm quoted-nul-data
  (equal (car (cons x *snapshot-nul-data*)) x))
(defthm quoted-diagnostic-data
  (equal (car (cons x "HARD ACL2 ERROR")) x))

(defthm quoted-ev-name
  (equal (car '(ev$ snapshot-data-one snapshot-data-two snapshot-data-three
                   snapshot-data-four snapshot-data-five snapshot-data-six
                   snapshot-data-seven snapshot-data-eight snapshot-data-nine
                   snapshot-data-ten snapshot-data-eleven snapshot-data-twelve))
         'ev$)
  :rule-classes nil)
