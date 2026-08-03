(in-package "ACL2")

;; PATTERN (fresh-verify N1, 2026-08-03): include-book of a book whose only
;; content is a LOCAL-ONLY encapsulate. On the include path ld-skip-proofsp
;; is 'include-book: the bracket BEGIN is emitted on include-book's branch of
;; encapsulate-fn and the event exits via the include path's
;; :empty-encapsulate SUCCESS exit — the fourth success exit, whose
;; (:ENCAPSULATE-END) the first fix round missed (leaving the BEGIN unclosed
;; and hard-failing recon on a legitimate ACL2 pattern). Uncertified include
;; is the corpus's existing mode (no .cert files anywhere; same as the
;; sorting books).
(include-book "cov-encapsulate-empty-helper")
