(in-package "ACL2")

;; FEATURE: a tail-recursive ACCUMULATOR function whose step IH substitutes the
;; accumulator to a CONSTRUCTED (growing) term — acc := (cons (car x) acc) — rather
;; than a selector like (cdr x).  Every prior recon-test's IH alist maps vars to
;; sub-terms that get SMALLER (cdr/car); this one maps acc to a term that gets
;; BIGGER.  Exercises an IH-substitution alist entry that is a constructor call,
;; with the measured subset {x} (acc is not measured) — i.e. a controller var and a
;; non-controller accumulator both substituted in the same case.

(defun rev-acc (x acc)
  (if (atom x)
      acc
    (rev-acc (cdr x) (cons (car x) acc))))

;; (len (rev-acc x acc)) = (len x) + (len acc); forces induction on rev-acc's
;; scheme (measured subset {x}; step IH x:=(cdr x), acc:=(cons (car x) acc)).
(defthm len-rev-acc
  (equal (len (rev-acc x acc))
         (+ (len x) (len acc)))
  :rule-classes nil)
