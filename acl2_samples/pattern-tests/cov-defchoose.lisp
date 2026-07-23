(in-package "ACL2")

; COVERAGE/defchoose (map frame: event forms — UNCOVERED): the choice
; principle + its defining axiom consumed via :use.

(defchoose pick (v) (x)
  (member-equal v x))

(defthm pick-picks-member
  (implies (member-equal a x)
           (member-equal (pick x) x))
  :hints (("Goal" :use (:instance pick (v a)))))
