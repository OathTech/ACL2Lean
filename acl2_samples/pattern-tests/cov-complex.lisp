(in-package "ACL2")

; COVERAGE/complex numbers (map frame: value surface — UNCOVERED):
; complex-rational arithmetic — pins reader/printer/eval treatment of
; #c literals end to end.

(defthm complex-add
  (equal (+ #c(1 2) #c(3 4)) #c(4 6)))

(defthm complex-parts
  (and (equal (realpart #c(5 7)) 5)
       (equal (imagpart #c(5 7)) 7)))
