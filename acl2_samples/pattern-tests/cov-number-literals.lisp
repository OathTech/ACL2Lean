(in-package "ACL2")

; COVERAGE/reader literals (gap audit B — value surface): negative
; rationals, bare ratios, radix macros #x/#b/#o — none appear anywhere
; in the samples.

(defthm neg-ratio
  (equal (+ -1/2 1/2) 0))

(defthm hex-lit
  (equal #x10 16))

(defthm bin-lit
  (equal #b101 5))

(defthm oct-lit
  (equal #o17 15))
