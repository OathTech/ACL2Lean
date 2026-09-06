;@isolate
; Reader acceptance measured against the pinned ACL2 image at NS1 C0.
; Canonicalization is allowed; malformed components are reader errors.
;@ match
'#C (1 2)
;@ match
'#C(1 . (2))
;@ match
'#C(#C(1 0) 2)
;@ match
'#C(#f1.5 2)
;@ match
'#C(#x10 #b11)
;@ refuse
'#C(1)
;@ refuse
'#C(1 2 3)
;@ refuse
'#C(1 . 2)
;@ refuse
'#C(nil 2)
;@ refuse
'#C(#C(1 2) 3)
;@ refuse
'#C(1.5 2)
; BUG-028: literal division by zero is rejected, unlike arithmetic completion.
;@ refuse
'1/0
;@ refuse
'0/0
;@ refuse
'#C(1/0 2)
;@ refuse
'#C(1 2/0)
; Host accepts this dispatch argument spelling. It is not currently needed
; by the captured log; the reader explicitly rejects its unsupported syntax.
;@ unsupported
'#2C(1 2)
