(set-logic BV)
(declare-const x (_ BitVec 4))
(assert false)
(reset-assertions)
(assert (= x #b0000))
(check-sat)