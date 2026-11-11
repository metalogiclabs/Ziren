import Mathlib

/-!
MathGraph research-only algebra lemma for StoreWord.top witness contraction.
This lemma is universal over commutative rings, including characteristic two.
It proves the *local algebraic gate step*, not that the entire generated old
and new Lean relations are interchangeable; the source-bound structural
certificate and a relation-level wrapper are independent obligations.
-/

namespace MathGraph.StoreWord

variable {F : Type*} [CommRing F] (sw sc oldByte writeByte baseByte : F)

theorem contract_sw_gate
    (hsw : sw * (sw - 1) = 0)
    (hwrite : sw * (oldByte - writeByte) = 0)
    (hread : sc * (oldByte - baseByte) = 0)
    (halias : (sw * (sw + sc)) * (writeByte - baseByte) = 0) :
    sw * (baseByte - writeByte) = 0 := by
  have hforward : sw * (writeByte - baseByte) = 0 := by
    calc
      sw * (writeByte - baseByte) =
          (sw * (sw + sc)) * (writeByte - baseByte) +
          (sw + sc - 1) * (sw * (oldByte - writeByte)) -
          sw * (sc * (oldByte - baseByte)) -
          (oldByte - baseByte) * (sw * (sw - 1)) := by ring
      _ = 0 := by simp [halias, hwrite, hread, hsw]
  calc
    sw * (baseByte - writeByte) = -(sw * (writeByte - baseByte)) := by ring
    _ = 0 := by rw [hforward]; ring

theorem contract_sc_byte
    (h : oldByte - baseByte = 0) : oldByte = baseByte :=
  sub_eq_zero.mp h

theorem contract_sw_byte
    (hwrite : oldByte - writeByte = 0)
    (halias : writeByte - baseByte = 0) :
    oldByte = baseByte :=
  (sub_eq_zero.mp hwrite).trans (sub_eq_zero.mp halias)

end MathGraph.StoreWord
