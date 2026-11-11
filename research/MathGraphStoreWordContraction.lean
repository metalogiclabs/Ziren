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

/-!
These two propositions explicitly eliminate one legacy existential field.
The certificate separately confirms that all surrounding source constraints,
ports and theorem signatures match after the same substitution.
-/

theorem sc_byte_rel_iff (baseByte outputByte : F) :
    (∃ oldByte : F, oldByte - baseByte = 0 ∧ outputByte = oldByte) ↔
    outputByte = baseByte := by
  constructor
  · rintro ⟨oldByte, hbase, hout⟩
    exact hout.trans (sub_eq_zero.mp hbase)
  · intro hout
    exact ⟨baseByte, by ring, hout⟩

theorem sw_byte_rel_iff (writeByte baseByte outputByte : F)
    (hbase : writeByte - baseByte = 0) :
    (∃ oldByte : F, oldByte - writeByte = 0 ∧ outputByte = oldByte) ↔
    outputByte = baseByte := by
  constructor
  · rintro ⟨oldByte, hwrite, hout⟩
    exact hout.trans ((sub_eq_zero.mp hwrite).trans (sub_eq_zero.mp hbase))
  · intro hout
    refine ⟨baseByte, ?_, hout⟩
    calc
      baseByte - writeByte = -(writeByte - baseByte) := by ring
      _ = 0 := by rw [hbase]; ring

theorem top_gate_rel_iff (sw sc writeByte baseByte : F)
    (hsw : sw * (sw - 1) = 0) :
    (∃ oldByte : F,
        sw * (oldByte - writeByte) = 0 ∧
        sc * (oldByte - baseByte) = 0 ∧
        (sw * (sw + sc)) * (writeByte - baseByte) = 0) ↔
    (sw * (baseByte - writeByte) = 0 ∧
      (sw * (sw + sc)) * (writeByte - baseByte) = 0) := by
  constructor
  · rintro ⟨oldByte, hwrite, hread, halias⟩
    exact ⟨contract_sw_gate sw sc oldByte writeByte baseByte hsw hwrite hread halias,
           halias⟩
  · rintro ⟨hnew, halias⟩
    refine ⟨baseByte, hnew, ?_, halias⟩
    ring

end MathGraph.StoreWord

/-!
Branch/Jump research principle: a gate-equality permits replacement of a
witness inside *any* gated expression over a field; a gated range argument is
likewise unchanged. The source certificate independently identifies the
relevant gated rows in all nine changed Branch/Jump modules.
-/

namespace MathGraph.TargetAlias

variable {F : Type*} [Field F]

theorem gated_substitution (gate oldTarget newTarget : F)
    (hgate : gate * (oldTarget - newTarget) = 0)
    (expression : F → F) :
    gate * (expression oldTarget - expression newTarget) = 0 := by
  rcases mul_eq_zero.mp hgate with hzero | htarget
  · simp [hzero]
  · have heq : oldTarget = newTarget := sub_eq_zero.mp htarget
    rw [heq]
    ring

theorem unmask_gated_equality (selectorSum gate oldTarget newTarget : F)
    (hselector : (selectorSum - 1) * gate = 0)
    (hguarded : selectorSum * (gate * (oldTarget - newTarget)) = 0) :
    gate * (oldTarget - newTarget) = 0 := by
  calc
    gate * (oldTarget - newTarget) =
        selectorSum * (gate * (oldTarget - newTarget)) -
        ((selectorSum - 1) * gate) * (oldTarget - newTarget) := by ring
    _ = 0 := by rw [hguarded, hselector]; ring

theorem gated_range_argument (gate oldTarget newTarget : F)
    (hgate : gate * (oldTarget - newTarget) = 0) :
    gate * oldTarget = gate * newTarget := by
  calc
    gate * oldTarget = gate * newTarget + gate * (oldTarget - newTarget) := by ring
    _ = gate * newTarget := by rw [hgate]; ring

theorem direct_substitution (oldTarget newTarget : F)
    (heq : oldTarget - newTarget = 0)
    (expression : F → F) :
    expression oldTarget = expression newTarget := by
  have h : oldTarget = newTarget := sub_eq_zero.mp heq
  rw [h]

end MathGraph.TargetAlias
