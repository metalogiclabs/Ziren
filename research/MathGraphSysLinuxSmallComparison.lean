import Mathlib

/-!
  A full 32-bit packed argument is not injective in KoalaBear's field.
  Ziren's repaired SysLinux uses a *purpose-built quotient*: it only needs
  exact comparisons to 0, 1, and 2 (similarly a1 to 1 and 3).

  This theorem explains why the compressed representation is adequate for
  that narrow observer when every input limb is byte-bounded. It does not
  assert that the compressed representation preserves arbitrary arithmetic.
-/

namespace MathGraph.SysLinux

private def modulus : ℕ := 2130706433

theorem compressed_below_modulus (a b c d : ℕ)
    (ha : a ≤ 255) (hb : b ≤ 255) (hc : c ≤ 255) (hd : d ≤ 255) :
    a + 256 * (b + c + d) < modulus := by
  dsimp [modulus]
  omega

theorem compressed_exact_small (a b c d k : ℕ)
    (ha : a ≤ 255) (hb : b ≤ 255) (hc : c ≤ 255) (hd : d ≤ 255)
    (hk : k ≤ 3) :
    ((a + 256 * (b + c + d)) % modulus = k) ↔
      (a = k ∧ b = 0 ∧ c = 0 ∧ d = 0) := by
  rw [Nat.mod_eq_of_lt (compressed_below_modulus a b c d ha hb hc hd)]
  omega

theorem archived_packed_alias_zero :
    (1 + 256 * 0 + 65536 * 0 + 16777216 * 127) % modulus = 0 := by
  decide

theorem repaired_compressed_does_not_alias_zero :
    (1 + 256 * (0 + 0 + 127)) % modulus = 32513 := by
  decide

#print axioms compressed_exact_small
#print "MATHGRAPH_SYSLINUX_SMALL_SELECTOR_LEMMA_DONE"

end MathGraph.SysLinux
