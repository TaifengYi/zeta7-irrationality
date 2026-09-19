import Zeta7Proof.AnnularHypergeometricFactorials
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Data.Nat.Factorial.BigOperators

/-! Factorial lower bounds for the actual step-twelve numerator progressions.
The proof lifts a consecutive-integer factorial divisibility through a congruence
modulo the full power of seven dividing n!, avoiding any finite coefficient test. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
open Finset
namespace Zeta7Annulus
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

theorem factorial_valuation_le_progression (a r n : ℕ)
    (hr : 0 < r) (ha : Nat.Coprime a 7) :
    padicValNat 7 n.factorial ≤ padicValNat 7 (∏ k ∈ range n, (a * k + r)) := by
  let q := 7 ^ padicValNat 7 n.factorial
  have hq : q ≠ 0 := pow_ne_zero _ (by decide)
  obtain ⟨b, _, hb⟩ := Nat.exists_mul_mod_eq_of_coprime r (ha.pow_right _) hq
  have hb' : a * b ≡ r [MOD q] := hb
  have hp : (∏ k ∈ range n, a * (b + k)) ≡
      (∏ k ∈ range n, (a * k + r)) [MOD q] := by
    apply Nat.ModEq.prod
    intro k hk
    simpa only [Nat.mul_add, Nat.add_comm] using hb'.add (Nat.ModEq.refl (a * k))
  have hd : q ∣ ∏ k ∈ range n, a * (b + k) := by
    rw [prod_mul_distrib, prod_const, card_range, ← Nat.ascFactorial_eq_prod_range]
    exact dvd_mul_of_dvd_right
      ((pow_padicValNat_dvd (p := 7) (n := n.factorial)).trans (Nat.factorial_dvd_ascFactorial b n)) _
  have hn : (∏ k ∈ range n, (a * k + r)) ≠ 0 := by
    apply ne_of_gt
    exact prod_pos (fun k _ => by omega)
  exact (Nat.pow_dvd_iff_le_padicValNat (by decide : 7 ≠ 1) hn).mp
    ((hp.dvd_iff (dvd_refl q)).mp hd)

theorem hypergeometricNumerator_valuation_lower (i : Fin 2) (n : ℕ) :
    2 * padicValNat 7 n.factorial ≤ padicValNat 7 (hypergeometricNumerator i n) := by
  have h1 := factorial_valuation_le_progression 12 (1 + 6 * i.val) n (by omega) (by decide)
  have h2 := factorial_valuation_le_progression 12 (5 + 6 * i.val) n (by omega) (by decide)
  have hn1 : (∏ k ∈ range n, (12 * k + (1 + 6 * i.val))) ≠ 0 :=
    ne_of_gt (prod_pos (fun k _ => by omega))
  have hn2 : (∏ k ∈ range n, (12 * k + (5 + 6 * i.val))) ≠ 0 :=
    ne_of_gt (prod_pos (fun k _ => by omega))
  rw [hypergeometricNumerator, prod_mul_distrib]
  simp only [Nat.add_assoc]
  rw [padicValNat.mul hn1 hn2]
  omega

theorem double_factorial_valuation_deficit (i : Fin 2) (n : ℕ) (hn : 0 < n) :
    padicValNat 7 (2 * n + i.val).factorial ≤
      2 * padicValNat 7 n.factorial + Nat.log 7 (12 * n) := by
  let J := Nat.log 7 (12 * n)
  have hi := i.isLt
  have hsmall : Nat.log 7 n < J + 1 :=
    (Nat.log_mono_right (by omega : n ≤ 12 * n)).trans_lt (Nat.lt_succ_self _)
  have hlarge : Nat.log 7 (2 * n + i.val) < J + 1 :=
    (Nat.log_mono_right (by omega : 2 * n + i.val ≤ 12 * n)).trans_lt (Nat.lt_succ_self _)
  rw [padicValNat_factorial hsmall, padicValNat_factorial hlarge]
  have hlevel (j : ℕ) (hj : j ∈ Ico 1 (J + 1)) :
      (2 * n + i.val) / 7 ^ j ≤ 2 * (n / 7 ^ j) + 1 := by
    have hq : 0 < 7 ^ j := pow_pos (by decide) _
    have hmod := Nat.mod_lt n hq
    have he := Nat.div_add_mod n (7 ^ j)
    apply Nat.le_of_lt_succ
    apply (Nat.div_lt_iff_lt_mul hq).mpr
    nlinarith
  calc
    _ ≤ ∑ j ∈ Ico 1 (J + 1), (2 * (n / 7 ^ j) + 1) := sum_le_sum hlevel
    _ = _ := by simp [sum_add_distrib, ← mul_sum, J]

end Zeta7Annulus
