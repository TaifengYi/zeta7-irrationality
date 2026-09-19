import Mathlib

/-! A rational product formula with explicit, finite prime support.
The three contributions all come from the same nonzero rational number. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Zeta7ProductFormula

/-- An explicit bound containing every prime in the numerator and denominator. -/
def primeBound (q : ℚ) : ℕ := max q.num.natAbs q.den + 8

def primeSupport (q : ℚ) : Finset ℕ :=
  (Finset.range (primeBound q)).filter Nat.Prime

def arch (q : ℚ) : ℝ := Real.log |(q : ℝ)|

def localTerm (p : ℕ) (q : ℚ) : ℝ :=
  -(padicValRat p q : ℝ) * Real.log p

def target (q : ℚ) : ℝ := localTerm 7 q

def auxiliary (q : ℚ) : ℝ :=
  ∑ p ∈ (primeSupport q).erase 7, localTerm p q

theorem localTerm_eq_log_norm (p : ℕ) [Fact p.Prime] (q : ℚ) (hq : q ≠ 0) :
    localTerm p q = Real.log ‖(q : ℚ_[p])‖ := by
  rw [Padic.norm_eq_zpow_neg_valuation (by exact_mod_cast hq), Real.log_zpow,
    Padic.valuation_ratCast]
  simp [localTerm]

theorem log_nat_factorization (n m : ℕ) (hn : n ≠ 0) (hm : n < m) :
    Real.log (n : ℝ) =
      ∑ p ∈ (Finset.range m).filter Nat.Prime,
        (padicValNat p n : ℝ) * Real.log p := by
  have hprod := Nat.prod_pow_prime_padicValNat n hn m hm
  have hp : (∏ p ∈ (Finset.range m).filter Nat.Prime,
      (p : ℝ) ^ padicValNat p n) = n := by exact_mod_cast hprod
  rw [← hp, Real.log_prod]
  · simp only [Real.log_pow]
  · intro p hp
    exact pow_ne_zero _ (by exact_mod_cast (Finset.mem_filter.mp hp).2.ne_zero)

theorem log_rat_factorization (q : ℚ) (hq : q ≠ 0) :
    arch q = ∑ p ∈ primeSupport q, (padicValRat p q : ℝ) * Real.log p := by
  have hn : q.num.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (Rat.num_ne_zero.mpr hq)
  have hb₁ : q.num.natAbs < primeBound q := by
    unfold primeBound
    omega
  have hb₂ : q.den < primeBound q := by
    unfold primeBound
    omega
  have heq : |(q : ℝ)| = (q.num.natAbs : ℝ) / (q.den : ℝ) := by
    simp [Rat.cast_def, abs_div]
  rw [arch, heq, Real.log_div (by exact_mod_cast hn) (by exact_mod_cast q.den_ne_zero),
    log_nat_factorization _ _ hn hb₁,
    log_nat_factorization _ _ q.den_ne_zero hb₂, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  simp only [padicValRat, padicValInt, Int.cast_sub, Int.cast_natCast]
  ring

theorem seven_mem_primeSupport (q : ℚ) : 7 ∈ primeSupport q := by
  simp only [primeSupport, Finset.mem_filter, Finset.mem_range]
  exact ⟨by unfold primeBound; omega, by decide⟩

/-- The logarithmic product formula, split into infinity, seven, and all other primes. -/
theorem productFormula (q : ℚ) (hq : q ≠ 0) :
    arch q + target q + auxiliary q = 0 := by
  have hsum := Finset.sum_erase_add (primeSupport q) (localTerm · q)
    (seven_mem_primeSupport q)
  have hall : (∑ p ∈ primeSupport q, localTerm p q) = -arch q := by
    rw [log_rat_factorization q hq, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    simp [localTerm]
  unfold target auxiliary
  linarith

/-- All omitted prime contributions vanish, so the finite sum includes every place. -/
theorem localTerm_eq_zero_outside (q : ℚ) (p : ℕ) (hp : p.Prime)
    (hout : p ∉ primeSupport q) : localTerm p q = 0 := by
  have hb : primeBound q ≤ p := by
    simpa [primeSupport, hp] using hout
  have hn : padicValNat p q.num.natAbs = 0 := by
    apply padicValNat.eq_zero_iff.mpr
    by_cases hzero : q.num.natAbs = 0
    · exact Or.inr (Or.inl hzero)
    · exact Or.inr (Or.inr (by
        intro hd
        have := Nat.le_of_dvd (Nat.pos_of_ne_zero hzero) hd
        unfold primeBound at hb
        omega))
  have hd : padicValNat p q.den = 0 := by
    apply padicValNat.eq_zero_of_not_dvd
    intro hd
    have := Nat.le_of_dvd q.den_pos hd
    unfold primeBound at hb
    omega
  simp [localTerm, padicValRat, padicValInt, hn, hd]

end Zeta7ProductFormula
