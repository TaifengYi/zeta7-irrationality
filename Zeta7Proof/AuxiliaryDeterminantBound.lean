import Zeta7Proof.AuxiliaryCaps
import Zeta7Proof.AuxiliaryThresholdCount

/-! Direct four-layer determinant bound, valid also when entries or determinants vanish. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
namespace Zeta7Auxiliary
variable {p : ℕ} [Fact p.Prime]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem integral_scale_mono {z : ℚ_[p]} {e f : ℕ}
    (h : Integral ((p : ℚ_[p]) ^ e * z)) (hef : e ≤ f) :
    Integral ((p : ℚ_[p]) ^ f * z) := by
  have hh := ((integral_nat (p := p) p).pow (f - e)).mul h
  simpa only [← mul_assoc, ← pow_add, Nat.sub_add_cancel hef] using hh

theorem determinant_four_caps (A : Matrix ι ι ℚ_[p]) (bad : Finset ι) (e : ι → ℕ)
    (he : ∀ j, e j ≤ 4) (hcap : ∀ i j, Integral ((p : ℚ_[p]) ^ e j * A i j))
    (hgood : ∀ i, i ∉ bad → ∀ j, Integral (A i j)) :
    Integral ((p : ℚ_[p]) ^ thresholdMass bad.card e * A.det) := by
  classical
  rw [Matrix.det_apply, Finset.mul_sum]
  apply integral_sum
  intro π _
  let s := Finset.univ.filter (fun j => π j ∈ bad)
  let f : ι → ℕ := fun j => if π j ∈ bad then e j else 0
  have hs : (∑ j, f j) = ∑ j ∈ s, e j := by
    simp only [f, s, Finset.sum_filter]
  have hsum : (∑ j, f j) ≤ thresholdMass bad.card e := by
    rw [hs]
    have hb := sum_caps_le_thresholdMass e he s
    simpa only [s, permutation_bad_card] using hb
  have hprod : Integral ((p : ℚ_[p]) ^ (∑ j, f j) * ∏ j, A (π j) j) := by
    rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
    apply integral_prod
    intro j _
    dsimp [f]
    split_ifs with hj
    · exact hcap (π j) j
    · simpa only [pow_zero, one_mul] using hgood (π j) hj j
  have hb := integral_scale_mono hprod hsum
  change ‖(p : ℚ_[p]) ^ thresholdMass bad.card e * (Equiv.Perm.sign π • ∏ j, A (π j) j)‖ ≤ 1
  rw [mul_smul_comm, norm_units_zsmul]
  exact hb

/-- Nonvanishing is required only at this conversion to the totalized valuation. -/
theorem scaled_integral_valuation {q : ℚ} (hq : q ≠ 0) (T : ℕ)
    (h : Integral ((p : ℚ_[p]) ^ T * (q : ℚ_[p]))) :
    -(padicValRat p q) ≤ (T : ℤ) := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hq0 : (q : ℚ_[p]) ≠ 0 := by exact_mod_cast hq
  have hh := (Padic.norm_le_one_iff_val_nonneg _).mp h
  rw [Padic.valuation_mul (pow_ne_zero _ hp0) hq0, Padic.valuation_pow,
    Padic.valuation_natCast, padicValNat_self,
    Padic.valuation_ratCast] at hh
  omega

end Zeta7Auxiliary
