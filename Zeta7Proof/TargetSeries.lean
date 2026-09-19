import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.Derivative
import Zeta7Proof.KubotaLeopoldt

/-! Exact formal coordinates and Lambert coefficients. The infinite product
uses the coefficient topology. No analytic continuation is asserted. -/

set_option autoImplicit false

namespace Zeta7Main
open PowerSeries
open scoped PowerSeries.WithPiTopology
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

noncomputable def eta : ℚ_[7] := zeta7Three / 2

/-- Indices shifted by one ensure every product factor has positive degree. -/
abbrev SevenProductIndex := {n : ℕ // ¬ 7 ∣ n + 1}

theorem seven_product_multipliable :
    Multipliable (fun n : SevenProductIndex => (1 : ℚ⟦X⟧) - X ^ (n.val + 1)) := by
  classical
  apply (multipliable_subtype_iff_mulIndicator
    (f := fun n : ℕ => (1 : ℚ⟦X⟧) - X ^ (n + 1))
    (s := {n : ℕ | ¬ 7 ∣ n + 1})).mpr
  have h : Multipliable (fun n : ℕ => (1 : ℚ⟦X⟧) +
      (if ¬ 7 ∣ n + 1 then -(X ^ (n + 1)) else 0)) := by
    apply WithPiTopology.multipliable_one_add_of_tendsto_order_atTop_nhds_top
    refine ENat.tendsto_nhds_top_iff_natCast_lt.mpr fun n =>
      Filter.eventually_atTop.mpr ⟨n, ?_⟩
    intro m hm
    by_cases hd : 7 ∣ m + 1
    · simp [hd]
    · simp only [hd, not_false_eq_true, ite_true, order_neg, order_X_pow]
      exact_mod_cast Nat.lt_add_one_of_le hm
  convert h using 1
  funext n
  by_cases hd : 7 ∣ n + 1 <;> simp [Set.mulIndicator, hd, sub_eq_add_neg]

/-- The standard Euler product over positive indices prime to seven. -/
noncomputable def sevenEulerProduct : ℚ⟦X⟧ :=
  ∏' n : SevenProductIndex, (1 - X ^ (n.val + 1))

theorem sevenEulerProduct_constant : constantCoeff sevenEulerProduct = 1 := by
  rw [sevenEulerProduct, seven_product_multipliable.map_tprod
    (constantCoeff : ℚ⟦X⟧ →+* ℚ) (WithPiTopology.continuous_constantCoeff ℚ)]
  simp

/-- Taking the inverse fourth power of the convergent formal Euler product. -/
noncomputable def xUnit : ℚ⟦X⟧ := sevenEulerProduct⁻¹ ^ 4
noncomputable def xSeries : ℚ⟦X⟧ := X * xUnit

theorem xUnit_constant : constantCoeff xUnit = 1 := by
  simp [xUnit, sevenEulerProduct_constant]

theorem xSeries_constant : constantCoeff xSeries = 0 := by simp [xSeries]
theorem xSeries_linear : coeff 1 xSeries = 1 := by
  simpa [xSeries, coeff_zero_eq_constantCoeff] using xUnit_constant

/-- Recursive compositional inverse, justified by the unit linear coefficient. -/
noncomputable def qSeries : ℚ⟦X⟧ :=
  xSeries.substInvOfIsUnit (xSeries_linear ▸ isUnit_one)

theorem x_subst_q : xSeries.subst qSeries = X :=
  subst_substInvOfIsUnit_right _ xSeries_constant _
theorem q_subst_x : qSeries.subst xSeries = X :=
  subst_substInvOfIsUnit_left _ xSeries_constant _
theorem qSeries_constant : constantCoeff qSeries = 0 := by simp [qSeries]

/-- Euler logarithmic derivative of X*u is 1+X*u'/u. -/
noncomputable def ASeries : ℚ⟦X⟧ := 1 + X * derivative ℚ xUnit * xUnit⁻¹
noncomputable def BSeries : ℚ⟦X⟧ := ASeries.subst qSeries

/-- A Lambert summand, with its formal geometric denominator. -/
noncomputable def lambertTerm (a : ℕ) : ℚ⟦X⟧ :=
  C ((a : ℚ) ^ 3)⁻¹ * (X ^ a * (1 - X ^ a)⁻¹)

/-- Finite divisor sum; zero at index zero by Nat.divisors_zero. -/
noncomputable def GCoeff (n : ℕ) : ℚ :=
  ∑ a ∈ n.divisors.filter (fun a => ¬ 7 ∣ a), ((a : ℚ) ^ 3)⁻¹

noncomputable def GSeries : ℚ⟦X⟧ := mk GCoeff

theorem GSeries_coeff (n : ℕ) : coeff n GSeries =
    ∑ a ∈ n.divisors.filter (fun a => ¬ 7 ∣ a), ((a : ℚ) ^ 3)⁻¹ := by
  simp [GSeries, GCoeff]

theorem GSeries_constant : constantCoeff GSeries = 0 := by
  simp [GSeries, GCoeff, constantCoeff_mk]

theorem geometric_inverse (a : ℕ) (ha : a ≠ 0) :
    (1 - (X : ℚ⟦X⟧) ^ a)⁻¹ = (mk 1 : ℚ⟦X⟧).expand a ha := by
  apply (inv_eq_iff_mul_eq_one (by simp [ha])).mpr
  have h := congrArg (expand a ha (R := ℚ)) (mk_one_mul_one_sub_eq_one ℚ)
  simpa only [map_mul, map_sub, map_one, expand_X] using h

theorem lambertTerm_coeff (a n : ℕ) (ha : a ≠ 0) :
    coeff n (lambertTerm a) =
      if n ≠ 0 ∧ a ∣ n then ((a : ℚ) ^ 3)⁻¹ else 0 := by
  have hgeom : (X : ℚ⟦X⟧) ^ a * (1 - X ^ a)⁻¹ = (1 - X ^ a)⁻¹ - 1 := by
    have h := PowerSeries.mul_inv_cancel (1 - (X : ℚ⟦X⟧) ^ a) (by simp [ha])
    linear_combination -h
  rw [lambertTerm, hgeom, coeff_C_mul, geometric_inverse a ha, map_sub,
    coeff_expand, coeff_mk]
  by_cases hn : n = 0
  · subst n; simp
  · by_cases had : a ∣ n <;> simp [hn, had, coeff_one]

/-- A coefficient of the infinite Lambert sum uses only divisors of its index. -/
theorem GSeries_coeff_lambert (n : ℕ) :
    coeff n GSeries =
      ∑ a ∈ n.divisors.filter (fun a => ¬ 7 ∣ a), coeff n (lambertTerm a) := by
  rw [GSeries_coeff]
  refine Finset.sum_congr rfl fun a ha => ?_
  have hd := Nat.mem_divisors.mp (Finset.mem_filter.mp ha).1
  rw [lambertTerm_coeff a n (ne_zero_of_dvd_ne_zero hd.2 hd.1),
    if_pos ⟨hd.2, hd.1⟩]

/-- The displayed infinite Lambert sum exists and equals the divisor series,
in the coefficient topology, in every degree. -/
theorem GSeries_hasSum_lambert :
    HasSum (fun a : ℕ => if ¬ 7 ∣ a then lambertTerm a else 0) GSeries := by
  classical
  apply (WithPiTopology.hasSum_iff_hasSum_coeff ℚ).mpr
  intro n
  have hfin : HasSum (fun a : ℕ => coeff n (if ¬ 7 ∣ a then lambertTerm a else 0))
      (∑ a ∈ n.divisors.filter (fun a => ¬ 7 ∣ a),
        coeff n (if ¬ 7 ∣ a then lambertTerm a else 0)) := by
    apply hasSum_sum_of_ne_finset_zero
    intro a ha
    by_cases h7 : 7 ∣ a
    · simp [h7]
    · have ha0 : a ≠ 0 := by intro h; subst a; exact h7 (dvd_zero 7)
      have hnot : ¬ (n ≠ 0 ∧ a ∣ n) := by
        intro h
        exact ha (Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨h.2, h.1⟩, h7⟩)
      simp [h7, lambertTerm_coeff a n ha0, hnot]
  have heq : (∑ a ∈ n.divisors.filter (fun a => ¬ 7 ∣ a),
        coeff n (if ¬ 7 ∣ a then lambertTerm a else 0)) = coeff n GSeries := by
    rw [GSeries_coeff_lambert]
    apply Finset.sum_congr rfl
    intro a ha
    rw [if_pos (Finset.mem_filter.mp ha).2]
  rw [heq] at hfin
  exact hfin

theorem GSeries_eq_lambert_tsum :
    GSeries = ∑' a : ℕ, if ¬ 7 ∣ a then lambertTerm a else 0 :=
  GSeries_hasSum_lambert.tsum_eq.symm

/-- The defining Euler logarithmic derivative, with division cleared. -/
theorem ASeries_mul_xSeries : ASeries * xSeries = X * derivative ℚ xSeries := by
  have hu := PowerSeries.inv_mul_cancel xUnit (by rw [xUnit_constant]; norm_num)
  simp only [ASeries, xSeries, Derivation.leibniz, derivative_X, smul_eq_mul]
  calc
    _ = X * xUnit + X ^ 2 * derivative ℚ xUnit * (xUnit⁻¹ * xUnit) := by ring
    _ = _ := by rw [hu]; ring

/-- Coercion to the seven-adic coefficient field happens after rational substitution. -/
noncomputable def HSeries : ℚ_[7]⟦X⟧ :=
  BSeries.map (algebraMap ℚ ℚ_[7]) *
    ((GSeries.subst qSeries).map (algebraMap ℚ ℚ_[7]) + C eta)

end Zeta7Main
