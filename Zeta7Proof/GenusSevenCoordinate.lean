import Zeta7Proof.Radius49Compatibility

/-! Gate 1: the normalized discriminant-quotient coordinate, in the coefficient topology.
No convergence on an analytic disc or modular continuation is asserted. -/

set_option autoImplicit false
noncomputable section
namespace Zeta7GenusSeven
open PowerSeries Zeta7Main Filter
open scoped PowerSeries.WithPiTopology Topology
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

theorem euler_multipliable :
    Multipliable (fun n : ℕ => (1 : ℚ⟦X⟧) - X ^ (n + 1)) := by
  simp_rw [sub_eq_add_neg]
  apply WithPiTopology.multipliable_one_add_of_tendsto_order_atTop_nhds_top
  refine ENat.tendsto_nhds_top_iff_natCast_lt.mpr fun n =>
    Filter.eventually_atTop.mpr ⟨n, ?_⟩
  intro m hm
  simp only [order_neg, order_X_pow]
  exact_mod_cast Nat.lt_add_one_of_le hm

def euler : ℚ⟦X⟧ := ∏' n : ℕ, (1 - X ^ (n + 1))
def delta : ℚ⟦X⟧ := X * euler ^ 24

theorem euler_constant : constantCoeff euler = 1 := by
  rw [euler, euler_multipliable.map_tprod
    (constantCoeff : ℚ⟦X⟧ →+* ℚ) (WithPiTopology.continuous_constantCoeff ℚ)]
  simp

theorem continuous_expand_seven : Continuous (expand 7 (by decide) (R := ℚ)) := by
  apply continuous_iff_continuousAt.mpr
  intro f
  apply (WithPiTopology.tendsto_iff_coeff_tendsto ℚ _ _ _).mpr
  intro n
  simp only [coeff_expand]
  split_ifs
  · exact (WithPiTopology.continuous_coeff ℚ (n / 7)).continuousAt
  · exact tendsto_const_nhds

def sevenMultipleIndex : ℕ ≃ {n : ℕ // 7 ∣ n + 1} :=
  Equiv.ofBijective (fun n => ⟨7 * n + 6, by omega⟩) (by
    constructor
    · intro a b h
      have := congrArg Subtype.val h
      dsimp at this
      omega
    · intro n
      obtain ⟨k, hk⟩ := n.property
      refine ⟨k - 1, ?_⟩
      apply Subtype.ext
      dsimp
      omega)

theorem euler_seven_factorization :
    euler = sevenEulerProduct * expand 7 (by decide) euler := by
  classical
  have he : expand 7 (by decide) euler =
      ∏' n : ℕ, (1 - (X : ℚ⟦X⟧) ^ (7 * (n + 1))) := by
    rw [euler, euler_multipliable.map_tprod
      (expand 7 (by decide) (R := ℚ)) continuous_expand_seven]
    apply tprod_congr
    intro n
    simp only [map_sub, map_one, map_pow, expand_X, ← pow_mul]
  have hm : Multipliable (fun n : ℕ => (1 : ℚ⟦X⟧) - X ^ (7 * (n + 1))) := by
    simp_rw [sub_eq_add_neg]
    apply WithPiTopology.multipliable_one_add_of_tendsto_order_atTop_nhds_top
    refine ENat.tendsto_nhds_top_iff_natCast_lt.mpr fun n =>
      Filter.eventually_atTop.mpr ⟨n, ?_⟩
    intro m hm
    simp only [order_neg, order_X_pow]
    exact_mod_cast (show n < 7 * (m + 1) by omega)
  have hr : (∏' n : {n : ℕ // 7 ∣ n + 1}, ((1 : ℚ⟦X⟧) - X ^ (n.val + 1))) =
      ∏' n : ℕ, (1 - (X : ℚ⟦X⟧) ^ (7 * (n + 1))) := by
    rw [← sevenMultipleIndex.tprod_eq]
    apply tprod_congr
    intro n
    change 1 - X ^ (7 * n + 6 + 1) = _
    congr 2
  have hmc : Multipliable
      (fun n : {n : ℕ // 7 ∣ n + 1} => (1 : ℚ⟦X⟧) - X ^ (n.val + 1)) := by
    apply sevenMultipleIndex.multipliable_iff.mp
    convert hm using 1
    funext n
    change 1 - X ^ (7 * n + 6 + 1) = _
    congr 2
  have h := hmc.tprod_mul_tprod_compl
    (f := fun n : ℕ => (1 : ℚ⟦X⟧) - X ^ (n + 1))
    (s := {n : ℕ | 7 ∣ n + 1}) seven_product_multipliable
  rw [he, ← hr, euler, sevenEulerProduct, mul_comm]
  exact h.symm

/-- Normalized eta quotient q*(Euler(q^7)/Euler(q))^4. Its sixth power is Delta(q^7)/Delta(q). -/
def d7 : ℚ⟦X⟧ := X * (expand 7 (by decide) euler * euler⁻¹) ^ 4

theorem euler_quotient :
    expand 7 (by decide) euler * euler⁻¹ = sevenEulerProduct⁻¹ := by
  symm
  apply (PowerSeries.inv_eq_iff_mul_eq_one (by rw [sevenEulerProduct_constant]; norm_num)).mpr
  calc
    _ = (sevenEulerProduct * expand 7 (by decide) euler) * euler⁻¹ := by ring
    _ = euler * euler⁻¹ := by rw [← euler_seven_factorization]
    _ = 1 := PowerSeries.mul_inv_cancel _ (by rw [euler_constant]; norm_num)

theorem d7_eq_xSeries : d7 = xSeries := by
  simp only [d7, euler_quotient, xSeries, xUnit]

theorem d7_constant : constantCoeff d7 = 0 := by rw [d7_eq_xSeries, xSeries_constant]

theorem d7_linear : coeff 1 d7 = 1 := by rw [d7_eq_xSeries, xSeries_linear]

theorem d7_sixth_delta : d7 ^ 6 * delta = expand 7 (by decide) delta := by
  have he := PowerSeries.inv_mul_cancel euler (by rw [euler_constant]; norm_num)
  simp only [d7, delta, map_mul, map_pow, expand_X]
  calc
    _ = X ^ 7 * (expand 7 (by decide) euler) ^ 24 * (euler⁻¹ * euler) ^ 24 := by ring
    _ = _ := by rw [he]; ring

theorem delta_linear : coeff 1 delta = 1 := by
  simp [delta, coeff_zero_eq_constantCoeff, euler_constant]

theorem delta_ne_zero : delta ≠ 0 := by
  intro h
  have := delta_linear
  rw [h, map_zero] at this
  norm_num at this

theorem sixth_power_injective_constant_one (u v : ℚ⟦X⟧)
    (hu : constantCoeff u = 1) (hv : constantCoeff v = 1) (h : u ^ 6 = v ^ 6) : u = v := by
  let s := u ^ 5 + u ^ 4 * v + u ^ 3 * v ^ 2 + u ^ 2 * v ^ 3 + u * v ^ 4 + v ^ 5
  have hs : constantCoeff s = 6 := by simp [s, hu, hv]; norm_num
  have hs0 : s ≠ 0 := by
    intro he
    rw [he, map_zero] at hs
    norm_num at hs
  have hm : (u - v) * s = 0 := by
    calc
      _ = u ^ 6 - v ^ 6 := by dsimp [s]; ring
      _ = 0 := sub_eq_zero.mpr h
  exact sub_eq_zero.mp ((mul_eq_zero.mp hm).resolve_right hs0)

/-- Uniqueness of the normalized sixth root; this is an all-degree formal argument. -/
theorem d7_unique (f : ℚ⟦X⟧) (hf0 : constantCoeff f = 0) (hf1 : coeff 1 f = 1)
    (hfdelta : f ^ 6 * delta = expand 7 (by decide) delta) : f = d7 := by
  have hp : f ^ 6 = d7 ^ 6 := mul_right_cancel₀ delta_ne_zero
    (hfdelta.trans d7_sixth_delta.symm)
  obtain ⟨u, hu⟩ := X_dvd_iff.mpr hf0
  have hu0 : constantCoeff u = 1 := by
    simpa [hu, coeff_zero_eq_constantCoeff] using hf1
  rw [hu, d7_eq_xSeries, xSeries, mul_pow, mul_pow] at hp
  have huv : u = xUnit := sixth_power_injective_constant_one u xUnit hu0 xUnit_constant
    (mul_left_cancel₀ (pow_ne_zero 6 (X_ne_zero (R := ℚ))) hp)
  rw [hu, huv, d7_eq_xSeries, xSeries]

/-- The annulus normalization substitutes x=t/49; there is no additional eta-quotient scale. -/
theorem normalisedHSeries_exact_scale (n : ℕ) :
    coeff n normalisedHSeries = (49 : ℚ_[7]) ^ (-(n : ℤ)) * coeff n HSeries :=
  Zeta7Radius49.normalisedHSeries_coeff_zpow n

theorem d7_subst_q : d7.subst qSeries = X := by rw [d7_eq_xSeries, x_subst_q]

theorem q_subst_d7 : qSeries.subst d7 = X := by rw [d7_eq_xSeries, q_subst_x]

def t7 : ℚ⟦X⟧ := C 49 * d7

theorem t7_eq_scaled_xSeries : t7 = C 49 * xSeries := by rw [t7, d7_eq_xSeries]

theorem t7_subst_q : t7.subst qSeries = C 49 * X := by
  rw [t7, subst_mul (HasSubst.of_constantCoeff_zero' qSeries_constant), subst_C, d7_subst_q]
  rfl

theorem oppositeH_exact_scale (n : ℕ) :
    oppositeH (-(n : ℤ)) = (49 : ℚ_[7]) ^ (-(n : ℤ)) * coeff n HSeries := by
  rw [oppositeH_nonpositive_coeff, zpow_neg, zpow_natCast, inv_pow]

end Zeta7GenusSeven
