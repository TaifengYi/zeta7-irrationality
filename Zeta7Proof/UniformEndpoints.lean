import Zeta7Proof.SerreEisenstein

/-! Uniform precision endpoints for the existing measure specialization.
The character estimate is uniform on all seven-adic units. The coefficient
estimate includes degree zero and retains the order of quantifiers required
for Serre convergence. -/

set_option autoImplicit false
namespace Zeta7Main
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩
open Filter Topology PowerSeries PadicLFunctions PadicInt

/-- Fermat and integral lifting for every seven-adic unit, not just integers. -/
theorem serre_unit_power_norm (x : ℤ_[7]ˣ) (r : ℕ) :
    ‖(x : ℤ_[7]) ^ (6 * 7 ^ r) - 1‖ ≤ (7 : ℝ) ^ (-(r + 1 : ℕ) : ℤ) := by
  have hx : toZMod (x : ℤ_[7]) ≠ 0 := (x.isUnit.map toZMod).ne_zero
  have hfermat : (7 : ℤ_[7]) ∣ (x : ℤ_[7]) ^ 6 - 1 := by
    apply Ideal.mem_span_singleton.mp
    change _ ∈ Ideal.span {((7 : ℕ) : ℤ_[7])}
    rw [← PadicInt.maximalIdeal_eq_span_p, ← PadicInt.ker_toZMod, RingHom.mem_ker]
    simpa only [map_sub, map_pow, map_one] using
      sub_eq_zero.mpr (ZMod.pow_card_sub_one_eq_one hx)
  have hlift := dvd_sub_pow_of_dvd_sub hfermat r
  apply (PadicInt.norm_le_pow_iff_mem_span_pow _ (r + 1)).mpr
  apply Ideal.mem_span_singleton.mpr
  simpa only [one_pow, ← pow_mul, Nat.cast_ofNat] using hlift

/-- Explicit error bound for the weight-minus-two character on the whole unit group. -/
theorem serre_weight_character_uniform_norm (x : ℤ_[7]ˣ) (r : ℕ) :
    ‖(((x : ℤ_[7]) : ℚ_[7]) ^ serreWeight r) -
      ((((x : ℤ_[7]) : ℚ_[7]) ^ 2)⁻¹)‖ ≤
      (7 : ℝ) ^ (-(r + 1 : ℕ) : ℤ) := by
  have hx0 : ((x : ℤ_[7]) : ℚ_[7]) ≠ 0 := by
    intro h
    apply x.ne_zero
    exact Subtype.coe_injective h
  have hxnorm : ‖((x : ℤ_[7]) : ℚ_[7])‖ = 1 := PadicInt.norm_units x
  have he : serreWeight r + 2 = 6 * 7 ^ r := by
    have := serreWeight_ge_four r
    unfold serreWeight at *
    omega
  have hid : (((x : ℤ_[7]) : ℚ_[7]) ^ serreWeight r) -
      ((((x : ℤ_[7]) : ℚ_[7]) ^ 2)⁻¹) =
      ((((x : ℤ_[7]) : ℚ_[7]) ^ (6 * 7 ^ r)) - 1) *
        ((((x : ℤ_[7]) : ℚ_[7]) ^ 2)⁻¹) := by
    apply mul_right_cancel₀ (pow_ne_zero 2 hx0)
    simp only [sub_mul, mul_assoc, inv_mul_cancel₀ (pow_ne_zero 2 hx0), mul_one]
    rw [← pow_add, he]
  rw [hid, norm_mul, norm_inv, norm_pow, hxnorm, one_pow, inv_one, mul_one]
  rw [← PadicInt.coe_pow, ← PadicInt.coe_one, ← PadicInt.coe_sub]
  exact serre_unit_power_norm x r

/-- The characters converge uniformly, strengthening the earlier pointwise endpoint. -/
theorem serre_weight_characters_tendstoUniformly :
    TendstoUniformly
      (fun r (x : ℤ_[7]ˣ) => (((x : ℤ_[7]) : ℚ_[7]) ^ serreWeight r))
      (fun x => ((((x : ℤ_[7]) : ℚ_[7]) ^ 2)⁻¹)) atTop := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  filter_upwards [seven_precision_bound_tendsto_zero.eventually (gt_mem_nhds hε)]
    with r hr x
  rw [dist_eq_norm']
  exact (serre_weight_character_uniform_norm x r).trans_lt hr

/-- Every coefficient, including zero, is simultaneously accurate to any fixed precision. -/
theorem classical_all_coefficients_all_precisions :
    ∀ M : ℤ, ∃ R : ℕ, ∀ r ≥ R, ∀ n : ℕ,
      (M : WithTop ℤ) ≤
        Padic.addValuation (coeff n (classicalEisensteinSeries r - eisensteinMinusTwo)) := by
  intro M
  have hε : 0 < (7 : ℝ) ^ (-M) := zpow_pos (by norm_num) _
  have h := (Metric.tendstoUniformly_iff.mp classical_eisenstein_tendstoUniformly)
    _ hε
  obtain ⟨R, hR⟩ := eventually_atTop.mp h
  refine ⟨R, fun r hr n => (seven_le_addValuation_iff M _).mpr ?_⟩
  have hbound := hR r hr n
  rw [dist_eq_norm', ← map_sub] at hbound
  exact hbound.le

/-- The original p-stabilised family, using the same weight sequence. -/
noncomputable def stabilisedEisensteinSeries (r : ℕ) : ℚ_[7]⟦X⟧ :=
  mk fun n => (stabilisedCoeff 7 (serreWeight r) n : ℚ_[7])

/-- Uniform error for positive coefficients of the original stabilised sequence. -/
theorem stabilised_nonconstant_uniform_norm (r n : ℕ) (hn : n ≠ 0) :
    ‖coeff n (stabilisedEisensteinSeries r - eisensteinMinusTwo)‖ ≤
      (7 : ℝ) ^ (-(r + 1 : ℕ) : ℤ) := by
  rw [map_sub, stabilisedEisensteinSeries, coeff_mk, eisensteinMinusTwo_coeff hn]
  simp only [stabilisedCoeff, ite_eq_right hn, sigmaP]
  push_cast
  rw [← Finset.sum_sub_distrib]
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
  intro d hd
  exact seven_unit_inverse_cube_error (Finset.mem_filter.mp hd).2 r

/-- Uniform convergence of the p-stabilised coefficients, including degree zero. -/
theorem stabilised_eisenstein_tendstoUniformly :
    TendstoUniformly (fun r n => coeff n (stabilisedEisensteinSeries r))
      (fun n => coeff n eisensteinMinusTwo) atTop := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  have hc : Tendsto
      (fun r => ‖(stabilisedCoeff 7 (serreWeight r) 0 : ℚ_[7]) - eta‖)
      atTop (𝓝 0) := by
    simpa using (serre_stabilised_constant_tendsto_eta.sub
      (tendsto_const_nhds (x := eta))).norm
  filter_upwards [hc.eventually (gt_mem_nhds hε),
    seven_precision_bound_tendsto_zero.eventually (gt_mem_nhds hε)] with r hr hp n
  rw [dist_eq_norm', ← map_sub]
  by_cases hn : n = 0
  · subst n
    simpa only [map_sub, stabilisedEisensteinSeries, coeff_mk,
      coeff_zero_eq_constantCoeff, eisensteinMinusTwo_constant] using hr
  · exact (stabilised_nonconstant_uniform_norm r n hn).trans_lt hp

/-- Strengthening of EisensteinLimit.classical_coefficients_tendsto on its exact indices. -/
theorem original_classical_coefficients_tendstoUniformly :
    TendstoUniformly
      (fun m n => (stabilisedCoeff 7 (interpolationWeight m) n : ℚ_[7]))
      (fun n => coeff n eisensteinMinusTwo) atTop := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  have h := (Metric.tendstoUniformly_iff.mp stabilised_eisenstein_tendstoUniformly) ε hε
  have hs := (tendsto_add_atTop_nat 1).eventually h
  simpa only [stabilisedEisensteinSeries, coeff_mk, serreWeight_succ] using hs

/-- The canonical Lambert-series expression itself has the constructed Serre presentation. -/
theorem target_G_add_eta_isPAdicModularForm :
    PowerSeries.isPAdicModularForm 7
      (GSeries.map (algebraMap ℚ ℚ_[7]) + C eta) := by
  rw [← eisensteinMinusTwo_eq_G_add_eta]
  exact eisensteinMinusTwo_isPAdicModularForm

end Zeta7Main
