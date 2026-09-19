import Zeta7Proof.AnnulusRepresentation

/-! Unconditional q-expansion estimates and the formal U_7 eigenidentity.
These estimates concern q, not the continued scalar x-coordinate function. -/

set_option autoImplicit false
noncomputable section
namespace Zeta7Main
open Filter Topology PowerSeries PadicInt
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

theorem seven_free_divisors_mul_seven (n : ℕ) :
    (7 * n).divisors.filter (fun d => ¬ 7 ∣ d) =
      n.divisors.filter (fun d => ¬ 7 ∣ d) := by
  ext d
  by_cases hd : 7 ∣ d
  · simp [hd]
  · have hc : Nat.Coprime d 7 :=
      ((Nat.Prime.coprime_iff_not_dvd (by decide : Nat.Prime 7)).mpr hd).symm
    simp only [Finset.mem_filter, Nat.mem_divisors, hc.dvd_mul_left,
      mul_ne_zero_iff, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, true_and]

/-- All-degree coefficient identity, including the genuine constant. -/
theorem eisensteinMinusTwo_coeff_seven_mul (n : ℕ) :
    coeff (7 * n) eisensteinMinusTwo = coeff n eisensteinMinusTwo := by
  by_cases hn : n = 0
  · simp [hn]
  · rw [eisensteinMinusTwo_coeff (by omega), eisensteinMinusTwo_coeff hn,
      seven_free_divisors_mul_seven]

/-- Coefficient extraction only; no analytic Hecke correspondence is asserted. -/
def qExpansionUSeven (f : ℚ_[7]⟦X⟧) : ℚ_[7]⟦X⟧ :=
  mk (fun n => coeff (7 * n) f)

theorem qExpansionUSeven_eisenstein :
    qExpansionUSeven eisensteinMinusTwo = eisensteinMinusTwo := by
  ext n
  simpa only [qExpansionUSeven, coeff_mk] using eisensteinMinusTwo_coeff_seven_mul n

theorem eisensteinMinusTwo_coeff_one : coeff 1 eisensteinMinusTwo = 1 := by
  rw [eisensteinMinusTwo_coeff (by decide)]
  norm_num [Finset.sum_filter]

theorem eisensteinMinusTwo_coeff_seven_pow (r : ℕ) :
    coeff (7 ^ r) eisensteinMinusTwo = 1 := by
  induction r with
  | zero => simpa using eisensteinMinusTwo_coeff_one
  | succ r ih =>
    rw [pow_succ, Nat.mul_comm, eisensteinMinusTwo_coeff_seven_mul, ih]

/-- The q-expansion does not converge on any Gauss circle of radius at least one.
This prevents confusing modular overconvergence with enlarging the q-disc. -/
theorem eisensteinMinusTwo_q_not_weighted_decay (ρ : ℝ) (hρ : 1 ≤ ρ) :
    ¬ Tendsto (fun n => ‖coeff n eisensteinMinusTwo‖ * ρ ^ n) atTop (𝓝 0) := by
  intro h
  obtain ⟨R, hR⟩ := eventually_atTop.mp
    (h.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)))
  have hp : ∀ r : ℕ, r ≤ 7 ^ r := by
    intro r
    induction r with
    | zero => norm_num
    | succ r ih =>
      rw [pow_succ]
      have : 0 < 7 ^ r := pow_pos (by decide) _
      omega
  have hbad := hR (7 ^ R) (hp R)
  rw [eisensteinMinusTwo_coeff_seven_pow, norm_one, one_mul] at hbad
  have hone : (1 : ℝ) ≤ ρ ^ (7 ^ R) := one_le_pow₀ hρ
  linarith

theorem eisensteinMinusTwo_nonconstant_norm (n : ℕ) (hn : n ≠ 0) :
    ‖coeff n eisensteinMinusTwo‖ ≤ 1 := by
  rw [eisensteinMinusTwo_coeff hn]
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one
  intro d hd
  have hc := ((Nat.Prime.coprime_iff_not_dvd
    (by decide : Nat.Prime 7)).mpr (Finset.mem_filter.mp hd).2)
  rw [norm_inv, norm_pow, Padic.norm_natCast_eq_one_iff.mpr hc, one_pow, inv_one]

theorem eisensteinMinusTwo_all_coefficients_norm (n : ℕ) :
    ‖coeff n eisensteinMinusTwo‖ ≤ max ‖eta‖ 1 := by
  by_cases hn : n = 0
  · subst n
    simpa only [coeff_zero_eq_constantCoeff, eisensteinMinusTwo_constant] using
      le_max_left ‖eta‖ 1
  · exact (eisensteinMinusTwo_nonconstant_norm n hn).trans (le_max_right _ _)

/-- Ordinary q-disc convergence. This is not the radius-49 continuation in x. -/
theorem eisensteinMinusTwo_q_weighted_decay (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    Tendsto (fun n => ‖coeff n eisensteinMinusTwo‖ * ρ ^ n) atTop (𝓝 0) := by
  have hp : Tendsto (fun n : ℕ => ρ ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1
  apply squeeze_zero (fun n => mul_nonneg (norm_nonneg _) (pow_nonneg hρ0 n))
    (fun n => mul_le_mul_of_nonneg_right (eisensteinMinusTwo_all_coefficients_norm n)
      (pow_nonneg hρ0 n))
  simpa using hp.const_mul (max ‖eta‖ 1)

theorem eisensteinMinusTwo_q_summable (q : ℚ_[7]) (hq : ‖q‖ < 1) :
    Summable (fun n => coeff n eisensteinMinusTwo * q ^ n) := by
  apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simpa only [norm_mul, norm_pow, Nat.cofinite_eq_atTop] using
    eisensteinMinusTwo_q_weighted_decay ‖q‖ (norm_nonneg q) hq

theorem eisensteinMinusTwo_q_hasGaussNorm (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    HasGaussNorm (norm : ℚ_[7] → ℝ) ρ eisensteinMinusTwo := by
  refine ⟨max ‖eta‖ 1, ?_⟩
  rintro _ ⟨n, rfl⟩
  exact (mul_le_mul_of_nonneg_right (eisensteinMinusTwo_all_coefficients_norm n)
    (pow_nonneg hρ0 n)).trans
    (mul_le_of_le_one_right (le_trans zero_le_one (le_max_right _ _))
      (pow_le_one₀ hρ0 hρ1))

end Zeta7Main
