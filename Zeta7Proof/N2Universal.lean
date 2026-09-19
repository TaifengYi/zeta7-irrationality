import Zeta7Proof.N2InfinityRiccati
import Zeta7Proof.GermResidueCalculus
import Zeta7Proof.N1Universal

/-! Rational Riccati exclusion by an algebraic residue-sum contradiction. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
open scoped RatFunc LaurentSeries
open PowerSeries
namespace Zeta7Germ

theorem actual_rho_local_nonzero (u : RatFunc ℂ) (a : ℂ) (ha : a ≠ 0) :
    localExpansion a (riccatiRho u) =
      localExpansion a u * (((shiftedX a)⁻¹ : ℂ⟦X⟧) : ℂ⸨X⸩) := by
  have hd : constantCoeff (shiftedX a) ≠ 0 := by simpa [shiftedX] using ha
  rw [coe_powerSeries_inv _ hd]
  simp [riccatiRho, localExpansion_X, div_eq_mul_inv]

theorem actual_rho_zero_coeff (u : RatFunc ℂ) (n : ℤ) :
    (localExpansion 0 (riccatiRho u)).coeff n = (localExpansion 0 u).coeff (n + 1) := by
  simp [riccatiRho, localExpansion_X, shiftedX, div_eq_mul_inv,
    HahnSeries.inv_single, HahnSeries.coeff_mul_single]

theorem actual_rho_zero_regular (u : RatFunc ℂ) (he : riccati u = 0) :
    lowerBound (localExpansion 0 (riccatiRho u)) 0 := by
  intro k hk
  rw [actual_rho_zero_coeff]
  by_cases hk1 : k + 1 < 0
  · exact actual_riccati_zero_regular u he _ hk1
  · have : k + 1 = 0 := by omega
    rw [this]
    exact actual_riccati_zero_constant u he

theorem actual_rho_local_bound (u : RatFunc ℂ) (he : riccati u = 0) (a : ℂ) :
    lowerBound (localExpansion a (riccatiRho u)) (-1) := by
  by_cases ha : a = 0
  · subst a
    intro k hk
    exact actual_rho_zero_regular u he k (by omega)
  · rw [actual_rho_local_nonzero u a ha]
    simpa using lowerBound_mul (actual_riccati_local_bound u he a)
      (lowerBound_powerSeries ((shiftedX a)⁻¹))

theorem actual_rho_residue (u : RatFunc ℂ) (he : riccati u = 0) (a : ℂ) (ha : a ≠ 0) :
    residue a (riccatiRho u) = (localExpansion a u).coeff (-1) / a := by
  rw [residue, actual_rho_local_nonzero u a ha]
  have hm := lowerBound_mul_leading (actual_riccati_local_bound u he a)
    (lowerBound_powerSeries ((shiftedX a)⁻¹))
  simpa [PowerSeries.coeff_coe, PowerSeries.coeff_zero_eq_constantCoeff,
    shiftedX, div_eq_mul_inv] using hm

theorem actual_rho_residue_nonneg (u : RatFunc ℂ) (he : riccati u = 0) (a : ℂ) :
    0 ≤ (residue a (riccatiRho u)).re := by
  by_cases ha : a = 0
  · subst a
    have hz : residue 0 (riccatiRho u) = 0 := actual_rho_zero_regular u he (-1) (by norm_num)
    simp [hz]
  · rw [actual_rho_residue u he a ha]
    by_cases hp : 1 + 13 * a + 49 * a ^ 2 = 0
    · rcases actual_riccati_root_residue u he a hp with h | h | h <;> rw [h] <;> norm_num
    · rcases actual_riccati_ordinary_residue u he a ha hp with h | h | h <;> rw [h] <;> norm_num

theorem actual_rho_root_residue_pos (u : RatFunc ℂ) (he : riccati u = 0) (a : ℂ)
    (ha : 1 + 13 * a + 49 * a ^ 2 = 0) : 0 < (residue a (riccatiRho u)).re := by
  rw [actual_rho_residue u he a (singular_root_algebra a ha).1]
  rcases actual_riccati_root_residue u he a ha with h | h | h <;> rw [h] <;> norm_num

theorem no_rational_riccati_solution (u : RatFunc ℂ) : riccati u ≠ 0 := by
  classical
  intro he
  have hsum := residue_sum_eq_zero (riccatiRho u) (actual_rho_local_bound u he)
    (actual_rho_infinity_decay u he)
  obtain ⟨a, b, hab, ha, hb⟩ := polynomialP_two_roots
  have hpos := actual_rho_root_residue_pos u he a ha
  have hmem : a ∈ finitePoles (riccatiRho u) := by
    by_contra hn
    rw [residue_zero_outside_finitePoles _ _ hn] at hpos
    norm_num at hpos
  have hsumpos : 0 < ∑ a ∈ finitePoles (riccatiRho u), (residue a (riccatiRho u)).re := by
    apply Finset.sum_pos'
    · intro a _
      exact actual_rho_residue_nonneg u he a
    · exact ⟨a, hmem, hpos⟩
  have hzero := congrArg Complex.reAddGroupHom hsum
  simp only [map_sum, map_zero, Complex.coe_reAddGroupHom] at hzero
  rw [hzero] at hsumpos
  exact lt_irrefl _ hsumpos

end Zeta7Germ
