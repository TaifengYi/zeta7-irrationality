import Zeta7Proof.ActualRootLocalData

/-! Finite-pole exclusion for the original rational operator. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
open scoped LaurentSeries RatFunc
open PowerSeries
namespace Zeta7Germ

theorem lowerBound_powerSeries (f : ℂ⟦X⟧) : lowerBound (f : ℂ⸨X⸩) 0 := by
  simpa using lowerBound_shifted_powerSeries f 0

theorem lowerBound_powerSeries_one (f : ℂ⟦X⟧) (hf : constantCoeff f = 0) :
    lowerBound (f : ℂ⸨X⸩) 1 := by
  intro k hk
  by_cases h : k < 0
  · exact lowerBound_powerSeries f k h
  · have : k = 0 := by omega
    subst k
    simpa [PowerSeries.coeff_coe, coeff_zero_eq_constantCoeff] using hf

def translatedP (a : ℂ) : ℂ⟦X⟧ :=
  1 + C 13 * shiftedX a + C 49 * shiftedX a ^ 2

theorem translatedP_constant (a : ℂ) :
    constantCoeff (translatedP a) = 1 + 13 * a + 49 * a ^ 2 := by
  simp [translatedP, shiftedX]

theorem localExpansion_P (a : ℂ) :
    localExpansion a P = (translatedP a : ℂ⸨X⸩) := by
  simp [P, translatedP, localExpansion_X, map_ofNat]

def regularV (a : ℂ) : ℂ⟦X⟧ := rootNumerator a * (translatedP a)⁻¹ ^ 2
def regularR (a : ℂ) : ℂ⟦X⟧ :=
  shiftedX a * (1 + C 10 * shiftedX a) * (translatedP a)⁻¹

theorem localExpansion_V_regular (a : ℂ) (ha : 1 + 13 * a + 49 * a ^ 2 ≠ 0) :
    localExpansion a V = (regularV a : ℂ⸨X⸩) := by
  have hd : constantCoeff (translatedP a) ≠ 0 := by rwa [translatedP_constant]
  simp [V, regularV, rootNumerator, localExpansion_P, localExpansion_X,
    coe_powerSeries_inv _ hd, map_ofNat, div_eq_mul_inv, inv_pow]

theorem localExpansion_R_regular (a : ℂ) (ha : 1 + 13 * a + 49 * a ^ 2 ≠ 0) :
    localExpansion a R = (regularR a : ℂ⸨X⸩) := by
  have hd : constantCoeff (translatedP a) ≠ 0 := by rwa [translatedP_constant]
  simp [R, regularR, localExpansion_P, localExpansion_X,
    coe_powerSeries_inv _ hd, map_ofNat, div_eq_mul_inv]

theorem actual_V_regular_lowerBound (a : ℂ)
    (ha : 1 + 13 * a + 49 * a ^ 2 ≠ 0) : lowerBound (localExpansion a V) 0 := by
  rw [localExpansion_V_regular a ha]
  exact lowerBound_powerSeries _

theorem actual_R_regular_lowerBound (a : ℂ)
    (ha : 1 + 13 * a + 49 * a ^ 2 ≠ 0) : lowerBound (localExpansion a R) 0 := by
  rw [localExpansion_R_regular a ha]
  exact lowerBound_powerSeries _

theorem actual_V_zero_lowerBound : lowerBound (localExpansion 0 V) 1 := by
  rw [localExpansion_V_regular 0 (by norm_num)]
  apply lowerBound_powerSeries_one
  simp [regularV, rootNumerator, shiftedX]

theorem actual_R_zero_lowerBound : lowerBound (localExpansion 0 R) 1 := by
  rw [localExpansion_R_regular 0 (by norm_num)]
  apply lowerBound_powerSeries_one
  simp [regularR, shiftedX]

theorem localExpansion_polynomial_lowerBound (a : ℂ) (p : Polynomial ℂ) :
    lowerBound (localExpansion a (p : RatFunc ℂ)) 0 := by
  rw [localExpansion_polynomial, embed_polynomial]
  exact lowerBound_powerSeries _

theorem localExpansion_L (a : ℂ) (f : RatFunc ℂ) :
    localExpansion a (L f) = localL a (localExpansion a V) (localExpansion a f) := by
  simp [L, localL, localExpansion_rationalD, map_ofNat]

theorem actual_L_no_finite_pole (a : ℂ) (f : RatFunc ℂ) (h : Polynomial ℂ)
    {n : ℤ} (hn : n < 0) (hf : lowerBound (localExpansion a f) n)
    (hlead : (localExpansion a f).coeff n ≠ 0) : L f ≠ (h : RatFunc ℂ) * R := by
  intro he
  have he' := congrArg (localExpansion a) he
  rw [localExpansion_L, map_mul] at he'
  have hh := localExpansion_polynomial_lowerBound a h
  by_cases ha : a = 0
  · subst a
    exact localL_zero_pole_excluded hn hf hlead actual_V_zero_lowerBound
      (by simpa using lowerBound_mul hh actual_R_zero_lowerBound) he'
  · by_cases hp : 1 + 13 * a + 49 * a ^ 2 = 0
    · exact localL_root_pole_excluded a ha hn hf hlead
        (actual_V_root_lowerBound a hp) (actual_V_root_coeff a hp)
        (by simpa using lowerBound_mul hh (actual_R_root_lowerBound a hp)) he'
    · exact localL_ordinary_pole_excluded a ha hn hf hlead
        (actual_V_regular_lowerBound a hp)
        (by simpa using lowerBound_mul hh (actual_R_regular_lowerBound a hp)) he'

theorem actual_L_solution_regular (f : RatFunc ℂ) (h : Polynomial ℂ)
    (he : L f = (h : RatFunc ℂ) * R) (a : ℂ) :
    lowerBound (localExpansion a f) 0 := by
  intro k hk
  by_contra hc
  have ho := HahnSeries.order_le_of_coeff_ne_zero hc
  have hn : (localExpansion a f).order < 0 := lt_of_le_of_lt ho hk
  have hnz : localExpansion a f ≠ 0 := HahnSeries.ne_zero_of_coeff_ne_zero hc
  exact actual_L_no_finite_pole a f h hn
    (fun _ hi => HahnSeries.coeff_eq_zero_of_lt_order hi)
    (mt HahnSeries.coeff_order_eq_zero.mp hnz) he

theorem localExpansion_polynomial_constant (a : ℂ) (p : Polynomial ℂ) :
    (localExpansion a (p : RatFunc ℂ)).coeff 0 = p.eval a := by
  rw [localExpansion_polynomial, embed_polynomial]
  simp [PowerSeries.coeff_coe, Polynomial.taylor_coeff_zero]

theorem denom_no_root_of_local_regular (f : RatFunc ℂ) (a : ℂ)
    (hf : lowerBound (localExpansion a f) 0) : f.denom.eval a ≠ 0 := by
  intro hd
  have he : (f.denom : RatFunc ℂ) * f = (f.num : RatFunc ℂ) := by
    conv_lhs => arg 2; rw [← RatFunc.num_div_denom f]
    simp only [RatFunc.coePolynomial_eq_algebraMap]
    have hd0 : algebraMap (Polynomial ℂ) (RatFunc ℂ) f.denom ≠ 0 :=
      fun hz => f.denom_ne_zero ((IsFractionRing.injective (Polynomial ℂ)
        (RatFunc ℂ)) (hz.trans (map_zero _).symm))
    field_simp [hd0]
  have hc := congrArg (fun z : RatFunc ℂ => (localExpansion a z).coeff 0) he
  rw [map_mul] at hc
  have hm := lowerBound_mul_leading (localExpansion_polynomial_lowerBound a f.denom) hf
  norm_num only [zero_add] at hm
  rw [hm, localExpansion_polynomial_constant, localExpansion_polynomial_constant, hd,
    zero_mul] at hc
  obtain ⟨u, v, huv⟩ := f.isCoprime_num_denom
  have hbez := congrArg (Polynomial.eval a) huv
  simp [← hc, hd] at hbez

theorem actual_L_solution_polynomial (f : RatFunc ℂ) (h : Polynomial ℂ)
    (he : L f = (h : RatFunc ℂ) * R) : ∃ p : Polynomial ℂ, f = (p : RatFunc ℂ) := by
  apply polynomial_of_denom_no_roots
  intro a
  exact denom_no_root_of_local_regular f a (actual_L_solution_regular f h he a)

end Zeta7Germ
