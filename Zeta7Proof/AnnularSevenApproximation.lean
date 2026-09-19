import Zeta7Proof.AnnularCandidateNonzero

/-! A strict radius-seven approximation of the original candidate. -/
noncomputable section
set_option autoImplicit false
namespace Zeta7Annulus
local instance AnnularSevenApproximation_prime : Fact (Nat.Prime 7) := ⟨by decide⟩
local instance AnnularSevenApproximation_radius : Fact (0 < (7 : ℝ)) := ⟨by norm_num⟩
namespace ClosedAnnulus

theorem seven_norm_le_one_of_sub {a : ClosedAnnulus 7 7}
    (ha : ‖a - 1‖ ≤ (7 : ℝ)⁻¹) : ‖a‖ ≤ 1 := by
  calc
    ‖a‖ = ‖(a - 1) + 1‖ := by rw [sub_add_cancel]
    _ ≤ max ‖a - 1‖ ‖(1 : ClosedAnnulus 7 7)‖ := norm_add_le_max _ _
    _ ≤ 1 := max_le (ha.trans (by norm_num)) (by rw [norm_one])

theorem seven_mul_sub_one {a b : ClosedAnnulus 7 7}
    (ha : ‖a - 1‖ ≤ (7 : ℝ)⁻¹) (hb : ‖b - 1‖ ≤ (7 : ℝ)⁻¹) :
    ‖a * b - 1‖ ≤ (7 : ℝ)⁻¹ := by
  have he : a * b - 1 = (a - 1) * b + (b - 1) := by ring
  rw [he]
  apply (norm_add_le_max _ _).trans
  exact max_le ((norm_mul_le _ _).trans (by
    calc
      ‖a - 1‖ * ‖b‖ ≤ (7 : ℝ)⁻¹ * 1 := mul_le_mul ha
        (seven_norm_le_one_of_sub hb) (norm_nonneg _) (by positivity)
      _ = _ := mul_one _)) hb

theorem annularN_seven_sub_one_bound :
    ‖annularN (r := 7) (R := 7) - 1‖ ≤ (7 : ℝ)⁻¹ := by
  have he : annularN (r := 7) (R := 7) - 1 = monomial 1 245 + monomial 2 2401 := by
    unfold annularN; ring
  rw [he]
  apply (norm_add_le_max _ _).trans
  rw [max_le_iff]
  constructor
  · rw [monomial_norm, norm_twofortyfive]; norm_num
  · rw [monomial_norm, norm_twentyfourhundredone]; norm_num

theorem nInverse_seven_sub_one_bound :
    ‖nInverse (r := 7) (R := 7) - 1‖ ≤ (7 : ℝ)⁻¹ := by
  have hi := annularN_mul_inverse (r := 7) (R := 7) (by norm_num) (by norm_num) le_rfl
  have he : nInverse (r := 7) (R := 7) - 1 = (1 - annularN) * nInverse := by
    linear_combination hi
  rw [he]
  calc
    _ ≤ ‖1 - annularN (r := 7) (R := 7)‖ * ‖nInverse (r := 7) (R := 7)‖ := norm_mul_le _ _
    _ ≤ (7 : ℝ)⁻¹ * 1 := mul_le_mul
      (by simpa only [norm_sub_rev] using annularN_seven_sub_one_bound)
      (nInverse_norm_le (by norm_num) (by norm_num) le_rfl) (norm_nonneg _) (by positivity)
    _ = _ := mul_one _

theorem candidateB_seven_sub_one_bound :
    ‖candidateB (r := 7) (R := 7) - 1‖ ≤ (7 : ℝ)⁻¹ := by
  have hh (i : Fin 2) : ‖actualHypergeometricValue (r := 7) (R := 7) i - 1‖ ≤ (7 : ℝ)⁻¹ :=
    hypergeometricCompose_sub_one_bound i _ annularSubstitution_seven_norm_bound
  unfold candidateB
  exact seven_mul_sub_one (seven_mul_sub_one (seven_mul_sub_one
    annularT_seven_sub_one_bound (by
      simpa only [pow_two] using seven_mul_sub_one nInverse_seven_sub_one_bound
        nInverse_seven_sub_one_bound)) (hh 0)) (hh 1)

theorem pContraction_seven_norm_bound :
    ‖pContraction (r := 7) (R := 7)‖ ≤ (7 : ℝ)⁻¹ := by
  unfold pContraction
  apply (norm_add_le_max _ _).trans
  rw [max_le_iff]
  constructor
  · rw [monomial_norm, norm_div, norm_one, norm_thirteen]; norm_num
  · rw [monomial_norm, norm_div, norm_fortynine, norm_thirteen]; norm_num

theorem pInverse_seven_approximation :
    ‖pInverse (r := 7) (R := 7) - monomial (-1) (1 / 13)‖ ≤ (1 / 49 : ℝ) := by
  have hi := annularP_mul_inverse (r := 7) (R := 7) (by norm_num) (by norm_num) le_rfl
  have hm : monomial (r := 7) (R := 7) (-1) (1 / 13) * annularP = 1 + pContraction := by
    rw [annularP_factorization, ← mul_assoc, monomial_mul]
    norm_num
  have he : pInverse (r := 7) (R := 7) - monomial (-1) (1 / 13) =
      -pContraction * pInverse := by
    linear_combination monomial (r := 7) (R := 7) (-1) (1 / 13) * hi - pInverse * hm
  rw [he]
  calc
    _ ≤ ‖-pContraction (r := 7) (R := 7)‖ * ‖pInverse (r := 7) (R := 7)‖ := norm_mul_le _ _
    _ ≤ (7 : ℝ)⁻¹ * (7 : ℝ)⁻¹ := mul_le_mul
      (by simpa only [norm_neg] using pContraction_seven_norm_bound)
      (pInverse_norm_le (by norm_num) (by norm_num) le_rfl) (norm_nonneg _) (by positivity)
    _ = _ := by norm_num

theorem candidateA_seven_approximation :
    ‖candidateA (r := 7) (R := 7) - monomial (-1) (1 / 13)‖ ≤ (1 / 49 : ℝ) := by
  have he : candidateA (r := 7) (R := 7) - monomial (-1) (1 / 13) =
      (candidateB - 1) * pInverse + (pInverse - monomial (-1) (1 / 13)) := by
    unfold candidateA; ring
  rw [he]
  apply (norm_add_le_max _ _).trans
  refine max_le ((norm_mul_le _ _).trans ?_) pInverse_seven_approximation
  calc
    _ ≤ (7 : ℝ)⁻¹ * (7 : ℝ)⁻¹ := mul_le_mul candidateB_seven_sub_one_bound
      (pInverse_norm_le (by norm_num) (by norm_num) le_rfl) (norm_nonneg _) (by positivity)
    _ = _ := by norm_num

theorem candidateA_seven_norm_bound : ‖candidateA (r := 7) (R := 7)‖ ≤ (7 : ℝ)⁻¹ := by
  unfold candidateA
  calc
    _ ≤ ‖candidateB (r := 7) (R := 7)‖ * ‖pInverse (r := 7) (R := 7)‖ := norm_mul_le _ _
    _ ≤ 1 * (7 : ℝ)⁻¹ := mul_le_mul (seven_norm_le_one_of_sub candidateB_seven_sub_one_bound)
      (pInverse_norm_le (by norm_num) (by norm_num) le_rfl) (norm_nonneg _) zero_le_one
    _ = _ := one_mul _

end ClosedAnnulus
end Zeta7Annulus
