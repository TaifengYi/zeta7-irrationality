import Zeta7Proof.AnnularReflectionCompatibility

/-! The support theorem for the complete relation of the original six germs. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
namespace Zeta7Annulus
local instance AnnularActualLaurentRelation_prime : Fact (Nat.Prime 7) := ⟨by decide⟩
local instance AnnularActualLaurentRelation_radius : Fact (0 < (7 : ℝ)) := ⟨by norm_num⟩
namespace ClosedAnnulus

def SupportedBelow (a : ClosedAnnulus 7 7) (n : ℤ) : Prop := ∀ k : ℤ, k < n → a.coeffs k = 0

theorem SupportedBelow.add {a b : ClosedAnnulus 7 7} {n : ℤ}
    (ha : SupportedBelow a n) (hb : SupportedBelow b n) : SupportedBelow (a + b) n := by
  intro k hk
  simp only [coeffs_add, Pi.add_apply, ha k hk, hb k hk, add_zero]

theorem SupportedBelow.mono {a : ClosedAnnulus 7 7} {m n : ℤ}
    (ha : SupportedBelow a m) (hnm : n ≤ m) : SupportedBelow a n :=
  fun k hk => ha k (hk.trans_le hnm)

theorem SupportedBelow.mul {a b : ClosedAnnulus 7 7} {m n : ℤ}
    (ha : SupportedBelow a m) (hb : SupportedBelow b n) : SupportedBelow (a * b) (m + n) := by
  intro k hk
  rw [coeffs_mul]
  unfold bilateralConvolution
  have hz (i : ℤ) : a.coeffs i * b.coeffs (k - i) = 0 := by
    by_cases hi : i < m
    · rw [ha i hi, zero_mul]
    · rw [hb (k - i) (by omega), mul_zero]
  simp only [hz, tsum_zero]

theorem monomial_supportedBelow (n : ℤ) (z : ℚ_[7]) : SupportedBelow (monomial n z) n := by
  intro k hk
  simp only [monomial_coeffs, bilateralMonomial, if_neg (ne_of_lt hk)]

theorem annularP_supportedBelow : SupportedBelow (annularP (r := 7) (R := 7)) 0 :=
  ((monomial_supportedBelow 0 1).add ((monomial_supportedBelow 1 13).mono (by norm_num))).add
    ((monomial_supportedBelow 2 49).mono (by norm_num))

theorem reverseQ_supportedBelow : SupportedBelow reverseQ (-2) := by
  exact (monomial_supportedBelow (-2) 1).mul annularP_supportedBelow

theorem actualOppositeSix_relation :
    (∑ j : Fin 6, actualOppositeSix j * oppositeGerm j) =
      reverseQ ^ 2 * actualConcomitantRemainder := by
  simp only [Fin.sum_univ_succ, actualOppositeSix, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Fin.sum_univ_zero, add_zero]
  change (-(reverseQ ^ 2 * actualVStar.euler.euler) + reverseNumerator * actualVStar) *
      oppositeGerm 0 + (-(reverseQ ^ 2 * actualVStar.euler) * oppositeGerm 1 +
      (-(reverseQ ^ 2 * actualVStar) * oppositeGerm 2 +
      (reverseQ ^ 2 * annularQuadraticAtInverse * oppositeGerm 3 +
      (-(constant 49 * reverseQ ^ 2 * oppositeHPrime) * oppositeGerm 4 +
      constant (49 ^ 2) * reverseQ ^ 2 * oppositeHSecond * oppositeGerm 5)))) = _
  rw [oppositeGerm_first_derivative, oppositeGerm_second_derivative, reverseNumerator_potential]
  unfold actualConcomitantRemainder oppositePrimitiveCombination concomitant
  ring

theorem actualOppositeSix_relation_below {k : ℤ} (hk : k < -6) :
    (∑ j : Fin 6, actualOppositeSix j * oppositeGerm j).coeffs k = 0 := by
  rw [actualOppositeSix_relation]
  have hq : SupportedBelow (reverseQ ^ 2) (-4) := by
    simpa only [pow_two, Int.reduceAdd] using reverseQ_supportedBelow.mul reverseQ_supportedBelow
  have hr : SupportedBelow actualConcomitantRemainder (-2) := fun _ h => actualConcomitantRemainder_below h
  exact (hq.mul hr) k hk

theorem coeff_finset_sum {ι : Type*} (s : Finset ι) (f : ι → ClosedAnnulus 7 7) (k : ℤ) :
    (∑ i ∈ s, f i).coeffs k = ∑ i ∈ s, (f i).coeffs k := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp only [Finset.sum_insert ha, coeffs_add, Pi.add_apply, ih]

theorem actualOppositeSix_relation_coefficient (k : ℤ) :
    (∑ j : Fin 6, actualOppositeSix j * oppositeGerm j).coeffs k =
      ∑ j : Fin 6, bilateralConvolution (actualAnnularCoefficients j)
        (actualNormalizedTargetCoefficients j) (-k) := by
  rw [coeff_finset_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [coeffs_mul, ← reflects_actualSix j]
  change bilateralConvolution (reverse (actualAnnularCoefficients j))
    (reverse (actualNormalizedTargetCoefficients j)) k = _
  rw [← reverse_convolution]
  rfl

end ClosedAnnulus

/-- Complete Laurent relation for the original, unscaled A_j and normalized
target germs. No claim is made about the undetermined constant of the concomitant. -/
theorem actualAnnularLaurentRelation_above (k : ℤ) (hk : 6 < k) :
    (∑ j : Fin 6, bilateralConvolution (actualAnnularCoefficients j)
      (actualNormalizedTargetCoefficients j) k) = 0 := by
  have he := ClosedAnnulus.actualOppositeSix_relation_coefficient (-k)
  rw [neg_neg] at he
  rw [← he]
  exact ClosedAnnulus.actualOppositeSix_relation_below (by omega)

end Zeta7Annulus
