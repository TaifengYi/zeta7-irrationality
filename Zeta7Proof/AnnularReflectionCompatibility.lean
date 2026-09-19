import Zeta7Proof.AnnularActualConcomitant

/-! Compatibility of the original six coefficients with the y-annulus calculation. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
namespace Zeta7Annulus.ClosedAnnulus
local instance AnnularReflectionCompatibility_prime : Fact (Nat.Prime 7) := ⟨by decide⟩
local instance AnnularReflectionCompatibility_radius1 : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
local instance AnnularReflectionCompatibility_radius7 : Fact (0 < (7 : ℝ)) := ⟨by norm_num⟩

def Reflects (a : ClosedAnnulus 1 1) (b : ClosedAnnulus 7 7) : Prop := reverse a.coeffs = b.coeffs
theorem Reflects.add {a b : ClosedAnnulus 1 1} {a' b' : ClosedAnnulus 7 7}
    (ha : Reflects a a') (hb : Reflects b b') : Reflects (a + b) (a' + b') := by
  unfold Reflects at *; rw [coeffs_add, reverse_add, ha, hb, coeffs_add]
theorem Reflects.neg {a : ClosedAnnulus 1 1} {a' : ClosedAnnulus 7 7}
    (ha : Reflects a a') : Reflects (-a) (-a') := by
  unfold Reflects at *; rw [coeffs_neg, reverse_neg, ha, coeffs_neg]
theorem Reflects.mul {a b : ClosedAnnulus 1 1} {a' b' : ClosedAnnulus 7 7}
    (ha : Reflects a a') (hb : Reflects b b') : Reflects (a * b) (a' * b') := by
  unfold Reflects at *; rw [coeffs_mul, reverse_convolution, ha, hb, coeffs_mul]
theorem reflects_monomial (n : ℤ) (z : ℚ_[7]) :
    Reflects (monomial (r := 1) (R := 1) n z) (monomial (r := 7) (R := 7) (-n) z) :=
  reverse_monomial n z
theorem reflects_constant (z : ℚ_[7]) :
    Reflects (constant (r := 1) (R := 1) z) (constant (r := 7) (R := 7) z) :=
  reflects_monomial 0 z
theorem Reflects.pow {a : ClosedAnnulus 1 1} {a' : ClosedAnnulus 7 7}
    (ha : Reflects a a') (n : ℕ) : Reflects (a ^ n) (a' ^ n) := by
  induction n with
  | zero => simpa only [pow_zero, map_one] using reflects_constant 1
  | succ n ih => simpa only [pow_succ] using ih.mul ha
theorem Reflects.euler {a : ClosedAnnulus 1 1} {a' : ClosedAnnulus 7 7}
    (ha : Reflects a a') : Reflects (euler a) (-euler a') := by
  funext k
  have hk := congrFun ha k
  change a.coeffs (-k) = a'.coeffs k at hk
  change ((-k : ℤ) : ℚ_[7]) * a.coeffs (-k) = -((k : ℚ_[7]) * a'.coeffs k)
  rw [hk, Int.cast_neg, neg_mul]

def reflectedPolynomialMap : Polynomial ℚ_[7] →+* ClosedAnnulus 7 7 :=
  Polynomial.eval₂RingHom constant (monomial (-1) 1)

theorem reflectedPolynomialMap_C (z : ℚ_[7]) :
    reflectedPolynomialMap (Polynomial.C z) = constant z := Polynomial.eval₂_C _ _
theorem reflectedPolynomialMap_X : reflectedPolynomialMap Polynomial.X = monomial (-1) 1 :=
  Polynomial.eval₂_X _ _

theorem reflects_polynomial (f : Polynomial ℚ_[7]) :
    Reflects (padicPolynomialMap (r := 1) (R := 1) f) (reflectedPolynomialMap f) := by
  induction f using Polynomial.induction_on with
  | C a => simpa only [padicPolynomialMap_C, reflectedPolynomialMap_C] using reflects_constant a
  | add f g hf hg => simpa only [map_add] using hf.add hg
  | monomial n a _ =>
      simpa only [map_mul, map_pow, padicPolynomialMap_C, reflectedPolynomialMap_C,
        padicPolynomialMap_X, reflectedPolynomialMap_X] using
        (reflects_constant a).mul ((reflects_monomial 1 1).pow (n + 1))

def reverseQ : ClosedAnnulus 7 7 := monomial (-2) 1 * annularP
def reverseNumerator : ClosedAnnulus 7 7 := monomial (-4) 1 * potentialNumerator

theorem reflects_Q : Reflects reflectedQ reverseQ := by
  rw [reflectedQ_eq]
  have he : reverseQ = constant 49 + monomial (-1) 13 + monomial (-2) 1 := by
    simp only [reverseQ, annularP, mul_add, mul_one, monomial_mul, one_mul]
    norm_num
    change _ = monomial 0 49 + monomial (-1) 13 + monomial (-2) 1
    abel
  rw [he]
  exact ((reflects_constant 49).add (reflects_monomial 1 13)).add (reflects_monomial 2 1)

theorem reflects_numerator : Reflects reflectedPotentialNumerator reverseNumerator := by
  have he : reverseNumerator =
      monomial (-1) (8 * 49) + monomial (-2) (8 * 16) + monomial (-3) 8 := by
    unfold reverseNumerator potentialNumerator
    simp only [← map_ofNat constant 8, ← map_ofNat constant 16, ← map_ofNat constant 49]
    change monomial (r := 7) (R := 7) (-4) 1 * (monomial (r := 7) (R := 7) 0 8 * monomial (r := 7) (R := 7) 1 1 *
      (monomial (r := 7) (R := 7) 0 1 + monomial (r := 7) (R := 7) 0 16 * monomial (r := 7) (R := 7) 1 1 +
        monomial (r := 7) (R := 7) 0 49 * (monomial (r := 7) (R := 7) 1 1) ^ 2)) = _
    simp only [mul_add, pow_two, monomial_mul]
    norm_num
    abel
  rw [he]
  exact ((reflects_monomial 1 (8 * 49)).add (reflects_monomial 2 (8 * 16))).add (reflects_monomial 3 8)

theorem reflects_v : Reflects reflectedCorrectedSolution actualVStar := by
  funext k
  change reflectedCorrectedSolution.coeffs (-k) = actualVStar.coeffs k
  rw [reflectedCorrectedSolution_coefficients, neg_neg]
  exact (congrFun (correctedSolutionOn_coefficients (r := 7) (R := 7) (by norm_num) le_rfl) k).symm

theorem reflectedPolynomialMap_h : reflectedPolynomialMap annularForcingQuadratic =
    annularQuadraticAtInverse := by
  simp only [annularForcingQuadratic, map_add, map_mul, map_pow,
    reflectedPolynomialMap_C, reflectedPolynomialMap_X]
  change monomial (r := 7) (R := 7) 0 annularQuadratic₀ + monomial (r := 7) (R := 7) 0 annularQuadratic₁ * monomial (r := 7) (R := 7) (-1) 1 +
    monomial (r := 7) (R := 7) 0 annularQuadratic₂ * (monomial (r := 7) (R := 7) (-1) 1) ^ 2 = _
  simp only [pow_two, monomial_mul, mul_one, one_mul]
  rfl

theorem reflectedPolynomialMap_hPrime : reflectedPolynomialMap annularForcingQuadratic.derivative =
    oppositeHPrime := by
  rw [forcingDerivative_eq, map_add, map_mul, reflectedPolynomialMap_C, reflectedPolynomialMap_C, reflectedPolynomialMap_X]
  change monomial (r := 7) (R := 7) 0 annularQuadratic₁ + monomial (r := 7) (R := 7) 0 (2 * annularQuadratic₂) * monomial (r := 7) (R := 7) (-1) 1 = _
  rw [monomial_mul, mul_one]; rfl

theorem reflectedPolynomialMap_hSecond : reflectedPolynomialMap annularForcingQuadratic.derivative.derivative =
    oppositeHSecond := by rw [forcingSecondDerivative_eq, reflectedPolynomialMap_C]; rfl

def actualOppositeSix : Fin 6 → ClosedAnnulus 7 7 := ![
  -(reverseQ ^ 2 * euler (euler actualVStar)) + reverseNumerator * actualVStar,
  -(reverseQ ^ 2 * euler actualVStar),
  -(reverseQ ^ 2 * actualVStar),
  reverseQ ^ 2 * annularQuadraticAtInverse,
  -(constant 49 * reverseQ ^ 2 * oppositeHPrime),
  constant (49 ^ 2) * reverseQ ^ 2 * oppositeHSecond]

theorem reflects_actualSix (j : Fin 6) : Reflects (actualAnnularSix j) (actualOppositeSix j) := by
  have hq := reflects_Q.pow 2
  have hd := reflects_v.euler
  have hdd := hd.euler
  have hn (a : ClosedAnnulus 7 7) : euler (-a) = -euler a := eulerAddHom.map_neg a
  simp only [hn, neg_neg] at hdd
  have hh := reflects_polynomial annularForcingQuadratic
  have hh1 := reflects_polynomial annularForcingQuadratic.derivative
  have hh2 := reflects_polynomial annularForcingQuadratic.derivative.derivative
  rw [reflectedPolynomialMap_h] at hh
  rw [reflectedPolynomialMap_hPrime] at hh1
  rw [reflectedPolynomialMap_hSecond] at hh2
  fin_cases j <;> simp only [actualAnnularSix, actualOppositeSix, Matrix.cons_val_zero', Matrix.cons_val_succ']
  · exact (hq.mul hdd).neg.add (reflects_numerator.mul reflects_v)
  · simpa only [mul_neg] using hq.mul hd
  · exact (hq.mul reflects_v).neg
  · exact hq.mul hh
  · exact (((reflects_constant 49).mul hq).mul hh1).neg
  · exact ((reflects_constant (49 ^ 2)).mul hq).mul hh2

theorem reverseNumerator_potential : reverseNumerator = reverseQ ^ 2 * annularPotential := by
  have he : (monomial (r := 7) (R := 7) (-2) 1) ^ 2 = monomial (-4) 1 := by
    rw [pow_two, monomial_mul]; norm_num
  unfold reverseNumerator reverseQ
  rw [mul_pow, he, mul_assoc, potentialNumerator_clear]

end Zeta7Annulus.ClosedAnnulus
