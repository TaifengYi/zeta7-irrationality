import Zeta7Proof.AnnularPowerSeriesTransport

/-! Actual normalized target germs on the circle |y|=7, with exact coefficient
transport. Only their existence in this annulus uses the internally proved radius-49 theorem. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
namespace Zeta7Annulus.ClosedAnnulus
local instance AnnularOppositeTarget_prime : Fact (Nat.Prime 7) := ⟨by decide⟩
local instance AnnularOppositeTarget_radius : Fact (0 < (7 : ℝ)) := ⟨by norm_num⟩
open PowerSeries

def Models (f : ℚ_[7]⟦X⟧) (a : ClosedAnnulus 7 7) : Prop := oppositeSeries f = a.coeffs

theorem Models.unique {f : ℚ_[7]⟦X⟧} {a b : ClosedAnnulus 7 7}
    (ha : Models f a) (hb : Models f b) : a = b := ClosedAnnulus.ext (ha.symm.trans hb)

theorem Models.of_eq {f g : ℚ_[7]⟦X⟧} {a : ClosedAnnulus 7 7}
    (ha : Models f a) (hfg : f = g) : Models g a := hfg ▸ ha

theorem Models.add {f g : ℚ_[7]⟦X⟧} {a b : ClosedAnnulus 7 7}
    (ha : Models f a) (hb : Models g b) : Models (f + g) (a + b) := by
  unfold Models at *
  rw [oppositeSeries_add, ha, hb, coeffs_add]

theorem Models.neg {f : ℚ_[7]⟦X⟧} {a : ClosedAnnulus 7 7}
    (ha : Models f a) : Models (-f) (-a) := by
  unfold Models at *
  rw [oppositeSeries_neg, ha, coeffs_neg]

theorem Models.sub {f g : ℚ_[7]⟦X⟧} {a b : ClosedAnnulus 7 7}
    (ha : Models f a) (hb : Models g b) : Models (f - g) (a - b) := by
  simpa only [sub_eq_add_neg] using ha.add hb.neg

theorem Models.mul {f g : ℚ_[7]⟦X⟧} {a b : ClosedAnnulus 7 7}
    (ha : Models f a) (hb : Models g b) : Models (f * g) (a * b) := by
  unfold Models at *
  rw [oppositeSeries_mul, ha, hb, coeffs_mul]

theorem models_C (z : ℚ_[7]) : Models (C z) (constant z) := oppositeSeries_C z

theorem models_nat (n : ℕ) : Models (n : ℚ_[7]⟦X⟧) (n : ClosedAnnulus 7 7) := by
  simpa only [map_natCast] using models_C (n : ℚ_[7])

theorem Models.pow {f : ℚ_[7]⟦X⟧} {a : ClosedAnnulus 7 7}
    (ha : Models f a) (n : ℕ) : Models (f ^ n) (a ^ n) := by
  induction n with
  | zero => simpa only [pow_zero, Nat.cast_one] using models_nat 1
  | succ n ih => simpa only [pow_succ] using ih.mul ha

theorem Models.euler {f : ℚ_[7]⟦X⟧} {a : ClosedAnnulus 7 7}
    (ha : Models f a) : Models (Zeta7Common.euler f) (-euler a) := by
  unfold Models at *
  rw [oppositeSeries_euler, ha, coeffs_neg]
  rfl

def oppositeGerm (j : Fin 6) : ClosedAnnulus 7 7 where
  coeffs := oppositeSeries (Zeta7Common.targetGerms j)
  inner := (reverse_decaysAt_iff _ _).mpr
    (actualNormalizedTargetCoefficients_decay j (by norm_num) (by norm_num))
  outer := (reverse_decaysAt_iff _ _).mpr
    (actualNormalizedTargetCoefficients_decay j (by norm_num) (by norm_num))

theorem models_germ (j : Fin 6) : Models (Zeta7Common.targetGerms j) (oppositeGerm j) := rfl

def oppositeX : ClosedAnnulus 7 7 := monomial (-1) (49 : ℚ_[7])⁻¹
theorem models_X : Models (X : ℚ_[7]⟦X⟧) oppositeX := oppositeSeries_X

def oppositeP : ClosedAnnulus 7 7 := 1 + 13 * oppositeX + 49 * oppositeX ^ 2
def oppositeW : ClosedAnnulus 7 7 := 8 * oppositeX * (1 + 16 * oppositeX + 49 * oppositeX ^ 2)
def oppositeS : ClosedAnnulus 7 7 := oppositeX * (1 + 10 * oppositeX)

theorem models_P : Models Zeta7Common.targetP oppositeP := by
  simpa only [Zeta7Common.targetP, oppositeP, Nat.cast_one, Nat.cast_ofNat] using
    ((models_nat 1).add ((models_nat 13).mul models_X)).add ((models_nat 49).mul (models_X.pow 2))
theorem models_W : Models Zeta7Common.targetW oppositeW := by
  simpa only [Zeta7Common.targetW, oppositeW, Nat.cast_one, Nat.cast_ofNat] using
    ((models_nat 8).mul models_X).mul
      (((models_nat 1).add ((models_nat 16).mul models_X)).add ((models_nat 49).mul (models_X.pow 2)))
theorem models_S : Models Zeta7Common.targetS oppositeS := by
  simpa only [Zeta7Common.targetS, oppositeS, Nat.cast_one, Nat.cast_ofNat] using
    models_X.mul ((models_nat 1).add ((models_nat 10).mul models_X))

theorem oppositeGerm_first_derivative : oppositeGerm 1 = -euler (oppositeGerm 0) :=
  (models_germ 1).unique ((models_germ 0).euler)

theorem oppositeGerm_second_derivative : oppositeGerm 2 = euler (euler (oppositeGerm 0)) := by
  have he := (models_germ 2).unique ((models_germ 1).euler)
  rw [he, oppositeGerm_first_derivative]
  have hn (a : ClosedAnnulus 7 7) : euler (-a) = -euler a := eulerAddHom.map_neg a
  rw [hn, neg_neg]

theorem oppositeTarget_cleared_equation :
    -(oppositeP ^ 3 * euler (euler (euler (oppositeGerm 0)))) +
      oppositeP * oppositeW * euler (oppositeGerm 0) -
      (oppositeW * euler oppositeP - constant (1 / 2 : ℚ_[7]) * oppositeP * euler oppositeW) *
        oppositeGerm 0 = oppositeP ^ 2 * oppositeS := by
  have hh : Models Zeta7Main.HSeries (oppositeGerm 0) := models_germ 0
  have hl := (((models_P.pow 3).mul hh.euler.euler.euler).sub
    ((models_P.mul models_W).mul hh.euler)).add
    (((models_W.mul models_P.euler).sub
      (((models_C (1 / 2 : ℚ_[7])).mul models_P).mul models_W.euler)).mul hh)
  have he := (hl.of_eq Zeta7Common.HSeries_cleared_differential_equation).unique
    ((models_P.pow 2).mul models_S)
  have hn (a : ClosedAnnulus 7 7) : euler (-a) = -euler a := eulerAddHom.map_neg a
  simp only [hn, neg_neg] at he
  linear_combination he

theorem oppositeK_cleared_derivative :
    oppositeP * euler (oppositeGerm 3) = -oppositeS * oppositeGerm 0 := by
  have he : Zeta7Common.targetP * Zeta7Common.euler (Zeta7Common.targetGerms 3) =
      Zeta7Common.targetS * Zeta7Main.HSeries := by
    rw [Zeta7Common.targetK_derivative, ← mul_assoc, Zeta7Common.targetForcing_cleared]
  have hh := ((models_P.mul (models_germ 3).euler).of_eq he).unique
    (models_S.mul (models_germ 0))
  linear_combination -hh

theorem oppositeJ1_derivative : euler (oppositeGerm 4) = -oppositeX * oppositeGerm 3 := by
  have he : Zeta7Common.euler (Zeta7Common.targetGerms 4) = X * Zeta7Common.targetGerms 3 :=
    Zeta7Common.euler_primitive_seven _
  have hh := (((models_germ 4).euler).of_eq he).unique (models_X.mul (models_germ 3))
  linear_combination -hh

theorem oppositeJ2_derivative : euler (oppositeGerm 5) = -oppositeX * oppositeGerm 4 := by
  have he : Zeta7Common.euler (Zeta7Common.targetGerms 5) = X * Zeta7Common.targetGerms 4 :=
    Zeta7Common.euler_primitive_seven _
  have hh := (((models_germ 5).euler).of_eq he).unique (models_X.mul (models_germ 4))
  linear_combination -hh

end Zeta7Annulus.ClosedAnnulus
