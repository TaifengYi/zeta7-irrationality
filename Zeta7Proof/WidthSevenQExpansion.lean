import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.RingTheory.PowerSeries.Expand

/-! Width-one and width-seven expansions are distinct. This module proves their
exact relation for a function that is already one-periodic and holomorphic at infinity. -/
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open Complex hiding eta
open UpperHalfPlane Function
open scoped Real Manifold
namespace Zeta7LevelSeven

theorem qParam_seven_pow (τ : ℍ) :
    Periodic.qParam 7 τ ^ 7 = Periodic.qParam 1 τ := by
  simp only [Periodic.qParam, ← exp_nat_mul]
  congr 1
  norm_num
  ring

theorem hasSum_expand_seven {F : PowerSeries ℂ} {z s : ℂ}
    (h : HasSum (fun n : ℕ ↦ F.coeff n * (z ^ 7) ^ n) s) :
    HasSum (fun n : ℕ ↦ (PowerSeries.expand 7 (by decide) F).coeff n * z ^ n) s := by
  have hi : Function.Injective (fun n : ℕ ↦ 7 * n) := by
    intro a b hab
    change 7 * a = 7 * b at hab
    omega
  apply (hi.hasSum_iff ?_).mp
  · change HasSum (fun n : ℕ ↦ (PowerSeries.expand 7 (by decide) F).coeff (7 * n) * z ^ (7 * n)) s
    simp only [PowerSeries.coeff_expand_mul, _root_.pow_mul]
    exact h
  · intro n hn
    have hd : ¬7 ∣ n := by
      rintro ⟨k, rfl⟩
      exact hn ⟨k, rfl⟩
    rw [PowerSeries.coeff_expand_of_not_dvd _ _ _ hd, zero_mul]

/-- Equality of complete power series, with the width conversion made explicit. -/
theorem qExpansion_seven_of_one {f : ℍ → ℂ}
    (hfper : Periodic (f ∘ ofComplex) 1) (hfhol : MDiff f)
    (hfbdd : IsBoundedAtImInfty f) :
    qExpansion 7 f = PowerSeries.expand 7 (by decide) (qExpansion 1 f) := by
  have hp7 : Periodic (f ∘ ofComplex) 7 := by simpa using hfper.nat_mul 7
  have ha := analyticAt_cuspFunction_zero (by norm_num : (0 : ℝ) < 7) hp7 hfhol hfbdd
  have hs (τ : ℍ) : HasSum (fun n : ℕ ↦
      (PowerSeries.expand 7 (by decide) (qExpansion 1 f)).coeff n •
        Periodic.qParam 7 τ ^ n) (f τ) := by
    simp only [smul_eq_mul]
    apply hasSum_expand_seven
    rw [qParam_seven_pow]
    simpa only [smul_eq_mul] using
      τ.hasSum_qExpansion (by norm_num : (0 : ℝ) < 1) hfper hfhol hfbdd
  let fc : C(ℍ, ℂ) := ⟨f, hfhol.continuous⟩
  ext n
  exact (qExpansion_coeff_unique fc (by norm_num : (0 : ℝ) < 7) ha hs n).symm

end Zeta7LevelSeven
