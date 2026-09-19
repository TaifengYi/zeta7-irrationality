import Zeta7Proof.LevelSevenE6Quotient

/-! The E₄ and E₆ quotient identities as identities of functions on the upper half-plane.

For every `τ ∈ ℍ`, with `x = etaCoordinate τ` and `A = actualA τ`:

* `E4_function`: `E₄(τ) P(x) = A² N(x)`, `P = 1 + 13x + 49x²`, `N = 1 + 245x + 2401x²`;
* `E6_function`: `E₆(τ) P(x)² = A³ T(x)`, `T = 1 - 490x - 21609x² - 235298x³ - 823543x⁴`.

They follow from the vanishing weight-ten and weight-eighteen forms after dividing by the
nonvanishing eta quotient `φ₀`. -/
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open UpperHalfPlane
namespace Zeta7LevelSeven

/-- `P(ξ) = 1 + 13ξ + 49ξ²`. -/
def polyP (ξ : ℂ) : ℂ := 1 + 13 * ξ + 49 * ξ ^ 2
/-- `N(ξ) = 1 + 245ξ + 2401ξ²`. -/
def polyN (ξ : ℂ) : ℂ := 1 + 245 * ξ + 2401 * ξ ^ 2
/-- `T(ξ) = 1 - 490ξ - 21609ξ² - 235298ξ³ - 823543ξ⁴`. -/
def polyT (ξ : ℂ) : ℂ := 1 - 490 * ξ - 21609 * ξ ^ 2 - 235298 * ξ ^ 3 - 823543 * ξ ^ 4

theorem phi_zero_ne (τ : ℍ) : phi 0 τ ≠ 0 := by
  unfold phi
  exact mul_ne_zero (zpow_ne_zero _ (etaTwo_ne_zero τ)) (zpow_ne_zero _ (etaTwoSeven_ne_zero τ))

theorem phiModularForm_apply (i : Fin 3) (τ : ℍ) :
    phiModularForm i τ = phi 0 τ * etaCoordinate τ ^ i.val :=
  phi_eq_phi_zero_mul_coordinate i τ

theorem phiCombination_apply (a b : ℚ) (τ : ℍ) :
    phiCombination a b τ = phi 0 τ * (1 + a * etaCoordinate τ + b * etaCoordinate τ ^ 2) := by
  change phiModularForm 0 τ + (a : ℂ) * phiModularForm 1 τ + (b : ℂ) * phiModularForm 2 τ = _
  rw [phiModularForm_apply, phiModularForm_apply, phiModularForm_apply]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one]
  ring

theorem actualASquare_apply (τ : ℍ) : actualASquare τ = actualA τ ^ 2 := by
  change actualA τ * actualA τ = _; ring

theorem actualACube_apply (τ : ℍ) : actualACube τ = actualA τ ^ 3 := by
  change actualA τ * actualASquare τ = _; rw [actualASquare_apply]; ring

/-- **`E₄ P(x) = A² N(x)` on `ℍ`.** -/
theorem E4_function (τ : ℍ) :
    classicalE4 τ * polyP (etaCoordinate τ) = actualA τ ^ 2 * polyN (etaCoordinate τ) := by
  have h := congrArg (fun f : ModularForm GammaSeven 10 => (f : ℍ → ℂ) τ) firstWeightTen_zero
  change phiCombination 13 49 τ * classicalE4 τ -
    phiCombination 245 2401 τ * actualASquare τ = 0 at h
  rw [phiCombination_apply, phiCombination_apply, actualASquare_apply] at h
  have h0 := phi_zero_ne τ
  have : phi 0 τ * (classicalE4 τ * polyP (etaCoordinate τ) -
      actualA τ ^ 2 * polyN (etaCoordinate τ)) = 0 := by
    unfold polyP polyN; push_cast at h; linear_combination h
  rcases mul_eq_zero.mp this with h1 | h1
  · exact absurd h1 h0
  · linear_combination h1

/-- **`E₆ P(x)² = A³ T(x)` on `ℍ`.** -/
theorem E6_function (τ : ℍ) :
    classicalE6 τ * polyP (etaCoordinate τ) ^ 2 = actualA τ ^ 3 * polyT (etaCoordinate τ) := by
  have h := weightEighteen_function τ
  change (phiCombination 13 49 τ * phiCombination 13 49 τ) * classicalE6 τ =
    (phiModularForm 0 τ * phiCombination (-490) (-21609) τ -
      phiModularForm 2 τ * (phiCombination 235298 823543 τ - phiModularForm 0 τ)) *
        actualACube τ at h
  rw [phiCombination_apply, phiCombination_apply, phiCombination_apply,
    phiModularForm_apply, phiModularForm_apply, actualACube_apply] at h
  have h0 := phi_zero_ne τ
  have : phi 0 τ ^ 2 * (classicalE6 τ * polyP (etaCoordinate τ) ^ 2 -
      actualA τ ^ 3 * polyT (etaCoordinate τ)) = 0 := by
    unfold polyP polyT; push_cast at h
    simp only [Fin.val_zero, Fin.val_two, pow_zero, mul_one] at h
    linear_combination h
  rcases mul_eq_zero.mp this with h1 | h1
  · exact absurd (pow_eq_zero_iff (by norm_num) |>.mp h1) h0
  · linear_combination h1

end Zeta7LevelSeven
