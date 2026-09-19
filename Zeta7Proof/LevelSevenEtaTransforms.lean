import Mathlib.NumberTheory.ModularForms.Discriminant

/-! Specialized eta-square transformations for the actual Dedekind function.
The S transformation reuses Mathlib's proved logarithmic-derivative argument. -/
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open Complex hiding eta
open ModularForm
open UpperHalfPlane hiding I
open scoped Real ModularForm MatrixGroups
namespace Zeta7LevelSeven

def etaTwo (τ : ℍ) : ℂ := eta τ ^ 2
def etaRoot : ℂ := exp (π * I / 6)

theorem etaTwo_ne_zero (τ : ℍ) : etaTwo τ ≠ 0 :=
  pow_ne_zero 2 (eta_ne_zero τ.im_pos)

theorem sqrt_sq_of_ne_zero {z : ℂ} (hz : z ≠ 0) : sqrt z ^ 2 = z := by
  rw [sqrt_eq_exp hz, ← exp_nat_mul]
  norm_num only [Nat.cast_ofNat]
  convert exp_log hz using 1 <;> congr 1 <;> ring

theorem etaTwo_S_value (τ : ℍ) :
    eta (-1 / (τ : ℂ)) ^ 2 = -I * τ * etaTwo τ := by
  have he := eta_comp_eq_csqrt_I_inv τ.im_pos
  change eta (-1 / (τ : ℂ)) = (sqrt I)⁻¹ * (sqrt (τ : ℂ) * eta τ) at he
  rw [he, mul_pow, mul_pow, inv_pow, sqrt_sq_of_ne_zero I_ne_zero,
    sqrt_sq_of_ne_zero τ.ne_zero]
  simp [etaTwo]
  ring

theorem etaTwo_S : etaTwo ∣[(1 : ℤ)] ModularGroup.S = (-I) • etaTwo := by
  ext τ
  rw [SL_slash_apply, modular_S_smul]
  change eta ((-(τ : ℂ))⁻¹) ^ 2 * denom ModularGroup.S τ ^ (-1 : ℤ) = -I * etaTwo τ
  rw [show (-(τ : ℂ))⁻¹ = -1 / (τ : ℂ) by simp [div_eq_mul_inv], etaTwo_S_value]
  simp [denom, ModularGroup.S]
  field_simp [τ.ne_zero]

theorem etaTwo_T_value (z : ℂ) : eta (z + 1) ^ 2 = etaRoot * eta z ^ 2 := by
  have hp : (∏' n : ℕ, (1 - eta_q n (z + 1))) = ∏' n : ℕ, (1 - eta_q n z) := by
    apply tprod_congr
    intro n
    simp [eta_q, Function.Periodic.qParam, mul_add, exp_add]
  simp only [eta, hp, mul_pow]
  rw [← mul_assoc]
  congr 1
  simp only [etaRoot, Function.Periodic.qParam, ← exp_nat_mul, ← exp_add]
  congr 1
  norm_num only [Nat.cast_ofNat, ofReal_ofNat]
  ring

theorem etaTwo_T : etaTwo ∣[(1 : ℤ)] ModularGroup.T = etaRoot • etaTwo := by
  ext τ
  rw [SL_slash_apply, modular_T_smul]
  simpa [etaTwo, denom, ModularGroup.T, add_comm] using etaTwo_T_value (τ : ℂ)

theorem etaRoot_pow_twelve : etaRoot ^ 12 = 1 := by
  rw [etaRoot, ← exp_nat_mul]
  norm_num only [Nat.cast_ofNat]
  rw [show (12 : ℂ) * (π * I / 6) = 2 * π * I by ring]
  exact exp_two_pi_mul_I

theorem etaRoot_pow_three : etaRoot ^ 3 = I := by
  rw [etaRoot, ← exp_nat_mul]
  norm_num only [Nat.cast_ofNat]
  rw [show (3 : ℂ) * (π * I / 6) = (π / 2) * I by ring]
  simp [exp_mul_I]

theorem etaRoot_zpow_neg_three : etaRoot ^ (-3 : ℤ) = -I := by
  rw [zpow_neg, zpow_ofNat, etaRoot_pow_three]
  simp

theorem etaRoot_ne_zero : etaRoot ≠ 0 := exp_ne_zero _

/-- Integer exponents record the multiplier, without choosing a character. -/
def EtaEigen (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (n : ℤ) : Prop :=
  etaTwo ∣[(1 : ℤ)] γ = etaRoot ^ n • etaTwo

theorem etaEigen_one : EtaEigen 1 0 := by simp [EtaEigen]
theorem etaEigen_S : EtaEigen ModularGroup.S (-3) := by
  change etaTwo ∣[(1 : ℤ)] ModularGroup.S = etaRoot ^ (-3 : ℤ) • etaTwo
  rw [etaRoot_zpow_neg_three]
  exact etaTwo_S
theorem etaEigen_T : EtaEigen ModularGroup.T 1 := by simpa [EtaEigen] using etaTwo_T

theorem EtaEigen.mul {γ δ : Matrix.SpecialLinearGroup (Fin 2) ℤ} {a b : ℤ}
    (hγ : EtaEigen γ a) (hδ : EtaEigen δ b) : EtaEigen (γ * δ) (a + b) := by
  simp only [EtaEigen] at *
  rw [SlashAction.slash_mul, hγ, SL_smul_slash, hδ, smul_smul,
    zpow_add₀ etaRoot_ne_zero]

theorem EtaEigen.inv {γ : Matrix.SpecialLinearGroup (Fin 2) ℤ} {a : ℤ}
    (hγ : EtaEigen γ a) : EtaEigen γ⁻¹ (-a) := by
  have h := congrArg (fun f : ℍ → ℂ ↦ f ∣[(1 : ℤ)] γ⁻¹) hγ
  simp only [← SlashAction.slash_mul, mul_inv_cancel, SlashAction.slash_one,
    SL_smul_slash] at h
  change etaTwo ∣[(1 : ℤ)] γ⁻¹ = etaRoot ^ (-a) • etaTwo
  conv_rhs => rw [h]
  rw [smul_smul, ← zpow_add₀ etaRoot_ne_zero, neg_add_cancel, zpow_zero, one_smul]

theorem EtaEigen.pow {γ : Matrix.SpecialLinearGroup (Fin 2) ℤ} {a : ℤ}
    (hγ : EtaEigen γ a) (n : ℕ) : EtaEigen (γ ^ n) (a * n) := by
  induction n with
  | zero => simpa using etaEigen_one
  | succ n ih => simpa [pow_succ, Nat.cast_add, mul_add] using ih.mul hγ

theorem EtaEigen.zpow {γ : Matrix.SpecialLinearGroup (Fin 2) ℤ} {a : ℤ}
    (hγ : EtaEigen γ a) (n : ℤ) : EtaEigen (γ ^ n) (a * n) := by
  cases n with
  | ofNat n => simpa using hγ.pow n
  | negSucc n =>
    rw [show Int.negSucc n = -((n + 1 : ℕ) : ℤ) by omega, zpow_neg, zpow_natCast, mul_neg]
    exact (hγ.pow (n + 1)).inv

theorem etaEigen_T_zpow (n : ℤ) : EtaEigen (ModularGroup.T ^ n) n := by
  simpa using etaEigen_T.zpow n

end Zeta7LevelSeven
