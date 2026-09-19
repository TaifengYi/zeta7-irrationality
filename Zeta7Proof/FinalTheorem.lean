import Zeta7Proof.FinalConditional
import Zeta7Proof.EnergyUpper

/-! **The irrationality theorem**, with the internal radius-49 theorem.

* `Zeta7Main.zeta7Three_irrational`: the actual 7-adic value `ζ₇(3)` (branch 4 of the constructed
  Kubota–Leopoldt function at 3) is not in the image of `ℚ`.
* `Zeta7Main.eta_irrational`: the same for `η = ζ₇(3)/2`; the rational value `0` is included.
* `Zeta7Main.c_theorem_explicit`: the C theorem with the explicit constants `J` and `I` of (48)–(49).

The proof combines, for one and the same determinant `D_d`: N (`D_d ≠ 0`), A (`v₇(D_d) ≥ (43-δ)d² - Kd`),
P (`actualAuxiliaryEstimate`), C (`c_theorem`) together with `energyI_le_explicitI` (the actual energy
of the six-circle measure is at most the explicit energy (48)), the kernel-checked margin
`S > 223/6250` and `log 7 < 2`. -/
noncomputable section
set_option autoImplicit false
namespace Zeta7Main
open Real

/-- **`ζ₇(3)` is irrational**. -/
theorem zeta7Three_irrational : ¬ Zeta7Partial.IsRationalSeven zeta7Three :=
  Zeta7Final.final_contradiction_of_energy_le Zeta7Valence.energyI_le_explicitI

/-- **`η` is irrational**. -/
theorem eta_irrational : ¬ Zeta7Partial.IsRationalSeven eta := by
  rintro ⟨q, hq⟩
  exact Zeta7Final.eta_not_rational_of_energy_le Zeta7Valence.energyI_le_explicitI q hq

/-- **C with the explicit constants**: for every rational `c` and `ε > 0`, eventually
`log |D_d| ≤ (J - (7/2) I + ε) d²` with `J, I` given by (48)–(49). -/
theorem c_theorem_explicit (c : ℚ) {ε : ℝ} (hε : 0 < ε) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀,
      Real.log |(Zeta7Common.actualCommonDeterminant d c : ℝ)| ≤
        (Zeta7Cert.explicitJ - 7 / 2 * Zeta7Cert.explicitI + ε) * (d : ℝ) ^ 2 := by
  obtain ⟨d₀, hd₀⟩ := Zeta7Arch.c_theorem c hε
  refine ⟨d₀, fun d hd => (hd₀ d hd).trans (mul_le_mul_of_nonneg_right ?_ (sq_nonneg _))⟩
  have hJ := Zeta7Final.constJ_eq_actual
  have hJe := Zeta7Cert.explicitJ_eq
  have hI := Zeta7Valence.energyI_le_explicitI
  rw [hJ, hJe]
  linarith

end Zeta7Main
