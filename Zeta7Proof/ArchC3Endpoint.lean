import Zeta7Proof.ArchEnergyIneq

/-! C3 endpoint: the energy inequality (43) and the Gram limsup (45) for the actual measure.

* (43), diagonal-corrected and uniform on `𝒦^n`: for every `ε > 0` there is `t > 0` such that
  for every `n > 0` and every `z ∈ 𝒦^n`,
  `n⁻² Σ_{i,j} max(log|z_i - z_j|, -M_t) - 2 n⁻¹ Σ U(z_i) ≤ -I + ε`.
* (45): for every `ε > 0`, eventually `det G_d ≤ exp((-I + ε) d²)`.

Here `μ = potentialMeasure` is the actual six-circle measure of C1, `U = potentialU`,
`I = energyI`, and `G_d = weightedGram d 𝒦 (e^{-2dU})` is the Gram matrix of (42). -/
noncomputable section
set_option autoImplicit false
namespace Zeta7Arch
open MeasureTheory Filter

theorem c3_endpoint :
    (∀ ε > 0, ∃ t > 0, ∀ n : ℕ, 0 < n → ∀ z : Fin n → ℂ, (∀ i, z i ∈ discK) →
      empiricalEnergy (truncM t) z ≤ -energyI + ε) ∧
    (∀ ε > 0, ∀ᶠ d : ℕ in atTop,
      (weightedGram d discK (gramWeight d)).det.re ≤ Real.exp ((-energyI + ε) * (d : ℝ) ^ 2)) := by
  refine ⟨fun ε hε => ?_, fun ε hε => gram_limsup hε⟩
  obtain ⟨t, ht, herr⟩ := regErr_small (half_pos hε)
  refine ⟨t, ht, fun n hn z hz => ?_⟩
  have := empiricalEnergy_le ht herr hn hz
  linarith

end Zeta7Arch
