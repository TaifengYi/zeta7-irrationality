import Zeta7Proof.AuxiliaryActualDepletion
import Zeta7Proof.AuxiliaryResidueCalculus

/-! Identifies the actual third layer and both Euler jets with the integral
singular part of the exact Lambert depletion, in every coefficient below p². -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
namespace Zeta7Auxiliary
open PowerSeries Zeta7Common
variable {p : ℕ} [Fact p.Prime]

theorem rationalH_third_layer_depletion (hp7 : p ≠ 7) (c : ℚ)
    (hc : ¬p ∣ c.den) (N : ℕ) (hN : N ≤ p^2) (n : Fin N) :
    layerCoefficient (rationalH_cap_three c hc N hN) n =
      layerCoefficient (singularH_cap_zero N hN) n := by
  have hH := rationalH_cap_three c hc N hN
  have hS := singularH_cap_zero (p := p) N hN
  have hR := regularH_cap_zero c hc N
  simp only [layerCoefficient_eq_residue, pow_zero, one_mul]
  apply integralResidue_congr_mod_prime (hH n n.isLt)
    (show Integral (coeff n.val ((singularH p).map (algebraMap ℚ ℚ_[p]))) from by
      simpa only [pow_zero, one_mul] using hS n n.isLt)
    (((integral_nat (p := p) p).pow 2).mul (show
      Integral (coeff n.val ((regularH p c).map (algebraMap ℚ ℚ_[p]))) from by
        simpa only [pow_zero, one_mul] using hR n n.isLt))
  have h := congrArg (fun f : PowerSeries ℚ => coeff n.val (f.map (algebraMap ℚ ℚ_[p])))
    (rationalH_scaled_depletion hp7 c)
  simp only [map_mul, map_add, map_C, coeff_C_mul] at h
  simp only [map_pow, map_natCast] at h
  simpa only [pow_succ, mul_assoc, mul_comm, mul_left_comm] using h

theorem rationalH_third_jet_layers (hp7 : p ≠ 7) (c : ℚ)
    (hc : ¬p ∣ c.den) (N : ℕ) (hN : N ≤ p^2) (n : Fin N) :
    layerCoefficient (rationalH_cap_three c hc N hN).euler n =
      (n.val : ZMod p)*layerCoefficient (singularH_cap_zero N hN) n ∧
    layerCoefficient (rationalH_cap_three c hc N hN).euler.euler n =
      (n.val : ZMod p)^2*layerCoefficient (singularH_cap_zero N hN) n := by
  rw [layerCoefficient_euler (rationalH_cap_three c hc N hN),
    layerCoefficient_euler (rationalH_cap_three c hc N hN).euler,
    layerCoefficient_euler (rationalH_cap_three c hc N hN),
    rationalH_third_layer_depletion hp7 c hc N hN n]
  constructor
  · rfl
  · ring

end Zeta7Auxiliary
