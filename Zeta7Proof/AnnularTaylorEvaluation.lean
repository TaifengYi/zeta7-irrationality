import Zeta7Proof.AnnularEulerRules

/-! Evaluation of summable Taylor series in the actual complete annulus ring.
All uses of additivity and reindexing carry their summability proofs. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
open PowerSeries Filter Topology
namespace Zeta7Annulus.ClosedAnnulus
local instance AnnularTaylorEvaluation_local1 : Fact (Nat.Prime 7) := ⟨by decide⟩
variable {r R : ℝ} [Fact (0 < r)] [Fact (0 < R)]

def TaylorSummable (f : ℚ_[7]⟦X⟧) (s : ClosedAnnulus r R) : Prop :=
  Summable (fun n : ℕ => constant (coeff n f) * s ^ n)

def taylorValue (f : ℚ_[7]⟦X⟧) (s : ClosedAnnulus r R) : ClosedAnnulus r R :=
  ∑' n : ℕ, constant (coeff n f) * s ^ n

theorem TaylorSummable.add {f g : ℚ_[7]⟦X⟧} {s : ClosedAnnulus r R}
    (hf : TaylorSummable f s) (hg : TaylorSummable g s) : TaylorSummable (f + g) s := by
  simpa only [TaylorSummable, map_add, add_mul] using Summable.add hf hg

theorem taylorValue_add {f g : ℚ_[7]⟦X⟧} {s : ClosedAnnulus r R}
    (hf : TaylorSummable f s) (hg : TaylorSummable g s) :
    taylorValue (f + g) s = taylorValue f s + taylorValue g s := by
  simp only [taylorValue, map_add, add_mul]
  exact hf.tsum_add hg

theorem TaylorSummable.C_mul {f : ℚ_[7]⟦X⟧} {s : ClosedAnnulus r R}
    (hf : TaylorSummable f s) (a : ℚ_[7]) : TaylorSummable (C a * f) s := by
  simpa only [TaylorSummable, coeff_C_mul, map_mul, mul_assoc] using hf.mul_left (constant a)

theorem taylorValue_C_mul (a : ℚ_[7]) {f : ℚ_[7]⟦X⟧} {s : ClosedAnnulus r R}
    (hf : TaylorSummable f s) :
    taylorValue (C a * f) s = constant a * taylorValue f s := by
  simp only [taylorValue, coeff_C_mul, map_mul, mul_assoc]
  exact hf.tsum_mul_left _

theorem TaylorSummable.X_mul {f : ℚ_[7]⟦X⟧} {s : ClosedAnnulus r R}
    (hf : TaylorSummable f s) : TaylorSummable (X * f) s := by
  apply (summable_nat_add_iff 1).mp
  simpa only [coeff_succ_X_mul, pow_succ, mul_assoc] using hf.mul_right s

theorem taylorValue_X_mul {f : ℚ_[7]⟦X⟧} {s : ClosedAnnulus r R}
    (hf : TaylorSummable f s) : taylorValue (X * f) s = s * taylorValue f s := by
  have hs := hf.X_mul
  unfold taylorValue
  rw [hs.tsum_eq_zero_add]
  simp only [coeff_zero_X_mul, map_zero, zero_mul, zero_add, coeff_succ_X_mul,
    pow_succ, ← mul_assoc]
  rw [hf.tsum_mul_right]
  exact mul_comm _ _

theorem taylorValue_derivative_chain {f : ℚ_[7]⟦X⟧} {s : ClosedAnnulus r R}
    (hf : TaylorSummable f s) (hdf : TaylorSummable (PowerSeries.derivative ℚ_[7] f) s) :
    euler (taylorValue f s) = taylorValue (PowerSeries.derivative ℚ_[7] f) s * euler s := by
  have hd := hf.map (eulerAddHom (r := r) (R := R)) euler_continuous
  change Summable (fun n : ℕ => euler (constant (coeff n f) * s ^ n)) at hd
  unfold taylorValue
  rw [euler_tsum hf, hd.tsum_eq_zero_add]
  simp only [pow_zero, mul_one, euler_constant, zero_add]
  rw [← hdf.tsum_mul_right]
  apply tsum_congr
  intro n
  rw [euler_constant_mul, euler_pow_succ, coeff_derivative, map_mul]
  have hn : constant (r := r) (R := R) ((n : ℚ_[7]) + 1) = (n : ClosedAnnulus r R) + 1 := by
    rw [map_add, map_natCast, map_one]
  rw [hn]
  ring

end Zeta7Annulus.ClosedAnnulus
