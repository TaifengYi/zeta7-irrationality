import Zeta7Proof.Radius49GeometryCore
import Zeta7Proof.Radius49Restricted
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean

/-! Mechanical deductions from the explicitly separated geometric input.
The parametric theorem below does not use an external mathematical axiom. -/

set_option autoImplicit false
noncomputable section
namespace Zeta7Main
open PowerSeries Filter Topology Zeta7Radius49
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

/-- Coefficient decay derived from a Gauss-completion representative, its full
cusp identity, and the already proved inverse coordinate. The geometric input
is an explicit hypothesis here; it is not a transitive axiom of this theorem. -/
theorem HSeries_radius49_of_geometric_continuation
    (hgeom : HasRadius49GeometricContinuation) :
    ∀ ρ : ℝ, 0 < ρ → ρ < 49 →
      Tendsto (fun n : ℕ => ‖coeff n HSeries‖ * ρ ^ n) atTop (𝓝 0) := by
  intro ρ hρ hρ49
  obtain ⟨F, hF⟩ := hgeom ρ hρ hρ49
  have hq : HasSubst qSeries := HasSubst.of_constantCoeff_zero' qSeries_constant
  have hxm : HasSubst (xSeries.map (algebraMap ℚ ℚ_[7])) :=
    HasSubst.of_constantCoeff_zero' (by
      rw [← coeff_zero_eq_constantCoeff, coeff_map, coeff_zero_eq_constantCoeff,
        xSeries_constant, map_zero])
  have hqm : HasSubst (qSeries.map (algebraMap ℚ ℚ_[7])) :=
    HasSubst.of_constantCoeff_zero' (by
      rw [← coeff_zero_eq_constantCoeff, coeff_map, coeff_zero_eq_constantCoeff,
        qSeries_constant, map_zero])
  have hinv : (xSeries.map (algebraMap ℚ ℚ_[7])).subst
      (qSeries.map (algebraMap ℚ ℚ_[7])) = X := by
    calc
      _ = (xSeries.subst qSeries).map (algebraMap ℚ ℚ_[7]) :=
        (map_subst (h := algebraMap ℚ ℚ_[7]) hq xSeries).symm
      _ = X := by
        rw [x_subst_q]
        exact PowerSeries.map_X _
  have hsame := congrArg
    (fun S : ℚ_[7]⟦X⟧ => S.subst (qSeries.map (algebraMap ℚ ℚ_[7])))
    (hF.trans HSeries_subst_xSeries.symm)
  simp only [subst_comp_subst_apply hxm hqm, hinv, X_subst] at hsame
  simpa only [hsame] using discSeries_decay ρ hρ F

end Zeta7Main
