/-
Copyright (c) 2026 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Topology.Algebra.UniformConvergence

/-! Minimal adaptation of ANR-FALSE/PadicModForms, commit
f463dbbae6d24e08538ebe49b86718f094c5026a, ForMathlib/PowerSeriesTopology.
Only the pulled-back uniform structure and its convergence equivalence are
needed. The scope is project-specific and does not change the coefficientwise
topology used in the existing formal infinite products and Lambert sums. -/

set_option autoImplicit false
open Filter Topology PowerSeries

namespace Zeta7UniformTopology
variable {R : Type*} [Ring R] [UniformSpace R]

noncomputable scoped instance uniformSpace : UniformSpace R⟦X⟧ :=
  .comap (fun f => UniformFun.ofFun fun n => coeff n f) inferInstance

/-- Convergence in this topology is uniform over all coefficient indices. -/
theorem tendsto_iff_tendstoUniformly {ι : Type*} {l : Filter ι}
    {F : ι → R⟦X⟧} {f : R⟦X⟧} :
    Tendsto F l (𝓝 f) ↔ TendstoUniformly (fun i n => coeff n (F i)) (coeff · f) l := by
  rw [(isUniformInducing_iff_uniformSpace.mpr rfl).isInducing.tendsto_nhds_iff]
  exact UniformFun.tendsto_iff_tendstoUniformly

end Zeta7UniformTopology
