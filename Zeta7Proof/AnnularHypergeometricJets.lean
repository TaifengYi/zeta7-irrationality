import Zeta7Proof.AnnularTaylorEvaluation

/-! Every ordinary derivative of the original hypergeometric series converges
at the actual annular substitution. The resulting values obey the Euler chain rule. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
open PowerSeries Filter Topology
namespace Zeta7Annulus
local instance AnnularHypergeometricJets_local1 : Fact (Nat.Prime 7) := ⟨by decide⟩

def hypergeometricJetSeries (i : Fin 2) (j : ℕ) : ℚ_[7]⟦X⟧ :=
  (PowerSeries.derivative ℚ_[7])^[j] (annularHypergeometricPadic i)

theorem hypergeometricJetSeries_succ (i : Fin 2) (j : ℕ) :
    hypergeometricJetSeries i (j + 1) = PowerSeries.derivative ℚ_[7] (hypergeometricJetSeries i j) :=
  Function.iterate_succ_apply' _ _ _

theorem hypergeometricJetSeries_coeff_bound (i : Fin 2) (j n : ℕ) (hn : 0 < n + j) :
    ‖coeff n (hypergeometricJetSeries i j)‖ ≤ 12 * ((n : ℝ) + j) := by
  rw [hypergeometricJetSeries, coeff_iterate_derivative]
  have hi : ‖((n + 1).ascFactorial j : ℚ_[7])‖ ≤ 1 := by
    exact_mod_cast Padic.norm_int_le_one ((n + 1).ascFactorial j : ℤ)
  calc
    _ ≤ ‖coeff (n + j) (annularHypergeometricPadic i)‖ := by
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) hi
    _ ≤ _ := by
      simpa only [annularHypergeometricPadic, coeff_mk, Nat.cast_add] using
        annularHypergeometricCoefficient_norm_bound i (n + j) hn

namespace ClosedAnnulus
variable {r R : ℝ} [Fact (0 < r)] [Fact (0 < R)]

theorem hypergeometricJetSeries_summable (i : Fin 2) (j : ℕ)
    (s : ClosedAnnulus r R) (hs : ‖s‖ < 1) : TaylorSummable (hypergeometricJetSeries i j) s := by
  apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
  rw [tendsto_zero_iff_norm_tendsto_zero, Nat.cofinite_eq_atTop]
  have ht1 := tendsto_self_mul_const_pow_of_lt_one (norm_nonneg s) hs
  have ht2 := (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg s) hs).const_mul (j : ℝ)
  have ht := (ht1.add ht2).const_mul (12 : ℝ)
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) ?_
    (by simpa only [zero_add, mul_zero] using ht)
  filter_upwards [eventually_gt_atTop 0] with n hn
  calc
    _ ≤ ‖constant (r := r) (R := R) (coeff n (hypergeometricJetSeries i j))‖ * ‖s ^ n‖ :=
      norm_mul_le _ _
    _ ≤ (12 * ((n : ℝ) + j)) * ‖s‖ ^ n := mul_le_mul
      (by simpa only [constant_norm] using hypergeometricJetSeries_coeff_bound i j n (by omega))
      (norm_pow_le _ _) (norm_nonneg _) (by positivity)
    _ = _ := by ring

def hypergeometricJetValue (i : Fin 2) (j : ℕ) (s : ClosedAnnulus r R) : ClosedAnnulus r R :=
  taylorValue (hypergeometricJetSeries i j) s

theorem hypergeometricJetValue_zero (i : Fin 2) (s : ClosedAnnulus r R) :
    hypergeometricJetValue i 0 s = hypergeometricCompose i s := by
  simp only [hypergeometricJetValue, taylorValue, hypergeometricJetSeries,
    Function.iterate_zero, id_eq, annularHypergeometricPadic, coeff_mk, hypergeometricCompose]

theorem hypergeometricJetValue_chain (i : Fin 2) (j : ℕ) (s : ClosedAnnulus r R) (hs : ‖s‖ < 1) :
    euler (hypergeometricJetValue i j s) = hypergeometricJetValue i (j + 1) s * euler s := by
  have hd : TaylorSummable (PowerSeries.derivative ℚ_[7] (hypergeometricJetSeries i j)) s := by
    rw [← hypergeometricJetSeries_succ]
    exact hypergeometricJetSeries_summable i (j + 1) s hs
  rw [hypergeometricJetValue, taylorValue_derivative_chain (hypergeometricJetSeries_summable i j s hs) hd]
  rw [← hypergeometricJetSeries_succ]
  rfl

def actualHypergeometricJet (i : Fin 2) (j : ℕ) : ClosedAnnulus r R :=
  hypergeometricJetValue i j annularSubstitution

theorem actualHypergeometricJet_zero (i : Fin 2) :
    actualHypergeometricJet (r := r) (R := R) i 0 = actualHypergeometricValue i :=
  hypergeometricJetValue_zero i _

theorem actualHypergeometricJet_chain (hr : 1 < r) (hR : R < 49) (hrR : r ≤ R)
    (i : Fin 2) (j : ℕ) :
    euler (actualHypergeometricJet (r := r) (R := R) i j) =
      actualHypergeometricJet i (j + 1) * euler annularSubstitution :=
  hypergeometricJetValue_chain i j _ (annularSubstitution_norm_lt_one hr hR hrR)

end ClosedAnnulus
end Zeta7Annulus
