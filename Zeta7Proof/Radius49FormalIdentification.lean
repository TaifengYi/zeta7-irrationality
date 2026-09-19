import Zeta7Proof.GenusSevenCoordinate

/-! Gates A and B of the independent radius audit: exact formal identities.
All substitutions use the existing zero-constant coordinates. No analytic
continuation, global inverse of A, or weight-zero recurrence is assumed. -/

set_option autoImplicit false
noncomputable section
namespace Zeta7Main
open PowerSeries
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

/-- The manuscript formula, with the project's rational-to-seven-adic maps. -/
theorem HSeries_eq_product_subst_qSeries :
    HSeries =
      (ASeries.map (algebraMap ℚ ℚ_[7]) *
        (GSeries.map (algebraMap ℚ ℚ_[7]) + C eta)).subst
          (qSeries.map (algebraMap ℚ ℚ_[7])) := by
  have hq : HasSubst qSeries := HasSubst.of_constantCoeff_zero' qSeries_constant
  have hqm : HasSubst (qSeries.map (algebraMap ℚ ℚ_[7])) :=
    HasSubst.of_constantCoeff_zero' (by
      rw [← coeff_zero_eq_constantCoeff, coeff_map, coeff_zero_eq_constantCoeff,
        qSeries_constant, map_zero])
  rw [subst_mul hqm, subst_add hqm, subst_C]
  unfold HSeries BSeries
  exact congrArg₂ (fun u v : ℚ_[7]⟦X⟧ => u * (v + C eta))
    (map_subst (h := algebraMap ℚ ℚ_[7]) hq ASeries)
    (map_subst (h := algebraMap ℚ ℚ_[7]) hq GSeries)

/-- Equality of complete q-series, using the proved compositional inverse. -/
theorem HSeries_subst_xSeries :
    HSeries.subst (xSeries.map (algebraMap ℚ ℚ_[7])) =
      ASeries.map (algebraMap ℚ ℚ_[7]) *
        (GSeries.map (algebraMap ℚ ℚ_[7]) + C eta) := by
  have hx : HasSubst xSeries := HasSubst.of_constantCoeff_zero' xSeries_constant
  have hqm : HasSubst (qSeries.map (algebraMap ℚ ℚ_[7])) :=
    HasSubst.of_constantCoeff_zero' (by
      rw [← coeff_zero_eq_constantCoeff, coeff_map, coeff_zero_eq_constantCoeff,
        qSeries_constant, map_zero])
  have hxm : HasSubst (xSeries.map (algebraMap ℚ ℚ_[7])) :=
    HasSubst.of_constantCoeff_zero' (by
      rw [← coeff_zero_eq_constantCoeff, coeff_map, coeff_zero_eq_constantCoeff,
        xSeries_constant, map_zero])
  have hinv : (qSeries.map (algebraMap ℚ ℚ_[7])).subst
      (xSeries.map (algebraMap ℚ ℚ_[7])) = X := by
    calc
      _ = (qSeries.subst xSeries).map (algebraMap ℚ ℚ_[7]) :=
        (map_subst (h := algebraMap ℚ ℚ_[7]) hx qSeries).symm
      _ = X := by
        rw [q_subst_x]
        exact PowerSeries.map_X _
  rw [HSeries_eq_product_subst_qSeries, subst_comp_subst_apply hqm hxm, hinv, X_subst]

/-- The same identity in the already identified discriminant-quotient coordinate. -/
theorem HSeries_subst_d7 :
    HSeries.subst (Zeta7GenusSeven.d7.map (algebraMap ℚ ℚ_[7])) =
      ASeries.map (algebraMap ℚ ℚ_[7]) *
        (GSeries.map (algebraMap ℚ ℚ_[7]) + C eta) := by
  rw [Zeta7GenusSeven.d7_eq_xSeries, HSeries_subst_xSeries]

/-- The multiplier times the genuine formal Eisenstein specialization. -/
theorem HSeries_subst_xSeries_eisenstein :
    HSeries.subst (xSeries.map (algebraMap ℚ ℚ_[7])) =
      ASeries.map (algebraMap ℚ ℚ_[7]) * eisensteinMinusTwo := by
  rw [eisensteinMinusTwo_eq_G_add_eta, HSeries_subst_xSeries]

/-- Normalization x=t/49 in every degree, with an integer exponent in Q_7. -/
theorem normalisedHSeries_coeff_neg_int (n : ℕ) :
    coeff n normalisedHSeries =
      (49 : ℚ_[7]) ^ (-(n : ℤ)) * coeff n HSeries := by
  rw [normalisedHSeries_coeff, zpow_neg, zpow_natCast, inv_pow]

end Zeta7Main
