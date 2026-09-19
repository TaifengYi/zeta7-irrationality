import Zeta7Proof.Radius49U7Formal

/-! Radius internalization, HM: the seven proved power-sum identities
`Σ_{k<7} x((τ+k)/7)^m = p_m(x(τ))` and `7 U₇(x^m) = p_m(x)` for `m = 1, …, 7`. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open PowerSeries Filter Topology UpperHalfPlane
namespace Zeta7Radius49
open Zeta7Arch Zeta7LevelSeven Zeta7Valence Zeta7Main

theorem cert_sum_1 (X : ℂ) (_ : X ≠ 0) : X ^ 1 * pM 1 X =
    ∑ i ∈ Finset.range (1 + 1), ((qM 1 i : ℚ) : ℂ) * (polyP X * polyN X ^ 3) ^ i * X ^ (1 - i) -
      (1 / 49 : ℂ) ^ 1 := by
  rw [trace_cert_1 X]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, polyP, polyN, polyPc, polyNc]
  push_cast
  norm_num

theorem powerSum_1 : ∀ᶠ τ : ℍ in atImInfty,
    ∑ k ∈ Finset.range 7, Xf (((τ : ℂ) + k) / 7) ^ 1 = pM 1 (etaCoordinate τ) :=
  powerSum_eventually 1 (by norm_num) (fun i => ((qM 1 i : ℚ) : ℂ)) (pM 1)
    (by apply Continuous.continuousAt; show Continuous fun X : ℂ => pM _ X; simp only [pM]; fun_prop)
    (by simp [pM]) cert_sum_1

theorem seven_uSeven_x_pow_1 : 7 * uSeven (xSeries ^ 1) = pM 1 xSeries :=
  seven_uSeven_xSeries_pow_of 1 (by norm_num) powerSum_1

theorem cert_sum_2 (X : ℂ) (_ : X ≠ 0) : X ^ 2 * pM 2 X =
    ∑ i ∈ Finset.range (2 + 1), ((qM 2 i : ℚ) : ℂ) * (polyP X * polyN X ^ 3) ^ i * X ^ (2 - i) -
      (1 / 49 : ℂ) ^ 2 := by
  rw [trace_cert_2 X]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, polyP, polyN, polyPc, polyNc]
  push_cast
  norm_num

theorem powerSum_2 : ∀ᶠ τ : ℍ in atImInfty,
    ∑ k ∈ Finset.range 7, Xf (((τ : ℂ) + k) / 7) ^ 2 = pM 2 (etaCoordinate τ) :=
  powerSum_eventually 2 (by norm_num) (fun i => ((qM 2 i : ℚ) : ℂ)) (pM 2)
    (by apply Continuous.continuousAt; show Continuous fun X : ℂ => pM _ X; simp only [pM]; fun_prop)
    (by simp [pM]) cert_sum_2

theorem seven_uSeven_x_pow_2 : 7 * uSeven (xSeries ^ 2) = pM 2 xSeries :=
  seven_uSeven_xSeries_pow_of 2 (by norm_num) powerSum_2

theorem cert_sum_3 (X : ℂ) (_ : X ≠ 0) : X ^ 3 * pM 3 X =
    ∑ i ∈ Finset.range (3 + 1), ((qM 3 i : ℚ) : ℂ) * (polyP X * polyN X ^ 3) ^ i * X ^ (3 - i) -
      (1 / 49 : ℂ) ^ 3 := by
  rw [trace_cert_3 X]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, polyP, polyN, polyPc, polyNc]
  push_cast
  norm_num

theorem powerSum_3 : ∀ᶠ τ : ℍ in atImInfty,
    ∑ k ∈ Finset.range 7, Xf (((τ : ℂ) + k) / 7) ^ 3 = pM 3 (etaCoordinate τ) :=
  powerSum_eventually 3 (by norm_num) (fun i => ((qM 3 i : ℚ) : ℂ)) (pM 3)
    (by apply Continuous.continuousAt; show Continuous fun X : ℂ => pM _ X; simp only [pM]; fun_prop)
    (by simp [pM]) cert_sum_3

theorem seven_uSeven_x_pow_3 : 7 * uSeven (xSeries ^ 3) = pM 3 xSeries :=
  seven_uSeven_xSeries_pow_of 3 (by norm_num) powerSum_3

theorem cert_sum_4 (X : ℂ) (_ : X ≠ 0) : X ^ 4 * pM 4 X =
    ∑ i ∈ Finset.range (4 + 1), ((qM 4 i : ℚ) : ℂ) * (polyP X * polyN X ^ 3) ^ i * X ^ (4 - i) -
      (1 / 49 : ℂ) ^ 4 := by
  rw [trace_cert_4 X]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, polyP, polyN, polyPc, polyNc]
  push_cast
  norm_num

theorem powerSum_4 : ∀ᶠ τ : ℍ in atImInfty,
    ∑ k ∈ Finset.range 7, Xf (((τ : ℂ) + k) / 7) ^ 4 = pM 4 (etaCoordinate τ) :=
  powerSum_eventually 4 (by norm_num) (fun i => ((qM 4 i : ℚ) : ℂ)) (pM 4)
    (by apply Continuous.continuousAt; show Continuous fun X : ℂ => pM _ X; simp only [pM]; fun_prop)
    (by simp [pM]) cert_sum_4

theorem seven_uSeven_x_pow_4 : 7 * uSeven (xSeries ^ 4) = pM 4 xSeries :=
  seven_uSeven_xSeries_pow_of 4 (by norm_num) powerSum_4

theorem cert_sum_5 (X : ℂ) (_ : X ≠ 0) : X ^ 5 * pM 5 X =
    ∑ i ∈ Finset.range (5 + 1), ((qM 5 i : ℚ) : ℂ) * (polyP X * polyN X ^ 3) ^ i * X ^ (5 - i) -
      (1 / 49 : ℂ) ^ 5 := by
  rw [trace_cert_5 X]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, polyP, polyN, polyPc, polyNc]
  push_cast
  norm_num

theorem powerSum_5 : ∀ᶠ τ : ℍ in atImInfty,
    ∑ k ∈ Finset.range 7, Xf (((τ : ℂ) + k) / 7) ^ 5 = pM 5 (etaCoordinate τ) :=
  powerSum_eventually 5 (by norm_num) (fun i => ((qM 5 i : ℚ) : ℂ)) (pM 5)
    (by apply Continuous.continuousAt; show Continuous fun X : ℂ => pM _ X; simp only [pM]; fun_prop)
    (by simp [pM]) cert_sum_5

theorem seven_uSeven_x_pow_5 : 7 * uSeven (xSeries ^ 5) = pM 5 xSeries :=
  seven_uSeven_xSeries_pow_of 5 (by norm_num) powerSum_5

theorem cert_sum_6 (X : ℂ) (_ : X ≠ 0) : X ^ 6 * pM 6 X =
    ∑ i ∈ Finset.range (6 + 1), ((qM 6 i : ℚ) : ℂ) * (polyP X * polyN X ^ 3) ^ i * X ^ (6 - i) -
      (1 / 49 : ℂ) ^ 6 := by
  rw [trace_cert_6 X]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, polyP, polyN, polyPc, polyNc]
  push_cast
  norm_num

theorem powerSum_6 : ∀ᶠ τ : ℍ in atImInfty,
    ∑ k ∈ Finset.range 7, Xf (((τ : ℂ) + k) / 7) ^ 6 = pM 6 (etaCoordinate τ) :=
  powerSum_eventually 6 (by norm_num) (fun i => ((qM 6 i : ℚ) : ℂ)) (pM 6)
    (by apply Continuous.continuousAt; show Continuous fun X : ℂ => pM _ X; simp only [pM]; fun_prop)
    (by simp [pM]) cert_sum_6

theorem seven_uSeven_x_pow_6 : 7 * uSeven (xSeries ^ 6) = pM 6 xSeries :=
  seven_uSeven_xSeries_pow_of 6 (by norm_num) powerSum_6

theorem cert_sum_7 (X : ℂ) (_ : X ≠ 0) : X ^ 7 * pM 7 X =
    ∑ i ∈ Finset.range (7 + 1), ((qM 7 i : ℚ) : ℂ) * (polyP X * polyN X ^ 3) ^ i * X ^ (7 - i) -
      (1 / 49 : ℂ) ^ 7 := by
  rw [trace_cert_7 X]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, polyP, polyN, polyPc, polyNc]
  push_cast
  norm_num

theorem powerSum_7 : ∀ᶠ τ : ℍ in atImInfty,
    ∑ k ∈ Finset.range 7, Xf (((τ : ℂ) + k) / 7) ^ 7 = pM 7 (etaCoordinate τ) :=
  powerSum_eventually 7 (by norm_num) (fun i => ((qM 7 i : ℚ) : ℂ)) (pM 7)
    (by apply Continuous.continuousAt; show Continuous fun X : ℂ => pM _ X; simp only [pM]; fun_prop)
    (by simp [pM]) cert_sum_7

theorem seven_uSeven_x_pow_7 : 7 * uSeven (xSeries ^ 7) = pM 7 xSeries :=
  seven_uSeven_xSeries_pow_of 7 (by norm_num) powerSum_7

end Zeta7Radius49
