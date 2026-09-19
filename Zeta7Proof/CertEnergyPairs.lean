import Zeta7Proof.CertEnergyTerms

/-! The explicit energies `E(y_i, y_j)` for all pairs, as upper bounds `E ≤ π c_ij` with
exact rationals `c_ij`, from the generated term certificates. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace Zeta7Cert
open Real

theorem energyE_0_0 : energyE (cy 0) (cy 0) ≤ π * (-1 : ℝ) := by
  have hS : mSet (cy 0) (cy 0) = (∅ : Finset ℕ) := by
    rw [mSet_eq (by norm_num) 1 (by norm_num) (by norm_num)]
    decide
  have hmin : ((min (cy 0) (cy 0) : ℚ) : ℝ) = (1 / 2 : ℝ) := by norm_num
  unfold energyE
  rw [hS, hmin]
  rw [Finset.sum_empty]
  linarith

theorem energyE_0_1 : energyE (cy 0) (cy 1) ≤ π * (-2 / 5 : ℝ) := by
  have hS : mSet (cy 0) (cy 1) = (∅ : Finset ℕ) := by
    rw [mSet_eq (by norm_num) 3 (by norm_num) (by norm_num)]
    decide
  have hmin : ((min (cy 0) (cy 1) : ℚ) : ℝ) = (1 / 5 : ℝ) := by norm_num
  unfold energyE
  rw [hS, hmin]
  rw [Finset.sum_empty]
  linarith

theorem energyE_0_2 : energyE (cy 0) (cy 2) ≤ π * (-19 / 100 : ℝ) := by
  have hS : mSet (cy 0) (cy 2) = (∅ : Finset ℕ) := by
    rw [mSet_eq (by norm_num) 4 (by norm_num) (by norm_num)]
    decide
  have hmin : ((min (cy 0) (cy 2) : ℚ) : ℝ) = (19 / 200 : ℝ) := by norm_num
  unfold energyE
  rw [hS, hmin]
  rw [Finset.sum_empty]
  linarith

theorem energyE_0_3 : energyE (cy 0) (cy 3) ≤ π * (-11 / 100 : ℝ) := by
  have hS : mSet (cy 0) (cy 3) = (∅ : Finset ℕ) := by
    rw [mSet_eq (by norm_num) 6 (by norm_num) (by norm_num)]
    decide
  have hmin : ((min (cy 0) (cy 3) : ℚ) : ℝ) = (11 / 200 : ℝ) := by norm_num
  unfold energyE
  rw [hS, hmin]
  rw [Finset.sum_empty]
  linarith

theorem energyE_0_4 : energyE (cy 0) (cy 4) ≤ π * (-158089174121110777 / 3062500000000000000 : ℝ) := by
  have hS : mSet (cy 0) (cy 4) = ({7} : Finset ℕ) := by
    rw [mSet_eq (by norm_num) 7 (by norm_num) (by norm_num)]
    decide
  have hmin : ((min (cy 0) (cy 4) : ℚ) : ℝ) = (7 / 200 : ℝ) := by norm_num
  unfold energyE
  rw [hS, hmin]
  rw [Finset.sum_singleton]
  linarith [eTerm_0_4_7]

theorem energyE_0_5 : energyE (cy 0) (cy 5) ≤ π * (395574566039673787 / 6125000000000000000 : ℝ) := by
  have hS : mSet (cy 0) (cy 5) = ({7} : Finset ℕ) := by
    rw [mSet_eq (by norm_num) 9 (by norm_num) (by norm_num)]
    decide
  have hmin : ((min (cy 0) (cy 5) : ℚ) : ℝ) = (23 / 1000 : ℝ) := by norm_num
  unfold energyE
  rw [hS, hmin]
  rw [Finset.sum_singleton]
  linarith [eTerm_0_5_7]

theorem energyE_1_1 : energyE (cy 1) (cy 1) ≤ π * (-2 / 5 : ℝ) := by
  have hS : mSet (cy 1) (cy 1) = (∅ : Finset ℕ) := by
    rw [mSet_eq (by norm_num) 4 (by norm_num) (by norm_num)]
    decide
  have hmin : ((min (cy 1) (cy 1) : ℚ) : ℝ) = (1 / 5 : ℝ) := by norm_num
  unfold energyE
  rw [hS, hmin]
  rw [Finset.sum_empty]
  linarith

theorem energyE_1_2 : energyE (cy 1) (cy 2) ≤ π * (-225344191231120963 / 1225000000000000000 : ℝ) := by
  have hS : mSet (cy 1) (cy 2) = ({7} : Finset ℕ) := by
    rw [mSet_eq (by norm_num) 7 (by norm_num) (by norm_num)]
    decide
  have hmin : ((min (cy 1) (cy 2) : ℚ) : ℝ) = (19 / 200 : ℝ) := by norm_num
  unfold energyE
  rw [hS, hmin]
  rw [Finset.sum_singleton]
  linarith [eTerm_1_2_7]

theorem energyE_1_3 : energyE (cy 1) (cy 3) ≤ π * (17473871930039177 / 1531250000000000000 : ℝ) := by
  have hS : mSet (cy 1) (cy 3) = ({7} : Finset ℕ) := by
    rw [mSet_eq (by norm_num) 9 (by norm_num) (by norm_num)]
    decide
  have hmin : ((min (cy 1) (cy 3) : ℚ) : ℝ) = (11 / 200 : ℝ) := by norm_num
  unfold energyE
  rw [hS, hmin]
  rw [Finset.sum_singleton]
  linarith [eTerm_1_3_7]

theorem energyE_1_4 : energyE (cy 1) (cy 4) ≤ π * (982414814731281811 / 6125000000000000000 : ℝ) := by
  have hS : mSet (cy 1) (cy 4) = ({7} : Finset ℕ) := by
    rw [mSet_eq (by norm_num) 11 (by norm_num) (by norm_num)]
    decide
  have hmin : ((min (cy 1) (cy 4) : ℚ) : ℝ) = (7 / 200 : ℝ) := by norm_num
  unfold energyE
  rw [hS, hmin]
  rw [Finset.sum_singleton]
  linarith [eTerm_1_4_7]

theorem energyE_1_5 : energyE (cy 1) (cy 5) ≤ π * (3417865465084745279 / 12250000000000000000 : ℝ) := by
  have hS : mSet (cy 1) (cy 5) = ({7, 14} : Finset ℕ) := by
    rw [mSet_eq (by norm_num) 14 (by norm_num) (by norm_num)]
    decide
  have hmin : ((min (cy 1) (cy 5) : ℚ) : ℝ) = (23 / 1000 : ℝ) := by norm_num
  unfold energyE
  rw [hS, hmin]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]
  linarith [eTerm_1_5_7, eTerm_1_5_14]

theorem energyE_2_2 : energyE (cy 2) (cy 2) ≤ π * (-123794970974755907 / 6125000000000000000 : ℝ) := by
  have hS : mSet (cy 2) (cy 2) = ({7} : Finset ℕ) := by
    rw [mSet_eq (by norm_num) 10 (by norm_num) (by norm_num)]
    decide
  have hmin : ((min (cy 2) (cy 2) : ℚ) : ℝ) = (19 / 200 : ℝ) := by norm_num
  unfold energyE
  rw [hS, hmin]
  rw [Finset.sum_singleton]
  linarith [eTerm_2_2_7]

theorem energyE_2_3 : energyE (cy 2) (cy 3) ≤ π * (113774657375926811 / 612500000000000000 : ℝ) := by
  have hS : mSet (cy 2) (cy 3) = ({7} : Finset ℕ) := by
    rw [mSet_eq (by norm_num) 13 (by norm_num) (by norm_num)]
    decide
  have hmin : ((min (cy 2) (cy 3) : ℚ) : ℝ) = (11 / 200 : ℝ) := by norm_num
  unfold energyE
  rw [hS, hmin]
  rw [Finset.sum_singleton]
  linarith [eTerm_2_3_7]

theorem energyE_2_4 : energyE (cy 2) (cy 4) ≤ π * (73050018644805901 / 218750000000000000 : ℝ) := by
  have hS : mSet (cy 2) (cy 4) = ({7, 14} : Finset ℕ) := by
    rw [mSet_eq (by norm_num) 17 (by norm_num) (by norm_num)]
    decide
  have hmin : ((min (cy 2) (cy 4) : ℚ) : ℝ) = (7 / 200 : ℝ) := by norm_num
  unfold energyE
  rw [hS, hmin]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]
  linarith [eTerm_2_4_7, eTerm_2_4_14]

theorem energyE_2_5 : energyE (cy 2) (cy 5) ≤ π * (222244188368437009 / 490000000000000000 : ℝ) := by
  have hS : mSet (cy 2) (cy 5) = ({7, 14, 21} : Finset ℕ) := by
    rw [mSet_eq (by norm_num) 21 (by norm_num) (by norm_num)]
    decide
  have hmin : ((min (cy 2) (cy 5) : ℚ) : ℝ) = (23 / 1000 : ℝ) := by norm_num
  unfold energyE
  rw [hS, hmin]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  linarith [eTerm_2_5_7, eTerm_2_5_14, eTerm_2_5_21]

theorem energyE_3_3 : energyE (cy 3) (cy 3) ≤ π * (7750171634986248959 / 24500000000000000000 : ℝ) := by
  have hS : mSet (cy 3) (cy 3) = ({7, 14} : Finset ℕ) := by
    rw [mSet_eq (by norm_num) 18 (by norm_num) (by norm_num)]
    decide
  have hmin : ((min (cy 3) (cy 3) : ℚ) : ℝ) = (11 / 200 : ℝ) := by norm_num
  unfold energyE
  rw [hS, hmin]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]
  linarith [eTerm_3_3_7, eTerm_3_3_14]

theorem energyE_3_4 : energyE (cy 3) (cy 4) ≤ π * (75433052779222331 / 164062500000000000 : ℝ) := by
  have hS : mSet (cy 3) (cy 4) = ({7, 14, 21} : Finset ℕ) := by
    rw [mSet_eq (by norm_num) 22 (by norm_num) (by norm_num)]
    decide
  have hmin : ((min (cy 3) (cy 4) : ℚ) : ℝ) = (7 / 200 : ℝ) := by norm_num
  unfold energyE
  rw [hS, hmin]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  linarith [eTerm_3_4_7, eTerm_3_4_14, eTerm_3_4_21]

theorem energyE_3_5 : energyE (cy 3) (cy 5) ≤ π * (28558097555282334481 / 49000000000000000000 : ℝ) := by
  have hS : mSet (cy 3) (cy 5) = ({7, 14, 21, 28} : Finset ℕ) := by
    rw [mSet_eq (by norm_num) 28 (by norm_num) (by norm_num)]
    decide
  have hmin : ((min (cy 3) (cy 5) : ℚ) : ℝ) = (23 / 1000 : ℝ) := by norm_num
  unfold energyE
  rw [hS, hmin]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  linarith [eTerm_3_5_7, eTerm_3_5_14, eTerm_3_5_21, eTerm_3_5_28]

theorem energyE_4_4 : energyE (cy 4) (cy 4) ≤ π * (41623758970731878849 / 73500000000000000000 : ℝ) := by
  have hS : mSet (cy 4) (cy 4) = ({7, 14, 21, 28} : Finset ℕ) := by
    rw [mSet_eq (by norm_num) 28 (by norm_num) (by norm_num)]
    decide
  have hmin : ((min (cy 4) (cy 4) : ℚ) : ℝ) = (7 / 200 : ℝ) := by norm_num
  unfold energyE
  rw [hS, hmin]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  linarith [eTerm_4_4_7, eTerm_4_4_14, eTerm_4_4_21, eTerm_4_4_28]

theorem energyE_4_5 : energyE (cy 4) (cy 5) ≤ π * (2527338498354108752363 / 3675000000000000000000 : ℝ) := by
  have hS : mSet (cy 4) (cy 5) = ({7, 14, 21, 28, 35} : Finset ℕ) := by
    rw [mSet_eq (by norm_num) 35 (by norm_num) (by norm_num)]
    decide
  have hmin : ((min (cy 4) (cy 5) : ℚ) : ℝ) = (23 / 1000 : ℝ) := by norm_num
  unfold energyE
  rw [hS, hmin]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  linarith [eTerm_4_5_7, eTerm_4_5_14, eTerm_4_5_21, eTerm_4_5_28, eTerm_4_5_35]

theorem energyE_5_5 : energyE (cy 5) (cy 5) ≤ π * (2892649108081420543873 / 3675000000000000000000 : ℝ) := by
  have hS : mSet (cy 5) (cy 5) = ({7, 14, 21, 28, 35, 42} : Finset ℕ) := by
    rw [mSet_eq (by norm_num) 43 (by norm_num) (by norm_num)]
    decide
  have hmin : ((min (cy 5) (cy 5) : ℚ) : ℝ) = (23 / 1000 : ℝ) := by norm_num
  unfold energyE
  rw [hS, hmin]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  linarith [eTerm_5_5_7, eTerm_5_5_14, eTerm_5_5_21, eTerm_5_5_28, eTerm_5_5_35, eTerm_5_5_42]

end Zeta7Cert
