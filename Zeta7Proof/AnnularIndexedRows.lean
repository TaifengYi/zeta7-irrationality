import Zeta7Proof.AnnularRowRecurrence0

import Zeta7Proof.AnnularRowRecurrence1

import Zeta7Proof.AnnularRowRecurrence2

import Zeta7Proof.AnnularRowReduction0

import Zeta7Proof.AnnularRowReduction1

import Zeta7Proof.AnnularRowReduction2

import Zeta7Proof.AnnularRowResidual

noncomputable section
set_option autoImplicit false
namespace Zeta7AnnularRows
open Polynomial

def rowNumerator : Fin 4 → Fin 4 → Polynomial ℚ :=
  ![![ell0_0, ell0_1, ell0_2, ell0_3],
    ![ell1_0, ell1_1, ell1_2, ell1_3],
    ![ell2_0, ell2_1, ell2_2, ell2_3],
    ![ell3_0, ell3_1, ell3_2, ell3_3]]

def multiplierNumerator : Fin 3 → Fin 3 → Polynomial ℚ :=
  ![![mu0_1, mu0_2, mu0_3],
    ![mu1_1, mu1_2, mu1_3],
    ![mu2_1, mu2_2, mu2_3]]

theorem indexed_reduction (k i : Fin 3) :
    raw_q * multiplierNumerator k i = rowNumerator k.castSucc i.succ * raw_ds * N ^ 2 := by
  fin_cases k <;> fin_cases i
  · exact reduction_0_1
  · exact reduction_0_2
  · exact reduction_0_3
  · exact reduction_1_1
  · exact reduction_1_2
  · exact reduction_1_3
  · exact reduction_2_1
  · exact reduction_2_2
  · exact reduction_2_3

theorem indexed_recurrence_0 (k : Fin 3) :
    rowNumerator k.succ 0 * P ^ 2 * N ^ 4 =
      derivativeNumerator (rowNumerator k.castSucc 0) * P * N ^ 3 + (C (5/144 : ℚ) * multiplierNumerator k 0 * P ^ 2 * N ^ 4 + C (77/144 : ℚ) * multiplierNumerator k 1 * P ^ 2 * N ^ 4) := by
  fin_cases k
  · exact recurrence_0_0
  · exact recurrence_1_0
  · exact recurrence_2_0

theorem indexed_recurrence_1 (k : Fin 3) :
    rowNumerator k.succ 1 * P ^ 2 * N ^ 4 =
      derivativeNumerator (rowNumerator k.castSucc 1) * P * N ^ 3 + (rowNumerator k.castSucc 0 * raw_ds + C (1/2 : ℚ) * multiplierNumerator k 0 * (3 * raw_s - P * N ^ 3) * P * N + C (77/144 : ℚ) * multiplierNumerator k 2 * P ^ 2 * N ^ 4) := by
  fin_cases k
  · exact recurrence_0_1
  · exact recurrence_1_1
  · exact recurrence_2_1

theorem indexed_recurrence_2 (k : Fin 3) :
    rowNumerator k.succ 2 * P ^ 2 * N ^ 4 =
      derivativeNumerator (rowNumerator k.castSucc 2) * P * N ^ 3 + (rowNumerator k.castSucc 0 * raw_ds + C (1/2 : ℚ) * multiplierNumerator k 1 * (5 * raw_s - 3 * P * N ^ 3) * P * N + C (5/144 : ℚ) * multiplierNumerator k 2 * P ^ 2 * N ^ 4) := by
  fin_cases k
  · exact recurrence_0_2
  · exact recurrence_1_2
  · exact recurrence_2_2

theorem indexed_recurrence_3 (k : Fin 3) :
    rowNumerator k.succ 3 * P ^ 2 * N ^ 4 =
      derivativeNumerator (rowNumerator k.castSucc 3) * P * N ^ 3 + ((rowNumerator k.castSucc 1 + rowNumerator k.castSucc 2) * raw_ds + multiplierNumerator k 2 * (4 * raw_s - 2 * P * N ^ 3) * P * N) := by
  fin_cases k
  · exact recurrence_0_3
  · exact recurrence_1_3
  · exact recurrence_2_3

theorem indexed_residual (i : Fin 4) :
    P ^ 3 * rowNumerator 3 i - P * raw_V * rowNumerator 1 i -
      C (1/2 : ℚ) * raw_dV * rowNumerator 0 i = 0 := by
  fin_cases i
  · exact residual_0
  · exact residual_1
  · exact residual_2
  · exact residual_3

theorem initial_numerator : rowNumerator 0 0 = T * P ^ 4 * N ^ 8 := by
  simp only [rowNumerator, Matrix.cons_val_zero, ell0_0, raw_ell0_0, T, Zeta7Riccati.T]
  ring

theorem initial_numerator_succ (i : Fin 3) : rowNumerator 0 i.succ = 0 := by
  fin_cases i <;> simp [rowNumerator, ell0_1, ell0_2, ell0_3, raw_ell0_1, raw_ell0_2, raw_ell0_3]

end Zeta7AnnularRows
