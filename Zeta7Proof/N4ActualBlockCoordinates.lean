import Zeta7Proof.N4CyclicStructure
import Zeta7Proof.ActualSevenGermIndependence

/-! The original monomial block combinations in the explicit connection.
Neither the series nor their primitive normalizations are changed. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
open scoped RatFunc LaurentSeries
open PowerSeries
namespace Zeta7Germ

def originalGermCoordinates : Fin 6 → SevenCoordinates :=
  ![((0, ![1, 0, 0]), 0), ((0, ![0, 1, 0]), 0), ((0, ![0, 0, 1]), 0),
    (0, ![1, 0, 0]), (0, ![RatFunc.X, 1, 0]),
    (0, ![RatFunc.X ^ 2 / 2, RatFunc.X, 1])]

theorem originalGermCoordinates_eval (c : ℚ) (j : Fin 6) :
    sevenEval c (originalGermCoordinates j) = Zeta7Common.complexLaurentGerms c (.inr j) := by
  rw [actual_original_six_frame]
  fin_cases j <;>
    simp [originalGermCoordinates, sevenEval, fourEval, jetEval, primitiveEval, originalSixFrame,
      map_ofNat] <;>
    ring

def blockCoordinateVector (d : ℕ) : Zeta7Common.BlockIndex d → SevenCoordinates
  | .inl k => (RatFunc.X : RatFunc ℂ) ^ k.val • (((1, 0), 0) : SevenCoordinates)
  | .inr jk => (RatFunc.X : RatFunc ℂ) ^ jk.2.val • originalGermCoordinates jk.1

theorem complexSeries_X_pow (n : ℕ) :
    complexSeries ((X : ℚ⟦X⟧) ^ n) = embed (RatFunc.X ^ n) := by
  simp [complexSeries, embed_X]

theorem blockCoordinateVector_eval (c : ℚ) (d : ℕ) (i : Zeta7Common.BlockIndex d) :
    sevenEval c (blockCoordinateVector d i) =
      complexSeries (Zeta7Common.blockSeries d (Zeta7Common.rationalGerms c) i) := by
  cases i with
  | inl k =>
      simp [blockCoordinateVector, sevenEval_smul, sevenEval, fourEval, jetEval,
        primitiveEval, Zeta7Common.blockSeries, complexSeries_X_pow]
  | inr jk =>
      rw [blockCoordinateVector, sevenEval_smul, originalGermCoordinates_eval]
      change _ = complexSeries (X ^ jk.2.val * Zeta7Common.rationalGerms c jk.1)
      rw [complexSeries_mul, complexSeries_X_pow]
      rfl

def actualBlockCoordinates (d : ℕ) (a : Zeta7Common.BlockIndex d → ℚ) : SevenCoordinates :=
  ∑ i, RatFunc.C (a i : ℂ) • blockCoordinateVector d i

theorem complexSeries_rat_smul (q : ℚ) (f : ℚ⟦X⟧) :
    complexSeries (q • f) = embed (RatFunc.C (q : ℂ)) * complexSeries f := by
  rw [PowerSeries.smul_eq_C_mul, complexSeries_mul]
  congr 1
  simp [complexSeries, embed_C]

theorem sevenEval_sum {ι : Type*} (c : ℚ) (s : Finset ι) (f : ι → SevenCoordinates) :
    sevenEval c (∑ i ∈ s, f i) = ∑ i ∈ s, sevenEval c (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [sevenEval_eq_zero_iff]
  | @insert i s hi ih => simp only [Finset.sum_insert hi, sevenEval_add, ih]

theorem complexSeries_sum {ι : Type*} (s : Finset ι) (f : ι → ℚ⟦X⟧) :
    complexSeries (∑ i ∈ s, f i) = ∑ i ∈ s, complexSeries (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [complexSeries]
  | @insert i s hi ih => simp only [Finset.sum_insert hi, complexSeries_add, ih]

theorem actualBlockCoordinates_eval (c : ℚ) (d : ℕ) (a : Zeta7Common.BlockIndex d → ℚ) :
    sevenEval c (actualBlockCoordinates d a) =
      complexSeries (∑ i, a i • Zeta7Common.blockSeries d (Zeta7Common.rationalGerms c) i) := by
  simp only [actualBlockCoordinates, sevenEval_sum, sevenEval_smul,
    blockCoordinateVector_eval, complexSeries_sum, complexSeries_rat_smul]

theorem complexSeries_injective : Function.Injective complexSeries := by
  intro f g h
  have hm := HahnSeries.ofPowerSeries_injective h
  ext n
  have hc := congrArg (PowerSeries.coeff n) hm
  simp only [PowerSeries.coeff_map] at hc
  exact (algebraMap ℚ ℂ).injective hc

theorem actualBlockCoordinates_ne_zero (c : ℚ) (d : ℕ)
    (a : Zeta7Common.BlockIndex d → ℚ) (ha : a ≠ 0) : actualBlockCoordinates d a ≠ 0 := by
  intro hz
  have he := actualBlockCoordinates_eval c d a
  rw [hz] at he
  have hs : (∑ i, a i • Zeta7Common.blockSeries d (Zeta7Common.rationalGerms c) i) = 0 := by
    apply complexSeries_injective
    simpa [sevenEval, fourEval, jetEval, primitiveEval, complexSeries] using he.symm
  apply ha
  funext i
  exact (Fintype.linearIndependent_iff.mp (Zeta7Common.rationalGerms_block_independent c d)) a hs i

/-- Every derivative row is tied to the all-degree original block combination. -/
theorem actualBlockCoordinates_iterate (c : ℚ) (d : ℕ)
    (a : Zeta7Common.BlockIndex d → ℚ) (n : ℕ) :
    sevenEval c (connection7^[n] (actualBlockCoordinates d a)) =
      laurentD^[n] (complexSeries
        (∑ i, a i • Zeta7Common.blockSeries d (Zeta7Common.rationalGerms c) i)) := by
  rw [sevenEval_iterate, actualBlockCoordinates_eval]

end Zeta7Germ
