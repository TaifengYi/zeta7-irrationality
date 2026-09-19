import Stage2A

/-!
# Stage 2B: level-seven coefficients and exact matrices

The rational recurrence below constructs a formal solution, not the
Kubota--Leopoldt value or a modular parametrization. Identifying this
solution with A(q(x))(G(q(x))+c) remains a separate obligation.
K is defined by C3 itself, not by an assumed certificate for DK = RH.
All matrix results allow arbitrary selected tail rows; no vanishing flag
or nonzero determinant is assumed to have been constructed.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Zeta7Stage2B

open Polynomial
def p : Polynomial ℚ := 1 + 13 * X + 49 * X ^ 2
def c₁ : Polynomial ℚ := -8 * X * (1 + 16 * X + 49 * X ^ 2) * p
def c₀ : Polynomial ℚ := (-4 * X + 196 * X ^ 3) * (1 + 19 * X + 49 * X ^ 2)
def forcing : Polynomial ℚ := X * (1 + 10 * X) * p ^ 2

/-- Coefficient of a lower-index term in the cleared equation P³ L H = P³ R. -/
def recurrenceWeight (k j : ℕ) : ℚ :=
  (p ^ 3).coeff k * (j : ℚ) ^ 3 + c₁.coeff k * j + c₀.coeff k

/-- Unique recursively constructed coefficients with initial value a and forcing scale b. -/
def solution (a b : ℚ) : ℕ → ℚ
  | 0 => a
  | n + 1 =>
      (b * forcing.coeff (n + 1) -
        ∑ j : Fin (n + 1), recurrenceWeight (n + 1 - j.val) j.val *
          solution a b j.val) / (n + 1 : ℚ) ^ 3
termination_by n => n
decreasing_by exact j.isLt

theorem solution_zero (a b : ℚ) : solution a b 0 = a := by
  rw [solution]

theorem solution_recurrence (a b : ℚ) (n : ℕ) :
    (n + 1 : ℚ) ^ 3 * solution a b (n + 1) +
      ∑ j : Fin (n + 1), recurrenceWeight (n + 1 - j.val) j.val *
        solution a b j.val = b * forcing.coeff (n + 1) := by
  rw [solution]
  have hn : (n + 1 : ℚ) ≠ 0 := by positivity
  field_simp
  ring

/-- The formal H used in the matrix, with the prescribed constant c. -/
def H (c : ℚ) : PowerSeries ℚ := PowerSeries.mk (solution c 1)

/-- Euler derivative, in the manuscript's x coordinate. -/
def euler (f : PowerSeries ℚ) : PowerSeries ℚ :=
  PowerSeries.X * PowerSeries.derivative ℚ f

/-- Ordinary primitive with zero constant term. -/
def primitive (f : PowerSeries ℚ) : PowerSeries ℚ :=
  PowerSeries.mk (fun n => if n = 0 then 0 else PowerSeries.coeff (n - 1) f / n)

def potential : PowerSeries ℚ :=
  (8 * PowerSeries.X * (1 + 16 * PowerSeries.X + 49 * PowerSeries.X ^ 2)) *
    ((p : PowerSeries ℚ) ^ 2)⁻¹

/-- Exactly C3, before any use of LH = R. -/
def quadratic (f : PowerSeries ℚ) : PowerSeries ℚ :=
  f * euler (euler f) - PowerSeries.C (1 / 2) * (euler f) ^ 2 -
    PowerSeries.C (1 / 2) * potential * f ^ 2

def germs (c : ℚ) : Fin 6 → PowerSeries ℚ :=
  ![H c, euler (H c), euler (euler (H c)), quadratic (H c),
    primitive (quadratic (H c)), primitive (primitive (quadratic (H c)))]

def coefficients (c : ℚ) (j : Fin 6) (n : ℕ) : ℚ :=
  PowerSeries.coeff n (germs c j)

theorem coeff_euler (f : PowerSeries ℚ) (n : ℕ) :
    PowerSeries.coeff n (euler f) = (n : ℚ) * PowerSeries.coeff n f := by
  cases n with
  | zero => simp [euler]
  | succ n =>
      simp only [euler, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative]
      push_cast
      ring

theorem coeff_primitive_zero (f : PowerSeries ℚ) :
    PowerSeries.coeff 0 (primitive f) = 0 := by
  simp [primitive]

theorem coeff_primitive_succ (f : PowerSeries ℚ) (n : ℕ) :
    PowerSeries.coeff (n + 1) (primitive f) =
      PowerSeries.coeff n f / (n + 1 : ℚ) := by
  simp [primitive]

theorem derivative_primitive (f : PowerSeries ℚ) :
    PowerSeries.derivative ℚ (primitive f) = f := by
  ext n
  rw [PowerSeries.coeff_derivative, coeff_primitive_succ]
  have hn : (n + 1 : ℚ) ≠ 0 := by positivity
  exact div_mul_cancel₀ _ hn

theorem coeff_jet (c : ℚ) (n : ℕ) :
    coefficients c 0 n = solution c 1 n ∧
    coefficients c 1 n = (n : ℚ) * solution c 1 n ∧
    coefficients c 2 n = (n : ℚ) ^ 2 * solution c 1 n := by
  simp [coefficients, germs, coeff_euler, H, pow_two, mul_assoc]

/-- Appendix (20), using successor indices to exclude truncated subtraction. -/
theorem coeff_primitive_blocks (c : ℚ) (n : ℕ) :
    coefficients c 4 (n + 1) = coefficients c 3 n / (n + 1 : ℚ) ∧
    coefficients c 5 (n + 2) =
      coefficients c 3 n / ((n + 1 : ℚ) * (n + 2 : ℚ)) := by
  simp [coefficients, germs, coeff_primitive_succ, show n + 2 = (n + 1) + 1 by omega,
    div_div]
  ring

open Zeta7Stage2A

/-- The manuscript's selected-row six-block matrix. -/
def levelMatrix (d : ℕ) (c : ℚ) (row : TailIndex d → ℕ) :
    Matrix (TailIndex d) (TailIndex d) ℚ :=
  tailMatrix d (coefficients c) row

def normalizedLevelMatrix (d : ℕ) (c : ℚ) (row : TailIndex d → ℕ) :
    Matrix (TailIndex d) (TailIndex d) ℚ :=
  normalizedTailMatrix d (coefficients c) row

/-- Entries really are coefficients of the polynomial multiples x^k g_j. -/
theorem levelMatrix_entry (d : ℕ) (c : ℚ) (row : TailIndex d → ℕ)
    (hrow : ∀ i, d ≤ row i) (i j : TailIndex d) :
    levelMatrix d c row i j =
      PowerSeries.coeff (row i) (PowerSeries.X ^ j.2.val * germs c j.1) := by
  rw [PowerSeries.coeff_X_pow_mul', ite_eq_left]
  · rfl
  · exact le_trans (Nat.le_of_lt j.2.isLt) (hrow i)

theorem normalizedLevelMatrix_eq (d : ℕ) (c : ℚ) (row : TailIndex d → ℕ)
    (hrow : ∀ i, d ≤ row i) :
    normalizedLevelMatrix d c row =
      normalizeMatrix (levelMatrix d c row) row (fun j => j.2.val) :=
  normalizedTailMatrix_eq d (coefficients c) row hrow

/-- C21's exact normalization identity, with no valuation estimate attached. -/
theorem det_normalizedLevelMatrix (d : ℕ) (c : ℚ) (row : TailIndex d → ℕ)
    (hrow : ∀ i, d ≤ row i) :
    (normalizedLevelMatrix d c row).det =
      (∏ i, (1 : ℚ) / 49 ^ row i) * (levelMatrix d c row).det *
        (∏ j : TailIndex d, (49 : ℚ) ^ j.2.val) :=
  det_normalizedTailMatrix d (coefficients c) row hrow

/-- Consecutive rows used in the evidence; these are not asserted to be flag jumps. -/
def consecutiveRow (d : ℕ) (i : TailIndex d) : ℕ := d + i.1.val * d + i.2.val

theorem consecutiveRow_bounds (d : ℕ) (i : TailIndex d) :
    d ≤ consecutiveRow d i ∧ consecutiveRow d i < 7 * d := by
  have hi := i.1.isLt
  have hk := i.2.isLt
  dsimp [consecutiveRow]
  constructor
  · omega
  · nlinarith

#print axioms solution_recurrence
#print axioms derivative_primitive
#print axioms coeff_jet
#print axioms coeff_primitive_blocks
#print axioms levelMatrix_entry
#print axioms normalizedLevelMatrix_eq
#print axioms det_normalizedLevelMatrix
#print axioms consecutiveRow_bounds

/-! ## Exact differential and parameter algebra -/

/-- Euler differentiation after removing the monomial x^n. -/
def shiftedEuler (n : ℚ) (f : Polynomial ℚ) : Polynomial ℚ :=
  C n * f + X * f.derivative

def band (n : ℚ) : Polynomial ℚ :=
  C (n ^ 3) +
  C ((2 * n + 1) * (13 * n ^ 2 + 13 * n + 9)) * X +
  C ((n + 1) * (267 * n ^ 2 + 534 * n + 433)) * X ^ 2 +
  C (49 * (2 * n + 3) * (13 * n ^ 2 + 39 * n + 35)) * X ^ 3 +
  C (2401 * (n + 2) ^ 3) * X ^ 4

/-- Cleared C14 as a polynomial identity in the exponent, hence all integer exponents. -/
theorem cleared_band_identity (n : ℚ) :
    p ^ 3 * shiftedEuler n (shiftedEuler n (shiftedEuler n p)) +
      c₁ * shiftedEuler n p + c₀ * p = p ^ 2 * band n := by
  simp [shiftedEuler, p, c₁, c₀, band, Polynomial.derivative_mul,
    Polynomial.derivative_pow, map_add, map_mul, map_pow, map_ofNat]
  ring

/-- Clears the derivative of V=Vnum/P²: 2 c₀ = 2 Vnum DP − P D Vnum. -/
theorem cleared_potential_derivative :
    let vnum : Polynomial ℚ := 8 * X * (1 + 16 * X + 49 * X ^ 2)
    2 * c₀ = 2 * vnum * (X * p.derivative) - p * (X * vnum.derivative) := by
  dsimp
  simp [c₀, p, Polynomial.derivative_mul, Polynomial.derivative_pow, map_ofNat]
  ring

/-- Exact all-degree linear dependence of the recurrence solution on its two inputs. -/
theorem solution_linear (a b : ℚ) (n : ℕ) :
    solution a b n = a * solution 1 0 n + b * solution 0 1 n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp [solution]
    | succ n =>
      have hs :
          (∑ j : Fin (n + 1), recurrenceWeight (n + 1 - j.val) j.val *
            solution a b j.val) =
          a * (∑ j : Fin (n + 1), recurrenceWeight (n + 1 - j.val) j.val *
            solution 1 0 j.val) +
          b * (∑ j : Fin (n + 1), recurrenceWeight (n + 1 - j.val) j.val *
            solution 0 1 j.val) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        rw [ih j.val j.isLt]
        ring
      simp only [solution]
      rw [hs]
      ring

/-- Rescaling in Stage2A is the actual power-series substitution t ↦ t/49. -/
theorem normalized_coefficients (c : ℚ) (j : Fin 6) (n : ℕ) :
    normalizeCoefficients (coefficients c j) n =
      PowerSeries.coeff n (PowerSeries.rescale (1 / 49 : ℚ) (germs c j)) := by
  simp [normalizeCoefficients, coefficients, div_eq_mul_inv, mul_comm]

/-- The factor 49 in C17 is required by ordinary, rather than Euler, integration. -/
theorem primitive_rescaling (f : PowerSeries ℚ) :
    primitive (PowerSeries.rescale (1 / 49 : ℚ) f) =
      PowerSeries.C 49 * PowerSeries.rescale (1 / 49 : ℚ) (primitive f) := by
  ext n
  cases n with
  | zero => simp [coeff_primitive_zero]
  | succ n =>
    simp only [coeff_primitive_succ, PowerSeries.coeff_rescale,
      PowerSeries.coeff_C_mul, pow_succ]
    ring

theorem double_primitive_rescaling (f : PowerSeries ℚ) :
    primitive (primitive (PowerSeries.rescale (1 / 49 : ℚ) f)) =
      PowerSeries.C (49 ^ 2) *
        PowerSeries.rescale (1 / 49 : ℚ) (primitive (primitive f)) := by
  ext n
  cases n with
  | zero => simp only [coeff_primitive_zero, PowerSeries.coeff_C_mul,
      PowerSeries.coeff_rescale, mul_zero]
  | succ n =>
    cases n with
    | zero => simp only [coeff_primitive_succ, coeff_primitive_zero,
        PowerSeries.coeff_C_mul, PowerSeries.coeff_rescale, zero_div, mul_zero]
    | succ n =>
      simp only [coeff_primitive_succ, PowerSeries.coeff_rescale,
        PowerSeries.coeff_C_mul, pow_succ]
      ring

/-- Coefficient definition of all seven monomial blocks, including the polynomial block. -/
def fullMatrix (d : ℕ) (c : ℚ) (row : TailIndex d → ℕ) :
    Matrix (Fin d ⊕ TailIndex d) (Fin d ⊕ TailIndex d) ℚ :=
  fun i j =>
    let r := Sum.elim Fin.val row i
    match j with
    | Sum.inl k => PowerSeries.coeff r (PowerSeries.X ^ k.val : PowerSeries ℚ)
    | Sum.inr k => PowerSeries.coeff r (PowerSeries.X ^ k.2.val * germs c k.1)

def topRight (d : ℕ) (c : ℚ) : Matrix (Fin d) (TailIndex d) ℚ :=
  fun i j => PowerSeries.coeff i.val (PowerSeries.X ^ j.2.val * germs c j.1)

theorem fullMatrix_blocks (d : ℕ) (c : ℚ) (row : TailIndex d → ℕ)
    (hrow : ∀ i, d ≤ row i) :
    fullMatrix d c row =
      Matrix.fromBlocks (1 : Matrix (Fin d) (Fin d) ℚ) (topRight d c)
        (0 : Matrix (TailIndex d) (Fin d) ℚ) (levelMatrix d c row) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · simp [fullMatrix, PowerSeries.coeff_X_pow, Matrix.one_apply, Fin.ext_iff]
  · rfl
  · have hne : row i ≠ j.val := by have := hrow i; have := j.isLt; omega
    simp [fullMatrix, PowerSeries.coeff_X_pow, hne]
  · exact (levelMatrix_entry d c row hrow i j).symm

/-- The determinant in the original seven-block monomial basis equals its tail. -/
theorem det_fullMatrix (d : ℕ) (c : ℚ) (row : TailIndex d → ℕ)
    (hrow : ∀ i, d ≤ row i) :
    (fullMatrix d c row).det = (levelMatrix d c row).det := by
  rw [fullMatrix_blocks d c row hrow, identity_block_det]

#print axioms cleared_band_identity
#print axioms cleared_potential_derivative
#print axioms solution_linear
#print axioms normalized_coefficients
#print axioms primitive_rescaling
#print axioms double_primitive_rescaling
#print axioms fullMatrix_blocks
#print axioms det_fullMatrix

/-! ## The recurrence satisfies the all-degree cleared formal differential equation -/

def clearedOperator (f : PowerSeries ℚ) : PowerSeries ℚ :=
  ((p ^ 3 : Polynomial ℚ) : PowerSeries ℚ) * euler (euler (euler f)) +
    (c₁ : PowerSeries ℚ) * euler f + (c₀ : PowerSeries ℚ) * f

theorem coeff_poly_mul (a : Polynomial ℚ) (f : PowerSeries ℚ) (n : ℕ) :
    PowerSeries.coeff n ((a : PowerSeries ℚ) * f) =
      ∑ j ∈ Finset.range (n + 1), a.coeff (n - j) * PowerSeries.coeff j f := by
  rw [mul_comm, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Polynomial.coeff_coe]
  ring

theorem coeff_clearedOperator (f : PowerSeries ℚ) (n : ℕ) :
    PowerSeries.coeff n (clearedOperator f) =
      ∑ j ∈ Finset.range (n + 1),
        recurrenceWeight (n - j) j * PowerSeries.coeff j f := by
  simp only [clearedOperator, map_add, coeff_poly_mul, coeff_euler,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [recurrenceWeight]
  ring

theorem recurrenceWeight_zero (n : ℕ) :
    recurrenceWeight 0 n = (n : ℚ) ^ 3 := by
  simp [recurrenceWeight, p, c₁, c₀, Polynomial.coeff_zero_eq_eval_zero]

/-- No differential equation hypothesis: it follows from the constructed coefficients. -/
theorem cleared_solution (a b : ℚ) :
    clearedOperator (PowerSeries.mk (solution a b)) =
      PowerSeries.C b * (forcing : PowerSeries ℚ) := by
  ext n
  rw [coeff_clearedOperator, PowerSeries.coeff_C_mul, Polynomial.coeff_coe]
  simp only [PowerSeries.coeff_mk]
  cases n with
  | zero => simp [recurrenceWeight_zero, forcing, Polynomial.coeff_zero_eq_eval_zero]
  | succ n =>
    rw [Finset.sum_range_succ, Nat.sub_self, recurrenceWeight_zero]
    have hr := solution_recurrence a b n
    rw [← Fin.sum_univ_eq_sum_range (fun j : ℕ =>
      recurrenceWeight (n + 1 - j) j * solution a b j)]
    push_cast
    linarith [hr]

theorem cleared_H (c : ℚ) :
    clearedOperator (H c) = (forcing : PowerSeries ℚ) := by
  simpa [H] using cleared_solution c 1

/-- Constant coefficients of the exact C3 quadratic and its two ordinary primitives. -/
theorem quadratic_constant (f : PowerSeries ℚ) :
    PowerSeries.coeff 0 (quadratic f) = 0 := by
  simp [quadratic, euler, potential, PowerSeries.coeff_zero_eq_constantCoeff]

theorem germs_constants (c : ℚ) :
    (fun j => coefficients c j 0) = ![c, 0, 0, 0, 0, 0] := by
  ext j
  fin_cases j <;>
    simp [coefficients, germs, H, solution_zero, coeff_euler,
      quadratic_constant, coeff_primitive_zero]

#print axioms coeff_clearedOperator
#print axioms recurrenceWeight_zero
#print axioms cleared_solution
#print axioms cleared_H
#print axioms quadratic_constant
#print axioms germs_constants

end Zeta7Stage2B
