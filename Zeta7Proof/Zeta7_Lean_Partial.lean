import Mathlib

/-!
# Partial formalization of the proposed seven-adic argument

**HISTORICAL MODULE.** This file is the first, conditional stage of the project. It is kept
because later modules use its definitions, for example `IsRationalSeven`. Its
`conditional_exclusion` is not used by the final theorem. The status text below describes this
file when it was created and is kept unchanged as a historical record. The completed,
unconditional theorems are `Zeta7Main.zeta7Three_irrational` and `Zeta7Main.eta_irrational`
(`Zeta7Proof/FinalTheorem.lean`). They depend only on `propext`, `Classical.choice` and
`Quot.sound`.

Original status (historical): INCOMPLETE; NOT COMPILER-TESTED IN THE AUTHORING ENVIRONMENT.

Paste this whole file into a Lean file inside a mathlib project.

This file supplies proof scripts for algebraic identities, finite rational
arithmetic, and a CONDITIONAL asymptotic contradiction. It does not supply
the analytic or arithmetic research lemmas. In particular, it contains no
unconditional theorem asserting the irrationality of a p-adic zeta value.

The absence of placeholders does not remove hypotheses from a theorem:
inspect the full type of conditional_exclusion at the end.
-/

set_option autoImplicit false

namespace Zeta7Partial

/-! ## 1. Algebraic differential identities -/

section DifferentialAlgebra

variable {A : Type*} [CommRing A]

/-- Twice the third-order operator, avoiding division by two. -/
def twiceOperator (D : A →+ A) (V f : A) : A :=
  2 * D (D (D f)) - 2 * V * D f - D V * f

def concomitant (D : A →+ A) (V v h : A) : A :=
  v * D (D h) - D v * D h + (D (D v) - V * v) * h

/-- The Leibniz rule suffices for the concomitant identity. -/
theorem concomitant_identity
    (D : A →+ A)
    (leibniz : ∀ a b : A, D (a * b) = D a * b + a * D b)
    (V v h : A) :
    2 * D (concomitant D V v h) =
      v * twiceOperator D V h + twiceOperator D V v * h := by
  simp only [concomitant, twiceOperator, map_add, map_sub, leibniz]
  ring

/-- Twice K, written without differentiating a numeral. -/
def twiceK (D : A →+ A) (V h : A) : A :=
  h * D (D h) + h * D (D h) - D h * D h - V * (h * h)

theorem twiceK_identity
    (D : A →+ A)
    (leibniz : ∀ a b : A, D (a * b) = D a * b + a * D b)
    (V h : A) :
    D (twiceK D V h) = h * twiceOperator D V h := by
  simp only [twiceK, twiceOperator, map_add, map_sub, leibniz]
  ring

/-- Quadratic combination h K - h' J1 + h'' J2. -/
def quadraticPrimitive (x a b c K J1 J2 : A) : A :=
  (a + b * x + c * (x * x)) * K -
    (b + (c + c) * x) * J1 + (c + c) * J2

theorem quadraticPrimitive_identity
    (D : A →+ A)
    (leibniz : ∀ a b : A, D (a * b) = D a * b + a * D b)
    (x a b c K J1 J2 : A)
    (hx : D x = x) (ha : D a = 0)
    (hb : D b = 0) (hc : D c = 0)
    (hJ1 : D J1 = x * K) (hJ2 : D J2 = x * J1) :
    D (quadraticPrimitive x a b c K J1 J2) =
      (a + b * x + c * (x * x)) * D K := by
  simp only [quadraticPrimitive, map_add, map_sub, leibniz,
    hx, ha, hb, hc, hJ1, hJ2]
  ring

end DifferentialAlgebra

/-! ## 2. Exact arithmetic, not a proof of the denominator estimate -/

def affineArea (left right intercept slope : ℚ) : ℚ :=
  intercept * (right - left) + slope * (right ^ 2 - left ^ 2) / 2

/-- Antiderivative differences for the nine stated affine pieces. -/
def profileArea : ℚ :=
  affineArea 0 (1 / 2) 15 (8 / 3) +
  affineArea (1 / 2) (3 / 4) 14 (14 / 3) +
  affineArea (3 / 4) 1 15 (10 / 3) +
  affineArea 1 (12 / 7) 19 (-2 / 3) +
  affineArea (12 / 7) 2 23 (-3) +
  affineArea 2 (7 / 3) 29 (-6) +
  affineArea (7 / 3) 3 22 (-3) +
  affineArea 3 (7 / 2) 28 (-5) +
  affineArea (7 / 2) 7 21 (-3)

theorem profileArea_exact : profileArea = 12325 / 168 := by
  norm_num [profileArea, affineArea]

theorem six_masses_sum :
    (1 / 25 + 2 / 25 + 7 / 50 + 17 / 100 + 6 / 25 + 33 / 100 : ℚ) = 1 := by
  norm_num

theorem correction_pivot :
    (9 + 433 * (-1 / 10) + 5145 * (-1 / 10) ^ 2 +
      19208 * (-1 / 10) ^ 3 : ℚ) = -1029 / 500 := by
  norm_num

theorem correction_pivot_nonzero :
    (9 + 433 * (-1 / 10) + 5145 * (-1 / 10) ^ 2 +
      19208 * (-1 / 10) ^ 3 : ℚ) ≠ 0 := by
  norm_num

theorem twice_sum_range (n : ℕ) :
    2 * (∑ k ∈ Finset.range n, (k : ℤ)) = (n : ℤ) * ((n : ℤ) - 1) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [Finset.sum_range_succ]
      push_cast
      nlinarith [ih]

/-- Only the exact baseline row-sum calculation, not a valuation bound. -/
theorem baseline_row_sum (d : ℕ) :
    2 * ((∑ k ∈ Finset.range (7 * d), (k : ℤ)) -
      7 * (∑ k ∈ Finset.range d, (k : ℤ))) = 42 * (d : ℤ) ^ 2 := by
  have hbig := twice_sum_range (7 * d)
  have hsmall := twice_sum_range d
  push_cast at hbig
  nlinarith

/-! ## 3. Sign propagation from EXPLICIT, UNPROVED real enclosures -/

noncomputable def surplus (ell energy assigned : ℝ) : ℝ :=
  43 * ell + (7 / 2 : ℝ) * energy - assigned - 12325 / 168

/--
These fields are assumptions, not certified facts about the six-circle
integrals. There is deliberately no constructor supplying these fields for
the actual logarithm, energy and assigned integral.
-/
structure Enclosures (ell energy assigned : ℝ) : Prop where
  log_lower : (19459101490553133 : ℝ) / 10000000000000000 ≤ ell
  log_upper : ell ≤ (19459101490553134 : ℝ) / 10000000000000000
  energy_lower : (13181130889804202 : ℝ) / 10000000000000000 ≤ energy
  energy_upper : energy ≤ (13181130889804203 : ℝ) / 10000000000000000
  assigned_lower : (148887558854475598 : ℝ) / 10000000000000000 ≤ assigned
  assigned_upper : assigned ≤ (148887558854475599 : ℝ) / 10000000000000000

theorem surplus_bounds_from_enclosures
    (ell energy assigned : ℝ) (h : Enclosures ell energy assigned) :
    (3568 : ℝ) / 100000 < surplus ell energy assigned ∧
      surplus ell energy assigned < (3569 : ℝ) / 100000 := by
  rcases h with ⟨hll, hlu, hel, heu, hjl, hju⟩
  unfold surplus
  constructor <;> linarith

theorem surplus_positive_from_enclosures
    (ell energy assigned : ℝ) (h : Enclosures ell energy assigned) :
    0 < surplus ell energy assigned := by
  have hpos := (surplus_bounds_from_enclosures ell energy assigned h).1
  linarith

/-! ## 4. An epsilon-form asymptotic contradiction -/

/--
An explicit formulation of an upper bound f(d) ≤ c d² + o(d²).
This definition supplies no bound for any concrete determinant.
-/
def QuadraticUpper (f : ℕ → ℝ) (c : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ d : ℕ, N ≤ d →
    f d ≤ (c + ε) * (d : ℝ) ^ 2

/--
Abstract logarithmic local contributions.

Producing this data from one common nonzero rational determinant is NOT
done in this file. The field names describe the intended application;
the fields themselves remain hypotheses.
-/
structure ThreePlaceData (archConstant targetConstant auxConstant : ℝ) where
  arch : ℕ → ℝ
  target : ℕ → ℝ
  auxiliary : ℕ → ℝ
  productFormula : ∀ d : ℕ, 1 ≤ d → arch d + target d + auxiliary d = 0
  archBound : QuadraticUpper arch archConstant
  targetBound : QuadraticUpper target targetConstant
  auxiliaryBound : QuadraticUpper auxiliary auxConstant

theorem no_three_place_data
    (a t c : ℝ) (hneg : a + t + c < 0)
    (data : ThreePlaceData a t c) : False := by
  let ε : ℝ := -(a + t + c) / 6
  have hε : 0 < ε := by
    dsimp [ε]
    linarith
  obtain ⟨Na, ha⟩ := data.archBound ε hε
  obtain ⟨Nt, ht⟩ := data.targetBound ε hε
  obtain ⟨Nc, hc⟩ := data.auxiliaryBound ε hε
  let d : ℕ := max Na (max Nt Nc) + 1
  have hNa : Na ≤ d := by
    exact le_trans (le_max_left Na (max Nt Nc)) (Nat.le_succ _)
  have hNt : Nt ≤ d := by
    exact le_trans (le_trans (le_max_left Nt Nc)
      (le_max_right Na (max Nt Nc))) (Nat.le_succ _)
  have hNc : Nc ≤ d := by
    exact le_trans (le_trans (le_max_right Nt Nc)
      (le_max_right Na (max Nt Nc))) (Nat.le_succ _)
  have hd : 1 ≤ d := by
    dsimp [d]
    omega
  have hdR : (0 : ℝ) < (d : ℝ) := by
    exact_mod_cast (show 0 < d by omega)
  have hd2 : (0 : ℝ) < (d : ℝ) ^ 2 := by positivity
  have ha' := ha d hNa
  have ht' := ht d hNt
  have hc' := hc d hNc
  have hsum := data.productFormula d hd
  have hcoef : a + t + c + 3 * ε < 0 := by
    dsimp [ε]
    linarith
  have hnegative := mul_neg_of_neg_of_pos hcoef hd2
  nlinarith [hnegative]

theorem no_data_from_enclosures
    (ell energy assigned : ℝ) (h : Enclosures ell energy assigned)
    (data : ThreePlaceData
      (assigned - (7 / 2 : ℝ) * energy)
      (-43 * ell) (12325 / 168)) : False := by
  have hpos := surplus_positive_from_enclosures ell energy assigned h
  apply no_three_place_data
    (assigned - (7 / 2 : ℝ) * energy) (-43 * ell) (12325 / 168) _ data
  unfold surplus at hpos
  linarith

/-! ## 5. Actual p-adic types; conditional conclusion only -/

instance seven_prime : Fact (Nat.Prime 7) := ⟨by norm_num⟩

/-- Irrationality in Q_7 means not lying in the image of Q. -/
def IsRationalSeven (z : ℚ_[7]) : Prop :=
  ∃ q : ℚ, (q : ℚ_[7]) = z

/--
This is NOT the irrationality theorem.

The argument unprovedDeterminantConstruction contains the main missing
formalization. hNumeric also remains an unproved input for the intended
six-circle constants. Neither input is constructed in this file.

The statement applies to an arbitrary z in Q_7. This file has not defined
or identified the Kubota-Leopoldt zeta value.
-/
theorem conditional_exclusion
    (z : ℚ_[7]) (energy assigned : ℝ)
    (hNumeric : Enclosures (Real.log 7) energy assigned)
    (unprovedDeterminantConstruction :
      IsRationalSeven z →
        Nonempty (ThreePlaceData
          (assigned - (7 / 2 : ℝ) * energy)
          (-43 * Real.log 7) (12325 / 168))) :
    ¬ IsRationalSeven z := by
  intro hz
  obtain ⟨data⟩ := unprovedDeterminantConstruction hz
  exact no_data_from_enclosures (Real.log 7) energy assigned hNumeric data

/-!
Read BOTH the theorem types and the axiom output. Ordinary explicit
hypotheses do not appear as extra axioms.
-/

#print conditional_exclusion
#print axioms concomitant_identity
#print axioms twiceK_identity
#print axioms quadraticPrimitive_identity
#print axioms profileArea_exact
#print axioms baseline_row_sum
#print axioms surplus_bounds_from_enclosures
#print axioms no_three_place_data
#print axioms conditional_exclusion

end Zeta7Partial
