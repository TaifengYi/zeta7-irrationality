import Mathlib

/-! P8, milestone 1: the exact normalized cap profile.

The profile `profileF` is defined literally from the normalized counts
`b, c₀, c₁, c₂, t, q, b₀, n₁, n₃, r`. It is proved, for every real `z ≥ 0`, to equal the explicit
hinge combination `profileHinge = Σ wₖ (aₖ - z)₊`, and hence the ten-piece affine table of the
paper. The integral over `[0, 7]` is `12325/168`. All steps are kernel-checked case analyses on
the breakpoints `1/2, 3/4, 1, 3/2, 12/7, 2, 9/4, 7/3, 3, 7/2, 7`; the Python certificate only
suggested the breakpoints. -/
noncomputable section
set_option autoImplicit false
namespace Zeta7Auxiliary

/-! ### Definitions -/

def prB (z : ℝ) : ℝ := 1 + 4 * z / 3
def prC0 (z : ℝ) : ℝ := min 3 (prB z)
def prC1 (z : ℝ) : ℝ := min (3 - prC0 z) 1
def prC2 (z : ℝ) : ℝ := 3 - prC0 z - prC1 z
def prT (z : ℝ) : ℝ := min 1 (2 * max (1 - z) 0)
def prQ (z : ℝ) : ℝ := min 2 (min 1 (max (7 - 2 * z) 0) + min 1 (max (7 - 3 * z) 0))
def prB0 (z : ℝ) : ℝ := min (prC0 z + 1 - prT z) (prB z)
def prN1 (z : ℝ) : ℝ := prC2 z + prT z
def prN3 (z : ℝ) : ℝ := 2 - prQ z + prB0 z
def prR (z : ℝ) : ℝ := min 6 (max (7 - z) 0)

/-- The normalized layer cost `f(z)`. -/
def profileF (z : ℝ) : ℝ :=
  prR z + min (prR z) (6 - prN1 z) + min (prR z) (prQ z + prN3 z) + min (prR z) (prQ z)

/-- The hinge `(a - z)₊`. -/
def hinge (a z : ℝ) : ℝ := max (a - z) 0

/-- The hinge decomposition of the profile. -/
def profileHinge (z : ℝ) : ℝ :=
  2 * hinge (1/2) z - 4/3 * hinge (3/4) z - 4 * hinge 1 z - 7/3 * hinge (12/7) z
    - 3 * hinge 2 z + 3 * hinge (7/3) z - 2 * hinge 3 z + 2 * hinge (7/2) z + 3 * hinge 7 z

/-! ### Component values -/

theorem hinge_lo {a z : ℝ} (h : z ≤ a) : hinge a z = a - z :=
  max_eq_left (by linarith)
theorem hinge_hi {a z : ℝ} (h : a ≤ z) : hinge a z = 0 :=
  max_eq_right (by linarith)

theorem prC0_lo {z : ℝ} (h : z ≤ 3/2) : prC0 z = 1 + 4 * z / 3 := by
  unfold prC0 prB; rw [min_eq_right (by linarith)]
theorem prC0_hi {z : ℝ} (h : 3/2 ≤ z) : prC0 z = 3 := by
  unfold prC0 prB; rw [min_eq_left (by linarith)]

theorem prC1_lo {z : ℝ} (h : z ≤ 3/4) : prC1 z = 1 := by
  unfold prC1; rw [prC0_lo (by linarith), min_eq_right (by linarith)]
theorem prC1_mid {z : ℝ} (h1 : 3/4 ≤ z) (h2 : z ≤ 3/2) : prC1 z = 2 - 4 * z / 3 := by
  unfold prC1; rw [prC0_lo h2, min_eq_left (by linarith)]; ring
theorem prC1_hi {z : ℝ} (h : 3/2 ≤ z) : prC1 z = 0 := by
  unfold prC1; rw [prC0_hi h, min_eq_left (by linarith)]; ring

theorem prT_lo {z : ℝ} (h : z ≤ 1/2) : prT z = 1 := by
  unfold prT; rw [max_eq_left (by linarith), min_eq_left (by linarith)]
theorem prT_mid {z : ℝ} (h1 : 1/2 ≤ z) (h2 : z ≤ 1) : prT z = 2 - 2 * z := by
  unfold prT; rw [max_eq_left (by linarith), min_eq_right (by linarith)]; ring
theorem prT_hi {z : ℝ} (h : 1 ≤ z) : prT z = 0 := by
  unfold prT; rw [max_eq_right (by linarith), min_eq_right (by linarith)]; ring

theorem prT_le_one (z : ℝ) : prT z ≤ 1 := min_le_left _ _
theorem prT_nonneg (z : ℝ) : 0 ≤ prT z :=
  le_min (by norm_num) (by have := le_max_right (1 - z) 0; linarith)

theorem prQ_1 {z : ℝ} (h : z ≤ 2) : prQ z = 2 := by
  unfold prQ; simp only [min_def, max_def]; split_ifs <;> linarith
theorem prQ_2 {z : ℝ} (h1 : 2 ≤ z) (h2 : z ≤ 7/3) : prQ z = 8 - 3 * z := by
  unfold prQ; simp only [min_def, max_def]; split_ifs <;> linarith
theorem prQ_3 {z : ℝ} (h1 : 7/3 ≤ z) (h2 : z ≤ 3) : prQ z = 1 := by
  unfold prQ; simp only [min_def, max_def]; split_ifs <;> linarith
theorem prQ_4 {z : ℝ} (h1 : 3 ≤ z) (h2 : z ≤ 7/2) : prQ z = 7 - 2 * z := by
  unfold prQ; simp only [min_def, max_def]; split_ifs <;> linarith
theorem prQ_5 {z : ℝ} (h1 : 7/2 ≤ z) : prQ z = 0 := by
  unfold prQ; simp only [min_def, max_def]; split_ifs <;> linarith

theorem prB0_lo {z : ℝ} (h : z ≤ 9/4) : prB0 z = 1 + 4 * z / 3 := by
  unfold prB0 prB
  have ht := prT_le_one z
  by_cases hz : z ≤ 3/2
  · rw [prC0_lo hz, min_eq_right (by linarith)]
  · rw [prC0_hi (by linarith), prT_hi (by linarith), min_eq_right (by linarith)]
theorem prB0_hi {z : ℝ} (h : 9/4 ≤ z) : prB0 z = 4 := by
  unfold prB0 prB
  rw [prC0_hi (by linarith), prT_hi (by linarith), min_eq_left (by linarith)]; ring

theorem prR_lo {z : ℝ} (h : z ≤ 1) : prR z = 6 := by
  unfold prR; rw [max_eq_left (by linarith), min_eq_left (by linarith)]
theorem prR_mid {z : ℝ} (h1 : 1 ≤ z) (h2 : z ≤ 7) : prR z = 7 - z := by
  unfold prR; rw [max_eq_left (by linarith), min_eq_right (by linarith)]
theorem prR_hi {z : ℝ} (h : 7 ≤ z) : prR z = 0 := by
  unfold prR; rw [max_eq_right (by linarith), min_eq_right (by linarith)]

/-! ### The profile identity -/

/-- Resolve every component and hinge on a closed interval, then the three outer minima. -/
syntax "profile_case" : tactic
macro_rules
  | `(tactic| profile_case) => `(tactic| (
      simp only [profileF, prN1, prN3, prC2, profileHinge]
      (first | rw [prR_lo (by linarith)] | rw [prR_mid (by linarith) (by linarith)] | rw [prR_hi (by linarith)])
      (first | rw [prQ_1 (by linarith)] | rw [prQ_2 (by linarith) (by linarith)] | rw [prQ_3 (by linarith) (by linarith)] | rw [prQ_4 (by linarith) (by linarith)] | rw [prQ_5 (by linarith)])
      (first | rw [prC0_lo (by linarith)] | rw [prC0_hi (by linarith)])
      (first | rw [prC1_lo (by linarith)] | rw [prC1_mid (by linarith) (by linarith)] | rw [prC1_hi (by linarith)])
      (first | rw [prT_lo (by linarith)] | rw [prT_mid (by linarith) (by linarith)] | rw [prT_hi (by linarith)])
      (first | rw [prB0_lo (by linarith)] | rw [prB0_hi (by linarith)])
      (first | rw [hinge_lo (a := 1/2) (by linarith)] | rw [hinge_hi (a := 1/2) (by linarith)])
      (first | rw [hinge_lo (a := 3/4) (by linarith)] | rw [hinge_hi (a := 3/4) (by linarith)])
      (first | rw [hinge_lo (a := 1) (by linarith)] | rw [hinge_hi (a := 1) (by linarith)])
      (first | rw [hinge_lo (a := 12/7) (by linarith)] | rw [hinge_hi (a := 12/7) (by linarith)])
      (first | rw [hinge_lo (a := 2) (by linarith)] | rw [hinge_hi (a := 2) (by linarith)])
      (first | rw [hinge_lo (a := 7/3) (by linarith)] | rw [hinge_hi (a := 7/3) (by linarith)])
      (first | rw [hinge_lo (a := 3) (by linarith)] | rw [hinge_hi (a := 3) (by linarith)])
      (first | rw [hinge_lo (a := 7/2) (by linarith)] | rw [hinge_hi (a := 7/2) (by linarith)])
      (first | rw [hinge_lo (a := 7) (by linarith)] | rw [hinge_hi (a := 7) (by linarith)])
      simp only [min_def]
      split_ifs <;> linarith))

theorem profile_piece_0 {z : ℝ} (h1 : (0 : ℝ) ≤ z) (h2 : z ≤ 1/2) :
    profileF z = profileHinge z := by
  profile_case

theorem profile_piece_1 {z : ℝ} (h1 : (1/2 : ℝ) ≤ z) (h2 : z ≤ 3/4) :
    profileF z = profileHinge z := by
  profile_case

theorem profile_piece_2 {z : ℝ} (h1 : (3/4 : ℝ) ≤ z) (h2 : z ≤ 1) :
    profileF z = profileHinge z := by
  profile_case

theorem profile_piece_3 {z : ℝ} (h1 : (1 : ℝ) ≤ z) (h2 : z ≤ 3/2) :
    profileF z = profileHinge z := by
  profile_case

theorem profile_piece_4 {z : ℝ} (h1 : (3/2 : ℝ) ≤ z) (h2 : z ≤ 12/7) :
    profileF z = profileHinge z := by
  profile_case

theorem profile_piece_5 {z : ℝ} (h1 : (12/7 : ℝ) ≤ z) (h2 : z ≤ 2) :
    profileF z = profileHinge z := by
  profile_case

theorem profile_piece_6 {z : ℝ} (h1 : (2 : ℝ) ≤ z) (h2 : z ≤ 9/4) :
    profileF z = profileHinge z := by
  profile_case

theorem profile_piece_7 {z : ℝ} (h1 : (9/4 : ℝ) ≤ z) (h2 : z ≤ 7/3) :
    profileF z = profileHinge z := by
  profile_case

theorem profile_piece_8 {z : ℝ} (h1 : (7/3 : ℝ) ≤ z) (h2 : z ≤ 3) :
    profileF z = profileHinge z := by
  profile_case

theorem profile_piece_9 {z : ℝ} (h1 : (3 : ℝ) ≤ z) (h2 : z ≤ 7/2) :
    profileF z = profileHinge z := by
  profile_case

theorem profile_piece_10 {z : ℝ} (h1 : (7/2 : ℝ) ≤ z) (h2 : z ≤ 7) :
    profileF z = profileHinge z := by
  profile_case

theorem profile_piece_last {z : ℝ} (h1 : (7 : ℝ) ≤ z) : profileF z = profileHinge z := by
  profile_case

/-- **Exact profile identity** on `[0, ∞)`. -/
theorem profileF_eq_hinge {z : ℝ} (hz : 0 ≤ z) : profileF z = profileHinge z := by
  rcases le_total z (1/2) with h1 | h1
  · exact profile_piece_0 (by linarith) h1
  rcases le_total z (3/4) with h2 | h2
  · exact profile_piece_1 (by linarith) h2
  rcases le_total z (1) with h3 | h3
  · exact profile_piece_2 (by linarith) h3
  rcases le_total z (3/2) with h4 | h4
  · exact profile_piece_3 (by linarith) h4
  rcases le_total z (12/7) with h5 | h5
  · exact profile_piece_4 (by linarith) h5
  rcases le_total z (2) with h6 | h6
  · exact profile_piece_5 (by linarith) h6
  rcases le_total z (9/4) with h7 | h7
  · exact profile_piece_6 (by linarith) h7
  rcases le_total z (7/3) with h8 | h8
  · exact profile_piece_7 (by linarith) h8
  rcases le_total z (3) with h9 | h9
  · exact profile_piece_8 (by linarith) h9
  rcases le_total z (7/2) with h10 | h10
  · exact profile_piece_9 (by linarith) h10
  rcases le_total z (7) with h11 | h11
  · exact profile_piece_10 (by linarith) h11
  exact profile_piece_last h11

/-! ### The affine table, support, sign, continuity -/

syntax "hinge_resolve" : tactic
macro_rules
  | `(tactic| hinge_resolve) => `(tactic| (
      simp only [profileHinge]
      (first | rw [hinge_lo (a := 1/2) (by linarith)] | rw [hinge_hi (a := 1/2) (by linarith)])
      (first | rw [hinge_lo (a := 3/4) (by linarith)] | rw [hinge_hi (a := 3/4) (by linarith)])
      (first | rw [hinge_lo (a := 1) (by linarith)] | rw [hinge_hi (a := 1) (by linarith)])
      (first | rw [hinge_lo (a := 12/7) (by linarith)] | rw [hinge_hi (a := 12/7) (by linarith)])
      (first | rw [hinge_lo (a := 2) (by linarith)] | rw [hinge_hi (a := 2) (by linarith)])
      (first | rw [hinge_lo (a := 7/3) (by linarith)] | rw [hinge_hi (a := 7/3) (by linarith)])
      (first | rw [hinge_lo (a := 3) (by linarith)] | rw [hinge_hi (a := 3) (by linarith)])
      (first | rw [hinge_lo (a := 7/2) (by linarith)] | rw [hinge_hi (a := 7/2) (by linarith)])
      (first | rw [hinge_lo (a := 7) (by linarith)] | rw [hinge_hi (a := 7) (by linarith)])
      ))

theorem profile_table_0 {z : ℝ} (h1 : (0 : ℝ) ≤ z) (h2 : z ≤ 1/2) :
    profileF z = 15 + 8/3 * z := by
  rw [profileF_eq_hinge (by linarith)]
  hinge_resolve
  ring

theorem profile_table_1 {z : ℝ} (h1 : (1/2 : ℝ) ≤ z) (h2 : z ≤ 3/4) :
    profileF z = 14 + 14/3 * z := by
  rw [profileF_eq_hinge (by linarith)]
  hinge_resolve
  ring

theorem profile_table_2 {z : ℝ} (h1 : (3/4 : ℝ) ≤ z) (h2 : z ≤ 1) :
    profileF z = 15 + 10/3 * z := by
  rw [profileF_eq_hinge (by linarith)]
  hinge_resolve
  ring

theorem profile_table_3 {z : ℝ} (h1 : (1 : ℝ) ≤ z) (h2 : z ≤ 12/7) :
    profileF z = 19 - 2/3 * z := by
  rw [profileF_eq_hinge (by linarith)]
  hinge_resolve
  ring

theorem profile_table_4 {z : ℝ} (h1 : (12/7 : ℝ) ≤ z) (h2 : z ≤ 2) :
    profileF z = 23 - 3 * z := by
  rw [profileF_eq_hinge (by linarith)]
  hinge_resolve
  ring

theorem profile_table_5 {z : ℝ} (h1 : (2 : ℝ) ≤ z) (h2 : z ≤ 7/3) :
    profileF z = 29 - 6 * z := by
  rw [profileF_eq_hinge (by linarith)]
  hinge_resolve
  ring

theorem profile_table_6 {z : ℝ} (h1 : (7/3 : ℝ) ≤ z) (h2 : z ≤ 3) :
    profileF z = 22 - 3 * z := by
  rw [profileF_eq_hinge (by linarith)]
  hinge_resolve
  ring

theorem profile_table_7 {z : ℝ} (h1 : (3 : ℝ) ≤ z) (h2 : z ≤ 7/2) :
    profileF z = 28 - 5 * z := by
  rw [profileF_eq_hinge (by linarith)]
  hinge_resolve
  ring

theorem profile_table_8 {z : ℝ} (h1 : (7/2 : ℝ) ≤ z) (h2 : z ≤ 7) :
    profileF z = 21 - 3 * z := by
  rw [profileF_eq_hinge (by linarith)]
  hinge_resolve
  ring

theorem profile_table_zero {z : ℝ} (h1 : (7 : ℝ) ≤ z) : profileF z = 0 := by
  rw [profileF_eq_hinge (by linarith)]
  hinge_resolve
  ring

/-- Endpoint agreement of consecutive pieces. -/
theorem profile_table_endpoints :
    (15 + 8/3 * (1/2 : ℝ) = 14 + 14/3 * (1/2)) ∧ (14 + 14/3 * (3/4 : ℝ) = 15 + 10/3 * (3/4)) ∧
    (15 + 10/3 * (1 : ℝ) = 19 - 2/3 * 1) ∧ (19 - 2/3 * (12/7 : ℝ) = 23 - 3 * (12/7)) ∧
    (23 - 3 * (2 : ℝ) = 29 - 6 * 2) ∧ (29 - 6 * (7/3 : ℝ) = 22 - 3 * (7/3)) ∧
    (22 - 3 * (3 : ℝ) = 28 - 5 * 3) ∧ (28 - 5 * (7/2 : ℝ) = 21 - 3 * (7/2)) ∧
    (21 - 3 * (7 : ℝ) = 0) := by
  norm_num

theorem profileF_nonneg {z : ℝ} (hz : 0 ≤ z) : 0 ≤ profileF z := by
  rw [profileF_eq_hinge hz]
  rcases le_total z (1/2) with h1 | h1
  · hinge_resolve; linarith
  rcases le_total z (3/4) with h2 | h2
  · hinge_resolve; linarith
  rcases le_total z 1 with h3 | h3
  · hinge_resolve; linarith
  rcases le_total z (12/7) with h4 | h4
  · hinge_resolve; linarith
  rcases le_total z 2 with h5 | h5
  · hinge_resolve; linarith
  rcases le_total z (7/3) with h6 | h6
  · hinge_resolve; linarith
  rcases le_total z 3 with h7 | h7
  · hinge_resolve; linarith
  rcases le_total z (7/2) with h8 | h8
  · hinge_resolve; linarith
  rcases le_total z 7 with h9 | h9
  · hinge_resolve; linarith
  · hinge_resolve; linarith

theorem profileF_bound {z : ℝ} (hz : 0 ≤ z) : profileF z ≤ 19 := by
  rw [profileF_eq_hinge hz]
  rcases le_total z (1/2) with h1 | h1
  · hinge_resolve; linarith
  rcases le_total z (3/4) with h2 | h2
  · hinge_resolve; linarith
  rcases le_total z 1 with h3 | h3
  · hinge_resolve; linarith
  rcases le_total z (12/7) with h4 | h4
  · hinge_resolve; linarith
  rcases le_total z 2 with h5 | h5
  · hinge_resolve; linarith
  rcases le_total z (7/3) with h6 | h6
  · hinge_resolve; linarith
  rcases le_total z 3 with h7 | h7
  · hinge_resolve; linarith
  rcases le_total z (7/2) with h8 | h8
  · hinge_resolve; linarith
  rcases le_total z 7 with h9 | h9
  · hinge_resolve; linarith
  · hinge_resolve; linarith

theorem continuous_hinge (a : ℝ) : Continuous (hinge a) :=
  (continuous_const.sub continuous_id).max continuous_const

theorem continuous_profileF : Continuous profileF := by
  unfold profileF prR prN1 prN3 prQ prB0 prC2 prC1 prC0 prT prB
  fun_prop

/-! ### The exact integral -/

theorem integral_hinge {a : ℝ} (ha0 : 0 ≤ a) (ha7 : a ≤ 7) :
    ∫ z in (0 : ℝ)..7, hinge a z = a ^ 2 / 2 := by
  have hi : ∀ u v : ℝ, IntervalIntegrable (hinge a) MeasureTheory.volume u v :=
    fun u v => (continuous_hinge a).intervalIntegrable u v
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi 0 a) (hi a 7)]
  have h1 : ∫ z in (0 : ℝ)..a, hinge a z = ∫ z in (0 : ℝ)..a, (a - z) := by
    apply intervalIntegral.integral_congr
    intro z hz
    rw [Set.uIcc_of_le ha0] at hz
    exact hinge_lo hz.2
  have h2 : ∫ z in a..(7 : ℝ), hinge a z = ∫ z in a..(7 : ℝ), (0 : ℝ) := by
    apply intervalIntegral.integral_congr
    intro z hz
    rw [Set.uIcc_of_le ha7] at hz
    exact hinge_hi hz.1
  rw [h1, h2, intervalIntegral.integral_sub intervalIntegrable_const
    intervalIntegral.intervalIntegrable_id, integral_id]
  simp
  ring

/-- The hinge weights and nodes. -/
def hingeW : Fin 9 → ℝ := ![2, -4/3, -4, -7/3, -3, 3, -2, 2, 3]
def hingeA : Fin 9 → ℝ := ![1/2, 3/4, 1, 12/7, 2, 7/3, 3, 7/2, 7]

theorem profileHinge_eq_sum (z : ℝ) :
    profileHinge z = ∑ k : Fin 9, hingeW k * hinge (hingeA k) z := by
  simp only [profileHinge, Fin.sum_univ_succ, Fin.sum_univ_zero, hingeW, hingeA]
  simp
  ring

theorem hingeA_mem (k : Fin 9) : 0 ≤ hingeA k ∧ hingeA k ≤ 7 := by
  fin_cases k <;> simp [hingeA] <;> norm_num

/-- **Exact integral** `∫₀⁷ f = 12325/168`. -/
theorem integral_profileF : ∫ z in (0 : ℝ)..7, profileF z = 12325 / 168 := by
  have h1 : ∫ z in (0 : ℝ)..7, profileF z = ∫ z in (0 : ℝ)..7, profileHinge z := by
    apply intervalIntegral.integral_congr
    intro z hz
    rw [Set.uIcc_of_le (by norm_num)] at hz
    exact profileF_eq_hinge hz.1
  rw [h1]
  simp only [profileHinge_eq_sum]
  rw [intervalIntegral.integral_finsetSum (fun k _ =>
    ((continuous_hinge (hingeA k)).intervalIntegrable 0 7).const_mul (hingeW k))]
  simp only [intervalIntegral.integral_const_mul]
  rw [Finset.sum_congr rfl (fun k _ => by
    rw [integral_hinge (hingeA_mem k).1 (hingeA_mem k).2])]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, hingeW, hingeA]
  simp
  norm_num

/-- The hinge weights reproduce the integral: `Σ wₖ aₖ²/2 = 12325/168`. -/
theorem hinge_moment : ∑ k : Fin 9, hingeW k * (hingeA k ^ 2 / 2) = 12325 / 168 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, hingeW, hingeA]
  simp
  norm_num

end Zeta7Auxiliary
