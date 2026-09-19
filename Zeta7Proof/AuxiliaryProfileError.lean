import Zeta7Proof.AuxiliaryProfile
import Zeta7Proof.AuxiliarySimultaneousCounts

/-! P8, milestone 2: the uniform profile error.

With `N_d = 7d + 176` (so `L₀ = 176`), for every `d ≥ 2` and every `p`,
`|sharpThreshold d p N_d - d f(p/d)| ≤ 920`. The exact counts are compared with the
normalized counts scaled by `d`, using `|a₊ - b₊| ≤ |a - b|` and the max-norm Lipschitz bound
for `min`. All casts, floors (`(p-1)/3`) and truncated subtractions are handled explicitly. -/
noncomputable section
set_option autoImplicit false
namespace Zeta7Auxiliary

/-! ### Reusable Lipschitz lemmas -/

theorem abs_pos_part_sub_le (a b : ℝ) : |max a 0 - max b 0| ≤ |a - b| :=
  abs_max_sub_max_le_abs a b 0

theorem abs_min_sub_min_le (a b c e : ℝ) : |min a b - min c e| ≤ max |a - c| |b - e| :=
  abs_min_sub_min_le_max a b c e

theorem abs_max_sub_max_le (a b c e : ℝ) : |max a b - max c e| ≤ max |a - c| |b - e| :=
  abs_max_sub_max_le_max a b c e

theorem cast_tsub (a b : ℕ) : ((a - b : ℕ) : ℝ) = max ((a : ℝ) - b) 0 := by
  rcases le_total b a with h | h
  · rw [Nat.cast_sub h, max_eq_left (by simp [h])]
  · rw [Nat.sub_eq_zero_of_le h, max_eq_right (by simp [h])]; simp

theorem abs_min_le_of {a b c e x y : ℝ} (h1 : |a - c| ≤ x) (h2 : |b - e| ≤ y) :
    |min a b - min c e| ≤ max x y :=
  (abs_min_sub_min_le a b c e).trans (max_le_max h1 h2)

/-! ### Scaled normalized counts -/

section scaled
variable {D P : ℝ} (hD : 0 < D)
include hD

theorem sc_min (a b : ℝ) : D * min a b = min (D * a) (D * b) := mul_min_of_nonneg a b hD.le
theorem sc_pos (a : ℝ) : D * max a 0 = max (D * a) 0 := by
  rw [mul_max_of_nonneg a 0 hD.le, mul_zero]

theorem sc_B : D * prB (P / D) = D + 4 * P / 3 := by
  unfold prB; field_simp
theorem sc_C0 : D * prC0 (P / D) = min (3 * D) (D + 4 * P / 3) := by
  unfold prC0; rw [sc_min hD, sc_B hD, mul_comm D 3]
theorem sc_C1 : D * prC1 (P / D) = min (3 * D - D * prC0 (P / D)) D := by
  unfold prC1; rw [sc_min hD, mul_sub, mul_one, mul_comm D 3]
theorem sc_C2 : D * prC2 (P / D) = 3 * D - D * prC0 (P / D) - D * prC1 (P / D) := by
  unfold prC2; ring
theorem sc_T : D * prT (P / D) = min D (2 * max (D - P) 0) := by
  unfold prT
  rw [sc_min hD, mul_one, ← mul_assoc, mul_comm D 2, mul_assoc, sc_pos hD, mul_sub, mul_one,
    mul_div_cancel₀ _ hD.ne']
theorem sc_Q : D * prQ (P / D) =
    min (2 * D) (min D (max (7 * D - 2 * P) 0) + min D (max (7 * D - 3 * P) 0)) := by
  unfold prQ
  rw [sc_min hD, mul_add, sc_min hD, sc_min hD, sc_pos hD, sc_pos hD, mul_sub, mul_sub,
    mul_one, mul_comm D 2, mul_comm D 7]
  congr 4 <;> field_simp
theorem sc_B0 : D * prB0 (P / D) =
    min (D * prC0 (P / D) + D - D * prT (P / D)) (D + 4 * P / 3) := by
  unfold prB0; rw [sc_min hD, sc_B hD]; ring_nf
theorem sc_N1 : D * prN1 (P / D) = D * prC2 (P / D) + D * prT (P / D) := by
  unfold prN1; ring
theorem sc_N3 : D * prN3 (P / D) = 2 * D - D * prQ (P / D) + D * prB0 (P / D) := by
  unfold prN3; ring
theorem sc_R : D * prR (P / D) = min (6 * D) (max (7 * D - P) 0) := by
  unfold prR
  rw [sc_min hD, sc_pos hD, mul_sub, mul_div_cancel₀ _ hD.ne', mul_comm D 6, mul_comm D 7]
theorem sc_F : D * profileF (P / D) =
    D * prR (P / D) + min (D * prR (P / D)) (6 * D - D * prN1 (P / D)) +
      min (D * prR (P / D)) (D * prQ (P / D) + D * prN3 (P / D)) +
      min (D * prR (P / D)) (D * prQ (P / D)) := by
  unfold profileF
  rw [mul_add, mul_add, mul_add, sc_min hD, sc_min hD, sc_min hD, mul_sub, mul_add,
    mul_comm D 6]

end scaled

/-! ### Individual approximation bounds -/

section errors
variable (d p : ℕ)

/-- Shorthand for the scaled normalized counts at `z = p/d`. -/
abbrev nc (g : ℝ → ℝ) : ℝ := (d : ℝ) * g ((p : ℝ) / d)

theorem floor_third_bounds :
    3 * (((p - 1) / 3 : ℕ) : ℝ) ≤ p ∧ (p : ℝ) ≤ 3 * (((p - 1) / 3 : ℕ) : ℝ) + 3 := by
  have h1 : 3 * ((p - 1) / 3) ≤ p := by omega
  have h2 : p ≤ 3 * ((p - 1) / 3) + 3 := by omega
  exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩

theorem c0_le (d p : ℕ) : derivativeThree d p ≤ 3 * d := min_le_left _ _

theorem c1_le (d p : ℕ) : derivativeTwo d p ≤ 3 * d - derivativeThree d p := min_le_left _ _

variable {d} (hd : 2 ≤ d)
include hd

theorem dpos : (0 : ℝ) < d := by
  have : (2 : ℝ) ≤ d := by exact_mod_cast hd
  linarith

theorem err_b : |(derivativeBudget d p : ℝ) - nc d p prB| ≤ 4 := by
  rw [nc, sc_B (dpos hd)]
  obtain ⟨h1, h2⟩ := floor_third_bounds p
  unfold derivativeBudget
  push_cast
  rw [abs_le]; constructor <;> linarith

theorem err_c0 : |(derivativeThree d p : ℝ) - nc d p prC0| ≤ 4 := by
  rw [nc, sc_C0 (dpos hd)]
  unfold derivativeThree
  push_cast
  have h := err_b p hd
  rw [nc, sc_B (dpos hd)] at h
  refine (abs_min_le_of (x := 0) (y := 4) (by simp) h).trans (by norm_num)

theorem err_c1 : |(derivativeTwo d p : ℝ) - nc d p prC1| ≤ 4 := by
  rw [nc, sc_C1 (dpos hd)]
  unfold derivativeTwo
  rw [Nat.cast_min, Nat.cast_sub (c0_le d p)]
  push_cast
  have h := err_c0 p hd
  refine (abs_min_le_of (x := 4) (y := 2) ?_ ?_).trans (by norm_num)
  · rw [show (3 * (d : ℝ) - derivativeThree d p) - (3 * d - nc d p prC0) =
      -((derivativeThree d p : ℝ) - nc d p prC0) by ring, abs_neg]; exact h
  · rw [show (d : ℝ) + 2 - d = 2 by ring]; norm_num

theorem cast_c2 : (derivativeOne d p : ℝ) =
    3 * d - derivativeThree d p - derivativeTwo d p := by
  have h0 := c0_le d p
  have h1 := c1_le d p
  unfold derivativeOne
  rw [Nat.cast_sub (by omega), Nat.cast_sub h0]
  push_cast; ring

theorem err_c2 : |(derivativeOne d p : ℝ) - nc d p prC2| ≤ 8 := by
  rw [cast_c2 p hd, nc, sc_C2 (dpos hd)]
  have h0 := err_c0 p hd
  have h1 := err_c1 p hd
  rw [nc] at h0 h1
  rw [abs_le] at h0 h1 ⊢
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2]

theorem err_s : |(primitiveShifts d : ℝ) - d| ≤ 2 := by
  unfold primitiveShifts
  rw [Nat.cast_sub hd]
  norm_num

theorem err_t : |(resonanceShifts d p : ℝ) - nc d p prT| ≤ 6 := by
  rw [nc, sc_T (dpos hd)]
  unfold resonanceShifts
  have hD := dpos hd
  have e1 : ((d - 4 : ℕ) : ℝ) = max ((d : ℝ) - 4) 0 := by rw [cast_tsub]; norm_num
  have e2 : ((d - p - 2 : ℕ) : ℝ) = max (max ((d : ℝ) - p) 0 - 2) 0 := by
    rw [cast_tsub, cast_tsub]; norm_num
  have e3 : ((d - p - 4 : ℕ) : ℝ) = max (max ((d : ℝ) - p) 0 - 4) 0 := by
    rw [cast_tsub, cast_tsub]; norm_num
  rw [Nat.cast_min, Nat.cast_add, e1, e2, e3]
  refine (abs_min_le_of (x := 4) (y := 6) ?_ ?_).trans (by norm_num)
  · simp only [max_def]; split_ifs <;> (rw [abs_le]; constructor <;> linarith)
  · generalize (d : ℝ) - p = u
    simp only [max_def]; split_ifs <;> (rw [abs_le]; constructor <;> linarith)

omit hd in
theorem abs_add4_le {a b c e : ℝ} {x y u v : ℝ} (h1 : |a| ≤ x) (h2 : |b| ≤ y) (h3 : |c| ≤ u)
    (h4 : |e| ≤ v) : |a + b + c + e| ≤ x + y + u + v := by
  rw [abs_le] at *
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, h4.1, h4.2]

theorem err_b0 : |(jointThirdRank d p : ℝ) - nc d p prB0| ≤ 12 := by
  rw [nc, sc_B0 (dpos hd)]
  unfold jointThirdRank
  have ht := resonanceShifts_le_primitiveShifts d p
  rw [Nat.cast_min, Nat.cast_sub (by omega), Nat.cast_add]
  have h0 := err_c0 p hd
  have hs := err_s hd
  have htt := err_t p hd
  have hb := err_b p hd
  rw [nc, sc_B (dpos hd)] at hb
  rw [nc] at h0 htt
  refine (abs_min_le_of (x := 12) (y := 4) ?_ hb).trans (by norm_num)
  rw [abs_le] at *
  constructor <;> linarith [h0.1, h0.2, hs.1, hs.2, htt.1, htt.2]

theorem err_n1 : |(simultaneousOne d p : ℝ) - nc d p prN1| ≤ 14 := by
  rw [nc, sc_N1 (dpos hd)]
  unfold simultaneousOne
  have h2 := err_c2 p hd
  have htt := err_t p hd
  rw [nc] at h2 htt
  push_cast
  rw [abs_le] at *
  constructor <;> linarith [h2.1, h2.2, htt.1, htt.2]

theorem err_q : |(jointFourthRank d p (7 * d + 176) : ℝ) - nc d p prQ| ≤ 355 := by
  rw [nc, sc_Q (dpos hd)]
  unfold jointFourthRank
  have e2 : ((7 * d + 176 - 2 * p : ℕ) : ℝ) = max (7 * (d : ℝ) + 176 - 2 * p) 0 := by
    rw [cast_tsub]; push_cast; ring_nf
  have e3 : ((7 * d + 176 - 3 * p : ℕ) : ℝ) = max (7 * (d : ℝ) + 176 - 3 * p) 0 := by
    rw [cast_tsub]; push_cast; ring_nf
  push_cast [Nat.cast_min]
  rw [e2, e3]
  have i1 : |min ((d : ℝ) + 2) (max (7 * (d : ℝ) + 176 - 2 * p) 0) -
      min (d : ℝ) (max (7 * d - 2 * p) 0)| ≤ 176 := by
    refine (abs_min_le_of (x := 2) (y := 176) ?_ ?_).trans (by norm_num)
    · push_cast; ring_nf; norm_num
    · refine (abs_pos_part_sub_le _ _).trans ?_
      ring_nf; norm_num
  have i2 : |min ((d : ℝ) + 1) (max (7 * (d : ℝ) + 176 - 3 * p) 0) -
      min (d : ℝ) (max (7 * d - 3 * p) 0)| ≤ 176 := by
    refine (abs_min_le_of (x := 1) (y := 176) ?_ ?_).trans (by norm_num)
    · push_cast; ring_nf; norm_num
    · refine (abs_pos_part_sub_le _ _).trans ?_
      ring_nf; norm_num
  refine (abs_min_le_of (x := 2) (y := 352) ?_ ?_).trans (by norm_num)
  · push_cast; ring_nf; norm_num
  · rw [abs_le] at *
    constructor <;> linarith [i1.1, i1.2, i2.1, i2.2]

theorem q_add_n3 :
    jointFourthRank d p (7 * d + 176) + simultaneousThree d p (7 * d + 176) =
      2 * d + 2 + jointThirdRank d p := by
  have hq : jointFourthRank d p (7 * d + 176) ≤ 2 * d + 2 := min_le_left _ _
  unfold simultaneousThree primitiveShifts
  omega

theorem err_qn3 :
    |((jointFourthRank d p (7 * d + 176) + simultaneousThree d p (7 * d + 176) : ℕ) : ℝ) -
      (nc d p prQ + nc d p prN3)| ≤ 14 := by
  rw [q_add_n3 p hd, nc, nc, sc_N3 (dpos hd)]
  have h := err_b0 p hd
  rw [nc] at h
  push_cast
  rw [abs_le] at *
  constructor <;> linarith [h.1, h.2]

theorem err_r : |(min (6 * d) (7 * d + 176 - p) : ℕ) - nc d p prR| ≤ 176 := by
  rw [nc, sc_R (dpos hd), Nat.cast_min, cast_tsub]
  refine (abs_min_le_of (x := 0) (y := 176) ?_ ?_).trans (by norm_num)
  · push_cast; simp
  · refine (abs_pos_part_sub_le _ _).trans ?_
    push_cast; ring_nf; norm_num

omit hd in
theorem prN1_le {z : ℝ} (hz : 0 ≤ z) : prN1 z ≤ 3 := by
  unfold prN1 prC2 prC1 prC0 prB
  have ht := prT_le_one z
  have h1 : (1 : ℝ) ≤ min 3 (1 + 4 * z / 3) := le_min (by norm_num) (by linarith)
  have h2 : (0 : ℝ) ≤ min (3 - min 3 (1 + 4 * z / 3)) 1 :=
    le_min (by have := min_le_left (3 : ℝ) (1 + 4 * z / 3); linarith) (by norm_num)
  linarith

theorem err_six_n1 :
    |((6 * d - simultaneousOne d p : ℕ) : ℝ) - (6 * (d : ℝ) - nc d p prN1)| ≤ 14 := by
  have hD := dpos hd
  have hz : (0 : ℝ) ≤ (p : ℝ) / d := div_nonneg (Nat.cast_nonneg _) hD.le
  have hn := prN1_le hz
  have hpos : 0 ≤ 6 * (d : ℝ) - nc d p prN1 := by
    rw [nc]; nlinarith
  rw [cast_tsub, ← max_eq_left hpos]
  refine (abs_pos_part_sub_le _ _).trans ?_
  push_cast
  rw [show (6 * (d : ℝ) - simultaneousOne d p) - (6 * d - nc d p prN1) =
    -((simultaneousOne d p : ℝ) - nc d p prN1) by ring, abs_neg]
  exact err_n1 p hd

/-- **Uniform profile error** (37): `|T(d, p, N_d) - d f(p/d)| ≤ 920` for `d ≥ 2`, all `p`. -/
theorem sharpThreshold_profile_error :
    |(sharpThreshold d p (7 * d + 176) : ℝ) - (d : ℝ) * profileF ((p : ℝ) / d)| ≤ 920 := by
  have hD := dpos hd
  rw [sc_F hD]
  simp only [sharpThreshold]
  push_cast [Nat.cast_min]
  have hr := err_r p hd
  have h6 := err_six_n1 p hd
  have hqn := err_qn3 p hd
  have hq := err_q p hd
  simp only [nc] at hr h6 hqn hq ⊢
  push_cast [Nat.cast_min] at hr h6 hqn hq ⊢
  have t2 := abs_min_le_of hr h6
  have t3 := abs_min_le_of hr hqn
  have t4 := abs_min_le_of hr hq
  have key := abs_add4_le hr t2 t3 t4
  norm_num at key
  rw [abs_le] at key ⊢
  constructor <;> linarith [key.1, key.2]

end errors

end Zeta7Auxiliary
