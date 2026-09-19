import Mathlib

/-! Kernel-checkable bounds for arctangent, arccosine and the energy summand.

* `arctan_le_atanPoly`, `atanPoly_le_arctan`: for `v ≥ 0`, the alternating Taylor sums with an odd
  (resp. even) number of terms are upper (resp. lower) bounds for `arctan v`; the proof integrates
  the geometric-sum bounds for `1/(1+s²)`.
* `arctan_le_two_arctan`, `two_arctan_le_arctan`: the half-angle reduction
  `arctan u = 2 arctan (u / (1 + √(1+u²)))`, with rational bounds for the square root.
* `arccos_le_arctan`: `arccos a ≤ arctan u` from a rational bound `√(1-a²)/a ≤ u`.
* `gfun_le`: `arccos x - x √(1-x²) ≤ arccos a - a s` for `a ≤ x ≤ b`, `s² ≤ 1 - b²`.
* `le_mul_sqrt`, `mul_sqrt_le`: rational bounds for `m √p`. -/
noncomputable section
set_option autoImplicit false
namespace Zeta7Cert
open Real Finset

/-- The alternating arctangent Taylor sum with `N` terms. -/
def atanPoly (N : ℕ) (v : ℝ) : ℝ :=
  ∑ k ∈ range N, (-1 : ℝ) ^ k * v ^ (2 * k + 1) / (2 * k + 1)

theorem geom_identity (s : ℝ) (N : ℕ) :
    (∑ k ∈ range N, (-(s ^ 2)) ^ k) * (1 + s ^ 2) = 1 - (-(s ^ 2)) ^ N := by
  have h := geom_sum_mul_neg (-(s ^ 2)) N
  rw [sub_neg_eq_add] at h
  exact h

theorem arctan_eq_integral (v : ℝ) : arctan v = ∫ s in (0 : ℝ)..v, 1 / (1 + s ^ 2) := by
  rw [integral_one_div_one_add_sq, arctan_zero, sub_zero]

theorem integral_geom (v : ℝ) (N : ℕ) :
    ∫ s in (0 : ℝ)..v, ∑ k ∈ range N, (-(s ^ 2)) ^ k = atanPoly N v := by
  rw [intervalIntegral.integral_finsetSum fun k _ => (by fun_prop : Continuous fun s : ℝ =>
    (-(s ^ 2)) ^ k).intervalIntegrable _ _]
  unfold atanPoly
  refine Finset.sum_congr rfl fun k _ => ?_
  have : (fun s : ℝ => (-(s ^ 2)) ^ k) = fun s => (-1 : ℝ) ^ k * s ^ (2 * k) := by
    funext s; rw [neg_pow, ← pow_mul]
  rw [this, intervalIntegral.integral_const_mul, integral_pow]
  push_cast
  ring

theorem cont_inv_one_add_sq : Continuous fun s : ℝ => 1 / (1 + s ^ 2) :=
  continuous_const.div (by fun_prop) fun s => by positivity

theorem geom_pos_cont (N : ℕ) : Continuous fun s : ℝ => ∑ k ∈ range N, (-(s ^ 2)) ^ k := by
  fun_prop

/-- Odd number of terms: an upper bound. -/
theorem arctan_le_atanPoly {v : ℝ} (hv : 0 ≤ v) (n : ℕ) : arctan v ≤ atanPoly (2 * n + 1) v := by
  rw [arctan_eq_integral, ← integral_geom]
  refine intervalIntegral.integral_mono_on hv
    (cont_inv_one_add_sq.intervalIntegrable _ _)
    ((geom_pos_cont _).intervalIntegrable _ _) fun s _ => ?_
  have hpos : 0 < 1 + s ^ 2 := by positivity
  have h := geom_identity s (2 * n + 1)
  rw [div_le_iff₀ hpos, h]
  have : (-(s ^ 2)) ^ (2 * n + 1) ≤ 0 := by
    rw [pow_succ, pow_mul, neg_sq]
    exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (by nlinarith [sq_nonneg s])
  linarith

/-- Even number of terms: a lower bound. -/
theorem atanPoly_le_arctan {v : ℝ} (hv : 0 ≤ v) (n : ℕ) : atanPoly (2 * n + 2) v ≤ arctan v := by
  rw [arctan_eq_integral, ← integral_geom]
  refine intervalIntegral.integral_mono_on hv ((geom_pos_cont _).intervalIntegrable _ _)
    (cont_inv_one_add_sq.intervalIntegrable _ _) fun s _ => ?_
  have hpos : 0 < 1 + s ^ 2 := by positivity
  have h := geom_identity s (2 * n + 2)
  rw [le_div_iff₀ hpos, h]
  have : 0 ≤ (-(s ^ 2)) ^ (2 * n + 2) := by
    rw [show 2 * n + 2 = 2 * (n + 1) by ring, pow_mul, neg_sq]; positivity
  linarith

/-! ### Half-angle reduction -/

theorem arctan_half_angle (u : ℝ) : arctan u = 2 * arctan (u / (1 + √(1 + u ^ 2))) := by
  set S := √(1 + u ^ 2) with hS
  have hS2 : S ^ 2 = 1 + u ^ 2 := Real.sq_sqrt (by positivity)
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  have h1S : 0 < 1 + S := by linarith
  set r := u / (1 + S) with hr
  have hr2 : 1 - r ^ 2 = 2 / (1 + S) := by
    rw [hr, div_pow]; field_simp; nlinarith
  have hrr : r * r < 1 := by
    have : 0 < 2 / (1 + S) := by positivity
    nlinarith
  rw [two_mul, arctan_add hrr]
  congr 1
  have : 1 - r * r = 2 / (1 + S) := by rw [← hr2]; ring
  rw [this, hr]
  field_simp
  ring

theorem arctan_le_two_arctan {u r q : ℝ} (hu : 0 ≤ u) (hq : 0 ≤ q) (hq2 : q ^ 2 ≤ 1 + u ^ 2)
    (hr : u ≤ r * (1 + q)) : arctan u ≤ 2 * arctan r := by
  rw [arctan_half_angle u]
  have hS : q ≤ √(1 + u ^ 2) := Real.le_sqrt_of_sq_le hq2
  have h1 : 0 < 1 + q := by linarith
  have hle : u / (1 + √(1 + u ^ 2)) ≤ r := by
    rw [div_le_iff₀ (by positivity)]
    calc u ≤ r * (1 + q) := hr
      _ ≤ r * (1 + √(1 + u ^ 2)) := by
        have hr0 : 0 ≤ r := by
          by_contra h
          push Not at h
          nlinarith
        exact mul_le_mul_of_nonneg_left (by linarith) hr0
  exact mul_le_mul_of_nonneg_left (arctan_strictMono.monotone hle) (by norm_num)

theorem two_arctan_le_arctan {u r q : ℝ} (hq : 0 ≤ q) (hq2 : 1 + u ^ 2 ≤ q ^ 2)
    (hr0 : 0 ≤ r) (hr : r * (1 + q) ≤ u) : 2 * arctan r ≤ arctan u := by
  rw [arctan_half_angle u]
  have hS : √(1 + u ^ 2) ≤ q := Real.sqrt_le_iff.mpr ⟨hq, hq2⟩
  have hle : r ≤ u / (1 + √(1 + u ^ 2)) := by
    rw [le_div_iff₀ (by positivity)]
    calc r * (1 + √(1 + u ^ 2)) ≤ r * (1 + q) := mul_le_mul_of_nonneg_left (by linarith) hr0
      _ ≤ u := hr
  exact mul_le_mul_of_nonneg_left (arctan_strictMono.monotone hle) (by norm_num)

/-- `arctan u = π/2 - arctan (1/u)` in bound form. -/
theorem arctan_le_of_inv {u v : ℝ} (hu : 0 < u) (hv : v ≤ u⁻¹) : arctan u ≤ π / 2 - arctan v := by
  have h := arctan_inv_of_pos hu
  have := arctan_strictMono.monotone hv
  linarith

/-! ### Arccosine and the energy summand -/

theorem arccos_le_arctan {a s u : ℝ} (ha : 0 < a) (hs : 0 ≤ s) (hs2 : 1 - a ^ 2 ≤ s ^ 2)
    (hu : s ≤ u * a) : arccos a ≤ arctan u := by
  rw [arccos_eq_arctan ha]
  apply arctan_strictMono.monotone
  rw [div_le_iff₀ ha]
  exact (Real.sqrt_le_iff.mpr ⟨hs, hs2⟩).trans hu

theorem gfun_le {x a b s : ℝ} (ha : 0 ≤ a) (hax : a ≤ x) (hxb : x ≤ b) (hs : 0 ≤ s)
    (hs2 : s ^ 2 ≤ 1 - b ^ 2) :
    arccos x - x * √(1 - x ^ 2) ≤ arccos a - a * s := by
  have hb1 : b ^ 2 ≤ 1 := by nlinarith
  have hx0 : 0 ≤ x := ha.trans hax
  have hb0 : 0 ≤ b := hx0.trans hxb
  have hb : b ≤ 1 := by nlinarith
  have harc : arccos x ≤ arccos a :=
    Real.strictAntiOn_arccos.antitoneOn ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ hax
  have hsq : s ≤ √(1 - x ^ 2) := Real.le_sqrt_of_sq_le (by nlinarith)
  have : a * s ≤ x * √(1 - x ^ 2) := mul_le_mul hax hsq hs hx0
  linarith

/-- Rational bounds for `m √p`. -/
theorem le_mul_sqrt {m p lo : ℝ} (hm : 0 ≤ m) (hlo : lo ^ 2 ≤ m ^ 2 * p) : lo ≤ m * √p := by
  rw [← Real.sqrt_sq hm, ← Real.sqrt_mul (sq_nonneg m)]
  exact Real.le_sqrt_of_sq_le hlo

theorem mul_sqrt_le {m p hi : ℝ} (hm : 0 ≤ m) (hhi : 0 ≤ hi) (h : m ^ 2 * p ≤ hi ^ 2) :
    m * √p ≤ hi := by
  rw [← Real.sqrt_sq hm, ← Real.sqrt_mul (sq_nonneg m)]
  exact Real.sqrt_le_iff.mpr ⟨hhi, h⟩

end Zeta7Cert
