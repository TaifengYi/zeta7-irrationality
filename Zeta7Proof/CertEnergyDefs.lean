import Zeta7Proof.CertArctan

/-! The explicit six-circle energy (48) and the surplus `S`, with the generic certificate lemmas.

* `energyE y t = -2π min(y,t) + Σ_{m ≥ 7, 7 | m, m² y t < 1} (4π φ(m)/m²)
    (arccos(m√(yt)) - m√(yt) √(1 - m² y t))`, for rational `y, t > 0`; the summation set `mSet`
  is exactly `{m | 7 ≤ m ∧ 7 ∣ m ∧ m² y t < 1}` (`mem_mSet`).
* `explicitW i = Σ_j w_j E(y_i, y_j)`, `explicitI = Σ_i w_i W_i`, `cb` the boundaries `b_i`,
  `explicitJ = Σ_i ((b_{i+1} - b_i) W_i - (b_{i+1}² - b_i²)/2 · t_i)` with `t_i = -2π y_i`,
  and `surplusS = 43 log 7 + (7/2) I - J - 12325/168`.
* `term_le`, `atan_up_direct`, `atan_up_inv`: the combinators used by the generated term
  certificates. -/
noncomputable section
set_option autoImplicit false
namespace Zeta7Cert
open Real Finset

/-- The C5 heights `y_i` as rationals. -/
def cy : Fin 6 → ℚ := ![1/2, 1/5, 19/200, 11/200, 7/200, 23/1000]

/-- The C5 weights `w_i` as rationals. -/
def cw : Fin 6 → ℚ := ![1/25, 2/25, 7/50, 17/100, 6/25, 33/100]

/-- The summation set `{m | 7 ≤ m, 7 ∣ m, m² y t < 1}`. -/
def mSet (y t : ℚ) : Finset ℕ :=
  (range (⌈(y * t)⁻¹⌉₊ + 1)).filter fun m => 7 ≤ m ∧ 7 ∣ m ∧ (m : ℚ) ^ 2 * y * t < 1

theorem mem_mSet {y t : ℚ} (hyt : 0 < y * t) {m : ℕ} :
    m ∈ mSet y t ↔ 7 ≤ m ∧ 7 ∣ m ∧ (m : ℚ) ^ 2 * y * t < 1 := by
  unfold mSet
  rw [mem_filter, mem_range]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    have hm1 : (1 : ℚ) ≤ m := by exact_mod_cast (le_trans (by norm_num) h.1)
    have h2 : (m : ℚ) ≤ (m : ℚ) ^ 2 := by nlinarith
    have h3 : (m : ℚ) ^ 2 < (y * t)⁻¹ := by
      by_contra hc
      push Not at hc
      have e : (y * t)⁻¹ * (y * t) = 1 := inv_mul_cancel₀ hyt.ne'
      have := mul_le_mul_of_nonneg_right hc hyt.le
      nlinarith [h.2.2]
    have h4 : (m : ℚ) < ⌈(y * t)⁻¹⌉₊ + 1 := by
      have := Nat.le_ceil ((y * t)⁻¹)
      linarith
    exact_mod_cast h4

/-- The cutoff set equals the multiples of seven in `[7, B]` when `B² y t < 1 ≤ (B+1)² y t`. -/
theorem mSet_eq {y t : ℚ} (hyt : 0 < y * t) (B : ℕ) (hB : (B : ℚ) ^ 2 * y * t < 1)
    (hB1 : 1 ≤ ((B : ℚ) + 1) ^ 2 * y * t) :
    mSet y t = (range (B + 1)).filter fun m => 7 ≤ m ∧ 7 ∣ m := by
  ext m
  rw [mem_mSet hyt, mem_filter, mem_range]
  constructor
  · rintro ⟨h7, hd, hm⟩
    refine ⟨?_, h7, hd⟩
    by_contra hcon
    push Not at hcon
    have : ((B : ℚ) + 1) ≤ m := by exact_mod_cast hcon
    have : ((B : ℚ) + 1) ^ 2 * y * t ≤ (m : ℚ) ^ 2 * y * t := by
      have h0 : (0 : ℚ) ≤ (B : ℚ) + 1 := by positivity
      have := pow_le_pow_left₀ h0 this 2
      rw [mul_assoc, mul_assoc]
      exact mul_le_mul_of_nonneg_right this hyt.le
    linarith
  · rintro ⟨hmB, h7, hd⟩
    refine ⟨h7, hd, ?_⟩
    have : (m : ℚ) ≤ B := by exact_mod_cast Nat.lt_succ_iff.mp hmB
    have h0 : (0 : ℚ) ≤ m := by positivity
    have := pow_le_pow_left₀ h0 this 2
    have : (m : ℚ) ^ 2 * y * t ≤ (B : ℚ) ^ 2 * y * t := by
      rw [mul_assoc, mul_assoc]
      exact mul_le_mul_of_nonneg_right this hyt.le
    linarith

/-- The summand `(4π φ(m)/m²)(arccos(m√(yt)) - m√(yt)√(1 - m²yt))`. -/
def eTerm (y t : ℚ) (m : ℕ) : ℝ :=
  4 * π * (Nat.totient m : ℝ) / (m : ℝ) ^ 2 *
    (arccos (m * √((y : ℝ) * t)) - m * √((y : ℝ) * t) * √(1 - (m : ℝ) ^ 2 * y * t))

/-- **The explicit mutual energy (48)**. -/
def energyE (y t : ℚ) : ℝ := -2 * π * ((min y t : ℚ) : ℝ) + ∑ m ∈ mSet y t, eTerm y t m

/-- `W_i = Σ_j w_j E(y_i, y_j)`. -/
def explicitW (i : Fin 6) : ℝ := ∑ j, (cw j : ℝ) * energyE (cy i) (cy j)

/-- `I = Σ_i w_i W_i`. -/
def explicitI : ℝ := ∑ i, (cw i : ℝ) * explicitW i

/-- `b_n = 7 Σ_{j<n} w_j`. -/
def cb (n : ℕ) : ℚ := 7 * ∑ j : Fin 6, if (j : ℕ) < n then cw j else 0

/-- `J = Σ_i ((b_{i+1} - b_i) W_i - (b_{i+1}² - b_i²)/2 · t_i)`, `t_i = -2π y_i`. -/
def explicitJ : ℝ :=
  ∑ i : Fin 6, (((cb (i + 1) - cb i : ℚ) : ℝ) * explicitW i -
    ((cb (i + 1) ^ 2 - cb i ^ 2 : ℚ) : ℝ) / 2 * (-2 * π * (cy i : ℝ)))

/-- **The surplus** `S = 43 log 7 + (7/2) I - J - 12325/168`. -/
def surplusS : ℝ := 43 * Real.log 7 + 7 / 2 * explicitI - explicitJ - 12325 / 168

/-! ### Certificate combinators -/

/-- One energy summand: `g(m√p) ≤ G` from rational data. -/
theorem term_le {m p a b s shi u A G : ℝ} (hm : 0 ≤ m) (hp : 0 ≤ p) (ha : 0 < a)
    (hlo : a ^ 2 ≤ m ^ 2 * p) (hhi : m ^ 2 * p ≤ b ^ 2) (hb : 0 ≤ b) (hs : 0 ≤ s)
    (hs2 : s ^ 2 ≤ 1 - b ^ 2) (hshi : 0 ≤ shi) (hshi2 : 1 - a ^ 2 ≤ shi ^ 2)
    (hu : shi ≤ u * a) (hat : arctan u ≤ A) (hG : A - a * s ≤ G) :
    arccos (m * √p) - m * √p * √(1 - m ^ 2 * p) ≤ G := by
  have hx2 : (m * √p) ^ 2 = m ^ 2 * p := by rw [mul_pow, Real.sq_sqrt hp]
  have h1 := gfun_le ha.le (le_mul_sqrt hm hlo) (mul_sqrt_le hm hb hhi) hs hs2
  rw [hx2] at h1
  have h2 := arccos_le_arctan ha hshi hshi2 hu
  linarith

/-- `term_le` in the form `m² y t` used by `eTerm`. -/
theorem term_le' {m y t a b s shi u A G : ℝ} (hm : 0 ≤ m) (hy : 0 ≤ y) (ht : 0 ≤ t) (ha : 0 < a)
    (hlo : a ^ 2 ≤ m ^ 2 * y * t) (hhi : m ^ 2 * y * t ≤ b ^ 2) (hb : 0 ≤ b) (hs : 0 ≤ s)
    (hs2 : s ^ 2 ≤ 1 - b ^ 2) (hshi : 0 ≤ shi) (hshi2 : 1 - a ^ 2 ≤ shi ^ 2)
    (hu : shi ≤ u * a) (hat : arctan u ≤ A) (hG : A - a * s ≤ G) :
    arccos (m * √(y * t)) - m * √(y * t) * √(1 - m ^ 2 * y * t) ≤ G := by
  have h := term_le (p := y * t) hm (mul_nonneg hy ht) ha (by rw [← mul_assoc]; exact hlo)
    (by rw [← mul_assoc]; exact hhi) hb hs hs2 hshi hshi2 hu hat hG
  rwa [← mul_assoc] at h

@[simp] theorem cyq_0 : cy 0 = 1 / 2 := rfl
@[simp] theorem cyq_1 : cy 1 = 1 / 5 := rfl
@[simp] theorem cyq_2 : cy 2 = 19 / 200 := rfl
@[simp] theorem cyq_3 : cy 3 = 11 / 200 := rfl
@[simp] theorem cyq_4 : cy 4 = 7 / 200 := rfl
@[simp] theorem cyq_5 : cy 5 = 23 / 1000 := rfl
@[simp] theorem cwq_0 : cw 0 = 1 / 25 := rfl
@[simp] theorem cwq_1 : cw 1 = 2 / 25 := rfl
@[simp] theorem cwq_2 : cw 2 = 7 / 50 := rfl
@[simp] theorem cwq_3 : cw 3 = 17 / 100 := rfl
@[simp] theorem cwq_4 : cw 4 = 6 / 25 := rfl
@[simp] theorem cwq_5 : cw 5 = 33 / 100 := rfl

theorem cy_0 : ((cy 0 : ℚ) : ℝ) = (1 / 2 : ℝ) := by norm_num
theorem cy_1 : ((cy 1 : ℚ) : ℝ) = (1 / 5 : ℝ) := by norm_num
theorem cy_2 : ((cy 2 : ℚ) : ℝ) = (19 / 200 : ℝ) := by norm_num
theorem cy_3 : ((cy 3 : ℚ) : ℝ) = (11 / 200 : ℝ) := by norm_num
theorem cy_4 : ((cy 4 : ℚ) : ℝ) = (7 / 200 : ℝ) := by norm_num
theorem cy_5 : ((cy 5 : ℚ) : ℝ) = (23 / 1000 : ℝ) := by norm_num

/-- Upper bound for `arctan u` by two half-angle reductions and an odd Taylor sum. -/
theorem atan_up_direct {u q1 r1 q2 r2 : ℝ} (n : ℕ) (hu : 0 ≤ u) (hq1 : 0 ≤ q1)
    (hq1s : q1 ^ 2 ≤ 1 + u ^ 2) (hr1 : u ≤ r1 * (1 + q1)) (hr10 : 0 ≤ r1) (hq2 : 0 ≤ q2)
    (hq2s : q2 ^ 2 ≤ 1 + r1 ^ 2) (hr2 : r1 ≤ r2 * (1 + q2)) (hr20 : 0 ≤ r2) :
    arctan u ≤ 4 * atanPoly (2 * n + 1) r2 := by
  have h1 := arctan_le_two_arctan hu hq1 hq1s hr1
  have h2 := arctan_le_two_arctan hr10 hq2 hq2s hr2
  have h3 := arctan_le_atanPoly hr20 n
  linarith

/-- Upper bound for `arctan u`, `u > 1`, through `π/2 - arctan(1/u)` and an even Taylor sum. -/
theorem atan_up_inv {u v q1 r1 q2 r2 : ℝ} (n : ℕ) (hu : 0 < u) (hv : v * u ≤ 1) (hq1 : 0 ≤ q1)
    (hq1s : 1 + v ^ 2 ≤ q1 ^ 2) (hr10 : 0 ≤ r1) (hr1 : r1 * (1 + q1) ≤ v) (hq2 : 0 ≤ q2)
    (hq2s : 1 + r1 ^ 2 ≤ q2 ^ 2) (hr20 : 0 ≤ r2) (hr2 : r2 * (1 + q2) ≤ r1) :
    arctan u ≤ 3.14159265358979323847 / 2 - 4 * atanPoly (2 * n + 2) r2 := by
  have hv' : v ≤ u⁻¹ := by
    have e : v * u * u⁻¹ = v := by field_simp
    have := mul_le_mul_of_nonneg_right hv (inv_pos.mpr hu).le
    linarith
  have h0 := arctan_le_of_inv hu hv'
  have h1 := two_arctan_le_arctan hq1 hq1s hr10 hr1
  have h2 := two_arctan_le_arctan hq2 hq2s hr20 hr2
  have h3 := atanPoly_le_arctan hr20 n
  have hpi := Real.pi_lt_d20
  linarith

end Zeta7Cert
