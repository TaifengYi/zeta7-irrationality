import Zeta7Proof.Radius49Bootstrap
import Mathlib.RingTheory.PowerSeries.Inverse

/-! Radius internalization, HM: ultrametric coefficient bounds for `ℚ₇`-power series.

* `Bnd ρ f B : ∀ i, ‖fᵢ‖ ρⁱ ≤ B`, with the ultrametric closure lemmas (`Bnd.add`, `Bnd.mul`, …).
* `bddSubring ρ`: series with some bound at radius `ρ` form a subring.
* `Bnd_of_mul_dominant`: if `D F = G`, `‖D₀‖ = 1` and `‖D_l‖ ρ^l ≤ 1`, then `F` inherits the
  bound of `G` (a dominant constant term makes `D` invertible with norm `1`).
* `expo_le`: the exponent inequality behind the improvement map `improve`. -/

noncomputable section
set_option autoImplicit false
open PowerSeries
namespace Zeta7Radius49
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

/-- Coefficient bound at radius `ρ`. -/
def Bnd (ρ : ℝ) (f : ℚ_[7]⟦X⟧) (B : ℝ) : Prop := ∀ i, ‖coeff i f‖ * ρ ^ i ≤ B

variable {ρ : ℝ}

theorem Bnd.nonneg {f : ℚ_[7]⟦X⟧} {B : ℝ} (h : Bnd ρ f B) : 0 ≤ B :=
  (by simp : 0 ≤ ‖coeff 0 f‖ * ρ ^ 0).trans (h 0)

theorem Bnd.mono {f : ℚ_[7]⟦X⟧} {B B' : ℝ} (h : Bnd ρ f B) (hB : B ≤ B') : Bnd ρ f B' :=
  fun i => (h i).trans hB

theorem Bnd.add (hρ : 0 ≤ ρ) {f g : ℚ_[7]⟦X⟧} {B : ℝ} (hf : Bnd ρ f B) (hg : Bnd ρ g B) :
    Bnd ρ (f + g) B := by
  intro i
  rw [map_add]
  calc ‖coeff i f + coeff i g‖ * ρ ^ i ≤ max ‖coeff i f‖ ‖coeff i g‖ * ρ ^ i :=
        mul_le_mul_of_nonneg_right (IsUltrametricDist.norm_add_le_max _ _) (pow_nonneg hρ i)
    _ = max (‖coeff i f‖ * ρ ^ i) (‖coeff i g‖ * ρ ^ i) :=
        max_mul_of_nonneg _ _ (pow_nonneg hρ i)
    _ ≤ B := max_le (hf i) (hg i)

theorem Bnd.neg {f : ℚ_[7]⟦X⟧} {B : ℝ} (hf : Bnd ρ f B) : Bnd ρ (-f) B := by
  intro i; rw [map_neg, norm_neg]; exact hf i

theorem Bnd.sub (hρ : 0 ≤ ρ) {f g : ℚ_[7]⟦X⟧} {B : ℝ} (hf : Bnd ρ f B) (hg : Bnd ρ g B) :
    Bnd ρ (f - g) B := by
  rw [sub_eq_add_neg]; exact hf.add hρ hg.neg

theorem Bnd.mul (hρ : 0 < ρ) {f g : ℚ_[7]⟦X⟧} {B C : ℝ} (hf : Bnd ρ f B) (hg : Bnd ρ g C) :
    Bnd ρ (f * g) (B * C) := by
  intro n
  have hpos : 0 < ρ ^ n := pow_pos hρ n
  have hB := hf.nonneg
  have hC := hg.nonneg
  rw [coeff_mul, ← le_div_iff₀ hpos]
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
  intro p hp
  have hp' := Finset.mem_antidiagonal.mp hp
  rw [le_div_iff₀ hpos, norm_mul, ← hp', pow_add]
  calc ‖coeff p.1 f‖ * ‖coeff p.2 g‖ * (ρ ^ p.1 * ρ ^ p.2) =
      (‖coeff p.1 f‖ * ρ ^ p.1) * (‖coeff p.2 g‖ * ρ ^ p.2) := by ring
    _ ≤ B * C := mul_le_mul (hf _) (hg _) (by positivity) hB

theorem Bnd.sum (hρ : 0 ≤ ρ) {s : Finset ℕ} {f : ℕ → ℚ_[7]⟦X⟧} {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ j ∈ s, Bnd ρ (f j) B) : Bnd ρ (∑ j ∈ s, f j) B := by
  induction s using Finset.induction_on with
  | empty => intro i; simp [hB]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add hρ
      (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

theorem Bnd_C_mul_X_pow (hρ : 0 ≤ ρ) (c : ℚ_[7]) (j : ℕ) :
    Bnd ρ (C c * X ^ j) (‖c‖ * ρ ^ j) := by
  intro i
  rw [coeff_C_mul_X_pow]
  split_ifs with h
  · rw [h]
  · simp only [norm_zero, zero_mul]; positivity

theorem Bnd_zero (hρ : 0 ≤ ρ) : Bnd ρ 0 0 := by intro i; simp

theorem Bnd_one : Bnd ρ 1 1 := by
  intro i
  rw [coeff_one]
  split_ifs with h
  · subst h; simp
  · simp

theorem Bnd_X (hρ : 0 ≤ ρ) : Bnd ρ X ρ := by
  have := Bnd_C_mul_X_pow hρ 1 1
  simpa using this

/-- Series with some bound at radius `ρ > 0`. -/
def bddSubring (ρ : ℝ) (hρ : 0 < ρ) : Subring ℚ_[7]⟦X⟧ where
  carrier := {f | ∃ B, Bnd ρ f B}
  add_mem' := by
    rintro f g ⟨B, hB⟩ ⟨C, hC⟩
    exact ⟨max B C, (hB.mono (le_max_left _ _)).add hρ.le (hC.mono (le_max_right _ _))⟩
  mul_mem' := by
    rintro f g ⟨B, hB⟩ ⟨C, hC⟩
    exact ⟨B * C, hB.mul hρ hC⟩
  zero_mem' := ⟨0, Bnd_zero hρ.le⟩
  one_mem' := ⟨1, Bnd_one⟩
  neg_mem' := by
    rintro f ⟨B, hB⟩
    exact ⟨B, hB.neg⟩

theorem X_mem_bddSubring (hρ : 0 < ρ) : (X : ℚ_[7]⟦X⟧) ∈ bddSubring ρ hρ := ⟨ρ, Bnd_X hρ.le⟩

/-- **Dominant constant term.** -/
theorem Bnd_of_mul_dominant (hρ : 0 < ρ) {D F G : ℚ_[7]⟦X⟧} {B : ℝ}
    (hD0 : ‖coeff 0 D‖ = 1) (hD : ∀ l, 1 ≤ l → ‖coeff l D‖ * ρ ^ l ≤ 1)
    (hG : Bnd ρ G B) (hDF : D * F = G) : Bnd ρ F B := by
  have hB := hG.nonneg
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    have hc := congrArg (coeff i) hDF
    rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ',
      Nat.sub_zero] at hc
    -- `D₀ Fᵢ = Gᵢ - Σ_{l ≥ 1} D_l F_{i-l}`
    have hsplit : coeff 0 D * coeff i F = coeff i G -
        ∑ l ∈ Finset.range i, coeff (l + 1) D * coeff (i - (l + 1)) F := by
      rw [← hc]; ring
    have hpos : 0 < ρ ^ i := pow_pos hρ i
    have hF : ‖coeff i F‖ = ‖coeff 0 D * coeff i F‖ := by rw [norm_mul, hD0, one_mul]
    rw [hF, hsplit]
    have hsum : ‖∑ l ∈ Finset.range i, coeff (l + 1) D * coeff (i - (l + 1)) F‖ * ρ ^ i ≤ B := by
      rw [← le_div_iff₀ hpos]
      apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
      intro l hl
      have hl' := Finset.mem_range.mp hl
      rw [le_div_iff₀ hpos, norm_mul]
      have hsplit' : ρ ^ i = ρ ^ (l + 1) * ρ ^ (i - (l + 1)) := by
        rw [← pow_add]; congr 1; omega
      rw [hsplit']
      calc ‖coeff (l + 1) D‖ * ‖coeff (i - (l + 1)) F‖ * (ρ ^ (l + 1) * ρ ^ (i - (l + 1))) =
          (‖coeff (l + 1) D‖ * ρ ^ (l + 1)) * (‖coeff (i - (l + 1)) F‖ * ρ ^ (i - (l + 1))) := by
            ring
        _ ≤ 1 * B := mul_le_mul (hD _ (by omega)) (ih _ (by omega)) (by positivity) zero_le_one
        _ = B := one_mul B
    calc ‖coeff i G - ∑ l ∈ Finset.range i, coeff (l + 1) D * coeff (i - (l + 1)) F‖ * ρ ^ i
        ≤ max ‖coeff i G‖ ‖∑ l ∈ Finset.range i, coeff (l + 1) D * coeff (i - (l + 1)) F‖ *
            ρ ^ i :=
          mul_le_mul_of_nonneg_right (by
            rw [sub_eq_add_neg]
            exact (IsUltrametricDist.norm_add_le_max _ _).trans (by rw [norm_neg])) hpos.le
      _ = max (‖coeff i G‖ * ρ ^ i)
          (‖∑ l ∈ Finset.range i, coeff (l + 1) D * coeff (i - (l + 1)) F‖ * ρ ^ i) :=
          max_mul_of_nonneg _ _ hpos.le
      _ ≤ B := max_le (hG i) hsum

/-- Dividing by `c X` with `‖c‖ = 7^{-2}`: `c X G = Q` gives `Bnd G (49 B / ρ)`. -/
theorem Bnd_of_X_mul (hρ : 0 < ρ) {c : ℚ_[7]} (hc : ‖c‖ = (49 : ℝ)⁻¹) {G Q : ℚ_[7]⟦X⟧} {B : ℝ}
    (hQ : Bnd ρ Q B) (h : C c * X * G = Q) : Bnd ρ G (49 * B / ρ) := by
  intro i
  have hq := congrArg (coeff (i + 1)) h
  rw [mul_comm (C c) X, mul_assoc, coeff_succ_X_mul, coeff_C_mul] at hq
  have hb := hQ (i + 1)
  rw [← hq, norm_mul, hc, pow_succ] at hb
  rw [le_div_iff₀ hρ]
  nlinarith [norm_nonneg (coeff i G), pow_nonneg hρ.le i]

/-! ### The exponent inequality -/

theorem improve_small {s : ℝ} (hs : s ≤ 1 / 4) : improve s = 7 * s := by
  unfold improve; exact min_eq_left (by linarith)

theorem improve_large' {s : ℝ} (hs : 1 / 4 ≤ s) : improve s = (12 + s) / 7 := by
  unfold improve; exact min_eq_right (by linarith)

/-- `-v + improve(s)·j ≤ s·k` whenever `4v ≥ 7j - k`, `k ≤ 7j`, `j ≤ 7k`. -/
theorem expo_linear {s : ℝ} (hs0 : 0 < s) (v j k : ℕ) (h1 : 7 * j ≤ 4 * v + k)
    (h2 : k ≤ 7 * j) (h3 : j ≤ 7 * k) : -(v : ℝ) + improve s * j ≤ s * k := by
  have h1' : (7 : ℝ) * j ≤ 4 * v + k := by exact_mod_cast h1
  have h2' : (k : ℝ) ≤ 7 * j := by exact_mod_cast h2
  have h3' : (j : ℝ) ≤ 7 * k := by exact_mod_cast h3
  rcases le_total s (1 / 4) with hs | hs
  · rw [improve_small hs]
    nlinarith
  · rw [improve_large' hs]
    nlinarith

theorem expo_le {s : ℝ} (hs0 : 0 < s) (v j k : ℕ) (h1 : 7 * j ≤ 4 * v + k)
    (h2 : k ≤ 7 * j) (h3 : j ≤ 7 * k) :
    (7 : ℝ) ^ (-(v : ℤ)) * ((7 : ℝ) ^ improve s) ^ j ≤ ((7 : ℝ) ^ s) ^ k := by
  have h7 : (1 : ℝ) < 7 := by norm_num
  rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
    ← Real.rpow_mul (by norm_num), ← Real.rpow_intCast, ← Real.rpow_add (by norm_num)]
  apply Real.rpow_le_rpow_of_exponent_le h7.le
  have := expo_linear hs0 v j k h1 h2 h3
  push_cast
  linarith

/-- The norm of an integer divisible by `7^v`. -/
theorem norm_int_le_of_dvd (c : ℤ) (v : ℕ) (h : (7 : ℤ) ^ v ∣ c) :
    ‖(c : ℚ_[7])‖ ≤ (7 : ℝ) ^ (-(v : ℤ)) := by
  have := (Padic.norm_int_le_pow_iff_dvd (p := 7) c v).mpr (by exact_mod_cast h)
  simpa using this

end Zeta7Radius49
