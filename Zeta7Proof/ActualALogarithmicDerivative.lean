import Zeta7Proof.ModularDifferentialTransport

/-! Differentiating the original convergent formal Euler product.
This identifies the actual A, without changing its definition to a Lambert
series or assuming a differential equation for the coordinate. -/
set_option autoImplicit false
noncomputable section
open PowerSeries Filter Topology
open scoped PowerSeries.WithPiTopology
namespace Zeta7Common
open Zeta7Main

theorem euler_tendsto {ι : Type*} {l : Filter ι} {f : ι → ℚ⟦X⟧} {g : ℚ⟦X⟧}
    (h : Tendsto f l (𝓝 g)) : Tendsto (fun i => euler (f i)) l (𝓝 (euler g)) := by
  rw [WithPiTopology.tendsto_iff_coeff_tendsto] at h ⊢
  intro n
  simpa only [euler_coeff] using (h n).const_mul (n : ℚ)

theorem euler_finset_prod {ι : Type*} (f g : ι → ℚ⟦X⟧)
    (h : ∀ i, euler (f i) = f i * g i) (s : Finset ι) :
    euler (∏ i ∈ s, f i) = (∏ i ∈ s, f i) * ∑ i ∈ s, g i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, euler_mul, h, ih]
    ring

/-- Leibniz's rule passes to coefficientwise convergent products and sums. -/
theorem euler_of_hasProd_hasSum {ι : Type*} (f g : ι → ℚ⟦X⟧) (F G : ℚ⟦X⟧)
    (hf : HasProd f F) (hg : HasSum g G) (h : ∀ i, euler (f i) = f i * g i) :
    euler F = F * G := by
  have hd := euler_tendsto hf
  have hm := Filter.Tendsto.mul hf hg
  exact tendsto_nhds_unique (by simpa only [euler_finset_prod f g h] using hd) hm

def firstLambert (a : ℕ) : ℚ⟦X⟧ := C (a : ℚ) * (X ^ a * (1 - X ^ a)⁻¹)

def sevenSigmaOne (n : ℕ) : ℚ := ∑ a ∈ n.divisors.filter (fun a => ¬ 7 ∣ a), (a : ℚ)
def sevenSigmaOneSeries : ℚ⟦X⟧ := mk sevenSigmaOne

theorem firstLambert_coeff (a n : ℕ) (ha : a ≠ 0) :
    coeff n (firstLambert a) = if n ≠ 0 ∧ a ∣ n then (a : ℚ) else 0 := by
  have hgeom : (X : ℚ⟦X⟧) ^ a * (1 - X ^ a)⁻¹ = (1 - X ^ a)⁻¹ - 1 := by
    have h := PowerSeries.mul_inv_cancel (1 - (X : ℚ⟦X⟧) ^ a) (by simp [ha])
    linear_combination -h
  rw [firstLambert, hgeom, coeff_C_mul, geometric_inverse a ha, map_sub,
    coeff_expand, coeff_mk]
  by_cases hn : n = 0
  · subst n; simp
  · by_cases had : a ∣ n <;> simp [hn, had, coeff_one]

theorem sevenSigmaOne_hasSum :
    HasSum (fun a : ℕ => if ¬ 7 ∣ a then firstLambert a else 0) sevenSigmaOneSeries := by
  classical
  apply (WithPiTopology.hasSum_iff_hasSum_coeff ℚ).mpr
  intro n
  have hfin : HasSum (fun a : ℕ => coeff n (if ¬ 7 ∣ a then firstLambert a else 0))
      (∑ a ∈ n.divisors.filter (fun a => ¬ 7 ∣ a),
        coeff n (if ¬ 7 ∣ a then firstLambert a else 0)) := by
    apply hasSum_sum_of_ne_finset_zero
    intro a ha
    by_cases h7 : 7 ∣ a
    · simp [h7]
    · have ha0 : a ≠ 0 := by intro hz; subst a; exact h7 (dvd_zero 7)
      have hn : ¬ (n ≠ 0 ∧ a ∣ n) := by
        intro h
        exact ha (Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨h.2, h.1⟩, h7⟩)
      simp [h7, firstLambert_coeff a n ha0, hn]
  have he : coeff n sevenSigmaOneSeries =
      ∑ a ∈ n.divisors.filter (fun a => ¬ 7 ∣ a),
        coeff n (if ¬ 7 ∣ a then firstLambert a else 0) := by
    simp only [sevenSigmaOneSeries, coeff_mk, sevenSigmaOne]
    apply Finset.sum_congr rfl
    intro a ha
    obtain ⟨hd, h7⟩ := Finset.mem_filter.mp ha
    obtain ⟨had, hn⟩ := Nat.mem_divisors.mp hd
    rw [if_pos h7, firstLambert_coeff a n (ne_zero_of_dvd_ne_zero hn had), if_pos ⟨hn, had⟩]
  rw [he]
  exact hfin

theorem sevenSigmaOne_hasSum_index :
    HasSum (fun a : SevenProductIndex => firstLambert (a.val + 1)) sevenSigmaOneSeries := by
  have h : HasSum (fun a : ℕ => if ¬ 7 ∣ a + 1 then firstLambert (a + 1) else 0)
      sevenSigmaOneSeries := by
    have ht := (hasSum_nat_add_iff' 1).mpr sevenSigmaOne_hasSum
    simpa using ht
  apply (hasSum_subtype_iff_indicator
    (f := fun n : ℕ => firstLambert (n + 1))
    (s := {n : ℕ | ¬ 7 ∣ n + 1})).mpr
  apply h.congr_fun
  intro n
  by_cases hd : 7 ∣ n + 1 <;> simp [Set.indicator, hd]

theorem euler_X_pow (a : ℕ) : euler (X ^ a : ℚ⟦X⟧) = C (a : ℚ) * X ^ a := by
  ext n
  simp only [euler_coeff, coeff_C_mul, coeff_X_pow]
  split_ifs with h <;> simp_all

theorem euler_seven_factor (a : SevenProductIndex) :
    euler (1 - X ^ (a.val + 1) : ℚ⟦X⟧) =
      (1 - X ^ (a.val + 1)) * (-firstLambert (a.val + 1)) := by
  rw [euler_sub, euler_one, euler_X_pow, zero_sub, firstLambert]
  have hu := PowerSeries.mul_inv_cancel (1 - (X : ℚ⟦X⟧) ^ (a.val + 1)) (by simp)
  linear_combination C ((a.val + 1 : ℕ) : ℚ) * X ^ (a.val + 1) * hu

/-- The logarithmic derivative of the actual product, with no division. -/
theorem sevenEulerProduct_euler :
    euler sevenEulerProduct = -sevenEulerProduct * sevenSigmaOneSeries := by
  have h := euler_of_hasProd_hasSum
    (fun a : SevenProductIndex => (1 : ℚ⟦X⟧) - X ^ (a.val + 1))
    (fun a => -firstLambert (a.val + 1)) sevenEulerProduct (-sevenSigmaOneSeries)
    seven_product_multipliable.hasProd sevenSigmaOne_hasSum_index.neg euler_seven_factor
  simpa using h

end Zeta7Common
