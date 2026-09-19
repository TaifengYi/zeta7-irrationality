import Zeta7Proof.GermRationalCalculus

/-! Local coefficient calculus. Bounds include the zero series. -/
noncomputable section
set_option autoImplicit false
open scoped LaurentSeries RatFunc
open HahnSeries
namespace Zeta7Germ

def ordinaryD (f : ℂ⸨X⸩) : ℂ⸨X⸩ := single (-1 : ℤ) 1 * laurentD f

@[simp] theorem ordinaryD_coeff (f : ℂ⸨X⸩) (n : ℤ) :
    (ordinaryD f).coeff n = ((n + 1 : ℤ) : ℂ) * f.coeff (n + 1) := by
  simp [ordinaryD, Derivation.smul_apply, smul_eq_mul, coeff_single_mul,
    laurentD, sub_neg_eq_add]

theorem ordinaryD_eq_mathlib (f : ℂ⸨X⸩) : ordinaryD f = LaurentSeries.derivative ℂ f := by
  ext n
  simp [ordinaryD_coeff, LaurentSeries.derivative, zsmul_eq_mul]

def lowerBound (f : ℂ⸨X⸩) (n : ℤ) : Prop := ∀ k : ℤ, k < n → f.coeff k = 0

theorem lowerBound_euler {f : ℂ⸨X⸩} {n : ℤ} (h : lowerBound f n) :
    lowerBound (laurentD f) n := by
  intro k hk
  change (k : ℂ) * f.coeff k = 0
  rw [h k hk, mul_zero]

theorem lowerBound_ordinary {f : ℂ⸨X⸩} {n : ℤ} (h : lowerBound f n) :
    lowerBound (ordinaryD f) (n - 1) := by
  intro k hk
  rw [ordinaryD_coeff, h (k + 1) (by omega), mul_zero]

theorem ordinaryD_leading (f : ℂ⸨X⸩) (n : ℤ) :
    (ordinaryD f).coeff (n - 1) = (n : ℂ) * f.coeff n := by
  simp [ordinaryD_coeff]

theorem ordinaryD_two_leading (f : ℂ⸨X⸩) (n : ℤ) :
    (ordinaryD (ordinaryD f)).coeff (n - 2) =
      (n : ℂ) * ((n : ℂ) - 1) * f.coeff n := by
  simp only [ordinaryD_coeff]
  have hn : n - 2 + 1 + 1 = n := by omega
  rw [hn]
  push_cast
  ring

theorem ordinaryD_three_leading (f : ℂ⸨X⸩) (n : ℤ) :
    (ordinaryD (ordinaryD (ordinaryD f))).coeff (n - 3) =
      (n : ℂ) * ((n : ℂ) - 1) * ((n : ℂ) - 2) * f.coeff n := by
  simp only [ordinaryD_coeff]
  have hn : n - 3 + 1 + 1 + 1 = n := by omega
  rw [hn]
  push_cast
  ring

theorem lowerBound_mul {f g : ℂ⸨X⸩} {n m : ℤ}
    (hf : lowerBound f n) (hg : lowerBound g m) : lowerBound (f * g) (n + m) := by
  classical
  intro k hk
  rw [coeff_mul]
  apply Finset.sum_eq_zero
  intro ij hij
  have he : ij.1 + ij.2 = k := (Finset.mem_antidiagonal.mp hij).2.2
  by_cases hi : ij.1 < n
  · rw [hf _ hi, zero_mul]
  · rw [hg _ (by omega), mul_zero]

theorem laurentD_eq_zero_iff (f : ℂ⸨X⸩) :
    laurentD f = 0 ↔ ∃ a : ℂ, f = HahnSeries.C a := by
  constructor
  · intro h
    refine ⟨f.coeff 0, ?_⟩
    ext n
    by_cases hn : n = 0
    · simp [hn, HahnSeries.C_apply]
    · have hc := congrArg (fun g : ℂ⸨X⸩ => g.coeff n) h
      change (n : ℂ) * f.coeff n = 0 at hc
      have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
      have hz := (mul_eq_zero.mp hc).resolve_left hn'
      simp [HahnSeries.C_apply, hn, hz]
  · rintro ⟨a, rfl⟩
    exact laurentEuler_C a

theorem rationalD_eq_zero_iff (f : RatFunc ℂ) :
    rationalD f = 0 ↔ ∃ a : ℂ, f = RatFunc.C a := by
  constructor
  · intro h
    have he : laurentD (embed f) = 0 := by rw [← embed_rationalD, h, map_zero]
    obtain ⟨a, ha⟩ := (laurentD_eq_zero_iff _).mp he
    refine ⟨a, embed_injective ?_⟩
    rw [embed_C]
    exact ha
  · rintro ⟨a, rfl⟩
    rw [← RatFunc.algebraMap_C]
    exact rationalD.map_algebraMap a

end Zeta7Germ
