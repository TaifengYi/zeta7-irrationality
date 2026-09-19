import Zeta7Proof.GermLocalExpansion
import Zeta7Proof.GermIndicialAlgebra

/-! Coefficient-level pole obstruction, before specializing the rational local data. -/
noncomputable section
set_option autoImplicit false
open scoped LaurentSeries RatFunc
open HahnSeries
namespace Zeta7Germ

theorem lowerBound_mul_leading {f g : ℂ⸨X⸩} {n m : ℤ}
    (hf : lowerBound f n) (hg : lowerBound g m) :
    (f * g).coeff (n + m) = f.coeff n * g.coeff m := by
  classical
  rw [coeff_mul]
  apply Finset.sum_eq_single (n, m)
  · intro ij hij hne
    have he : ij.1 + ij.2 = n + m := (Finset.mem_antidiagonal.mp hij).2.2
    by_cases hi : ij.1 < n
    · rw [hf _ hi, zero_mul]
    · have hj : ij.2 < m := by
        by_contra hj
        have h1 : ij.1 = n := by omega
        have h2 : ij.2 = m := by omega
        exact hne (Prod.ext h1 h2)
      rw [hg _ hj, mul_zero]
  · intro hnot
    by_cases hfn : f.coeff n = 0
    · simp [hfn]
    · have hgm : g.coeff m = 0 := by
        by_contra hgm
        apply hnot
        simp [Finset.mem_antidiagonal, mem_support, hfn, hgm]
      simp [hgm]

def localL (a : ℂ) (v f : ℂ⸨X⸩) : ℂ⸨X⸩ :=
  localD a (localD a (localD a f)) - v * localD a f - localD a v * f / 2

theorem localL_root_leading (a : ℂ) {v f : ℂ⸨X⸩} {n : ℤ}
    (hf : lowerBound f n) (hv : lowerBound v (-2))
    (hvlead : v.coeff (-2) = -8 * a ^ 2 / 9) :
    (localL a v f).coeff (n - 3) = a ^ 3 * indicial (n : ℂ) * f.coeff n := by
  have h1 := lowerBound_mul_leading hv (lowerBound_localD a hf)
  have h2 := lowerBound_mul_leading (lowerBound_localD a hv) hf
  have hi1 : (-2 : ℤ) + (n - 1) = n - 3 := by omega
  have hi2 : ((-2 : ℤ) - 1) + n = n - 3 := by omega
  rw [hi1, localD_leading a hf, hvlead] at h1
  rw [hi2, localD_leading a hv, hvlead] at h2
  have hhalf : (2 : ℂ⸨X⸩)⁻¹ = HahnSeries.C (1 / 2 : ℂ) := by
    rw [map_div₀, map_one, map_ofNat, one_div]
  simp only [localL, coeff_sub, div_eq_mul_inv, hhalf, HahnSeries.C_apply,
    coeff_mul_single_zero, h1, h2, localD_three_leading a hf]
  dsimp [indicial]
  norm_num
  ring

theorem localL_root_pole_excluded (a : ℂ) (ha : a ≠ 0)
    {v f g : ℂ⸨X⸩} {n : ℤ} (hn : n < 0)
    (hf : lowerBound f n) (hflead : f.coeff n ≠ 0)
    (hv : lowerBound v (-2)) (hvlead : v.coeff (-2) = -8 * a ^ 2 / 9)
    (hg : lowerBound g (-1)) : localL a v f ≠ g := by
  intro he
  have hc := congrArg (fun z : ℂ⸨X⸩ => z.coeff (n - 3)) he
  rw [localL_root_leading a hf hv hvlead, hg _ (by omega)] at hc
  exact (mul_ne_zero (mul_ne_zero (pow_ne_zero 3 ha) (indicial_negative_integer n hn)) hflead) hc

theorem localL_ordinary_pole_excluded (a : ℂ) (ha : a ≠ 0)
    {v f g : ℂ⸨X⸩} {n : ℤ} (hn : n < 0)
    (hf : lowerBound f n) (hflead : f.coeff n ≠ 0)
    (hv : lowerBound v 0) (hg : lowerBound g 0) : localL a v f ≠ g := by
  intro he
  have h1 : (v * localD a f).coeff (n - 3) = 0 :=
    lowerBound_mul hv (lowerBound_localD a hf) _ (by omega)
  have h2 : (localD a v * f).coeff (n - 3) = 0 :=
    lowerBound_mul (lowerBound_localD a hv) hf _ (by omega)
  have hc := congrArg (fun z : ℂ⸨X⸩ => z.coeff (n - 3)) he
  have hhalf : (2 : ℂ⸨X⸩)⁻¹ = HahnSeries.C (1 / 2 : ℂ) := by
    rw [map_div₀, map_one, map_ofNat, one_div]
  simp only [localL, coeff_sub, div_eq_mul_inv, hhalf, HahnSeries.C_apply,
    coeff_mul_single_zero, h1, h2, zero_mul, sub_zero,
    localD_three_leading a hf] at hc
  rw [hg (n - 3) (by omega)] at hc
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hn1 : (n : ℂ) - 1 ≠ 0 := by
    have hh : ((n - 1 : ℤ) : ℂ) ≠ 0 := by exact_mod_cast (show n - 1 ≠ 0 by omega)
    simpa using hh
  have hn2 : (n : ℂ) - 2 ≠ 0 := by
    have hh : ((n - 2 : ℤ) : ℂ) ≠ 0 := by exact_mod_cast (show n - 2 ≠ 0 by omega)
    simpa using hh
  exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero 3 ha)
    hn0) hn1) hn2) hflead) hc

theorem localD_zero (f : ℂ⸨X⸩) : localD 0 f = laurentD f := by
  ext n
  simp [localD_coeff, laurentD]

theorem localL_zero_pole_excluded {v f g : ℂ⸨X⸩} {n : ℤ} (hn : n < 0)
    (hf : lowerBound f n) (hflead : f.coeff n ≠ 0)
    (hv : lowerBound v 1) (hg : lowerBound g 1) : localL 0 v f ≠ g := by
  intro he
  have h1 : (v * laurentD f).coeff n = 0 :=
    lowerBound_mul hv (lowerBound_euler hf) _ (by omega)
  have h2 : (laurentD v * f).coeff n = 0 :=
    lowerBound_mul (lowerBound_euler hv) hf _ (by omega)
  have hc := congrArg (fun z : ℂ⸨X⸩ => z.coeff n) he
  have hhalf : (2 : ℂ⸨X⸩)⁻¹ = HahnSeries.C (1 / 2 : ℂ) := by
    rw [map_div₀, map_one, map_ofNat, one_div]
  simp only [localL, localD_zero, coeff_sub, div_eq_mul_inv, hhalf,
    HahnSeries.C_apply, coeff_mul_single_zero, h1, h2, zero_mul, sub_zero,
    ] at hc
  rw [hg n (by omega)] at hc
  change (n : ℂ) * ((n : ℂ) * ((n : ℂ) * f.coeff n)) = 0 at hc
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  exact (mul_ne_zero hn0 (mul_ne_zero hn0 (mul_ne_zero hn0 hflead))) hc

end Zeta7Germ
