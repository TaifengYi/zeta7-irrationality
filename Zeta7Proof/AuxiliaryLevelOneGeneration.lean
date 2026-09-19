import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing
import Mathlib

/-! Weighted generation by E4 and E6, proved using the discriminant equivalence.
This supplies the general-weight input; no finite coefficient comparison is used. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
namespace Zeta7Auxiliary
open UpperHalfPlane ModularForm MatrixGroups EisensteinSeries
open scoped ModularForm

def weightedMonomial {n : ℕ} (a b : ℕ) (h : 2 * a + 3 * b = n) :
    ModularForm 𝒮ℒ (2 * (n : ℤ)) :=
  ModularForm.mcast (by exact_mod_cast (by omega : a * 4 + b * 6 = 2 * n))
    ((E₄.pow a).mul (E₆.pow b))

theorem weightedMonomial_apply {n : ℕ} (a b : ℕ) (h : 2 * a + 3 * b = n) (z : ℍ) :
    weightedMonomial a b h z = E₄ z ^ a * E₆ z ^ b := by
  simp [weightedMonomial, ModularForm.coe_pow]

def weightedSpan (n : ℕ) : Submodule ℂ (ModularForm 𝒮ℒ (2 * (n : ℤ))) :=
  Submodule.span ℂ {f | ∃ a b, ∃ h : 2 * a + 3 * b = n, f = weightedMonomial a b h}

theorem weightedMonomial_mem {n : ℕ} (a b : ℕ) (h : 2 * a + 3 * b = n) :
    weightedMonomial a b h ∈ weightedSpan n :=
  Submodule.subset_span ⟨a, b, h, rfl⟩

def multiplyDiscriminant (n : ℕ) :
    ModularForm 𝒮ℒ (2 * (n : ℤ)) →ₗ[ℂ] ModularForm 𝒮ℒ (2 * ((n + 6 : ℕ) : ℤ)) where
  toFun f := ModularForm.mcast (by push_cast; ring)
    ((CuspForm.discriminant : ModularForm 𝒮ℒ 12).mul f)
  map_add' f g := by ext z; simp [mul_add]
  map_smul' c f := by ext z; simp [mul_left_comm]

theorem multiplyDiscriminant_apply (n : ℕ) (f : ModularForm 𝒮ℒ (2 * (n : ℤ))) (z : ℍ) :
    multiplyDiscriminant n f z = ModularForm.discriminant z * f z := rfl

theorem multiplyDiscriminant_monomial {n : ℕ} (a b : ℕ) (h : 2 * a + 3 * b = n) :
    multiplyDiscriminant n (weightedMonomial a b h) = (1 / 1728 : ℂ) •
      (weightedMonomial (a + 3) b (by omega) - weightedMonomial a (b + 2) (by omega)) := by
  ext z
  simp only [multiplyDiscriminant_apply, weightedMonomial_apply,
    ModularForm.smul_apply, ModularForm.sub_apply, smul_eq_mul]
  rw [ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq]
  simp only [pow_add]
  ring

theorem multiplyDiscriminant_mem {n : ℕ} {f : ModularForm 𝒮ℒ (2 * (n : ℤ))}
    (hf : f ∈ weightedSpan n) : multiplyDiscriminant n f ∈ weightedSpan (n + 6) := by
  change f ∈ Submodule.span ℂ _ at hf
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨a, b, h, rfl⟩ := hf
    rw [multiplyDiscriminant_monomial]
    exact Submodule.smul_mem _ _ (Submodule.sub_mem _
      (weightedMonomial_mem _ _ _) (weightedMonomial_mem _ _ _))
  | zero => rw [map_zero]; exact (weightedSpan (n + 6)).zero_mem
  | add f g _ _ hf hg => rw [map_add]; exact (weightedSpan (n + 6)).add_mem hf hg
  | smul c f _ hf => rw [map_smul]; exact (weightedSpan (n + 6)).smul_mem c hf

theorem weightedMonomial_qExpansion_zero {n : ℕ} (a b : ℕ) (h : 2 * a + 3 * b = n) :
    (qExpansion 1 (weightedMonomial a b h)).coeff 0 = 1 := by
  simp only [weightedMonomial, ModularForm.qExpansion_mcast,
    ModularForm.qExpansion_mul one_pos one_mem_strictPeriods_SL,
    ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL]
  rw [PowerSeries.coeff_zero_eq_constantCoeff]
  simp only [map_mul, map_pow, ← PowerSeries.coeff_zero_eq_constantCoeff,
    E₄, E₆, E_qExpansion_coeff_zero _ (by decide : Even 4),
    E_qExpansion_coeff_zero _ (by decide : Even 6), one_pow, mul_one]

theorem two_three_representation (n : ℕ) (hn : 2 ≤ n) :
    ∃ a b : ℕ, 2 * a + 3 * b = n := by
  by_cases he : n % 2 = 0
  · exact ⟨n / 2, 0, by omega⟩
  · exact ⟨(n - 3) / 2, 1, by omega⟩

theorem weightedSpan_mcast {n m : ℕ} (h : n = m)
    (f : ModularForm 𝒮ℒ (2 * (n : ℤ))) (hf : f ∈ weightedSpan n) :
    ModularForm.mcast (congrArg (fun k : ℕ => 2 * (k : ℤ)) h) f ∈ weightedSpan m := by
  subst m
  exact hf

/-- Every level-one modular form is in the span of monomials of its exact weight. -/
theorem levelOne_mem_weightedSpan (n : ℕ) (f : ModularForm 𝒮ℒ (2 * (n : ℤ))) :
    f ∈ weightedSpan n := by
  induction n using Nat.strong_induction_on with | h n ih =>
  by_cases hn0 : n = 0
  · subst n
    let f0 : ModularForm 𝒮ℒ 0 := ModularForm.mcast (by norm_num) f
    obtain ⟨c, hc⟩ := ModularFormClass.levelOne_weight_zero_const f0
    have he : f = c • weightedMonomial 0 0 (by omega) := by
      ext z
      have hz := congrFun hc z
      simpa only [f0, ModularForm.mcast_apply, weightedMonomial_apply,
        pow_zero, mul_one, ModularForm.smul_apply, smul_eq_mul, Function.const_apply] using hz
    rw [he]
    exact (weightedSpan 0).smul_mem c (weightedMonomial_mem _ _ _)
  by_cases hn1 : n = 1
  · subst n
    let f1 : ModularForm 𝒮ℒ 2 := ModularForm.mcast (by norm_num) f
    have hz := rank_zero_iff_forall_zero.mp ModularForm.levelOne_weight_two_rank_zero f1
    have he : f = 0 := by ext z; exact congrArg (fun g : ModularForm 𝒮ℒ 2 => g z) hz
    rw [he]
    exact (weightedSpan 1).zero_mem
  obtain ⟨a, b, hab⟩ := two_three_representation n (by omega)
  let m := weightedMonomial a b hab
  let c := (qExpansion 1 f).coeff 0
  let g := f - c • m
  have hg : (qExpansion 1 g).coeff 0 = 0 := by
    exact (ModularForm.isCuspForm_iff_coeffZero_eq_zero g).mp
      (ModularForm.sub_smul_isCuspForm f m (weightedMonomial_qExpansion_zero a b hab))
  let s := ModularForm.toCuspForm g hg
  have hcm : c • m ∈ weightedSpan n :=
    (weightedSpan n).smul_mem c (weightedMonomial_mem a b hab)
  suffices hgmem : g ∈ weightedSpan n by
    have hsum := (weightedSpan n).add_mem hgmem hcm
    simpa only [g, sub_add_cancel] using hsum
  by_cases hn6 : n < 6
  · have hs0 : s = 0 := rank_zero_iff_forall_zero.mp
      (CuspForm.rank_eq_zero_of_weight_lt_twelve (by omega)) s
    have hg0 : g = 0 := by
      ext z
      exact congrArg (fun t : CuspForm 𝒮ℒ (2 * (n : ℤ)) => t z) hs0
    rw [hg0]
    exact (weightedSpan n).zero_mem
  · let t := CuspForm.discriminantEquiv s
    let t' : ModularForm 𝒮ℒ (2 * ((n - 6 : ℕ) : ℤ)) := ModularForm.mcast (by omega) t
    have ht := multiplyDiscriminant_mem (ih (n - 6) (by omega) t')
    have hn : n - 6 + 6 = n := by omega
    have hrepr : g = ModularForm.mcast (congrArg (fun k : ℕ => 2 * (k : ℤ)) hn)
        (multiplyDiscriminant (n - 6) t') := by
      ext z
      exact (ModularForm.discriminant_mul_discriminantEquiv_apply s z).symm
    rw [hrepr]
    exact weightedSpan_mcast hn _ ht

end Zeta7Auxiliary
