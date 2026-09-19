import Zeta7Proof.GermRationalOperator
import Zeta7Proof.ActualPrimitiveFrame

/-! The actual LH equation and ordinary primitives in the canonical Laurent field. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
open scoped LaurentSeries RatFunc
open PowerSeries
namespace Zeta7Germ

def laurentL (f : ℂ⸨X⸩) : ℂ⸨X⸩ :=
  laurentD (laurentD (laurentD f)) - embed V * laurentD f - embed (rationalD V) * f / 2

abbrev actualH (c : ℚ) : ℂ⸨X⸩ := complexSeries (Zeta7Common.rationalH c)

theorem complexSeries_sub (f g : ℚ⟦X⟧) :
    complexSeries (f - g) = complexSeries f - complexSeries g := by simp [complexSeries]

theorem complexSeries_half : complexSeries (C (1 / 2 : ℚ)) = (1 / 2 : ℂ⸨X⸩) := by
  simp [complexSeries, map_div₀, map_ofNat]

theorem actualH_laurentL (c : ℚ) : laurentL (actualH c) = embed R := by
  have h := congrArg complexSeries (Zeta7Common.rationalH_modularL c)
  simp only [Zeta7Common.modularL, complexSeries_sub, complexSeries_mul,
    complexSeries_euler, complexSeries_half, ← embed_V, ← embed_R,
    ← embed_rationalD] at h
  dsimp [laurentL, actualH]
  linear_combination h

theorem primitiveFrame_laurentD_zero (c : ℚ) :
    laurentD (complexSeries (Zeta7Common.primitiveFrame c 0)) = embed R * actualH c := by
  rw [← complexSeries_euler, Zeta7Common.primitiveFrame_euler_zero,
    complexSeries_mul, ← embed_R]

theorem primitiveFrame_laurentD_one (c : ℚ) :
    laurentD (complexSeries (Zeta7Common.primitiveFrame c 1)) =
      -embed RatFunc.X * embed R * actualH c := by
  rw [← complexSeries_euler, Zeta7Common.primitiveFrame_euler_one]
  simp only [complexSeries_mul, ← embed_R]
  have hx : complexSeries (-X) = -embed RatFunc.X := by simp [complexSeries, embed_X]
  rw [hx]

theorem primitiveFrame_laurentD_two (c : ℚ) :
    laurentD (complexSeries (Zeta7Common.primitiveFrame c 2)) =
      embed RatFunc.X ^ 2 * embed R * actualH c / 2 := by
  rw [← complexSeries_euler, Zeta7Common.primitiveFrame_euler_two]
  simp only [complexSeries_mul, complexSeries_half, ← embed_R]
  have hx : complexSeries (X ^ 2) = embed RatFunc.X ^ 2 := by
    simp [complexSeries, embed_X]
  rw [hx]
  ring

/-- The correction retains its rational term C R. -/
theorem actual_correction_derivative (c : ℚ) (f : RatFunc ℂ) :
    laurentD (embed (rationalD (rationalD f) - V * f) * actualH c -
      embed (rationalD f) * laurentD (actualH c) +
      embed f * laurentD (laurentD (actualH c))) =
        embed (L f) * actualH c + embed (f * R) := by
  have h := actualH_laurentL c
  dsimp [laurentL] at h
  simp only [map_add, map_sub, map_mul, Derivation.leibniz, smul_eq_mul,
    ← embed_rationalD, L, map_div₀, map_ofNat]
  have htwo : (2 : ℂ⸨X⸩) ≠ 0 := by
    rw [← map_ofNat (HahnSeries.C (Γ := ℤ) (R := ℂ)) 2]
    exact (map_ne_zero (HahnSeries.C (Γ := ℤ) (R := ℂ))).mpr (by norm_num)
  have ht : (2 : ℂ⸨X⸩)⁻¹ * 2 = 1 := inv_mul_cancel₀ htwo
  linear_combination embed f * h + embed f * actualH c * embed (rationalD V) * ht

end Zeta7Germ
