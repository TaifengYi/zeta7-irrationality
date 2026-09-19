import Zeta7Proof.GermRationalOperator

/-! Exact signs and eliminations for the explicit connections in N2--N3. -/
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 4096
open scoped RatFunc
namespace Zeta7Germ

def connection3 (v : Fin 3 → RatFunc ℂ) : Fin 3 → RatFunc ℂ :=
  ![rationalD (v 0) + rationalD V * v 2 / 2,
    v 0 + rationalD (v 1) + V * v 2, v 1 + rationalD (v 2)]

theorem connection3_leibniz (f : RatFunc ℂ) (v : Fin 3 → RatFunc ℂ) :
    connection3 (f • v) = rationalD f • v + f • connection3 v := by
  ext i
  fin_cases i <;>
    simp [connection3, Derivation.leibniz, smul_eq_mul] <;> ring

/-- A normalized invariant line gives the Riccati equation for MINUS u. -/
theorem normalized_line_riccati (a b u : RatFunc ℂ)
    (h : connection3 ![a, b, 1] = u • ![a, b, 1]) : riccati (-u) = 0 := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  simp [connection3, smul_eq_mul] at h0 h1 h2
  subst b
  have ha : a = u ^ 2 - rationalD u - V := by linear_combination h1
  rw [ha] at h0
  simp only [map_sub, Derivation.leibniz_pow, smul_eq_mul] at h0
  simp only [riccati, map_neg]
  linear_combination h0

/-- Eliminating the three jet coordinates produces the correction LC = -hR. -/
theorem correction_elimination (a b c h : RatFunc ℂ)
    (h0 : h * R + rationalD a + rationalD V * c / 2 = 0)
    (h1 : a + rationalD b + V * c = 0)
    (h2 : b + rationalD c = 0) : L c = -h * R := by
  have hb : b = -rationalD c := by linear_combination h2
  have ha : a = rationalD (rationalD c) - V * c := by
    rw [hb, map_neg] at h1
    linear_combination h1
  rw [ha, map_sub, Derivation.leibniz] at h0
  simp only [smul_eq_mul] at h0
  dsimp [L]
  linear_combination h0

end Zeta7Germ
