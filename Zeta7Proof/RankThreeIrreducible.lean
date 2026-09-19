import Zeta7Proof.N2Universal
import Zeta7Proof.GermConnectionAlgebra

/-! The rank-three connection is irreducible. A nondegenerate horizontal pairing
turns a stable plane into a stable line, so both dimensions are excluded. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
open scoped RatFunc
namespace Zeta7Germ

theorem connection3_no_stable_line (S : Submodule (RatFunc ℂ) (Fin 3 → RatFunc ℂ))
    (hstable : ∀ v ∈ S, connection3 v ∈ S) : Module.finrank (RatFunc ℂ) S ≠ 1 := by
  intro hdim
  have hS : S ≠ ⊥ := by
    intro hz
    have hzero : Module.finrank (RatFunc ℂ) S = 0 := Submodule.finrank_eq_zero.mpr hz
    omega
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS
  have hspan := eq_span_singleton_of_mem_of_finrank_eq_one hdim hv hv0
  have hconn := hstable v hv
  rw [hspan] at hconn
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hconn
  have hv2 : v 2 ≠ 0 := by
    intro hz
    have h2 := congrFun hc 2
    simp [connection3, hz, smul_eq_mul] at h2
    have h1 := congrFun hc 1
    simp [connection3, hz, ← h2, smul_eq_mul] at h1
    apply hv0
    ext i
    fin_cases i <;> simp_all
  let w : Fin 3 → RatFunc ℂ := (v 2)⁻¹ • v
  have hw : w ∈ S := S.smul_mem _ hv
  have hw2 : w 2 = 1 := by simp [w, hv2, smul_eq_mul]
  have hw0 : w ≠ 0 := by intro hz; have := congrFun hz 2; simp [hw2] at this
  have hwspan := eq_span_singleton_of_mem_of_finrank_eq_one hdim hw hw0
  have hwconn := hstable w hw
  rw [hwspan] at hwconn
  obtain ⟨u, hu⟩ := Submodule.mem_span_singleton.mp hwconn
  have hweq : w = ![w 0, w 1, 1] := by ext i; fin_cases i <;> simp [hw2]
  have heq : connection3 ![w 0, w 1, 1] = u • ![w 0, w 1, 1] := by
    rw [← hweq]
    exact hu.symm
  exact no_rational_riccati_solution (-u) (normalized_line_riccati _ _ _ heq)

def connectionPairing : LinearMap.BilinForm (RatFunc ℂ) (Fin 3 → RatFunc ℂ) where
  toFun v :=
    { toFun := fun w => v 0 * w 2 - v 1 * w 1 + v 2 * w 0 + V * v 2 * w 2
      map_add' := by intro w z; simp; ring
      map_smul' := by intro a w; simp [smul_eq_mul]; ring }
  map_add' := by intro v w; ext z; simp; ring
  map_smul' := by intro a v; ext w; simp [smul_eq_mul]; ring

theorem connectionPairing_apply (v w : Fin 3 → RatFunc ℂ) :
    connectionPairing v w = v 0 * w 2 - v 1 * w 1 + v 2 * w 0 + V * v 2 * w 2 := rfl

theorem connectionPairing_symm (v w : Fin 3 → RatFunc ℂ) :
    connectionPairing v w = connectionPairing w v := by
  simp only [connectionPairing_apply]
  ring

theorem connectionPairing_separating (v : Fin 3 → RatFunc ℂ)
    (hv : ∀ w, connectionPairing v w = 0) : v = 0 := by
  have h0 := hv ![0, 0, 1]
  have h1 := hv ![0, 1, 0]
  have h2 := hv ![1, 0, 0]
  simp [connectionPairing_apply] at h0 h1 h2
  ext i
  fin_cases i <;> simp_all

theorem connectionPairing_nondegenerate : connectionPairing.Nondegenerate := by
  constructor
  · exact connectionPairing_separating
  · intro v hv
    apply connectionPairing_separating v
    intro w
    rw [connectionPairing_symm]
    exact hv w

theorem connectionPairing_derivative (v w : Fin 3 → RatFunc ℂ) :
    rationalD (connectionPairing v w) =
      connectionPairing (connection3 v) w + connectionPairing v (connection3 w) := by
  simp [connectionPairing_apply, connection3, Derivation.leibniz, smul_eq_mul]
  ring

theorem connection3_orthogonal_stable (S : Submodule (RatFunc ℂ) (Fin 3 → RatFunc ℂ))
    (hstable : ∀ v ∈ S, connection3 v ∈ S) :
    ∀ v ∈ connectionPairing.orthogonal S, connection3 v ∈ connectionPairing.orthogonal S := by
  intro v hv w hw
  have hd := connectionPairing_derivative w v
  rw [hv w hw, map_zero, hv (connection3 w) (hstable w hw), zero_add] at hd
  exact hd.symm

theorem connection3_no_stable_plane (S : Submodule (RatFunc ℂ) (Fin 3 → RatFunc ℂ))
    (hstable : ∀ v ∈ S, connection3 v ∈ S) : Module.finrank (RatFunc ℂ) S ≠ 2 := by
  intro hdim
  have hd := LinearMap.BilinForm.finrank_orthogonal connectionPairing_nondegenerate S
  simp only [Module.finrank_pi, Module.finrank_self, Finset.card_univ, Fintype.card_fin,
    Finset.sum_const, nsmul_eq_mul, mul_one, hdim] at hd
  norm_num at hd
  exact connection3_no_stable_line _ (connection3_orthogonal_stable S hstable) hd

theorem connection3_irreducible (S : Submodule (RatFunc ℂ) (Fin 3 → RatFunc ℂ))
    (hstable : ∀ v ∈ S, connection3 v ∈ S) : S = ⊥ ∨ S = ⊤ := by
  have hle : Module.finrank (RatFunc ℂ) S ≤ 3 := by simpa using S.finrank_le
  by_cases h0 : Module.finrank (RatFunc ℂ) S = 0
  · exact Or.inl (Submodule.finrank_eq_zero.mp h0)
  by_cases h3 : Module.finrank (RatFunc ℂ) S = 3
  · apply Or.inr
    apply Submodule.eq_top_of_finrank_eq
    simpa using h3
  have h1 := connection3_no_stable_line S hstable
  have h2 := connection3_no_stable_plane S hstable
  omega

end Zeta7Germ
