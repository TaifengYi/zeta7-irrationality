import Zeta7Proof.Radius49USeven
import Zeta7Proof.Radius49Bootstrap
import Zeta7Proof.ModularDifferentialTransport

/-! Radius internalization, Phases IV/VII: the exact twisted `U₇` fixed-point identity for `H`.

Write `A = E₂*` (the project's `ASeries`), `x = xSeries`, `q = qSeries` (its compositional
inverse) and `E = E₋₂*` (`eisensteinMinusTwo`). The weight `-2` operator `U₇` is transported to
the weight `0` coordinate series by
`twistU g = (A · U₇((g ∘ x) · A⁻¹)) ∘ q`,
the formal version of `g ↦ A · U₇(g / A)` (Coleman's twisted `U`-operator). Since `H ∘ x = A E` and
`U₇ E = E` (`uSeven_eisensteinMinusTwo`), `twistU H = H`. The operator is `ℚ₇`-linear and
`X`-adically contracting (`X^{7i+1} ∣ g ⇒ coeff i (twistU g) = 0`), whence the exact finite
coefficient identity
`hᵢ = Σ_{n ≤ 7i} tᵢₙ hₙ`,  `tᵢₙ = coeff i (twistU (Xⁿ))`
(`HSeries_twisted_fixed`), the input of `boundedAt_of_matrix`.

No declaration here uses the published radius input. -/

set_option autoImplicit false
noncomputable section
namespace Zeta7Main
open PowerSeries Filter Topology Zeta7Radius49
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

/-- `A = E₂*` over `ℚ₇`. -/
def Aq : ℚ_[7]⟦X⟧ := ASeries.map (algebraMap ℚ ℚ_[7])
/-- The coordinate `x(q)` over `ℚ₇`. -/
def xq : ℚ_[7]⟦X⟧ := xSeries.map (algebraMap ℚ ℚ_[7])
/-- The inverse coordinate `q(x)` over `ℚ₇`. -/
def qx : ℚ_[7]⟦X⟧ := qSeries.map (algebraMap ℚ ℚ_[7])

theorem Aq_constant : constantCoeff Aq = 1 := by
  rw [Aq, ← coeff_zero_eq_constantCoeff, coeff_map, coeff_zero_eq_constantCoeff, Zeta7Common.ASeries_constant,
    map_one]

theorem xq_constant : constantCoeff xq = 0 := by
  rw [xq, ← coeff_zero_eq_constantCoeff, coeff_map, coeff_zero_eq_constantCoeff, xSeries_constant,
    map_zero]

theorem qx_constant : constantCoeff qx = 0 := by
  rw [qx, ← coeff_zero_eq_constantCoeff, coeff_map, coeff_zero_eq_constantCoeff, qSeries_constant,
    map_zero]

theorem hasSubst_xq : HasSubst xq := HasSubst.of_constantCoeff_zero' xq_constant
theorem hasSubst_qx : HasSubst qx := HasSubst.of_constantCoeff_zero' qx_constant

theorem Aq_mul_inv : Aq * Aq⁻¹ = 1 :=
  PowerSeries.mul_inv_cancel _ (by rw [Aq_constant]; exact one_ne_zero)

/-- `U₇` as a `ℚ₇`-linear map. -/
def uSevenLin : ℚ_[7]⟦X⟧ →ₗ[ℚ_[7]] ℚ_[7]⟦X⟧ where
  toFun := uSeven
  map_add' := uSeven_add
  map_smul' c f := by ext n; simp only [coeff_uSeven, map_smul, RingHom.id_apply]

/-- The twisted operator `g ↦ (A · U₇((g ∘ x) · A⁻¹)) ∘ q`, as a `ℚ₇`-linear map. -/
def twistLin : ℚ_[7]⟦X⟧ →ₗ[ℚ_[7]] ℚ_[7]⟦X⟧ :=
  (substAlgHom (R := ℚ_[7]) hasSubst_qx).toLinearMap ∘ₗ LinearMap.mulLeft ℚ_[7] Aq ∘ₗ uSevenLin ∘ₗ
    LinearMap.mulRight ℚ_[7] Aq⁻¹ ∘ₗ (substAlgHom (R := ℚ_[7]) hasSubst_xq).toLinearMap

theorem twistLin_apply (g : ℚ_[7]⟦X⟧) :
    twistLin g = (Aq * uSeven (g.subst xq * Aq⁻¹)).subst qx := by
  simp only [twistLin, LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply,
    coe_substAlgHom, LinearMap.mulLeft_apply, LinearMap.mulRight_apply]
  rfl

/-- **The twisted fixed point.** `H` is fixed by the transported weight `-2` operator `U₇`. -/
theorem twistLin_HSeries : twistLin HSeries = HSeries := by
  rw [twistLin_apply]
  have hE : HSeries.subst xq = Aq * eisensteinMinusTwo := HSeries_subst_xSeries_eisenstein
  have hk : Aq * eisensteinMinusTwo * Aq⁻¹ = eisensteinMinusTwo := by
    rw [mul_comm Aq, mul_assoc, Aq_mul_inv, mul_one]
  rw [hE, hk, uSeven_eisensteinMinusTwo,
    eisensteinMinusTwo_eq_G_add_eta]
  exact HSeries_eq_product_subst_qSeries.symm

/-- The explicit twisted `U₇` matrix `tᵢₙ = coeff i (twistU (Xⁿ))`. -/
def twistMatrix (i n : ℕ) : ℚ_[7] := coeff i (twistLin (X ^ n))

theorem X_pow_dvd_subst {f a : ℚ_[7]⟦X⟧} (ha : constantCoeff a = 0) {m : ℕ}
    (hf : X ^ m ∣ f) : X ^ m ∣ f.subst a := by
  obtain ⟨g, rfl⟩ := hf
  have hs : HasSubst a := HasSubst.of_constantCoeff_zero' ha
  rw [subst_mul hs, subst_pow hs, subst_X hs]
  obtain ⟨u, hu⟩ := X_dvd_iff.mpr ha
  rw [hu, mul_pow, mul_assoc]
  exact dvd_mul_right _ _

theorem X_pow_dvd_uSeven {f : ℚ_[7]⟦X⟧} {i : ℕ} (hf : X ^ (7 * i + 1) ∣ f) :
    X ^ (i + 1) ∣ uSeven f := by
  rw [X_pow_dvd_iff] at hf ⊢
  intro m hm
  rw [coeff_uSeven]
  exact hf _ (by omega)

/-- `X`-adic contraction: high-order input does not reach coefficient `i`. -/
theorem coeff_twistLin_eq_zero {g : ℚ_[7]⟦X⟧} {i : ℕ} (hg : X ^ (7 * i + 1) ∣ g) :
    coeff i (twistLin g) = 0 := by
  rw [twistLin_apply]
  have h1 : X ^ (7 * i + 1) ∣ g.subst xq * Aq⁻¹ :=
    (X_pow_dvd_subst xq_constant hg).mul_right _
  have h2 : X ^ (i + 1) ∣ Aq * uSeven (g.subst xq * Aq⁻¹) := (X_pow_dvd_uSeven h1).mul_left _
  have h3 := X_pow_dvd_subst qx_constant h2
  exact (X_pow_dvd_iff.mp h3) i (by omega)

/-- **The exact twisted fixed-point coefficient identity** `hᵢ = Σ_{n ≤ 7i} tᵢₙ hₙ`. -/
theorem HSeries_twisted_fixed (i : ℕ) :
    coeff i HSeries =
      ∑ n ∈ Finset.range (7 * i + 1), twistMatrix i n * coeff n HSeries := by
  set N := 7 * i + 1
  set T : ℚ_[7]⟦X⟧ := ∑ n ∈ Finset.range N, coeff n HSeries • X ^ n with hT
  have hR : X ^ N ∣ HSeries - T := by
    rw [X_pow_dvd_iff]
    intro m hm
    rw [map_sub, hT, map_sum]
    simp only [map_smul, coeff_X_pow, smul_eq_mul, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq, ite_cond_eq_true _ _ (eq_true (Finset.mem_range.mpr hm)), sub_self]
  have hsplit : HSeries = T + (HSeries - T) := by ring
  conv_lhs => rw [← twistLin_HSeries, hsplit, map_add, map_add, coeff_twistLin_eq_zero hR,
    add_zero, hT, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro n _
  rw [map_smul, map_smul, smul_eq_mul, twistMatrix, mul_comm]

/-- **Conditional internal radius theorem (reduction).** The twisted matrix bound for each
improvement step and an initial overconvergence radius `7^{s₀}`, `s₀ > 0`, imply coefficient
decay of `HSeries` at every radius `7^r`, `r < 2`. -/
theorem HSeries_decay_of_matrix_bound
    (hM : ∀ s : ℝ, 0 < s → s < 2 → ∃ K : ℝ, 0 ≤ K ∧ ∀ i n,
      ‖twistMatrix i n‖ * ((7 : ℝ) ^ improve s) ^ i ≤ K * ((7 : ℝ) ^ s) ^ n)
    (hO : ∃ s₀ : ℝ, 0 < s₀ ∧ BoundedAt (fun n => coeff n HSeries) ((7 : ℝ) ^ s₀)) :
    ∀ r : ℝ, r < 2 →
      Tendsto (fun n => ‖coeff n HSeries‖ * ((7 : ℝ) ^ r) ^ n) atTop (𝓝 0) := by
  obtain ⟨s₀, hs₀, h₀⟩ := hO
  apply decay_all_below_two (fun n => coeff n HSeries) hs₀ h₀
  intro s hs0 hs2 hb
  obtain ⟨K, hK0, hK⟩ := hM s hs0 hs2
  exact boundedAt_of_matrix (fun n => coeff n HSeries) twistMatrix HSeries_twisted_fixed
    (by positivity) (by positivity) hK0 hK hb

/-- **The radius-49 statement reduced to the two explicit remaining propositions** (the twisted
`U₇` matrix bound, i.e. the Buzzard continuation step, and initial overconvergence, i.e.
Coleman's theorem at `κ = -2`). Axiom-free. -/
theorem hasRadius49_of_matrix_bound_and_initial
    (hM : ∀ s : ℝ, 0 < s → s < 2 → ∃ K : ℝ, 0 ≤ K ∧ ∀ i n,
      ‖twistMatrix i n‖ * ((7 : ℝ) ^ improve s) ^ i ≤ K * ((7 : ℝ) ^ s) ^ n)
    (hO : ∃ s₀ : ℝ, 0 < s₀ ∧ BoundedAt (fun n => coeff n HSeries) ((7 : ℝ) ^ s₀)) :
    HasRadius49GeometricContinuation := by
  apply hasRadius49_of_valueGroup_decay
  intro r hr
  exact HSeries_decay_of_matrix_bound hM hO r (by exact_mod_cast hr)

/-- **Obstruction lemma.** `U₇`-fixedness alone cannot pin the constant: every `G + c` is fixed.
Hence the initial overconvergence input (which forces `c = η`) is logically necessary. -/
theorem uSeven_G_add_const (c : ℚ_[7]) :
    uSeven (GSeries.map (algebraMap ℚ ℚ_[7]) + C c) = GSeries.map (algebraMap ℚ ℚ_[7]) + C c := by
  rw [uSeven_add, uSeven_C, uSeven_map, uSeven_GSeries]

end Zeta7Main
