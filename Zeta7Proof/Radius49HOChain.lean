import Zeta7Proof.Radius49HOBnd

/-! Radius internalization, HO step (iii): initial overconvergence of `H` at `κ = -2`.

The weight `-2` Eisenstein series is the limit of the classical `7`-stabilized Eisenstein series
of weights `k_r = 6·7^r - 2 → -2` in `ℤ₇ × ℤ/6` (`classical_eisenstein_tendstoUniformly`; the
branch is `k_r ≡ 4 (mod 6)`, the branch of `-2`). With `j = 7^r` the weight-zero approximants
`g_r = A · F*_{k_r} / E₆^{j}` (in the coordinate `x`) satisfy

* `g_r · T(x)^j = P_r(x)`, a polynomial of degree `≤ 4j` (`approx_poly_deg`);
* `g_r = twistLin (R^j · g_r)` with the Katz ratio `R = E₆ / V(E₆) = T(x) / T̃(x)`
  (`g_fixed`, from `U₇ F*_{k_r} = F*_{k_r}`);
* `‖g_r‖₁ ≤ max(1, |η|)` and `g_r → H` uniformly in the coefficients at radius `1`.

The chain `7^{u}, 7^{7u}, …, 7^{1/4}` from `u = 1/(4·7^{r+1})` with the near-ordinary estimate
`twistLin_near` gives a bound for `g_r` at radius `7^{1/4}` independent of `r`, hence
`initial_HSeries_overconvergent`. No published radius input is used. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open PowerSeries Filter Topology
namespace Zeta7Radius49
open Zeta7Main
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

/-! ### Degree-tracked polynomial structure of the approximants (over `ℚ`, in `q`) -/

def pPx : Polynomial ℚ := 1 + 13 * Polynomial.X + 49 * Polynomial.X ^ 2
def pNx : Polynomial ℚ := 1 + 245 * Polynomial.X + 2401 * Polynomial.X ^ 2
def pTx : Polynomial ℚ := 1 - 490 * Polynomial.X - 21609 * Polynomial.X ^ 2 -
  235298 * Polynomial.X ^ 3 - 823543 * Polynomial.X ^ 4
def pNtx : Polynomial ℚ := 1 + 5 * Polynomial.X + Polynomial.X ^ 2
def pTtx : Polynomial ℚ := 1 + 14 * Polynomial.X + 63 * Polynomial.X ^ 2 +
  70 * Polynomial.X ^ 3 - 7 * Polynomial.X ^ 4

theorem pPx_deg : pPx.natDegree ≤ 2 := by unfold pPx; compute_degree
theorem pNx_deg : pNx.natDegree ≤ 2 := by unfold pNx; compute_degree
theorem pTx_deg : pTx.natDegree ≤ 4 := by unfold pTx; compute_degree
theorem pNtx_deg : pNtx.natDegree ≤ 2 := by unfold pNtx; compute_degree
theorem pTtx_deg : pTtx.natDegree ≤ 4 := by unfold pTtx; compute_degree

theorem pPx_aeval : Polynomial.aeval xSeries pPx = Px := by simp [pPx, map_ofNat]
theorem pNx_aeval : Polynomial.aeval xSeries pNx = Nx := by simp [pNx, map_ofNat]
theorem pTx_aeval : Polynomial.aeval xSeries pTx = Tx := by simp [pTx, map_ofNat]
theorem pNtx_aeval : Polynomial.aeval xSeries pNtx = Ntx := by simp [pNtx, map_ofNat]
theorem pTtx_aeval : Polynomial.aeval xSeries pTtx = Ttx := by simp [pTtx, map_ofNat]

theorem deg_mono3 {a b c : Polynomial ℚ} {da db dc : ℕ} (ha : a.natDegree ≤ da)
    (hb : b.natDegree ≤ db) (hc : c.natDegree ≤ dc) (m n k : ℕ) :
    (a ^ m * b ^ n * c ^ k).natDegree ≤ m * da + n * db + k * dc := by
  refine Polynomial.natDegree_mul_le.trans (add_le_add (Polynomial.natDegree_mul_le.trans
    (add_le_add ?_ ?_)) ?_)
  · exact Polynomial.natDegree_pow_le.trans (Nat.mul_le_mul_left _ ha)
  · exact Polynomial.natDegree_pow_le.trans (Nat.mul_le_mul_left _ hb)
  · exact Polynomial.natDegree_pow_le.trans (Nat.mul_le_mul_left _ hc)

/-- The polynomial property of weight `6j - 2` combinations, with degree `≤ 4j`. -/
theorem span_poly_deg (j : ℕ) {F : ℚ⟦X⟧} (hF : F ∈ Submodule.span ℚ (monoSet (6 * j - 2)))
    (hj : 1 ≤ j) :
    (∃ p : Polynomial ℚ, p.natDegree ≤ 4 * j ∧
        ASeries * F * Tx ^ j = E6Q ^ j * Polynomial.aeval xSeries p) ∧
      (∃ p : Polynomial ℚ, p.natDegree ≤ 4 * j ∧
        ASeries * vSeven F * Tx ^ j = E6Q ^ j * Polynomial.aeval xSeries p) := by
  induction hF using Submodule.span_induction with
  | mem s hs =>
    obtain ⟨a, b, hab, rfl⟩ := hs
    obtain ⟨t, rfl⟩ : ∃ t, a = 3 * t + 1 := ⟨a / 3, by omega⟩
    obtain rfl : j = b + 2 * t + 1 := by omega
    refine ⟨⟨pNx ^ (3 * t + 1) * pTx ^ b * pPx ^ (t + 1), ?_, ?_⟩,
      ⟨pNtx ^ (3 * t + 1) * pTtx ^ b * pPx ^ (t + 1), ?_, ?_⟩⟩
    · exact (deg_mono3 pNx_deg pTx_deg pPx_deg _ _ _).trans (by omega)
    · rw [map_mul, map_mul, map_pow, map_pow, map_pow, pNx_aeval, pTx_aeval, pPx_aeval]
      exact mono_identity t b
    · exact (deg_mono3 pNtx_deg pTtx_deg pPx_deg _ _ _).trans (by omega)
    · rw [map_mul, map_mul, map_pow, map_pow, map_pow, pNtx_aeval, pTtx_aeval, pPx_aeval]
      have hV : vSeven (E4Q ^ (3 * t + 1) * E6Q ^ b) =
          vSeven E4Q ^ (3 * t + 1) * vSeven E6Q ^ b := by
        simp only [vSeven, map_mul, map_pow]
      rw [hV]; exact Vmono_identity t b
  | zero =>
    refine ⟨⟨0, by simp, by simp⟩, ⟨0, by simp, ?_⟩⟩
    simp [vSeven]
  | add x y _ _ hx hy =>
    obtain ⟨⟨S1, hS1, e1⟩, ⟨V1, hV1, f1⟩⟩ := hx
    obtain ⟨⟨S2, hS2, e2⟩, ⟨V2, hV2, f2⟩⟩ := hy
    refine ⟨⟨S1 + S2, (Polynomial.natDegree_add_le _ _).trans (max_le hS1 hS2), ?_⟩,
      ⟨V1 + V2, (Polynomial.natDegree_add_le _ _).trans (max_le hV1 hV2), ?_⟩⟩
    · rw [map_add]; linear_combination e1 + e2
    · have : vSeven (x + y) = vSeven x + vSeven y := map_add (vSevenHom ℚ) x y
      rw [this, map_add]; linear_combination f1 + f2
  | smul c x _ hx =>
    obtain ⟨⟨S1, hS1, e1⟩, ⟨V1, hV1, f1⟩⟩ := hx
    refine ⟨⟨c • S1, (Polynomial.natDegree_smul_le _ _).trans hS1, ?_⟩,
      ⟨c • V1, (Polynomial.natDegree_smul_le _ _).trans hV1, ?_⟩⟩
    · rw [map_smul, smul_eq_C_mul, smul_eq_C_mul]; linear_combination C c * e1
    · have : vSeven (c • x) = c • vSeven x := map_smul (vSevenHom ℚ) c x
      rw [this, map_smul, smul_eq_C_mul, smul_eq_C_mul]; linear_combination C c * f1

/-- **Polynomial structure of the approximants, with degree.** -/
theorem approx_poly_deg (r : ℕ) :
    ∃ p : Polynomial ℚ, p.natDegree ≤ 4 * 7 ^ r ∧
      ASeries * Fst r * Tx ^ (7 ^ r) = E6Q ^ (7 ^ r) * Polynomial.aeval xSeries p := by
  have hj : 1 ≤ 7 ^ r := Nat.one_le_pow r 7 (by norm_num)
  obtain ⟨⟨S1, hS1, e1⟩, ⟨V1, hV1, f1⟩⟩ := span_poly_deg (7 ^ r) (Fr_span r) hj
  refine ⟨S1 - ((7 : ℚ) ^ (serreWeight r - 1)) • V1, ?_, ?_⟩
  · exact (Polynomial.natDegree_sub_le _ _).trans
      (max_le hS1 ((Polynomial.natDegree_smul_le _ _).trans hV1))
  · rw [Fst, map_sub, map_smul, smul_eq_C_mul]
    linear_combination e1 - C ((7 : ℚ) ^ (serreWeight r - 1)) * f1

/-! ### Transport to the coordinate `x` over `ℚ₇` -/

local notation "φ7" => algebraMap ℚ ℚ_[7]

theorem qx_subst_xq : qx.subst xq = X := by
  have hx : HasSubst xSeries := HasSubst.of_constantCoeff_zero' xSeries_constant
  calc qx.subst xq = (qSeries.subst xSeries).map (algebraMap ℚ ℚ_[7]) :=
        (map_subst (h := algebraMap ℚ ℚ_[7]) hx qSeries).symm
    _ = X := by rw [q_subst_x]; exact PowerSeries.map_X _

theorem subst_xq_substQ (f : ℚ_[7]⟦X⟧) : (substQ f).subst xq = f := by
  rw [substQ_apply, subst_comp_subst_apply hasSubst_qx hasSubst_xq, qx_subst_xq, X_subst]

theorem substQ_subst_xq (f : ℚ_[7]⟦X⟧) : substQ (f.subst xq) = f := by
  rw [substQ_apply, subst_comp_subst_apply hasSubst_xq hasSubst_qx, xq_subst_qx, X_subst]

theorem substQ_C (c : ℚ_[7]) : substQ (C c) = C c := by
  rw [substQ_apply, ← coe_substAlgHom hasSubst_qx]
  have e : (C c : ℚ_[7]⟦X⟧) = c • (1 : ℚ_[7]⟦X⟧) := by rw [smul_eq_C_mul, mul_one]
  rw [e, map_smul, map_one]

theorem substQ_aeval_coeff (p : Polynomial ℚ) (i : ℕ) :
    coeff i (substQ ((Polynomial.aeval xSeries p).map φ7)) = φ7 (p.coeff i) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, Polynomial.coeff_add, hp, hq]
  | monomial n a =>
    rw [Polynomial.aeval_monomial, map_mul, map_pow, Polynomial.coeff_monomial]
    have hC : (algebraMap ℚ ℚ⟦X⟧ a).map φ7 = C (φ7 a) := by
      rw [show algebraMap ℚ ℚ⟦X⟧ a = C a from rfl, map_C]
    rw [hC, show xSeries.map φ7 = xq from rfl, map_mul, map_pow, substQ_C, substQ_xq,
      coeff_C_mul_X_pow]
    split_ifs with h1 h2 h2
    · rfl
    · exact absurd h1.symm h2
    · exact absurd h2.symm h1
    · rw [map_zero]

theorem substQ_aeval_deg (p : Polynomial ℚ) {d : ℕ} (hp : p.natDegree ≤ d) (i : ℕ)
    (hi : d < i) : coeff i (substQ ((Polynomial.aeval xSeries p).map φ7)) = 0 := by
  rw [substQ_aeval_coeff, Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), map_zero]

theorem Tx_map : Tx.map φ7 = polyTg xq := by
  simp [polyTg, xq, map_ofNat]

theorem Ttx_map : Ttx.map φ7 = polyTtg xq := by
  simp [polyTtg, xq, map_ofNat]

/-! ### The approximants and their fixed-point relation -/

/-- `F*_{k_r}` over `ℚ₇`. -/
def Fq (r : ℕ) : ℚ_[7]⟦X⟧ := (Fst r).map φ7

/-- `A · F*_{k_r} / E₆^{7^r}` in the coordinate `q`. -/
def aq (r : ℕ) : ℚ_[7]⟦X⟧ := Aq * Fq r * Eq6i ^ (7 ^ r)

/-- The weight-zero approximant in the coordinate `x`. -/
def gA (r : ℕ) : ℚ_[7]⟦X⟧ := substQ (aq r)

/-- The Katz ratio `E₆ / V(E₆)` in the coordinate `x`. -/
def rK : ℚ_[7]⟦X⟧ := substQ (Eq6 * vSeven Eq6i)

theorem vSeven_Eq6_mul_inv : vSeven Eq6 * vSeven Eq6i = 1 := by
  have h := congrArg (vSevenHom ℚ_[7]) Eq6_mul_inv
  rw [map_mul, map_one] at h
  exact h

theorem uSeven_Fq (r : ℕ) : uSeven (Fq r) = Fq r := by
  rw [Fq, uSeven_map, uSeven_Fst]

/-- **The twisted fixed-point relation of the approximants.** -/
theorem g_fixed (r : ℕ) : twistLin (rK ^ (7 ^ r) * gA r) = gA r := by
  set j := 7 ^ r
  have e1 : rK ^ j * gA r = substQ ((Eq6 * vSeven Eq6i) ^ j * aq r) := by
    simp only [rK, gA, map_mul, map_pow]
  have hA : Aq * Aq⁻¹ = 1 := Aq_mul_inv
  have e2 : (Eq6 * vSeven Eq6i) ^ j * aq r * Aq⁻¹ = vSeven (Eq6i ^ j) * Fq r := by
    have hv : vSeven (Eq6i ^ j) = vSeven Eq6i ^ j := map_pow (vSevenHom ℚ_[7]) Eq6i j
    rw [hv, aq]
    have h1 : (Eq6 * Eq6i) ^ j = 1 := by rw [Eq6_mul_inv, one_pow]
    calc (Eq6 * vSeven Eq6i) ^ j * (Aq * Fq r * Eq6i ^ j) * Aq⁻¹
        = vSeven Eq6i ^ j * Fq r * (Eq6 * Eq6i) ^ j * (Aq * Aq⁻¹) := by ring
      _ = vSeven Eq6i ^ j * Fq r := by rw [h1, hA]; ring
  rw [twistLin_apply, e1, subst_xq_substQ, e2, uSeven_vSeven_mul, uSeven_Fq, ← substQ_apply, gA,
    aq]
  congr 1
  ring

/-- `R · T̃(x) = T(x)`. -/
theorem rK_mul : rK * polyTtg (X : ℚ_[7]⟦X⟧) = polyTg X := by
  have hk : Eq6 * polyTtg xq = vSeven Eq6 * polyTg xq := by
    have h := congrArg (PowerSeries.map φ7) katz_formal
    rw [map_mul, map_mul, vSeven_map, Ttx_map, Tx_map] at h
    exact h
  have h2 : Eq6 * vSeven Eq6i * polyTtg xq = polyTg xq := by
    calc Eq6 * vSeven Eq6i * polyTtg xq = vSeven Eq6i * (Eq6 * polyTtg xq) := by ring
      _ = (vSeven Eq6 * vSeven Eq6i) * polyTg xq := by rw [hk]; ring
      _ = polyTg xq := by rw [vSeven_Eq6_mul_inv, one_mul]
  have h3 := congrArg substQ h2
  rw [map_mul, polyTtg_map, polyTg_map, substQ_xq] at h3
  exact h3

theorem Bnd_rK {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ 1 / 4) : Bnd ((7 : ℝ) ^ s) rK 1 :=
  Bnd_of_dom (by positivity) polyTtg_coeff_zero (Bnd_polyTtg_sub hs0 hs) (Bnd_polyTg hs0 hs)
    (by rw [mul_comm]; exact rK_mul)

/-- **The approximants are polynomials over `T(x)^j`.** -/
theorem gA_poly (r : ℕ) : ∃ p : Polynomial ℚ, p.natDegree ≤ 4 * 7 ^ r ∧
    gA r * polyTg (X : ℚ_[7]⟦X⟧) ^ (7 ^ r) =
      substQ ((Polynomial.aeval xSeries p).map φ7) := by
  obtain ⟨p, hp, e⟩ := approx_poly_deg r
  refine ⟨p, hp, ?_⟩
  have h := congrArg (PowerSeries.map φ7) e
  simp only [map_mul, map_pow] at h
  rw [Tx_map] at h
  change Aq * Fq r * polyTg xq ^ 7 ^ r = Eq6 ^ 7 ^ r * _ at h
  have h2 : aq r * polyTg xq ^ 7 ^ r = (Polynomial.aeval xSeries p).map φ7 := by
    have h1 : (Eq6 * Eq6i) ^ (7 ^ r) = 1 := by rw [Eq6_mul_inv, one_pow]
    calc aq r * polyTg xq ^ 7 ^ r = Eq6i ^ 7 ^ r * (Aq * Fq r * polyTg xq ^ 7 ^ r) := by
          rw [aq]; ring
      _ = (Eq6 * Eq6i) ^ (7 ^ r) * (Polynomial.aeval xSeries p).map φ7 := by rw [h]; ring
      _ = _ := by rw [h1, one_mul]
  have h3 := congrArg substQ h2
  rw [map_mul, map_pow, polyTg_map, substQ_xq] at h3
  exact h3

/-! ### Uniform bounds at radius `1` and convergence -/

theorem Fq_eq (r : ℕ) : Fq r = classicalEisensteinSeries r -
    C ((7 : ℚ_[7]) ^ (serreWeight r - 1)) * vSeven (classicalEisensteinSeries r) := by
  rw [Fq, Fst, map_sub, map_mul, map_C, vSeven_map, classicalEisensteinSeries, map_pow,
    map_ofNat]

theorem Fq_close {ε : ℝ} (hε : 0 < ε) : ∃ R : ℕ, ∀ r, R ≤ r →
    Bnd 1 (Fq r - eisensteinMinusTwo) ε ∧ Bnd 1 (Fq r) BE := by
  set ε' := min ε 1 with hε'
  have hε'0 : 0 < ε' := lt_min hε one_pos
  have hU := Metric.tendstoUniformly_iff.mp classical_eisenstein_tendstoUniformly ε' hε'0
  obtain ⟨R1, hR1⟩ := eventually_atTop.mp hU
  obtain ⟨R2, hR2⟩ := exists_pow_lt_of_lt_one (div_pos hε'0 (by linarith [one_le_BE] :
    (0 : ℝ) < BE)) (by norm_num : (7 : ℝ)⁻¹ < 1)
  refine ⟨max R1 R2, fun r hr => ?_⟩
  have hD : Bnd 1 (classicalEisensteinSeries r - eisensteinMinusTwo) ε' := by
    intro n
    rw [one_pow, mul_one, map_sub]
    have := hR1 r (le_of_max_le_left hr) n
    rw [dist_eq_norm'] at this
    exact this.le
  have hCE : Bnd 1 (classicalEisensteinSeries r) BE := by
    have h := Bnd_eisensteinMinusTwo.add zero_le_one
      (hD.mono ((min_le_right _ _).trans one_le_BE))
    simpa using h
  have hpow : ‖(7 : ℚ_[7]) ^ (serreWeight r - 1)‖ * BE ≤ ε' := by
    rw [norm_seven_pow]
    have h1 : ((7 : ℝ)⁻¹) ^ (serreWeight r - 1) ≤ ((7 : ℝ)⁻¹) ^ R2 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num)
        (by have := serreWeight_exponent_ge r; have := le_of_max_le_right hr; omega)
    have h2 := (lt_div_iff₀ (by linarith [one_le_BE] : (0 : ℝ) < BE)).mp hR2
    nlinarith [one_le_BE]
  have hV : Bnd 1 (C ((7 : ℚ_[7]) ^ (serreWeight r - 1)) *
      vSeven (classicalEisensteinSeries r)) ε' :=
    ((Bnd_C zero_le_one _).mul one_pos (Bnd_vSeven_one hCE)).mono hpow
  have hdiff : Fq r - eisensteinMinusTwo = (classicalEisensteinSeries r - eisensteinMinusTwo) -
      C ((7 : ℚ_[7]) ^ (serreWeight r - 1)) * vSeven (classicalEisensteinSeries r) := by
    rw [Fq_eq]; ring
  have hsmall : Bnd 1 (Fq r - eisensteinMinusTwo) ε' := by
    rw [hdiff]; exact hD.sub zero_le_one hV
  refine ⟨hsmall.mono (min_le_left _ _), ?_⟩
  have h := Bnd_eisensteinMinusTwo.add zero_le_one
    (hsmall.mono ((min_le_right _ _).trans one_le_BE))
  simpa using h

theorem HSeries_eq_substQ : HSeries = substQ (Aq * eisensteinMinusTwo) := by
  have h : HSeries.subst xq = Aq * eisensteinMinusTwo := HSeries_subst_xSeries_eisenstein
  rw [← h, substQ_subst_xq]

theorem Bnd_Fq_aq {r : ℕ} (hF : Bnd 1 (Fq r) BE) : Bnd 1 (aq r) BE := by
  have h := (Bnd_Aq.mul one_pos hF).mul one_pos (Bnd_Eq6i.pow one_pos (7 ^ r))
  rw [aq]
  simpa using h

theorem Bnd_gA_one {r : ℕ} (hF : Bnd 1 (Fq r) BE) : Bnd 1 (gA r) BE := by
  rw [gA, substQ_apply]
  exact Bnd_subst_one qx_constant Bnd_qx (Bnd_Fq_aq hF)

theorem gA_close {ε : ℝ} (hε : 0 < ε) : ∃ R : ℕ, ∀ r, R ≤ r →
    Bnd 1 (gA r - HSeries) ε ∧ Bnd 1 (Fq r) BE := by
  obtain ⟨R1, hR1⟩ := Fq_close hε
  obtain ⟨R2, hR2⟩ := exists_pow_lt_of_lt_one (div_pos hε (by linarith [one_le_BE] :
    (0 : ℝ) < BE)) (by norm_num : (7 : ℝ)⁻¹ < 1)
  refine ⟨max R1 R2, fun r hr => ⟨?_, (hR1 r (le_of_max_le_left hr)).2⟩⟩
  obtain ⟨hc, hF⟩ := hR1 r (le_of_max_le_left hr)
  have e : aq r - Aq * eisensteinMinusTwo =
      Aq * (Fq r - eisensteinMinusTwo) + Aq * Fq r * (Eq6i ^ (7 ^ r) - 1) := by
    rw [aq]; ring
  have h1 : Bnd 1 (Aq * (Fq r - eisensteinMinusTwo)) ε := by
    have := Bnd_Aq.mul one_pos hc; simpa using this
  have h2 : Bnd 1 (Aq * Fq r * (Eq6i ^ (7 ^ r) - 1)) ε := by
    have := (Bnd_Aq.mul one_pos hF).mul one_pos (Bnd_Eq6i_pow_sub r)
    refine this.mono ?_
    have hpow : ((7 : ℝ)⁻¹) ^ (r + 1) ≤ ((7 : ℝ)⁻¹) ^ R2 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num)
        (by have := le_of_max_le_right hr; omega)
    have h3 := (lt_div_iff₀ (by linarith [one_le_BE] : (0 : ℝ) < BE)).mp hR2
    nlinarith [one_le_BE]
  have h4 : Bnd 1 (aq r - Aq * eisensteinMinusTwo) ε := by
    rw [e]; exact h1.add zero_le_one h2
  rw [gA, HSeries_eq_substQ, ← map_sub, substQ_apply]
  exact Bnd_subst_one qx_constant Bnd_qx h4

/-! ### The chain -/

theorem chain_step {g R : ℚ_[7]⟦X⟧} {j : ℕ} (hfix : twistLin (R ^ j * g) = g)
    (hR : ∀ v : ℝ, 0 ≤ v → v ≤ 1 / 4 → Bnd ((7 : ℝ) ^ v) R 1) {B v : ℝ} (hv0 : 0 < v)
    (hv : v ≤ 1 / 4) (hg : Bnd ((7 : ℝ) ^ v) g ((7 : ℝ) ^ (7 / 3 * v) * B)) :
    Bnd ((7 : ℝ) ^ (7 * v)) g ((7 : ℝ) ^ (7 / 3 * (7 * v)) * B) := by
  have hRj := (hR v hv0.le hv).pow (by positivity) j
  rw [one_pow] at hRj
  have h1 := twistLin_near hv0 hv (hRj.mul (by positivity) hg)
  rw [hfix, one_mul] at h1
  have e : (7 : ℝ) ^ (7 / 3 * (7 * v)) = ((7 : ℝ) ^ v) ^ 14 * (7 : ℝ) ^ (7 / 3 * v) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_add (by norm_num)]
    congr 1
    push_cast
    ring
  rw [e, mul_assoc]
  exact h1

theorem chain {g R : ℚ_[7]⟦X⟧} {j : ℕ} (hfix : twistLin (R ^ j * g) = g)
    (hR : ∀ v : ℝ, 0 ≤ v → v ≤ 1 / 4 → Bnd ((7 : ℝ) ^ v) R 1) {B u : ℝ} (hu : 0 < u)
    (hg : Bnd ((7 : ℝ) ^ u) g ((7 : ℝ) ^ (7 / 3 * u) * B)) :
    ∀ m : ℕ, (7 : ℝ) ^ m * u ≤ 1 / 4 →
      Bnd ((7 : ℝ) ^ ((7 : ℝ) ^ (m + 1) * u)) g
        ((7 : ℝ) ^ (7 / 3 * ((7 : ℝ) ^ (m + 1) * u)) * B) := by
  intro m
  induction m with
  | zero =>
    intro h
    rw [pow_zero, one_mul] at h
    rw [zero_add, pow_one]
    exact chain_step hfix hR hu h hg
  | succ m ih =>
    intro h
    have hle : (7 : ℝ) ^ m * u ≤ 1 / 4 := by
      have : (7 : ℝ) ^ m * u ≤ (7 : ℝ) ^ (m + 1) * u := by
        apply mul_le_mul_of_nonneg_right _ hu.le
        exact pow_le_pow_right₀ (by norm_num) (by omega)
      linarith
    have e : (7 : ℝ) ^ (m + 1 + 1) * u = 7 * ((7 : ℝ) ^ (m + 1) * u) := by ring
    rw [e]
    exact chain_step hfix hR (by positivity) h (ih hle)

/-- The uniform bound of the approximants at radius `7^{1/4}`. -/
theorem gA_bound {r : ℕ} (hF : Bnd 1 (Fq r) BE) :
    Bnd ((7 : ℝ) ^ (1 / 4 : ℝ)) (gA r)
      ((7 : ℝ) ^ (7 / 3 * (1 / 4 : ℝ)) * (BE * (7 : ℝ) ^ (1 / 7 : ℝ))) := by
  set u : ℝ := 1 / (4 * (7 : ℝ) ^ (r + 1)) with hu
  have hu0 : 0 < u := by positivity
  have hu4 : u ≤ 1 / 4 := by
    rw [hu]
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
    have : (1 : ℝ) ≤ (7 : ℝ) ^ (r + 1) := one_le_pow₀ (by norm_num)
    linarith
  obtain ⟨p, hp, e⟩ := gA_poly r
  set P := substQ ((Polynomial.aeval xSeries p).map φ7)
  have hρ1 : (1 : ℝ) ≤ (7 : ℝ) ^ u := Real.one_le_rpow (by norm_num) hu0.le
  -- the polynomial at radius `1`, then at radius `7^u`
  have hT1 : Bnd 1 (polyTg (X : ℚ_[7]⟦X⟧)) 1 := by
    have := Bnd_polyTg (s := 0) le_rfl (by norm_num)
    simpa using this
  have hP1 : Bnd 1 P BE := by
    rw [← e]
    have := (Bnd_gA_one hF).mul one_pos (hT1.pow one_pos (7 ^ r))
    simpa using this
  have hPu : Bnd ((7 : ℝ) ^ u) P (BE * ((7 : ℝ) ^ u) ^ (4 * 7 ^ r)) :=
    Bnd_of_deg hρ1 (fun i hi => substQ_aeval_deg p hp i hi) hP1
  have hgu : Bnd ((7 : ℝ) ^ u) (gA r) (BE * ((7 : ℝ) ^ u) ^ (4 * 7 ^ r)) :=
    Bnd_of_dom (by positivity) (polyTg_pow_coeff_zero _) (Bnd_polyTg_pow_sub hu0.le hu4 _) hPu
      (by rw [mul_comm]; exact e)
  have hexp : ((7 : ℝ) ^ u) ^ (4 * 7 ^ r) = (7 : ℝ) ^ (1 / 7 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    congr 1
    rw [hu]
    push_cast
    field_simp
    ring
  rw [hexp] at hgu
  have hstart : Bnd ((7 : ℝ) ^ u) (gA r)
      ((7 : ℝ) ^ (7 / 3 * u) * (BE * (7 : ℝ) ^ (1 / 7 : ℝ))) := by
    refine hgu.mono ?_
    have h1 : (1 : ℝ) ≤ (7 : ℝ) ^ (7 / 3 * u) := Real.one_le_rpow (by norm_num) (by positivity)
    have h2 : 0 ≤ BE * (7 : ℝ) ^ (1 / 7 : ℝ) := by
      have := one_le_BE; positivity
    nlinarith
  have hc := chain (g_fixed r) (fun v hv0 hv => Bnd_rK hv0 hv) hu0 hstart r (by
    rw [hu]
    field_simp
    rw [pow_succ]
    nlinarith [pow_pos (by norm_num : (0 : ℝ) < 7) r])
  have e2 : (7 : ℝ) ^ (r + 1) * u = 1 / 4 := by
    rw [hu]; field_simp
  rw [e2] at hc
  exact hc

/-- **Initial overconvergence of `H` (Coleman's theorem at `κ = -2`, internal).** -/
theorem initial_HSeries_overconvergent :
    ∃ s₀ : ℝ, 0 < s₀ ∧ BoundedAt (fun n => coeff n HSeries) ((7 : ℝ) ^ s₀) := by
  refine ⟨1 / 4, by norm_num, ?_⟩
  set K : ℝ := (7 : ℝ) ^ (7 / 3 * (1 / 4 : ℝ)) * (BE * (7 : ℝ) ^ (1 / 7 : ℝ)) with hK
  have hK0 : 0 < K := by have := one_le_BE; positivity
  refine ⟨K, fun n => ?_⟩
  set ρ : ℝ := (7 : ℝ) ^ (1 / 4 : ℝ)
  have hρn : 0 < ρ ^ n := by positivity
  obtain ⟨R, hR⟩ := gA_close (div_pos hK0 hρn)
  obtain ⟨hc, hF⟩ := hR R le_rfl
  have hb := gA_bound hF n
  have hd : ‖coeff n (gA R - HSeries)‖ ≤ K / ρ ^ n := by simpa using hc n
  have hg : ‖coeff n (gA R)‖ ≤ K / ρ ^ n := by
    rw [le_div_iff₀ hρn]; exact hb
  have hH : ‖coeff n HSeries‖ ≤ K / ρ ^ n := by
    have e : coeff n HSeries = coeff n (gA R) - coeff n (gA R - HSeries) := by
      rw [map_sub]; ring
    rw [e, sub_eq_add_neg]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (by rw [norm_neg]; exact max_le hg hd)
  simp only
  rwa [le_div_iff₀ hρn] at hH

end Zeta7Radius49
