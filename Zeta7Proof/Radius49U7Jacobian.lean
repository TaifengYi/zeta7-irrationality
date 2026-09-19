import Zeta7Proof.Radius49U7Psi
import Zeta7Proof.Radius49Twisted
import Mathlib.RingTheory.PowerSeries.Derivative

/-! Radius internalization, HM: the Jacobian (trace) formula for the twisted `U₇` operator.

Differentiating the proved modular equation `Ψ(x, V x) = 0` with `θ = X d/dX`, using
`θ x = x A` and `θ ∘ V = 7 V ∘ θ`, and reducing `-Y Ψ_Y / Ψ_X` modulo `Ψ` (the explicit
certificate `jacobian_cert`) gives `A · L(x, V x) = 7 · V(x T(x) N(x)² A)` with
`L(Y, X) = Σ_{k<7} a_k(X) Y^k`. Consequently every twisted column is an explicit combination of
seven consecutive weight-zero columns:
`7 X T(X) N(X)² · twistLin (Xⁿ) = Σ_{k<7} a_k(X) · colX (n+k)`  (`twistLin_jacobian`),
where `colX m = U₇(x^m) ∘ q` satisfies `7 colX m = p_m(X)` (`m ≤ 7`) and the recurrence with
`e_k(X)` (`colX_rec`). No published radius input is used. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.style.longLine false
open PowerSeries
namespace Zeta7Radius49
open Zeta7Main

/-- Derivatives `e_k'`. -/
def eKd {R : Type*} [CommRing R] : ℕ → R → R
  | 1, X => 4018 + 845152 * X + 42605745 * X ^ 2 + 896014784 * X ^ 3 + 9281329610 * X ^ 4 + 47455841832 * X ^ 5 + 96889010407 * X ^ 6
  | 2, X => (-8624) + (-579670) * X + (-13714512) * X ^ 2 + (-151531912) * X ^ 3 + (-807072140) * X ^ 4 + (-1694851494) * X ^ 5
  | 3, X => 5915 + 186592 * X + 2319366 * X ^ 2 + 13176688 * X ^ 3 + 28824005 * X ^ 4
  | 4, X => (-1904) + (-31556) * X + (-201684) * X ^ 2 + (-470596) * X ^ 3
  | 5, X => 322 + 2744 * X + 7203 * X ^ 2
  | 6, X => (-28) + (-98) * X
  | 7, X => 1
  | _, _ => 0

/-- The Jacobian numerator coefficients `a_k`. -/
def aJ {R : Type*} [CommRing R] : ℕ → R → R
  | 0, X => 7 * X + 1292424 * X ^ 2 + 7121366 * X ^ 3 + 144943568 * X ^ 4 + 4871256845 * X ^ 5 + 76833267728 * X ^ 6 + 636699211246 * X ^ 7 + 2712892291396 * X ^ 8 + 4747561509943 * X ^ 9
  | 1, X => (-28) * X + 25381020 * X ^ 2 + 155296680 * X ^ 3 + (-298357864) * X ^ 4 + (-19485027380) * X ^ 5 + (-307333070912) * X ^ 6 + (-2546796844984) * X ^ 7 + (-10851569165584) * X ^ 8 + (-18990246039772) * X ^ 9
  | 2, X => 140 * X + 190236032 * X ^ 2 + 1876871304 * X ^ 3 + 10778530784 * X ^ 4 + 111214540892 * X ^ 5 + 1536665354560 * X ^ 6 + 12733984224920 * X ^ 7 + 54257845827920 * X ^ 8 + 94951230198860 * X ^ 9
  | 3, X => (-616) * X + 657230532 * X ^ 2 + 10813758256 * X ^ 3 + 77861049392 * X ^ 4 + (-42567290584) * X ^ 5 + (-6085646764456) * X ^ 6 + (-56029530589648) * X ^ 7 + (-238734521642848) * X ^ 8 + (-417785412874984) * X ^ 9
  | 4, X => 1820 * X + 997444000 * X ^ 2 + 34329305920 * X ^ 3 + 573502168512 * X ^ 4 + 5706714865124 * X ^ 5 + 38895711886304 * X ^ 6 + 198650153908752 * X ^ 7 + 705351995762960 * X ^ 8 + 1234365992585180 * X ^ 9
  | 5, X => 3332 * X + 470852564 * X ^ 2 + 50185298632 * X ^ 3 + 1733571191688 * X ^ 4 + 28573743458988 * X ^ 5 + 254141851624304 * X ^ 6 + 1230102876127272 * X ^ 7 + 2913646320959304 * X ^ 8 + 2259839278732868 * X ^ 9
  | 6, X => (-117208) * X + (-163268) * X ^ 2
  | _, _ => 0

/-- The quotient in the Jacobian certificate. -/
def qJ {R : Type*} [CommRing R] : ℕ → R → R
  | 0, X => (-7) + (-1292424) * X + (-7121366) * X ^ 2 + (-144943568) * X ^ 3 + (-4871256845) * X ^ 4 + (-76833267728) * X ^ 5 + (-636699211246) * X ^ 6 + (-2712892291396) * X ^ 7 + (-4747561509943) * X ^ 8
  | 1, X => (-25381412) * X + (-213112760) * X ^ 2 + 1118606692 * X ^ 3 + 72867084640 * X ^ 4 + 1400270162900 * X ^ 5 + 13667282447616 * X ^ 6 + 67047195201644 * X ^ 7 + 132931722278404 * X ^ 8
  | 2, X => (-190234660) * X + (-3148123972) * X ^ 2 + (-27288920848) * X ^ 3 + (-405496102340) * X ^ 4 + (-6977138650300) * X ^ 5 + (-68027949266172) * X ^ 6 + (-334073307883336) * X ^ 7 + (-664658611392020) * X ^ 8
  | 3, X => (-657237392) * X + (-20013977284) * X ^ 2 + (-205258445532) * X ^ 3 + 275511369392 * X ^ 4 + 27583143114352 * X ^ 5 + 295483799166948 * X ^ 6 + 1457598272562908 * X ^ 7 + 2924497890124888 * X ^ 8
  | 4, X => (-997413816) * X + (-66892263368) * X ^ 2 + (-1635500397076) * X ^ 3 + (-20813952365724) * X ^ 4 + (-168316831770136) * X ^ 5 + (-1000005317697848) * X ^ 6 + (-4185992805624028) * X ^ 7 + (-8640561948096260) * X ^ 8
  | 5, X => (-470941744) * X + (-99714586440) * X ^ 2 + (-5131720436696) * X ^ 3 + (-111976255577732) * X ^ 4 + (-1234136622682992) * X ^ 5 + (-7077548432210536) * X ^ 6 + (-19104187516010632) * X ^ 7 + (-15818874951130076) * X ^ 8
  | _, _ => 0

def polyTg {R : Type*} [CommRing R] (X : R) : R :=
  1 - 490 * X - 21609 * X ^ 2 - 235298 * X ^ 3 - 823543 * X ^ 4
def polyNg {R : Type*} [CommRing R] (X : R) : R := 1 + 245 * X + 2401 * X ^ 2

/-- `∂Ψ/∂X`. -/
def psiX {R : Type*} [CommRing R] (Y X : R) : R :=
  -(eKd 1 X * Y ^ 6) + eKd 2 X * Y ^ 5 - eKd 3 X * Y ^ 4 + eKd 4 X * Y ^ 3 - eKd 5 X * Y ^ 2 +
    eKd 6 X * Y - eKd 7 X

/-- `∂Ψ/∂Y`. -/
def psiY {R : Type*} [CommRing R] (Y X : R) : R :=
  7 * Y ^ 6 - 6 * eK 1 X * Y ^ 5 + 5 * eK 2 X * Y ^ 4 - 4 * eK 3 X * Y ^ 3 + 3 * eK 4 X * Y ^ 2 -
    2 * eK 5 X * Y + eK 6 X

def lJ {R : Type*} [CommRing R] (Y X : R) : R := ∑ k ∈ Finset.range 7, aJ k X * Y ^ k
def qJt {R : Type*} [CommRing R] (Y X : R) : R := ∑ k ∈ Finset.range 6, qJ k X * Y ^ k

/-- **The Jacobian certificate** `-Y Ψ_Y T N² - Ψ_X L = Q Ψ`. -/
theorem jacobian_cert {R : Type*} [CommRing R] (Y X : R) :
    -(Y * psiY Y X * (polyTg X * polyNg X ^ 2)) - psiX Y X * lJ Y X = qJt Y X * psi Y X := by
  simp only [psiY, psiX, lJ, qJt, psi, eK, eKd, aJ, qJ, polyTg, polyNg, Finset.sum_range_succ,
    Finset.sum_range_zero]
  ring

/-! ### Ring homomorphisms and derivations -/

section Maps
variable {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)

theorem eKd_map (k : ℕ) (X : R) : φ (eKd k X) = eKd k (φ X) := by
  rcases k with _ | _ | _ | _ | _ | _ | _ | _ | k <;> simp [eKd, map_ofNat]

theorem aJ_map (k : ℕ) (X : R) : φ (aJ k X) = aJ k (φ X) := by
  rcases k with _ | _ | _ | _ | _ | _ | _ | _ | k <;> simp [aJ, map_ofNat]

theorem psiX_map (Y X : R) : φ (psiX Y X) = psiX (φ Y) (φ X) := by simp [psiX, eKd_map]
theorem polyTg_map (X : R) : φ (polyTg X) = polyTg (φ X) := by simp [polyTg, map_ofNat]
theorem polyNg_map (X : R) : φ (polyNg X) = polyNg (φ X) := by simp [polyNg, map_ofNat]
theorem lJ_map (Y X : R) : φ (lJ Y X) = lJ (φ Y) (φ X) := by simp [lJ, aJ_map]

end Maps

section Deriv
variable {K A : Type*} [CommRing K] [CommRing A] [Algebra K A] (d : Derivation K A A)

theorem d_ofNat (n : ℕ) [n.AtLeastTwo] : d (no_index (OfNat.ofNat n : A)) = 0 := by
  show d ((n : ℕ) : A) = 0
  exact d.map_natCast n

theorem d_eK (k : ℕ) (f : A) : d (eK k f) = eKd k f * d f := by
  rcases k with _ | _ | _ | _ | _ | _ | _ | _ | k <;>
    simp [eK, eKd, Derivation.leibniz, Derivation.leibniz_pow, d_ofNat, smul_eq_mul] <;> ring

theorem d_psi (f g : A) : d (psi f g) = psiY f g * d f + psiX f g * d g := by
  simp only [psi, psiY, psiX, map_add, map_sub, map_neg, Derivation.leibniz, Derivation.leibniz_pow,
    d_eK, smul_eq_mul]
  ring

end Deriv

/-! ### `θ` over `ℚ₇` -/

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

/-- `θ = X d/dX`. -/
def theta (f : ℚ_[7]⟦X⟧) : ℚ_[7]⟦X⟧ := X * derivative ℚ_[7] f

theorem derivative_map_rat (f : ℚ⟦X⟧) :
    derivative ℚ_[7] (f.map (algebraMap ℚ ℚ_[7])) =
      (derivative ℚ f).map (algebraMap ℚ ℚ_[7]) := by
  ext n
  simp [coeff_derivative, map_mul, map_add, map_natCast]

theorem xq_eq : xq = X * xUnit.map (algebraMap ℚ ℚ_[7]) := by
  simp [xq, xSeries, map_mul, map_X]

theorem theta_xq : theta xq = xq * Aq := by
  set u := xUnit.map (algebraMap ℚ ℚ_[7])
  set ui := (xUnit⁻¹).map (algebraMap ℚ ℚ_[7])
  have hinv : u * ui = 1 := by
    rw [← map_mul, PowerSeries.mul_inv_cancel _ (by rw [xUnit_constant]; exact one_ne_zero),
      map_one]
  have hA : Aq = 1 + X * (derivative ℚ xUnit).map (algebraMap ℚ ℚ_[7]) * ui := by
    simp [Aq, ASeries, ui, map_add, map_mul, map_one, map_X]
  rw [theta, xq_eq, hA, Derivation.leibniz, derivative_X, ← derivative_map_rat]
  simp only [smul_eq_mul, mul_one]
  linear_combination (-(X ^ 2 * derivative ℚ_[7] u)) * hinv

theorem vSeven_X {R : Type*} [CommRing R] : vSeven (X : R⟦X⟧) = X ^ 7 := by
  simp [vSeven, vSevenHom, coe_substAlgHom, subst_X hasSubst_X_pow_seven]

theorem vSeven_mul' (f g : ℚ_[7]⟦X⟧) : vSeven (f * g) = vSeven f * vSeven g :=
  map_mul (vSevenHom ℚ_[7]) f g

theorem theta_vSeven (f : ℚ_[7]⟦X⟧) : theta (vSeven f) = 7 * vSeven (theta f) := by
  have hd : derivative ℚ_[7] (vSeven f) = vSeven (derivative ℚ_[7] f) * (7 * X ^ 6) := by
    rw [vSeven, vSevenHom, coe_substAlgHom, derivative_subst hasSubst_X_pow_seven,
      Derivation.leibniz_pow, derivative_X]
    simp [smul_eq_mul, vSeven, vSevenHom, coe_substAlgHom]
  rw [theta, hd, theta, vSeven_mul', vSeven_X]
  ring

/-! ### The Jacobian identity -/

theorem psi_xq : psi xq (vSeven xq) = 0 := by
  have h := congrArg (PowerSeries.map (algebraMap ℚ ℚ_[7])) psi_xSeries_vSeven
  rwa [psi_map, vSeven_map, map_zero] at h

theorem psiX_xq_ne : psiX xq (vSeven xq) ≠ 0 := by
  intro h
  have h0 := congrArg (constantCoeff (R := ℚ_[7])) h
  rw [psiX_map, map_zero] at h0
  have hx : constantCoeff xq = 0 := xq_constant
  have hv : constantCoeff (vSeven xq) = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_vSeven]; simp [xq_constant]
  rw [hx, hv] at h0
  simp [psiX, eKd] at h0

/-- **The Jacobian identity** `A · L(x, V x) = 7 · V(x T(x) N(x)² A)`. -/
theorem jacobian_identity :
    Aq * lJ xq (vSeven xq) = 7 * vSeven (xq * (polyTg xq * polyNg xq ^ 2) * Aq) := by
  have h1 : X * derivative ℚ_[7] xq = xq * Aq := theta_xq
  have h2 : X * derivative ℚ_[7] (vSeven xq) = 7 * (vSeven xq * vSeven Aq) := by
    have := theta_vSeven xq
    rw [theta, theta, h1] at this
    rw [this, vSeven_mul']
  have hθ : psiY xq (vSeven xq) * (xq * Aq) +
      psiX xq (vSeven xq) * (7 * (vSeven xq * vSeven Aq)) = 0 := by
    have h := congrArg (fun f => X * derivative ℚ_[7] f) psi_xq
    simp only [d_psi, map_zero, mul_zero] at h
    linear_combination h - (psiY xq (vSeven xq)) * h1 - (psiX xq (vSeven xq)) * h2
  have hc := jacobian_cert xq (vSeven xq)
  rw [psi_xq, mul_zero] at hc
  have hV : vSeven (xq * (polyTg xq * polyNg xq ^ 2) * Aq) =
      vSeven xq * (polyTg (vSeven xq) * polyNg (vSeven xq) ^ 2) * vSeven Aq := by
    rw [vSeven_mul', vSeven_mul', vSeven_mul',
      show vSeven (polyNg xq ^ 2) = vSeven (polyNg xq) ^ 2 from map_pow (vSevenHom ℚ_[7]) _ 2,
      show vSeven (polyTg xq) = polyTg (vSeven xq) from
        polyTg_map (vSevenHom ℚ_[7]).toRingHom xq,
      show vSeven (polyNg xq) = polyNg (vSeven xq) from
        polyNg_map (vSevenHom ℚ_[7]).toRingHom xq]
  rw [hV]
  apply mul_left_cancel₀ psiX_xq_ne
  linear_combination (-Aq) * hc - (polyTg (vSeven xq) * polyNg (vSeven xq) ^ 2) * hθ

/-! ### The twisted columns -/

theorem uSeven_sum {R : Type*} [CommRing R] (s : Finset ℕ) (f : ℕ → R⟦X⟧) :
    uSeven (∑ k ∈ s, f k) = ∑ k ∈ s, uSeven (f k) := by
  ext n; simp [coeff_uSeven, map_sum]

/-- `7 x T(x) N(x)² · A U₇(xⁿ / A) = Σ_k a_k(x) U₇(x^{n+k})`. -/
theorem twist_q_identity (n : ℕ) :
    7 * (xq * (polyTg xq * polyNg xq ^ 2)) * (Aq * uSeven (xq ^ n * Aq⁻¹)) =
      ∑ k ∈ Finset.range 7, aJ k xq * uSeven (xq ^ (n + k)) := by
  have hstep : 7 * (xq * (polyTg xq * polyNg xq ^ 2)) * (Aq * uSeven (xq ^ n * Aq⁻¹)) =
      uSeven (vSeven (7 * (xq * (polyTg xq * polyNg xq ^ 2) * Aq)) * (xq ^ n * Aq⁻¹)) := by
    rw [uSeven_vSeven_mul]; ring
  have h7 : vSeven (7 * (xq * (polyTg xq * polyNg xq ^ 2) * Aq)) =
      7 * vSeven (xq * (polyTg xq * polyNg xq ^ 2) * Aq) := by
    rw [vSeven_mul', show vSeven (7 : ℚ_[7]⟦X⟧) = 7 from map_ofNat (vSevenHom ℚ_[7]) 7]
  rw [hstep, h7, ← jacobian_identity]
  have hcancel : Aq * lJ xq (vSeven xq) * (xq ^ n * Aq⁻¹) = lJ xq (vSeven xq) * xq ^ n := by
    rw [show Aq * lJ xq (vSeven xq) * (xq ^ n * Aq⁻¹) =
      lJ xq (vSeven xq) * xq ^ n * (Aq * Aq⁻¹) by ring, Aq_mul_inv, mul_one]
  rw [hcancel, lJ, Finset.sum_mul, uSeven_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [show aJ k (vSeven xq) = vSeven (aJ k xq) from
      (aJ_map (vSevenHom ℚ_[7]).toRingHom k xq).symm,
    show vSeven (aJ k xq) * xq ^ k * xq ^ n = vSeven (aJ k xq) * xq ^ (n + k) by ring,
    uSeven_vSeven_mul]

/-- The weight-zero columns in the coordinate `X = x`. -/
def colX (m : ℕ) : ℚ_[7]⟦X⟧ := (uSeven (xq ^ m)).subst qx

/-- Substitution of `q(x)` as a ring homomorphism. -/
def substQ : ℚ_[7]⟦X⟧ →+* ℚ_[7]⟦X⟧ := (substAlgHom (R := ℚ_[7]) hasSubst_qx).toRingHom

theorem substQ_apply (f : ℚ_[7]⟦X⟧) : substQ f = f.subst qx := by
  simp [substQ, coe_substAlgHom]

theorem xq_subst_qx : xq.subst qx = X := by
  have hq : HasSubst qSeries := HasSubst.of_constantCoeff_zero' qSeries_constant
  calc xq.subst qx = (xSeries.subst qSeries).map (algebraMap ℚ ℚ_[7]) :=
        (map_subst (h := algebraMap ℚ ℚ_[7]) hq xSeries).symm
    _ = X := by rw [x_subst_q]; exact PowerSeries.map_X _

theorem substQ_xq : substQ xq = X := by rw [substQ_apply, xq_subst_qx]

/-- **The twisted columns via seven weight-zero columns.** -/
theorem twistLin_jacobian (n : ℕ) :
    7 * (X * (polyTg X * polyNg X ^ 2)) * twistLin (X ^ n) =
      ∑ k ∈ Finset.range 7, aJ k X * colX (n + k) := by
  have h := congrArg substQ (twist_q_identity n)
  have hXn : (X ^ n : ℚ_[7]⟦X⟧).subst xq = xq ^ n := by
    rw [subst_pow hasSubst_xq, subst_X hasSubst_xq]
  rw [twistLin_apply, hXn, ← substQ_apply, map_mul]
  simp only [map_mul, map_sum, map_pow, map_ofNat, polyTg_map, polyNg_map, aJ_map, substQ_xq] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro k _
  rw [colX, ← substQ_apply]

/-! ### Facts about the weight-zero columns -/

theorem colX_zero : colX 0 = 1 := by
  have h1 : uSeven (1 : ℚ_[7]⟦X⟧) = 1 := by
    ext n; simp [coeff_uSeven, coeff_one]
  rw [colX, pow_zero, h1, ← substQ_apply, map_one]

theorem colX_small (m : ℕ) (hm : 1 ≤ m ∧ m ≤ 7) : 7 * colX m = pM m X := by
  have hQ : 7 * uSeven (xSeries ^ m) = pM m xSeries := by
    obtain ⟨h1, h7⟩ := hm
    interval_cases m
    exacts [seven_uSeven_x_pow_1, seven_uSeven_x_pow_2, seven_uSeven_x_pow_3,
      seven_uSeven_x_pow_4, seven_uSeven_x_pow_5, seven_uSeven_x_pow_6, seven_uSeven_x_pow_7]
  have hmap := congrArg (PowerSeries.map (algebraMap ℚ ℚ_[7])) hQ
  rw [map_mul, ← uSeven_map, map_pow, pM_map, map_ofNat] at hmap
  change 7 * uSeven (xq ^ m) = pM m xq at hmap
  have h := congrArg substQ hmap
  rw [map_mul, map_ofNat, pM_map, substQ_xq] at h
  rw [colX, ← substQ_apply]
  exact h

theorem colX_rec (m : ℕ) :
    colX (m + 7) =
      eK 1 X * colX (m + 6) - eK 2 X * colX (m + 5) + eK 3 X * colX (m + 4) -
        eK 4 X * colX (m + 3) + eK 5 X * colX (m + 2) - eK 6 X * colX (m + 1) +
        eK 7 X * colX m := by
  have hR := congrArg (PowerSeries.map (algebraMap ℚ ℚ_[7])) (uSeven_x_pow_recurrence m)
  simp only [map_add, map_sub, map_mul, ← uSeven_map, map_pow, eK_map,
    show xSeries.map (algebraMap ℚ ℚ_[7]) = xq from rfl] at hR
  have h := congrArg substQ hR
  simp only [map_add, map_sub, map_mul, eK_map, substQ_xq] at h
  simp only [colX, ← substQ_apply]
  exact h

end Zeta7Radius49
