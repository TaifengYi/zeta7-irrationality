import Zeta7Proof.AuxiliaryJointFourth

/-! P6, the algebra of the third layer in characteristic `p`.

* `Γ, DΓ, D²Γ` have polynomial numerators of degree `≤ 4σ + 4` over `P̄^{2σ+2}`.
* **Identity (33) in cleared form.** For every polynomial `a`,
  `S(P̄a, Γ) = P̄^{-2σ} 𝒥(a)` with the explicit polynomial
  `𝒥(a) = Q̄·D(N₁(a)) - (DQ̄)·N₁(a)`, `N₁(a) = Q̄(P̄·Da + (1+2σ)(DP̄)a) - 2P̄(DQ̄)a`.
  The only analytic input is the proved cleared Riccati identity of `Γ`.
* `𝒥` is linear, commutes with multiplication by `x^p`, and kills `A₀ = Q̄²P̄^{p-2σ-1}`.
* Using the negative resonance and the proportionality (29), `deg 𝒥(ā⁺) ≤ 4σ + 2`. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
namespace Zeta7Auxiliary
open PowerSeries Zeta7Common

variable {p : ℕ} [Fact p.Prime]

/-- `σ`-weight `m = 2σ`. -/
abbrev gm (p : ℕ) : ℕ := 2 * ((p - 1) / 3)

/-- The inverse series `P̄⁻¹`. -/
abbrev Pinv (p : ℕ) [Fact p.Prime] : PowerSeries (ZMod p) := (reducedP p)⁻¹

theorem hassePolyP_coe' :
    ((hassePolyP : Polynomial (ZMod p)) : PowerSeries (ZMod p)) = reducedP p :=
  hassePolyP_coe_reducedP p

theorem P_mul_Pinv :
    ((hassePolyP : Polynomial (ZMod p)) : PowerSeries (ZMod p)) * Pinv p = 1 := by
  rw [hassePolyP_coe']; exact reducedP_mul_inv p

theorem euler_one_zmod : euler (1 : PowerSeries (ZMod p)) = 0 := euler_one_gen

theorem euler_sub_gen {R : Type*} [CommRing R] (a b : PowerSeries R) :
    euler (a - b) = euler a - euler b := by
  simp [euler, mul_sub]

/-- Derivative of an inverse. -/
theorem euler_inv_of_mul {f g : PowerSeries (ZMod p)} (h : f * g = 1) :
    euler g = -(euler f) * g ^ 2 := by
  have hd := congrArg euler h
  rw [euler_mul_general, euler_one_zmod] at hd
  linear_combination g * hd - euler g * h

theorem euler_pow_inv_of_mul {f g : PowerSeries (ZMod p)} (h : f * g = 1) (k : ℕ) :
    euler (g ^ k) = -((k : PowerSeries (ZMod p)) * euler f * g ^ (k + 1)) := by
  induction k with
  | zero => simp [euler_one_zmod]
  | succ k ih =>
    rw [pow_succ, euler_mul_general, ih, euler_inv_of_mul h]
    push_cast
    ring

theorem coeC_nat (k : ℕ) :
    ((Polynomial.C (k : ZMod p) : Polynomial (ZMod p)) : PowerSeries (ZMod p)) = (k : PowerSeries (ZMod p)) := by
  rw [Polynomial.coe_C, map_natCast]

theorem euler_natCast_gen (n : ℕ) : euler (n : PowerSeries (ZMod p)) = 0 := by
  rw [← map_natCast (C (R := ZMod p)) n, euler_C_gen]

/-- **Fraction rule**: `D(R P̄^{-k}) = (P̄ DR - k R DP̄) P̄^{-(k+1)}`. -/
theorem euler_frac (R : Polynomial (ZMod p)) (k : ℕ) :
    euler ((R : PowerSeries (ZMod p)) * Pinv p ^ k) =
      ((hassePolyP * eulerPoly R - Polynomial.C (k : ZMod p) * R * eulerPoly hassePolyP :
        Polynomial (ZMod p)) : PowerSeries (ZMod p)) * Pinv p ^ (k + 1) := by
  have hP := P_mul_Pinv (p := p)
  rw [euler_mul_general, euler_pow_inv_of_mul hP, ← eulerPoly_coe]
  simp only [Polynomial.coe_sub, Polynomial.coe_mul, coeC_nat, ← eulerPoly_coe]
  linear_combination (-(((eulerPoly R : Polynomial (ZMod p)) : PowerSeries (ZMod p)) * Pinv p ^ k)) * hP

/-! ### The numerators of `Γ, DΓ, D²Γ` -/

theorem gamma_eq (hp : 5 ≤ p) :
    hasseGammaSeries p hp =
      (((reducedQuotient p hp) ^ 2 : Polynomial (ZMod p)) : PowerSeries (ZMod p)) *
        Pinv p ^ gm p := by
  rw [hasseGammaSeries, Polynomial.coe_pow]

def gammaR1 (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) : Polynomial (ZMod p) :=
  hassePolyP * eulerPoly ((reducedQuotient p hp) ^ 2) -
    Polynomial.C (gm p : ZMod p) * (reducedQuotient p hp) ^ 2 * eulerPoly hassePolyP

def gammaR2 (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) : Polynomial (ZMod p) :=
  hassePolyP * eulerPoly (gammaR1 p hp) -
    Polynomial.C ((gm p + 1 : ℕ) : ZMod p) * gammaR1 p hp * eulerPoly hassePolyP

theorem euler_gamma (hp : 5 ≤ p) :
    euler (hasseGammaSeries p hp) =
      ((gammaR1 p hp : Polynomial (ZMod p)) : PowerSeries (ZMod p)) * Pinv p ^ (gm p + 1) := by
  rw [gamma_eq, euler_frac]
  rfl

theorem euler_euler_gamma (hp : 5 ≤ p) :
    euler (euler (hasseGammaSeries p hp)) =
      ((gammaR2 p hp : Polynomial (ZMod p)) : PowerSeries (ZMod p)) * Pinv p ^ (gm p + 2) := by
  rw [euler_gamma, euler_frac]
  rfl

/-- Numerators over the common denominator `P̄^{2σ+2}`. -/
def gammaNum (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) : Fin 3 → Polynomial (ZMod p) :=
  ![(reducedQuotient p hp) ^ 2 * hassePolyP ^ 2, gammaR1 p hp * hassePolyP, gammaR2 p hp]

theorem eulerIter_gamma (hp : 5 ≤ p) (k : Fin 3) :
    (euler^[k.val]) (hasseGammaSeries p hp) =
      ((gammaNum p hp k : Polynomial (ZMod p)) : PowerSeries (ZMod p)) * Pinv p ^ (gm p + 2) := by
  have hP := P_mul_Pinv (p := p)
  fin_cases k
  · show hasseGammaSeries p hp = _
    rw [gamma_eq]
    show _ = (((reducedQuotient p hp) ^ 2 * hassePolyP ^ 2 : Polynomial (ZMod p)) :
      PowerSeries (ZMod p)) * _
    rw [Polynomial.coe_mul, Polynomial.coe_pow, Polynomial.coe_pow]
    linear_combination
      (-(((reducedQuotient p hp : Polynomial (ZMod p)) : PowerSeries (ZMod p)) ^ 2 * Pinv p ^ gm p *
        (1 + ((hassePolyP : Polynomial (ZMod p)) : PowerSeries (ZMod p)) * Pinv p))) * hP
  · show euler (hasseGammaSeries p hp) = _
    rw [euler_gamma]
    show _ = ((gammaR1 p hp * hassePolyP : Polynomial (ZMod p)) : PowerSeries (ZMod p)) * _
    rw [Polynomial.coe_mul]
    linear_combination
      (-(((gammaR1 p hp : Polynomial (ZMod p)) : PowerSeries (ZMod p)) * Pinv p ^ (gm p + 1))) * hP
  · exact euler_euler_gamma hp

theorem natDegree_mul_le' {f g : Polynomial (ZMod p)} {a b : ℕ} (hf : f.natDegree ≤ a)
    (hg : g.natDegree ≤ b) : (f * g).natDegree ≤ a + b :=
  Polynomial.natDegree_mul_le.trans (Nat.add_le_add hf hg)

theorem natDegree_sub_le' {f g : Polynomial (ZMod p)} {a : ℕ} (hf : f.natDegree ≤ a)
    (hg : g.natDegree ≤ a) : (f - g).natDegree ≤ a :=
  (Polynomial.natDegree_sub_le _ _).trans (max_le hf hg)

theorem natDegree_C_mul_le' (c : ZMod p) {f : Polynomial (ZMod p)} {a : ℕ}
    (hf : f.natDegree ≤ a) : (Polynomial.C c * f).natDegree ≤ a :=
  (Polynomial.natDegree_C_mul_le _ _).trans hf

theorem hassePolyP_natDegree_le : (hassePolyP : Polynomial (ZMod p)).natDegree ≤ 2 := by
  rw [← redZ_intPolyP]
  exact Polynomial.natDegree_map_le.trans intPolyP_natDegree

theorem reducedQuotient_natDegree_le (hp : 11 ≤ p) :
    (reducedQuotient p (by omega)).natDegree ≤ gm p := (reducedQuotient_degree p hp).le

theorem gammaR1_natDegree (hp : 11 ≤ p) : (gammaR1 p (by omega)).natDegree ≤ 2 * gm p + 2 := by
  have hQ := reducedQuotient_natDegree_le (p := p) hp
  have hQ2 : ((reducedQuotient p (by omega)) ^ 2).natDegree ≤ 2 * gm p :=
    Polynomial.natDegree_pow_le.trans (by omega)
  have hP := hassePolyP_natDegree_le (p := p)
  unfold gammaR1
  apply natDegree_sub_le'
  · have := natDegree_mul_le' hP ((eulerPoly_natDegree_le _).trans hQ2); omega
  · have := natDegree_mul_le' (natDegree_C_mul_le' (gm p : ZMod p) hQ2)
      ((eulerPoly_natDegree_le hassePolyP).trans hP)
    omega

theorem gammaR2_natDegree (hp : 11 ≤ p) : (gammaR2 p (by omega)).natDegree ≤ 2 * gm p + 4 := by
  have h1 := gammaR1_natDegree (p := p) hp
  have hP := hassePolyP_natDegree_le (p := p)
  unfold gammaR2
  apply natDegree_sub_le'
  · have := natDegree_mul_le' hP ((eulerPoly_natDegree_le _).trans h1); omega
  · have := natDegree_mul_le' (natDegree_C_mul_le' ((gm p + 1 : ℕ) : ZMod p) h1)
      ((eulerPoly_natDegree_le hassePolyP).trans hP)
    omega

theorem gammaNum_natDegree (hp : 11 ≤ p) (k : Fin 3) :
    (gammaNum p (by omega) k).natDegree ≤ 2 * gm p + 4 := by
  have hQ := reducedQuotient_natDegree_le (p := p) hp
  have hP := hassePolyP_natDegree_le (p := p)
  fin_cases k
  · show ((reducedQuotient p _) ^ 2 * hassePolyP ^ 2).natDegree ≤ _
    have := natDegree_mul_le' (Polynomial.natDegree_pow_le.trans (Nat.mul_le_mul_left 2 hQ))
      (Polynomial.natDegree_pow_le.trans (Nat.mul_le_mul_left 2 hP))
    omega
  · show (gammaR1 p _ * hassePolyP).natDegree ≤ _
    have := natDegree_mul_le' (gammaR1_natDegree hp) hP
    omega
  · exact gammaR2_natDegree hp

/-! ### The uncleared Riccati identity -/

theorem gamma_riccati (hp : 11 ≤ p) :
    2 * hasseGammaSeries p (by omega) * euler (euler (hasseGammaSeries p (by omega))) -
      (euler (hasseGammaSeries p (by omega)))^2 -
      redV2 p * (hasseGammaSeries p (by omega))^2 = 0 := by
  set G := hasseGammaSeries p (by omega) with hG
  have hR := hasseGammaSeries_clearedRiccati p (by omega)
  change clearedRiccati G = 0 at hR
  unfold clearedRiccati hasseP hasseW at hR
  have hPV := redV2_band (p := p)
  unfold bandP bandW at hPV
  have hP2 : IsUnit ((1 + 13 * X + 49 * X^2 : PowerSeries (ZMod p))^2) := by
    apply IsUnit.pow
    exact (bandP_isUnit (R := ZMod p))
  apply hP2.mul_left_cancel
  rw [mul_zero]
  linear_combination hR - G^2 * hPV

/-! ### The polynomial `𝒥` -/

/-- `N₁(a) = Q̄(P̄·Da + (1+2σ)(DP̄)a) - 2P̄(DQ̄)a`. -/
def N1poly (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (a : Polynomial (ZMod p)) : Polynomial (ZMod p) :=
  reducedQuotient p hp * (hassePolyP * eulerPoly a +
      Polynomial.C ((gm p + 1 : ℕ) : ZMod p) * eulerPoly hassePolyP * a) -
    Polynomial.C 2 * hassePolyP * eulerPoly (reducedQuotient p hp) * a

/-- `𝒥(a) = Q̄·D N₁(a) - (DQ̄) N₁(a)`. -/
def Jpoly (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (a : Polynomial (ZMod p)) : Polynomial (ZMod p) :=
  reducedQuotient p hp * eulerPoly (N1poly p hp a) -
    eulerPoly (reducedQuotient p hp) * N1poly p hp a

theorem reducedQuotient_unit (hp : 5 ≤ p) :
    ((reducedQuotient p hp : Polynomial (ZMod p)) : PowerSeries (ZMod p)) *
      ((reducedQuotient p hp : Polynomial (ZMod p)) : PowerSeries (ZMod p))⁻¹ = 1 := by
  apply PowerSeries.mul_inv_cancel
  rw [Polynomial.constantCoeff_coe, reducedQuotient_constant]
  exact one_ne_zero

theorem J_algebra {R : Type*} [CommRing R] (q qi P Pi A eq e2q eP e2P eA e2A m : R)
    (hq : q * qi = 1) (hP : P * Pi = 1) :
    q ^ 2 * ((e2P * A + 2 * eP * eA + P * e2A) -
        (2 * eq * qi - m * eP * Pi) * (eP * A + P * eA) -
        (2 * e2q * qi - 2 * eq ^ 2 * qi ^ 2 - m * e2P * Pi + m * eP ^ 2 * Pi ^ 2) * (P * A)) =
      q * (eq * (P * eA + (1 + m) * eP * A) +
          q * (eP * eA + P * e2A + (1 + m) * (e2P * A + eP * eA)) -
          2 * (eP * eq * A + P * e2q * A + P * eq * eA)) -
        eq * (q * (P * eA + (1 + m) * eP * A) - 2 * P * eq * A) := by
  linear_combination
    (-(2 * q * eq * eP * A) - 2 * q * eq * P * eA -
      2 * q * e2q * P * A + 2 * eq ^ 2 * P * A * (q * qi + 1)) * hq +
    (q ^ 2 * (m * eP * eA + m * e2P * A - m * eP ^ 2 * A * Pi)) * hP

/-- The series form of `𝒥`. -/
def Jform (q P A : PowerSeries (ZMod p)) (m : ℕ) : PowerSeries (ZMod p) :=
  q * euler (q * (P * euler A + (1 + (m : PowerSeries (ZMod p))) * euler P * A) -
      2 * P * euler q * A) -
    euler q * (q * (P * euler A + (1 + (m : PowerSeries (ZMod p))) * euler P * A) -
      2 * P * euler q * A)

theorem Jpoly_coe (hp : 5 ≤ p) (a : Polynomial (ZMod p)) :
    ((Jpoly p hp a : Polynomial (ZMod p)) : PowerSeries (ZMod p)) =
      Jform (reducedQuotient p hp : PowerSeries (ZMod p))
        ((hassePolyP : Polynomial (ZMod p)) : PowerSeries (ZMod p))
        (a : PowerSeries (ZMod p)) (gm p) := by
  have h2 : ((Polynomial.C (2 : ZMod p) : Polynomial (ZMod p)) : PowerSeries (ZMod p)) = 2 := by
    rw [Polynomial.coe_C, map_ofNat]
  simp only [Jpoly, N1poly, Jform, Polynomial.coe_sub, Polynomial.coe_mul,
    Polynomial.coe_add, coeC_nat, h2, eulerPoly_coe]
  push_cast
  ring

/-- **Identity (33)**: `S(P̄a, Γ) = P̄^{-2σ} 𝒥(a)` in `𝔽_p[[x]]`. -/
theorem gamma_concomitant (hp : 11 ≤ p) (a : Polynomial (ZMod p)) :
    concomitant (redV2 p) (0 : ZMod p) (hasseGammaSeries p (by omega))
        (((hassePolyP * a : Polynomial (ZMod p))) : PowerSeries (ZMod p)) =
      Pinv p ^ gm p * ((Jpoly p (by omega) a : Polynomial (ZMod p)) : PowerSeries (ZMod p)) := by
  have hp5 : 5 ≤ p := by omega
  set G := hasseGammaSeries p hp5 with hGdef
  set P : PowerSeries (ZMod p) := ((hassePolyP : Polynomial (ZMod p)) : PowerSeries (ZMod p))
    with hPdef
  set Pi := Pinv p with hPidef
  set q : PowerSeries (ZMod p) := ((reducedQuotient p hp5 : Polynomial (ZMod p)) :
    PowerSeries (ZMod p)) with hqdef
  set qi := q⁻¹ with hqidef
  set A : PowerSeries (ZMod p) := ((a : Polynomial (ZMod p)) : PowerSeries (ZMod p)) with hAdef
  set m : PowerSeries (ZMod p) := ((gm p : ℕ) : PowerSeries (ZMod p)) with hmdef
  have hP : P * Pi = 1 := P_mul_Pinv
  have hq : q * qi = 1 := reducedQuotient_unit hp5
  have hDPi : euler Pi = -(euler P) * Pi ^ 2 := euler_inv_of_mul hP
  have hDqi : euler qi = -(euler q) * qi ^ 2 := euler_inv_of_mul hq
  have hDPim : euler (Pi ^ gm p) = -(m * euler P * Pi ^ (gm p + 1)) :=
    euler_pow_inv_of_mul hP _
  have hm : euler m = 0 := by rw [hmdef]; exact euler_natCast_gen _
  have hG : G = q ^ 2 * Pi ^ gm p := by
    rw [hGdef, gamma_eq, Polynomial.coe_pow]
  set u := 2 * euler q * qi - m * euler P * Pi with hudef
  have h2 : euler (2 : PowerSeries (ZMod p)) = 0 := euler_ofNat_gen 2
  have hDG : euler G = G * u := by
    rw [hG, euler_mul_general, hDPim, pow_two, euler_mul_general, hudef]
    linear_combination (-(2 * q * euler q * Pi ^ gm p)) * hq
  have hDu : euler u = 2 * euler (euler q) * qi - 2 * (euler q) ^ 2 * qi ^ 2 -
      m * euler (euler P) * Pi + m * (euler P) ^ 2 * Pi ^ 2 := by
    rw [hudef, euler_sub_gen, euler_mul_general, euler_mul_general, euler_mul_general,
      euler_mul_general, hDqi, hDPi, h2, hm]
    ring
  have hD2G : euler (euler G) = G * (u ^ 2 + euler u) := by
    rw [hDG, euler_mul_general, hDG]
    ring
  have hRic0 := gamma_riccati (p := p) hp
  rw [← hGdef, hD2G, hDG] at hRic0
  have hGu : IsUnit (G ^ 2) := by
    apply IsUnit.pow
    apply PowerSeries.isUnit_iff_constantCoeff.mpr
    rw [hGdef, hasseGammaSeries_constant]
    exact isUnit_one
  have hRic : u ^ 2 + 2 * euler u - redV2 p = 0 := by
    apply hGu.mul_left_cancel
    rw [mul_zero]
    linear_combination hRic0
  -- step 1
  have hv : ((hassePolyP * a : Polynomial (ZMod p)) : PowerSeries (ZMod p)) = P * A := by
    rw [Polynomial.coe_mul]
  rw [hv]
  have hconc : concomitant (redV2 p) (0 : ZMod p) G (P * A) =
      G * (euler (euler (P * A)) - u * euler (P * A) - euler u * (P * A)) := by
    unfold concomitant
    simp only [thetaS_zero_eq]
    rw [hD2G, hDG]
    linear_combination (G * (P * A)) * hRic
  rw [hconc, Jpoly_coe hp5 a, Jform, ← hPdef, ← hqdef, ← hAdef, ← hmdef, hG]
  have key := J_algebra q qi P Pi A (euler q) (euler (euler q)) (euler P) (euler (euler P))
    (euler A) (euler (euler A)) m hq hP
  simp only [euler_mul_general, euler_sub_gen, euler_add_gen, hDu, h2, hm, euler_one_zmod]
  linear_combination Pi ^ gm p * key

/-! ### Algebraic properties of `𝒥` -/

theorem eulerPoly_add (f g : Polynomial (ZMod p)) :
    eulerPoly (f + g) = eulerPoly f + eulerPoly g := by
  simp [eulerPoly, mul_add]

theorem eulerPoly_sub (f g : Polynomial (ZMod p)) :
    eulerPoly (f - g) = eulerPoly f - eulerPoly g := by
  simp [eulerPoly, mul_sub]

theorem eulerPoly_mul (f g : Polynomial (ZMod p)) :
    eulerPoly (f * g) = eulerPoly f * g + f * eulerPoly g := by
  simp only [eulerPoly, Polynomial.derivative_mul]
  ring

theorem eulerPoly_C (c : ZMod p) : eulerPoly (Polynomial.C c) = 0 := by
  simp [eulerPoly]

theorem eulerPoly_X_pow_p : eulerPoly (Polynomial.X ^ p : Polynomial (ZMod p)) = 0 := by
  simp [eulerPoly, Polynomial.derivative_X_pow]

theorem eulerPoly_pow_succ (f : Polynomial (ZMod p)) (k : ℕ) :
    eulerPoly (f ^ (k + 1)) = Polynomial.C ((k + 1 : ℕ) : ZMod p) * f ^ k * eulerPoly f := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, eulerPoly_mul, ih]
    simp only [Nat.cast_add, Nat.cast_one, map_add, map_one]
    ring

theorem N1poly_sub (hp : 5 ≤ p) (a b : Polynomial (ZMod p)) :
    N1poly p hp (a - b) = N1poly p hp a - N1poly p hp b := by
  simp only [N1poly, eulerPoly_sub]
  ring

theorem Jpoly_sub (hp : 5 ≤ p) (a b : Polynomial (ZMod p)) :
    Jpoly p hp (a - b) = Jpoly p hp a - Jpoly p hp b := by
  simp only [Jpoly, N1poly_sub, eulerPoly_sub]
  ring

theorem N1poly_C_mul (hp : 5 ≤ p) (c : ZMod p) (a : Polynomial (ZMod p)) :
    N1poly p hp (Polynomial.C c * a) = Polynomial.C c * N1poly p hp a := by
  simp only [N1poly, eulerPoly_mul, eulerPoly_C]
  ring

theorem Jpoly_C_mul (hp : 5 ≤ p) (c : ZMod p) (a : Polynomial (ZMod p)) :
    Jpoly p hp (Polynomial.C c * a) = Polynomial.C c * Jpoly p hp a := by
  simp only [Jpoly, N1poly_C_mul, eulerPoly_mul, eulerPoly_C]
  ring

theorem N1poly_X_pow_mul (hp : 5 ≤ p) (a : Polynomial (ZMod p)) :
    N1poly p hp (Polynomial.X ^ p * a) = Polynomial.X ^ p * N1poly p hp a := by
  simp only [N1poly, eulerPoly_mul, eulerPoly_X_pow_p]
  ring

/-- `𝒥` commutes with multiplication by `x^p` in characteristic `p`. -/
theorem Jpoly_X_pow_mul (hp : 5 ≤ p) (a : Polynomial (ZMod p)) :
    Jpoly p hp (Polynomial.X ^ p * a) = Polynomial.X ^ p * Jpoly p hp a := by
  simp only [Jpoly, N1poly_X_pow_mul, eulerPoly_mul, eulerPoly_X_pow_p]
  ring

/-- `N₁(A₀) = 0`: the homogeneous Laurent polynomial `w₀` satisfies `(D - ū) w₀ = 0`. -/
theorem N1poly_homA0 (hp : 11 ≤ p) : N1poly p (by omega) (homA0 p (by omega)) = 0 := by
  have hk : p - 2 * ((p - 1) / 3) - 1 = (p - 2 * ((p - 1) / 3) - 2) + 1 := by omega
  have hsum : Polynomial.C (((p - 2 * ((p - 1) / 3) - 2 + 1 : ℕ)) : ZMod p) +
      Polynomial.C ((gm p + 1 : ℕ) : ZMod p) = 0 := by
    rw [← map_add, ← Nat.cast_add, show p - 2 * ((p - 1) / 3) - 2 + 1 + (2 * ((p - 1) / 3) + 1) = p by omega,
      ZMod.natCast_self, map_zero]
  unfold N1poly homA0
  rw [hk]
  simp only [eulerPoly_mul, eulerPoly_pow_succ, pow_two]
  rw [show (Polynomial.C (2 : ZMod p)) = 2 from map_ofNat _ 2]
  linear_combination
    ((reducedQuotient p (by omega)) ^ 3 * hassePolyP ^ (p - 2 * ((p - 1) / 3) - 2 + 1) *
      eulerPoly hassePolyP) * hsum

theorem Jpoly_homA0 (hp : 11 ≤ p) : Jpoly p (by omega) (homA0 p (by omega)) = 0 := by
  simp only [Jpoly, N1poly_homA0 hp, eulerPoly]
  simp

theorem natDegree_C_le (c : ZMod p) : (Polynomial.C c).natDegree ≤ 0 := by simp

theorem N1poly_natDegree (hp : 11 ≤ p) (a : Polynomial (ZMod p)) :
    (N1poly p (by omega) a).natDegree ≤ a.natDegree + gm p + 2 := by
  have hQ := reducedQuotient_natDegree_le (p := p) hp
  have hP := hassePolyP_natDegree_le (p := p)
  have ha := eulerPoly_natDegree_le a
  have hQe := (eulerPoly_natDegree_le (reducedQuotient p (by omega))).trans hQ
  have hPe := (eulerPoly_natDegree_le (hassePolyP : Polynomial (ZMod p))).trans hP
  unfold N1poly
  apply natDegree_sub_le'
  · have h1 := natDegree_mul_le' hP ha
    have h2 := natDegree_mul_le' (natDegree_mul_le' (natDegree_C_le ((gm p + 1 : ℕ) : ZMod p))
      hPe) (le_refl a.natDegree)
    have h3 := (Polynomial.natDegree_add_le _ _).trans (max_le (h1.trans (by omega : 2 + a.natDegree ≤ a.natDegree + 2))
      (h2.trans (by omega : 0 + 2 + a.natDegree ≤ a.natDegree + 2)))
    have := natDegree_mul_le' hQ h3
    omega
  · have := natDegree_mul_le' (natDegree_mul_le' (natDegree_mul_le'
      (natDegree_C_le (2 : ZMod p)) hP) hQe) (le_refl a.natDegree)
    omega

theorem Jpoly_natDegree (hp : 11 ≤ p) (a : Polynomial (ZMod p)) :
    (Jpoly p (by omega) a).natDegree ≤ a.natDegree + 2 * gm p + 2 := by
  have hQ := reducedQuotient_natDegree_le (p := p) hp
  have hQe := (eulerPoly_natDegree_le (reducedQuotient p (by omega))).trans hQ
  have hN := N1poly_natDegree hp a
  unfold Jpoly
  apply natDegree_sub_le'
  · have := natDegree_mul_le' hQ ((eulerPoly_natDegree_le _).trans hN); omega
  · have := natDegree_mul_le' hQe hN; omega

/-- The reduced positive numerator `ā⁺`. -/
abbrev redPosA (p : ℕ) [Fact p.Prime] : Polynomial (ZMod p) := redZ p (posAPoly p)

/-- The polynomial form of (29): `ã⁻ - A₀ = λ x^p ā⁺`. -/
theorem resonance_proportional_poly (hp : 11 ≤ p) :
    redZ p (negAPoly p) - homA0 p (by omega) =
      Polynomial.X ^ p * (Polynomial.C (resLambda p hp) * redPosA p) := by
  have h := (resonance_proportional (p := p) hp).1
  rw [← negAPoly_coe, ← posAPoly_coe, zred_coe, zred_coe] at h
  apply Polynomial.coe_injective (R := ZMod p)
  simp only [Polynomial.coe_sub, Polynomial.coe_mul, Polynomial.coe_pow, Polynomial.coe_X,
    Polynomial.coe_C]
  exact h

/-- **Degree bound (33)**: `deg 𝒥(ā⁺) ≤ 4σ + 2`, from the negative resonance at infinity. -/
theorem Jpoly_posA_natDegree (hp : 11 ≤ p) :
    (Jpoly p (by omega) (redPosA p)).natDegree ≤ 2 * gm p + 2 := by
  have hprop := resonance_proportional_poly (p := p) hp
  have hJ : Jpoly p (by omega) (redZ p (negAPoly p)) =
      Polynomial.X ^ p * (Polynomial.C (resLambda p hp) * Jpoly p (by omega) (redPosA p)) := by
    have h1 := Jpoly_sub (p := p) (by omega) (redZ p (negAPoly p)) (homA0 p (by omega))
    rw [hprop, Jpoly_homA0 hp, sub_zero, Jpoly_X_pow_mul, Jpoly_C_mul] at h1
    exact h1.symm
  have hdeg := Jpoly_natDegree hp (redZ p (negAPoly p))
  have hnd : (redZ p (negAPoly p)).natDegree ≤ p :=
    Polynomial.natDegree_map_le.trans negAPoly_natDegree
  rw [hJ] at hdeg
  by_cases h0 : Jpoly p (by omega) (redPosA p) = 0
  · rw [h0]; simp
  · have hl := resLambda_ne_zero (p := p) hp
    rw [Polynomial.natDegree_mul (pow_ne_zero _ Polynomial.X_ne_zero)
      (mul_ne_zero (Polynomial.C_ne_zero.mpr hl) h0), Polynomial.natDegree_X_pow,
      Polynomial.natDegree_C_mul hl] at hdeg
    omega

/-- `S(v̄⁺, Γ)` over the common denominator `P̄^{2σ+2}`. -/
theorem gamma_concomitant_pos (hp : 11 ≤ p) :
    concomitant (redV2 p) (0 : ZMod p) (hasseGammaSeries p (by omega))
        (((hassePolyP * redPosA p : Polynomial (ZMod p))) : PowerSeries (ZMod p)) =
      ((hassePolyP ^ 2 * Jpoly p (by omega) (redPosA p) : Polynomial (ZMod p)) :
        PowerSeries (ZMod p)) * Pinv p ^ (gm p + 2) := by
  rw [gamma_concomitant hp, Polynomial.coe_mul, Polynomial.coe_pow]
  have hP := P_mul_Pinv (p := p)
  linear_combination
    (-(((Jpoly p (by omega) (redPosA p) : Polynomial (ZMod p)) : PowerSeries (ZMod p)) *
      Pinv p ^ gm p * (1 + ((hassePolyP : Polynomial (ZMod p)) : PowerSeries (ZMod p)) *
        Pinv p))) * hP

end Zeta7Auxiliary
