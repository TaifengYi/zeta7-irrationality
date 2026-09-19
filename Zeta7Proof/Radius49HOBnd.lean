import Zeta7Proof.Radius49HONear
import Zeta7Proof.Radius49HOAlg
import Zeta7Proof.AuxiliaryIntegralCoordinates
import Zeta7Proof.EisensteinUniform

/-! Radius internalization, HO step (ii): coefficient bounds for the classical approximants.

* generic `Bnd` tools: constants, powers, substitution of an integral series at radius `1`,
  `V₇`, polynomials of bounded degree, and division by a series with dominant constant term;
* `Bnd` of the explicit polynomials `T(X)`, `T̃(X)` at radius `7^s`, `0 ≤ s ≤ 1/4`;
* the integrality inputs over `ℚ₇`: `A`, `q(x)`, `E₆ ≡ 1 (mod 7)` and
  `E₆^{7^r} ≡ 1 (mod 7^{r+1})`, and `E₋₂` at radius `1`.
No published radius input is used. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open PowerSeries Filter Topology
namespace Zeta7Radius49
open Zeta7Main
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

variable {ρ : ℝ}

/-! ### Generic tools -/

theorem Bnd_C (hρ : 0 ≤ ρ) (c : ℚ_[7]) : Bnd ρ (C c) ‖c‖ := by
  have := Bnd_C_mul_X_pow hρ c 0
  simpa using this

theorem Bnd.pow (hρ : 0 < ρ) {f : ℚ_[7]⟦X⟧} {B : ℝ} (hf : Bnd ρ f B) (n : ℕ) :
    Bnd ρ (f ^ n) (B ^ n) := by
  induction n with
  | zero => simpa using (Bnd_one : Bnd ρ 1 1)
  | succ n ih => rw [pow_succ, pow_succ]; exact ih.mul hρ hf

/-- Dominance in the form used below: `D₀ = 1`, `Bnd ρ (D - 1) 1`. -/
theorem Bnd_of_dom (hρ : 0 < ρ) {D F G : ℚ_[7]⟦X⟧} {B : ℝ} (hD0 : coeff 0 D = 1)
    (hD : Bnd ρ (D - 1) 1) (hG : Bnd ρ G B) (hDF : D * F = G) : Bnd ρ F B := by
  refine Bnd_of_mul_dominant hρ (by rw [hD0, norm_one]) (fun l hl => ?_) hG hDF
  have := hD l
  rwa [map_sub, coeff_one, if_neg (by omega), sub_zero] at this

theorem Bnd_one_of_sub (hρ : 0 ≤ ρ) {D : ℚ_[7]⟦X⟧} (hD : Bnd ρ (D - 1) 1) : Bnd ρ D 1 := by
  have h := hD.add hρ (Bnd_one (ρ := ρ))
  simpa using h

/-- Substitution of an integral series without constant term preserves radius-`1` bounds. -/
theorem Bnd_subst_one {a : ℚ_[7]⟦X⟧} (ha0 : constantCoeff a = 0) (ha : Bnd 1 a 1)
    {f : ℚ_[7]⟦X⟧} {B : ℝ} (hf : Bnd 1 f B) : Bnd 1 (f.subst a) B := by
  have hB := hf.nonneg
  have hs : HasSubst a := HasSubst.of_constantCoeff_zero' ha0
  intro i
  set N := i + 1
  set T : ℚ_[7]⟦X⟧ := ∑ n ∈ Finset.range N, coeff n f • X ^ n with hT
  have hR : X ^ N ∣ f - T := by
    rw [X_pow_dvd_iff]
    intro m hm
    rw [map_sub, hT, map_sum]
    simp only [map_smul, coeff_X_pow, smul_eq_mul, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq, ite_cond_eq_true _ _ (eq_true (Finset.mem_range.mpr hm)), sub_self]
  have hR' := X_pow_dvd_subst ha0 hR
  have e1 : (f - T).subst a = f.subst a - T.subst a := by
    rw [← coe_substAlgHom hs, map_sub]
  have e : coeff i (f.subst a) = coeff i (T.subst a) := by
    have h0 := (X_pow_dvd_iff.mp hR') i (by omega)
    rw [e1, map_sub] at h0
    exact sub_eq_zero.mp h0
  have hTs : T.subst a = ∑ n ∈ Finset.range N, coeff n f • a ^ n := by
    rw [hT, ← coe_substAlgHom hs, map_sum]
    simp only [map_smul, map_pow, coe_substAlgHom, subst_X hs]
  rw [e, hTs]
  have ha1 : ∀ n : ℕ, Bnd 1 (a ^ n) 1 := fun n => by simpa using ha.pow one_pos n
  have hsum : Bnd 1 (∑ n ∈ Finset.range N, coeff n f • a ^ n) B := by
    apply Bnd.sum zero_le_one hB
    intro n _
    rw [smul_eq_C_mul]
    have h1 := (Bnd_C zero_le_one (coeff n f)).mul one_pos (ha1 n)
    have h2 : ‖coeff n f‖ ≤ B := by simpa using hf n
    exact h1.mono (by simpa using h2)
  exact hsum i

theorem Bnd_vSeven_one {f : ℚ_[7]⟦X⟧} {B : ℝ} (hf : Bnd 1 f B) : Bnd 1 (vSeven f) B := by
  intro i
  rw [coeff_vSeven]
  split_ifs
  · simpa using hf (i / 7)
  · simpa using hf.nonneg

/-- A series of degree `≤ d` bounded at radius `1` by `M` is bounded at radius `ρ ≥ 1`
by `M ρ^d`. -/
theorem Bnd_of_deg (hρ : 1 ≤ ρ) {P : ℚ_[7]⟦X⟧} {M : ℝ} {d : ℕ}
    (hdeg : ∀ i, d < i → coeff i P = 0) (hP : Bnd 1 P M) : Bnd ρ P (M * ρ ^ d) := by
  intro i
  by_cases hi : d < i
  · rw [hdeg i hi, norm_zero, zero_mul]
    exact mul_nonneg hP.nonneg (by positivity)
  · have h1 : ‖coeff i P‖ ≤ M := by simpa using hP i
    calc ‖coeff i P‖ * ρ ^ i ≤ M * ρ ^ d :=
          mul_le_mul h1 (pow_le_pow_right₀ hρ (by omega)) (by positivity) hP.nonneg

/-! ### Norms of explicit constants -/

theorem norm_seven : ‖(7 : ℚ_[7])‖ = (7 : ℝ)⁻¹ := by
  have h := Padic.norm_p (p := 7)
  simpa only [Nat.cast_ofNat] using h

theorem norm_seven_pow (n : ℕ) : ‖(7 : ℚ_[7]) ^ n‖ = ((7 : ℝ)⁻¹) ^ n := by
  rw [norm_pow, norm_seven]

theorem norm_nat_le_one (n : ℕ) : ‖(n : ℚ_[7])‖ ≤ 1 := by
  have := Padic.norm_int_le_one (p := 7) (n : ℤ)
  simpa using this

theorem norm_nat_eq_one {a : ℕ} (h : ¬ 7 ∣ a) : ‖(a : ℚ_[7])‖ = 1 := by
  have e : (a : ℚ_[7]) = ((a : ℚ) : ℚ_[7]) := by norm_cast
  rw [e, Padic.eq_padicNorm]
  exact_mod_cast (padicNorm.nat_eq_one_iff a).mpr h

/-- `‖c‖ (7^s)^j ≤ 1` for `7 ∣ c`, `j ≤ 4`, `0 ≤ s ≤ 1/4`. -/
theorem small_le_one {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ 1 / 4) {j : ℕ} (hj : j ≤ 4) {c : ℕ}
    (h : 7 ∣ c) : ‖(c : ℚ_[7])‖ * ((7 : ℝ) ^ s) ^ j ≤ 1 := by
  have hn : ‖(c : ℚ_[7])‖ ≤ (7 : ℝ)⁻¹ := by
    have := norm_nat_seven_pow (v := 1) (by simpa using h)
    simpa using this
  have hp : ((7 : ℝ) ^ s) ^ j ≤ 7 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    calc (7 : ℝ) ^ (s * (j : ℝ)) ≤ (7 : ℝ) ^ (1 : ℝ) := by
          apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
          have : (j : ℝ) ≤ 4 := by exact_mod_cast hj
          nlinarith
      _ = 7 := Real.rpow_one 7
  calc ‖(c : ℚ_[7])‖ * ((7 : ℝ) ^ s) ^ j ≤ (7 : ℝ)⁻¹ * 7 :=
        mul_le_mul hn hp (by positivity) (by norm_num)
    _ = 1 := by norm_num

/-! ### The polynomials `T(X)` and `T̃(X)` near the ordinary locus -/

/-- `T̃(x) = 1 + 14x + 63x² + 70x³ - 7x⁴`. -/
def polyTtg {R : Type*} [CommRing R] (X : R) : R :=
  1 + 14 * X + 63 * X ^ 2 + 70 * X ^ 3 - 7 * X ^ 4

theorem polyTtg_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (x : R) :
    φ (polyTtg x) = polyTtg (φ x) := by
  simp [polyTtg, map_ofNat]

theorem polyTg_sub_one : polyTg (X : ℚ_[7]⟦X⟧) - 1 =
    -(C ((490 : ℕ) : ℚ_[7]) * X ^ 1 + C ((21609 : ℕ) : ℚ_[7]) * X ^ 2 +
      C ((235298 : ℕ) : ℚ_[7]) * X ^ 3 + C ((823543 : ℕ) : ℚ_[7]) * X ^ 4) := by
  simp only [polyTg, Nat.cast_ofNat, map_ofNat, pow_one]; ring

theorem polyTtg_sub_one : polyTtg (X : ℚ_[7]⟦X⟧) - 1 =
    C ((14 : ℕ) : ℚ_[7]) * X ^ 1 + C ((63 : ℕ) : ℚ_[7]) * X ^ 2 +
      C ((70 : ℕ) : ℚ_[7]) * X ^ 3 - C ((7 : ℕ) : ℚ_[7]) * X ^ 4 := by
  simp only [polyTtg, Nat.cast_ofNat, map_ofNat, pow_one]; ring

theorem Bnd_polyTg_sub {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ 1 / 4) :
    Bnd ((7 : ℝ) ^ s) (polyTg (X : ℚ_[7]⟦X⟧) - 1) 1 := by
  have hρ : (0 : ℝ) ≤ (7 : ℝ) ^ s := by positivity
  have t : ∀ c j : ℕ, 7 ∣ c → j ≤ 4 → Bnd ((7 : ℝ) ^ s) (C (c : ℚ_[7]) * X ^ j) 1 :=
    fun c j h hj => (Bnd_C_mul_X_pow hρ _ j).mono (small_le_one hs0 hs hj h)
  rw [polyTg_sub_one]
  exact ((((t 490 1 (by norm_num) (by norm_num)).add hρ (t 21609 2 (by norm_num) (by norm_num))).add
    hρ (t 235298 3 (by norm_num) (by norm_num))).add hρ (t 823543 4 (by norm_num) (by norm_num))).neg

theorem Bnd_polyTtg_sub {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ 1 / 4) :
    Bnd ((7 : ℝ) ^ s) (polyTtg (X : ℚ_[7]⟦X⟧) - 1) 1 := by
  have hρ : (0 : ℝ) ≤ (7 : ℝ) ^ s := by positivity
  have t : ∀ c j : ℕ, 7 ∣ c → j ≤ 4 → Bnd ((7 : ℝ) ^ s) (C (c : ℚ_[7]) * X ^ j) 1 :=
    fun c j h hj => (Bnd_C_mul_X_pow hρ _ j).mono (small_le_one hs0 hs hj h)
  rw [polyTtg_sub_one]
  exact (((t 14 1 (by norm_num) (by norm_num)).add hρ (t 63 2 (by norm_num) (by norm_num))).add
    hρ (t 70 3 (by norm_num) (by norm_num))).sub hρ (t 7 4 (by norm_num) (by norm_num))

theorem polyTg_coeff_zero : coeff 0 (polyTg (X : ℚ_[7]⟦X⟧)) = 1 := by
  simp [polyTg, coeff_X_pow, map_ofNat]

theorem polyTtg_coeff_zero : coeff 0 (polyTtg (X : ℚ_[7]⟦X⟧)) = 1 := by
  simp [polyTtg, coeff_X_pow, map_ofNat]

theorem Bnd_polyTg {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ 1 / 4) :
    Bnd ((7 : ℝ) ^ s) (polyTg (X : ℚ_[7]⟦X⟧)) 1 :=
  Bnd_one_of_sub (by positivity) (Bnd_polyTg_sub hs0 hs)

theorem Bnd_polyTg_pow_sub {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ 1 / 4) (j : ℕ) :
    Bnd ((7 : ℝ) ^ s) (polyTg (X : ℚ_[7]⟦X⟧) ^ j - 1) 1 := by
  have h := (Bnd_polyTg hs0 hs).pow (by positivity) j
  rw [one_pow] at h
  exact h.sub (by positivity) Bnd_one

theorem polyTg_pow_coeff_zero (j : ℕ) : coeff 0 (polyTg (X : ℚ_[7]⟦X⟧) ^ j) = 1 := by
  rw [coeff_zero_eq_constantCoeff, map_pow, ← coeff_zero_eq_constantCoeff, polyTg_coeff_zero,
    one_pow]

/-! ### Integrality over `ℚ₇` -/

theorem Bnd_of_integer {f : ℚ⟦X⟧} (hf : Zeta7Auxiliary.IntegerSeries f) :
    Bnd 1 (f.map (algebraMap ℚ ℚ_[7])) 1 := by
  obtain ⟨g, rfl⟩ := hf
  intro i
  rw [one_pow, mul_one, coeff_map, coeff_map]
  have := Padic.norm_int_le_one (p := 7) (coeff i g)
  simpa using this

theorem Bnd_Aq : Bnd 1 Aq 1 := Bnd_of_integer Zeta7Auxiliary.ASeries_integer

theorem Bnd_qx : Bnd 1 qx 1 := Bnd_of_integer Zeta7Auxiliary.qSeries_integer

/-- `E₆` over `ℚ₇`. -/
def Eq6 : ℚ_[7]⟦X⟧ := E6Q.map (algebraMap ℚ ℚ_[7])

theorem Eq6_const : constantCoeff Eq6 = 1 := by
  rw [Eq6, ← coeff_zero_eq_constantCoeff, coeff_map, coeff_zero_eq_constantCoeff, E6Q_const,
    map_one]

/-- `E₆ ≡ 1 (mod 7)`. -/
theorem Bnd_Eq6_sub : Bnd 1 (Eq6 - 1) (7 : ℝ)⁻¹ := by
  intro i
  rw [one_pow, mul_one]
  have hc : coeff i (Eq6 - 1) =
      (((-504 * ∑ d ∈ i.divisors, (d : ℤ) ^ 5) : ℤ) : ℚ_[7]) := by
    have : coeff i (Eq6 - 1) = algebraMap ℚ ℚ_[7] (coeff i (E6Q - 1)) := by
      rw [Eq6, map_sub, coeff_map, map_sub, map_sub, coeff_one, coeff_one]
      split_ifs <;> simp
    rw [this]
    simp only [E6Q, Zeta7Common.eisensteinSixQ, Zeta7Common.sigmaFive, sub_sub_cancel_left,
      map_neg, coeff_C_mul, coeff_mk]
    push_cast
    simp
  rw [hc]
  have := norm_int_le_of_dvd (-504 * ∑ d ∈ i.divisors, (d : ℤ) ^ 5) 1
    (Dvd.dvd.mul_right (by norm_num) _)
  simpa using this

/-- One Frobenius step of the congruence: `y ≡ 0 (mod δ)`, `δ ≤ 1/7` ⇒
`(1 + y)^7 ≡ 1 (mod δ/7)`. -/
theorem Bnd_pow_seven_sub {y : ℚ_[7]⟦X⟧} {δ : ℝ} (hδ : δ ≤ (7 : ℝ)⁻¹) (hy : Bnd 1 y δ) :
    Bnd 1 ((1 + y) ^ 7 - 1) (δ * (7 : ℝ)⁻¹) := by
  have hδ0 := hy.nonneg
  have hy1 : Bnd 1 y 1 := hy.mono (hδ.trans (by norm_num))
  set u : ℚ_[7]⟦X⟧ := 1 + C ((3 : ℕ) : ℚ_[7]) * y ^ 1 + C ((5 : ℕ) : ℚ_[7]) * y ^ 2 +
    C ((5 : ℕ) : ℚ_[7]) * y ^ 3 + C ((3 : ℕ) : ℚ_[7]) * y ^ 4 + y ^ 5 with hu
  have e : (1 + y) ^ 7 - 1 = C (7 : ℚ_[7]) * (y * u) + y ^ 7 := by
    rw [hu]; simp only [map_ofNat, map_natCast, Nat.cast_ofNat]; ring
  have hc : ∀ c : ℕ, ∀ n : ℕ, Bnd 1 (C (c : ℚ_[7]) * y ^ n) 1 := fun c n => by
    have := (Bnd_C zero_le_one (c : ℚ_[7])).mul one_pos (hy1.pow one_pos n)
    exact this.mono (by rw [one_pow, mul_one]; exact norm_nat_le_one c)
  have hu1 : Bnd 1 u 1 := by
    have h55 := (hy1.pow one_pos 5)
    rw [one_pow] at h55
    rw [hu]
    exact ((((Bnd_one.add zero_le_one (hc 3 1)).add zero_le_one (hc 5 2)).add zero_le_one
      (hc 5 3)).add zero_le_one (hc 3 4)).add zero_le_one h55
  have h1 : Bnd 1 (C (7 : ℚ_[7]) * (y * u)) (δ * (7 : ℝ)⁻¹) := by
    have := (Bnd_C zero_le_one (7 : ℚ_[7])).mul one_pos (hy.mul one_pos hu1)
    rw [norm_seven] at this
    exact this.mono (by nlinarith)
  have h2 : Bnd 1 (y ^ 7) (δ * (7 : ℝ)⁻¹) := by
    refine (hy.pow one_pos 7).mono ?_
    have h6 : δ ^ 6 ≤ (7 : ℝ)⁻¹ := by
      calc δ ^ 6 ≤ ((7 : ℝ)⁻¹) ^ 6 := pow_le_pow_left₀ hδ0 hδ 6
        _ ≤ (7 : ℝ)⁻¹ := by norm_num
    calc δ ^ 7 = δ * δ ^ 6 := by ring
      _ ≤ δ * (7 : ℝ)⁻¹ := mul_le_mul_of_nonneg_left h6 hδ0
  rw [e]
  exact h1.add zero_le_one h2

/-- `E₆^{7^r} ≡ 1 (mod 7^{r+1})`. -/
theorem Bnd_Eq6_pow_sub (r : ℕ) : Bnd 1 (Eq6 ^ (7 ^ r) - 1) (((7 : ℝ)⁻¹) ^ (r + 1)) := by
  induction r with
  | zero => simpa using Bnd_Eq6_sub
  | succ r ih =>
    have h := Bnd_pow_seven_sub (by
      calc ((7 : ℝ)⁻¹) ^ (r + 1) ≤ ((7 : ℝ)⁻¹) ^ 1 :=
            pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
        _ = (7 : ℝ)⁻¹ := pow_one _) ih
    have e : (1 + (Eq6 ^ 7 ^ r - 1)) ^ 7 = Eq6 ^ 7 ^ (r + 1) := by
      rw [add_sub_cancel, ← pow_mul, pow_succ]
    rw [e] at h
    simpa [pow_succ] using h

/-- The inverse of `E₆` over `ℚ₇`. -/
def Eq6i : ℚ_[7]⟦X⟧ := Eq6⁻¹

theorem Eq6_mul_inv : Eq6 * Eq6i = 1 :=
  PowerSeries.mul_inv_cancel _ (by rw [Eq6_const]; exact one_ne_zero)

theorem Bnd_Eq6i : Bnd 1 Eq6i 1 :=
  Bnd_of_dom one_pos (by rw [coeff_zero_eq_constantCoeff, Eq6_const])
    (Bnd_Eq6_sub.mono (by norm_num)) Bnd_one Eq6_mul_inv

/-- `E₆^{-7^r} ≡ 1 (mod 7^{r+1})`. -/
theorem Bnd_Eq6i_pow_sub (r : ℕ) :
    Bnd 1 (Eq6i ^ (7 ^ r) - 1) (((7 : ℝ)⁻¹) ^ (r + 1)) := by
  have e : Eq6i ^ (7 ^ r) - 1 = -((Eq6 ^ (7 ^ r) - 1) * Eq6i ^ (7 ^ r)) := by
    have h1 : (Eq6 * Eq6i) ^ (7 ^ r) = 1 := by rw [Eq6_mul_inv, one_pow]
    rw [mul_pow] at h1
    linear_combination h1
  rw [e]
  have h := (Bnd_Eq6_pow_sub r).mul one_pos (Bnd_Eq6i.pow one_pos (7 ^ r))
  rw [one_pow, mul_one] at h
  exact h.neg

/-! ### `E₋₂` at radius `1` -/

/-- The radius-`1` bound of `E₋₂`. -/
def BE : ℝ := max 1 ‖eta‖

theorem one_le_BE : 1 ≤ BE := le_max_left _ _

theorem Bnd_eisensteinMinusTwo : Bnd 1 eisensteinMinusTwo BE := by
  intro n
  rw [one_pow, mul_one]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [coeff_zero_eq_constantCoeff, eisensteinMinusTwo_constant]; exact le_max_right _ _
  · rw [eisensteinMinusTwo_coeff hn.ne']
    refine le_trans ?_ one_le_BE
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one
    intro a ha
    have h7 := (Finset.mem_filter.mp ha).2
    rw [norm_inv, norm_pow, norm_nat_eq_one h7]
    norm_num

end Zeta7Radius49
