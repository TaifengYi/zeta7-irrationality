import Zeta7Proof.AuxiliaryDerivativeClearing

/-! P4: degree bounds for the cleared maps, their reductions modulo `p`, and the
divisibility `Q̄ ∣ P̄₂` forced by the double poles of `v₀` on the reduced exact kernel,
together with the resulting `d + 2` bound for the reduced first-order map. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
namespace Zeta7Auxiliary
open Zeta7Common

variable {p : ℕ} [Fact p.Prime]

local notation "σp" => (p-1)/3

/-! ### Degree bounds over `ℤ_[p]` -/

theorem intPolyP_natDegree : (intPolyP p).natDegree ≤ 2 := by
  unfold intPolyP; compute_degree

theorem intPolyW_natDegree : (intPolyW p).natDegree ≤ 3 := by
  unfold intPolyW; compute_degree

theorem intPolyQ_natDegree (hp : 5 ≤ p) :
    (integralQuotientPolynomial p hp).natDegree ≤ 2 * σp :=
  (integralQuotientPolynomial_degree p hp).le

theorem rhoPoly_natDegree (hp : 5 ≤ p) : (rhoPoly p hp).natDegree ≤ 2 * σp + 2 := by
  unfold rhoPoly
  refine (Polynomial.natDegree_C_mul_le _ _).trans ((Polynomial.natDegree_sub_le_of_le
    (m := 2 * σp + 2) (n := 2 * σp + 2) ?_ ?_).trans (max_le le_rfl le_rfl))
  · refine Polynomial.natDegree_mul_le_of_le (m := 2) ?_ (intPolyQ_natDegree hp) |>.trans (by omega)
    · exact (Polynomial.natDegree_C_mul_le _ _).trans
        ((eulerPoly_natDegree_le _).trans intPolyP_natDegree)
  · refine Polynomial.natDegree_mul_le_of_le (m := 2 * σp) ?_ intPolyP_natDegree |>.trans (by omega)
    exact (eulerPoly_natDegree_le _).trans (intPolyQ_natDegree hp)

/-- `deg (PQ)² F₀ ≤ n + 4σ + 4`. -/
theorem clearedF0_natDegree (hp : 11 ≤ p) (P0 P1 P2 : Polynomial ℤ_[p]) (n : ℕ)
    (h0 : P0.natDegree ≤ n) (h1 : P1.natDegree ≤ n) (h2 : P2.natDegree ≤ n) :
    (clearedF0 p hp P0 P1 P2).natDegree ≤ n + 4 * σp + 4 := by
  have hPQ : (intPolyP p * integralQuotientPolynomial p (hp5 hp)).natDegree ≤ 2 * σp + 2 :=
    (Polynomial.natDegree_mul_le_of_le intPolyP_natDegree (intPolyQ_natDegree _)).trans
      (by omega)
  have hr := rhoPoly_natDegree (p := p) (hp5 hp)
  unfold clearedF0
  apply Polynomial.natDegree_add_le_of_degree_le
  apply Polynomial.natDegree_add_le_of_degree_le
  · exact (Polynomial.natDegree_mul_le_of_le (Polynomial.natDegree_pow_le_of_le 2 hPQ) h0).trans
      (by omega)
  · exact (Polynomial.natDegree_mul_le_of_le (Polynomial.natDegree_mul_le_of_le hPQ hr) h1).trans
      (by omega)
  · refine (Polynomial.natDegree_mul_le_of_le (m := 4 * σp + 4)
      ((Polynomial.natDegree_C_mul_le _ _).trans ?_) h2).trans (by omega)
    apply Polynomial.natDegree_add_le_of_degree_le
    · exact (Polynomial.natDegree_mul_le_of_le
        (Polynomial.natDegree_pow_le_of_le 2 (intPolyQ_natDegree _)) intPolyW_natDegree).trans
          (by omega)
    · exact (Polynomial.natDegree_pow_le_of_le 2 hr).trans (by omega)

/-! ### Reduction modulo `p` -/

abbrev redZ (p : ℕ) [Fact p.Prime] : Polynomial ℤ_[p] →+* Polynomial (ZMod p) :=
  Polynomial.mapRingHom PadicInt.toZMod

theorem redZ_intPolyP : redZ p (intPolyP p) = hassePolyP := by
  simp [intPolyP, hassePolyP, map_ofNat]

theorem redZ_intPolyW : redZ p (intPolyW p) = hassePolyW := by
  simp [intPolyW, hassePolyW, map_ofNat]

theorem redZ_intPolyQ (hp : 5 ≤ p) :
    redZ p (integralQuotientPolynomial p hp) = reducedQuotient p hp := rfl

theorem redZ_C (a : ℤ_[p]) : redZ p (Polynomial.C a) = Polynomial.C (PadicInt.toZMod a) :=
  Polynomial.map_C _

theorem redZ_eulerPoly (f : Polynomial ℤ_[p]) : redZ p (eulerPoly f) = eulerPoly (redZ p f) :=
  eulerPoly_map _ f

theorem half_weight_cast (hp : 5 ≤ p) : (2 : ZMod p) * (((p-1)/2 : ℕ) : ZMod p) = -1 := by
  have h := prime_half_weight p hp
  have hc : ((2*((p-1)/2) : ℕ) : ZMod p) = ((p-1 : ℕ) : ZMod p) := by rw [h]
  rw [Nat.cast_mul, Nat.cast_sub (Fact.out : p.Prime).one_le, ZMod.natCast_self] at hc
  simpa using hc

theorem toZMod_einvZ (hp : 5 ≤ p) : PadicInt.toZMod (einvZ p hp) = -2 := by
  have hm : einvZ p hp * (((p-1)/2 : ℕ) : ℤ_[p]) = 1 := by
    apply Subtype.ext
    have hne : (((p-1)/2 : ℕ) : ℚ_[p]) ≠ 0 := by exact_mod_cast (show (p-1)/2 ≠ 0 by omega)
    change (((p-1)/2 : ℕ) : ℚ_[p])⁻¹ * (((p-1)/2 : ℕ) : ℚ_[p]) = 1
    exact inv_mul_cancel₀ hne
  have h := congrArg PadicInt.toZMod hm
  rw [map_mul, map_natCast, map_one] at h
  have hw := half_weight_cast (p := p) hp
  linear_combination (-2 : ZMod p) * h + PadicInt.toZMod (einvZ p hp) * hw

theorem toZMod_halfZ (hp : 2 < p) : PadicInt.toZMod (halfZ p hp) * 2 = 1 := by
  have hm : halfZ p hp * 2 = 1 := by
    apply Subtype.ext
    change (1/2 : ℚ_[p]) * 2 = 1
    norm_num
  have h := congrArg PadicInt.toZMod hm
  rwa [map_mul, map_ofNat, map_one] at h

/-- The reduced cleared logarithmic derivative `ρ̄ = 2 E(Q̄) P̄ + Q̄ T`. -/
theorem redZ_rhoPoly (hp : 5 ≤ p) :
    redZ p (rhoPoly p hp) =
      2 * eulerPoly (reducedQuotient p hp) * hassePolyP +
        reducedQuotient p hp * (Polynomial.C (-2 * ((σp : ℕ) : ZMod p)) * eulerPoly hassePolyP) := by
  unfold rhoPoly
  simp only [map_mul, map_sub, redZ_C, redZ_eulerPoly]
  rw [redZ_intPolyP, redZ_intPolyQ, toZMod_einvZ, map_natCast]
  simp only [map_neg, map_mul, map_ofNat, map_natCast]
  ring

/-! ### The divisibility forced by the reduced exact kernel -/

theorem reducedQuotient_coprime_eulerPoly (hp : 11 ≤ p) :
    IsCoprime (reducedQuotient p (hp5 hp)) (eulerPoly (reducedQuotient p (hp5 hp))) := by
  unfold eulerPoly
  apply IsCoprime.mul_right
  · exact polynomial_coprime_X_of_constant_one _ (reducedQuotient_constant p _)
  · exact reducedQuotient_separable p hp

theorem isCoprime_C_two (hp : 11 ≤ p) (Q : Polynomial (ZMod p)) :
    IsCoprime Q (Polynomial.C (2 : ZMod p)) := by
  have h2 : (2 : ZMod p) ≠ 0 := two_unit hp
  refine ⟨0, Polynomial.C (2 : ZMod p)⁻¹, ?_⟩
  rw [zero_mul, zero_add, ← map_mul, inv_mul_cancel₀ h2, map_one]

set_option hygiene false in
local notation "Q" => reducedQuotient p (hp5 hp)
set_option hygiene false in
local notation "E" => eulerPoly (reducedQuotient p (hp5 hp))
set_option hygiene false in
local notation "P" => (hassePolyP : Polynomial (ZMod p))
set_option hygiene false in
local notation "T" => Polynomial.C (-2 * ((σp : ℕ) : ZMod p)) * eulerPoly (hassePolyP : Polynomial (ZMod p))

/-- **P4: `Q̄ ∣ P̄₂`** whenever the reduction of the cleared exact map vanishes. -/
theorem reducedQuotient_dvd_of_cleared (hp : 11 ≤ p) (P0 P1 P2 : Polynomial ℤ_[p])
    (h : redZ p (clearedF0 p hp P0 P1 P2) = 0) :
    reducedQuotient p (hp5 hp) ∣ redZ p P2 := by
  have hρ := redZ_rhoPoly (p := p) (hp5 hp)
  have hh := toZMod_halfZ (p := p) (hp2 hp)
  unfold clearedF0 at h
  simp only [map_add, map_mul, map_pow, redZ_C] at h
  rw [redZ_intPolyP, redZ_intPolyQ, redZ_intPolyW, hρ] at h
  have hdiv : Q ∣ redZ p P2 * (Polynomial.C (2 : ZMod p) * E^2 * P^2) := by
    refine ⟨-(Q * P^2 * redZ p P0 + P * (2 * E * P + Q * T) * redZ p P1 +
      Polynomial.C (PadicInt.toZMod (halfZ p (hp2 hp))) *
        (Q * (hassePolyW : Polynomial (ZMod p)) + (4 * E * P * T + Q * T^2)) * redZ p P2), ?_⟩
    have hC : Polynomial.C (PadicInt.toZMod (halfZ p (hp2 hp))) * 4 = Polynomial.C (2 : ZMod p) := by
      have h4 : PadicInt.toZMod (halfZ p (hp2 hp)) * 4 = 2 := by linear_combination 2 * hh
      rw [show (4 : Polynomial (ZMod p)) = Polynomial.C 4 from (map_ofNat Polynomial.C 4).symm,
        ← map_mul, h4]
    linear_combination h - E^2 * P^2 * redZ p P2 * hC
  have hcop : IsCoprime Q (Polynomial.C (2 : ZMod p) * E^2 * P^2) :=
    ((isCoprime_C_two hp Q).mul_right ((reducedQuotient_coprime_eulerPoly hp).pow_right)).mul_right
      (reducedQuotient_coprime p hp).pow_right
  exact hcop.dvd_of_dvd_mul_right hdiv

/-- **P4: the reduced first-order map has image of dimension at most `n + 3`.** -/
theorem reduced_clearedF1_factor (hp : 11 ≤ p) (P1 P2 : Polynomial ℤ_[p]) (n : ℕ)
    (h1 : (redZ p P1).natDegree ≤ n) (h2 : (redZ p P2).natDegree ≤ n)
    (hdiv : reducedQuotient p (hp5 hp) ∣ redZ p P2) :
    ∃ g : Polynomial (ZMod p), redZ p (clearedF1 p hp P1 P2) = reducedQuotient p (hp5 hp) * g ∧
      g.natDegree ≤ n + 2 := by
  obtain ⟨S, hS⟩ := hdiv
  have hQd : (reducedQuotient p (hp5 hp)).natDegree = 2 * σp := reducedQuotient_degree p hp
  have hQ0 : reducedQuotient p (hp5 hp) ≠ 0 := by
    intro h0
    have := reducedQuotient_constant p (hp5 hp)
    rw [h0, Polynomial.coeff_zero] at this
    exact zero_ne_one this
  have hSd : S.natDegree + 2 * σp ≤ n ∨ S = 0 := by
    by_cases hS0 : S = 0
    · exact Or.inr hS0
    · left
      have := Polynomial.natDegree_mul hQ0 hS0
      rw [← hS, hQd] at this
      omega
  have hρd : (redZ p (rhoPoly p (hp5 hp))).natDegree ≤ 2 * σp + 2 :=
    (Polynomial.natDegree_map_le).trans (rhoPoly_natDegree _)
  refine ⟨hassePolyP * redZ p P1 + redZ p (rhoPoly p (hp5 hp)) * S, ?_, ?_⟩
  · unfold clearedF1
    simp only [map_add, map_mul]
    rw [redZ_intPolyP, redZ_intPolyQ, hS]
    ring
  · apply Polynomial.natDegree_add_le_of_degree_le
    · exact (Polynomial.natDegree_mul_le_of_le (hassePolyP_natDegree p hp).le h1).trans
        (by omega)
    · rcases hSd with hSd | hS0
      · exact (Polynomial.natDegree_mul_le_of_le hρd le_rfl).trans (by omega)
      · rw [hS0, mul_zero, Polynomial.natDegree_zero]; exact Nat.zero_le _

end Zeta7Auxiliary
