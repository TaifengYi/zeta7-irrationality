import Zeta7Proof.AuxiliaryDerivativeBasis

/-! P5: the actual five-band operator over an arbitrary commutative coefficient ring.

For a shift `s`, `θ_s = D - s` is the Euler operator conjugated by `x^s`; the Laurent
exponent `n` of a coefficient at index `m` of `x^s · f` is `m - s`. The operator
`L_s f = θ_s³ f - V θ_s f - ½ (DV) f` is `x^s L x^{-s}`. For every coefficient ring in which
`P² V = W` and `2` is invertible, `P · L_s (P f) = Σ bᵢ θ_sⁱ f`, and the coefficient of
`x^k` is `Σ_j β_j(k - j - s) f_{k-j}` with the five closed-form band weights. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
namespace Zeta7Auxiliary
open PowerSeries Zeta7Common

section Band
variable {R : Type*} [CommRing R]

/-- The twisted Euler operator `θ_s = D - s`. -/
def thetaS (s : R) (f : PowerSeries R) : PowerSeries R := euler f - C s * f

theorem coeff_thetaS (s : R) (f : PowerSeries R) (n : ℕ) :
    coeff n (thetaS s f) = ((n : R) - s) * coeff n f := by
  simp only [thetaS, map_sub, euler_coeff, coeff_C_mul]
  ring

theorem coeff_thetaS_iter (s : R) (f : PowerSeries R) (i n : ℕ) :
    coeff n ((thetaS s)^[i] f) = ((n : R) - s)^i * coeff n f := by
  induction i generalizing f with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply, ih, coeff_thetaS]
    ring

theorem thetaS_mul (s : R) (f g : PowerSeries R) :
    thetaS s (f * g) = euler f * g + f * thetaS s g := by
  simp only [thetaS, euler_mul_general]
  ring

theorem thetaS_add (s : R) (f g : PowerSeries R) :
    thetaS s (f + g) = thetaS s f + thetaS s g := by
  simp only [thetaS, euler_add_gen]
  ring

theorem euler_C_gen (a : R) : euler (C a : PowerSeries R) = 0 := by
  simp [euler]

theorem euler_one_gen : euler (1 : PowerSeries R) = 0 := by
  simpa using euler_C_gen (R := R) 1

theorem euler_ofNat_gen (n : ℕ) [n.AtLeastTwo] :
    euler (no_index (OfNat.ofNat n : PowerSeries R)) = 0 := by
  rw [show (OfNat.ofNat n : PowerSeries R) = C (OfNat.ofNat n) from (map_ofNat C n).symm,
    euler_C_gen]

theorem euler_X_gen : euler (X : PowerSeries R) = X := by
  ext n
  rw [euler_coeff, coeff_X]
  split_ifs with h
  · subst h; simp
  · simp

theorem euler_X_pow_gen (k : ℕ) : euler (X^k : PowerSeries R) = (k : PowerSeries R) * X^k := by
  ext n
  rw [euler_coeff, coeff_X_pow, show (k : PowerSeries R) = C (k : R) from (map_natCast C k).symm,
    coeff_C_mul, coeff_X_pow]
  split_ifs with h
  · subst h; simp
  · simp

/-- The actual operator `L_s = x^s L x^{-s}` with potential `V`. -/
def resOp (half : R) (V : PowerSeries R) (s : R) (f : PowerSeries R) : PowerSeries R :=
  thetaS s (thetaS s (thetaS s f)) - V * thetaS s f - C half * euler V * f

def bandP : PowerSeries R := 1 + 13 * X + 49 * X^2
def bandW : PowerSeries R := 8 * X * (1 + 16 * X + 49 * X^2)
def bandB3 : PowerSeries R := 1 + 26 * X + 267 * X^2 + 1274 * X^3 + 2401 * X^4
def bandB2 : PowerSeries R := 39 * X + 801 * X^2 + 5733 * X^3 + 14406 * X^4
def bandB1 : PowerSeries R := 31 * X + 967 * X^2 + 9163 * X^3 + 28812 * X^4
def bandB0 : PowerSeries R := 9 * X + 433 * X^2 + 5145 * X^3 + 19208 * X^4

/-- The five-band operator `Σ bᵢ θ_sⁱ`. -/
def bandSeries (s : R) (f : PowerSeries R) : PowerSeries R :=
  bandB3 * thetaS s (thetaS s (thetaS s f)) + bandB2 * thetaS s (thetaS s f) +
    bandB1 * thetaS s f + bandB0 * f

theorem bandP_euler : euler (bandP : PowerSeries R) = 13 * X + 98 * X^2 := by
  simp only [bandP, euler_add_gen, euler_mul_general, euler_one_gen, euler_ofNat_gen,
    euler_X_gen, euler_X_pow_gen]
  push_cast
  ring

theorem bandP_euler2 : euler (euler (bandP : PowerSeries R)) = 13 * X + 196 * X^2 := by
  simp only [bandP_euler, euler_add_gen, euler_mul_general, euler_ofNat_gen,
    euler_X_gen, euler_X_pow_gen]
  push_cast
  ring

theorem bandP_euler3 : euler (euler (euler (bandP : PowerSeries R))) = 13 * X + 392 * X^2 := by
  simp only [bandP_euler2, euler_add_gen, euler_mul_general, euler_ofNat_gen,
    euler_X_gen, euler_X_pow_gen]
  push_cast
  ring

theorem bandW_euler : euler (bandW : PowerSeries R) = 2 * (4 * X + 128 * X^2 + 588 * X^3) := by
  simp only [bandW, euler_add_gen, euler_mul_general, euler_one_gen, euler_ofNat_gen,
    euler_X_gen, euler_X_pow_gen]
  push_cast
  ring

theorem bandP_isUnit : IsUnit (bandP : PowerSeries R) := by
  apply PowerSeries.isUnit_iff_constantCoeff.mpr
  simp [bandP]

/-- **The five-band identity** `P · L_s(P f) = Σ bᵢ θ_sⁱ f`. -/
theorem band_identity (half : R) (hhalf : half * 2 = 1) (V : PowerSeries R)
    (hV : bandP^2 * V = bandW) (s : R) (f : PowerSeries R) :
    bandP * resOp half V s (bandP * f) = bandSeries s f := by
  have hDV : bandP^3 * euler V =
      bandP * (2 * (4 * X + 128 * X^2 + 588 * X^3)) - 2 * euler bandP * bandW := by
    have h := congrArg euler hV
    rw [euler_mul_general, pow_two, euler_mul_general, bandW_euler] at h
    rw [← hV]
    linear_combination bandP * h
  have hh : (C half : PowerSeries R) * 2 = 1 := by
    rw [show (2 : PowerSeries R) = C 2 from (map_ofNat C 2).symm, ← map_mul, hhalf, map_one]
  apply bandP_isUnit.mul_left_cancel
  simp only [resOp, bandSeries, thetaS_mul, thetaS_add]
  rw [bandP_euler3, bandP_euler2, bandP_euler] at *
  unfold bandP bandW bandB3 bandB2 bandB1 bandB0 at *
  linear_combination
    (-((13 * X + 98 * X ^ 2) * f + (1 + 13 * X + 49 * X ^ 2) * thetaS s f)) * hV -
    (C half * f) * hDV +
    ((13 * X + 98 * X ^ 2) * (8 * X * (1 + 16 * X + 49 * X ^ 2)) * f -
      (1 + 13 * X + 49 * X ^ 2) * (4 * X + 128 * X ^ 2 + 588 * X ^ 3) * f) * hh

/-- The five band weights, as functions of the Laurent exponent `n`. -/
def bandWeight (j : ℕ) (n : R) : R :=
  match j with
  | 0 => n^3
  | 1 => (2*n + 1) * (13*n^2 + 13*n + 9)
  | 2 => (n + 1) * (267*n^2 + 534*n + 433)
  | 3 => 49 * (2*n + 3) * (13*n^2 + 39*n + 35)
  | 4 => 2401 * (n + 2)^3
  | _ => 0

/-- The integer coefficient tables of `b₃, b₂, b₁, b₀`. -/
def bandTable (i j : ℕ) : ℕ :=
  match i with
  | 3 => [1, 26, 267, 1274, 2401].getD j 0
  | 2 => [0, 39, 801, 5733, 14406].getD j 0
  | 1 => [0, 31, 967, 9163, 28812].getD j 0
  | 0 => [0, 9, 433, 5145, 19208].getD j 0
  | _ => 0

theorem bandB_expand (i : ℕ) (hi : i < 4) :
    (match i with | 3 => bandB3 | 2 => bandB2 | 1 => bandB1 | _ => bandB0 : PowerSeries R) =
      ∑ j ∈ Finset.range 5, C ((bandTable i j : ℕ) : R) * X^j := by
  interval_cases i <;>
    simp [bandB3, bandB2, bandB1, bandB0, bandTable, Finset.sum_range_succ] <;> ring

theorem coeff_five_mul (c : ℕ → R) (g : PowerSeries R) (k : ℕ) :
    coeff k ((∑ j ∈ Finset.range 5, C (c j) * X^j) * g) =
      ∑ j ∈ Finset.range 5, if j ≤ k then c j * coeff (k - j) g else 0 := by
  rw [Finset.sum_mul, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_assoc, coeff_C_mul, coeff_X_pow_mul']
  split_ifs <;> simp

theorem bandWeight_table (j : ℕ) (hj : j < 5) (n : R) :
    bandWeight j n = (bandTable 3 j : R) * n^3 + (bandTable 2 j : R) * n^2 +
      (bandTable 1 j : R) * n + (bandTable 0 j : R) := by
  interval_cases j <;> simp [bandWeight, bandTable] <;> ring

/-- **Five-band coefficient formula**, valid for every shift and every index. -/
theorem coeff_bandSeries (s : R) (f : PowerSeries R) (k : ℕ) :
    coeff k (bandSeries s f) = ∑ j ∈ Finset.range 5,
      if j ≤ k then bandWeight j (((k - j : ℕ) : R) - s) * coeff (k - j) f else 0 := by
  have h3 := bandB_expand (R := R) 3 (by norm_num)
  have h2 := bandB_expand (R := R) 2 (by norm_num)
  have h1 := bandB_expand (R := R) 1 (by norm_num)
  have h0 := bandB_expand (R := R) 0 (by norm_num)
  simp only at h3 h2 h1 h0
  rw [bandSeries, h3, h2, h1, h0, map_add, map_add, map_add, coeff_five_mul, coeff_five_mul,
    coeff_five_mul, coeff_five_mul, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [bandWeight_table j (Finset.mem_range.mp hj)]
  split_ifs
  · simp only [coeff_thetaS]
    ring
  · simp

end Band

end Zeta7Auxiliary
