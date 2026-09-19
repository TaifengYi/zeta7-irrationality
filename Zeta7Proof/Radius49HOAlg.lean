import Zeta7Proof.Radius49HOGen
import Zeta7Proof.SerreEisenstein
import PadicLFunctions.EisensteinComplex

/-! Radius internalization, HO: the algebra of the classical approximants (over `ℚ`, in `q`).

* `E4_formal`, `E6_formal`, `VE4_formal`, `VE6_formal`: `E₄ P = A² N`, `E₆ P² = A³ T` and their
  Frobenius versions, as identities of `q`-series.
* `katz_formal : E₆ · T̃(x) = V(E₆) · T(x)` (the Katz ratio).
* `approx_poly`: for the weights `k_r = 6·7^r - 2`, `j = 7^r`, the `7`-stabilized Serre series
  `Fst r = F_r - 7^{k-1} V(F_r)` satisfies `A · Fst r · T(x)^j = E₆^j · S(x)` with `S ∈ ℚ[x]`.
* `uSeven_Fst : U₇ (Fst r) = Fst r`. No published radius input is used. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open PowerSeries UpperHalfPlane Complex Filter Topology
namespace Zeta7Radius49
open Zeta7Main Zeta7Arch Zeta7LevelSeven Zeta7Valence

/-! ### The polynomials in `x` -/

abbrev Px : ℚ⟦X⟧ := 1 + 13 * xSeries + 49 * xSeries ^ 2
abbrev Nx : ℚ⟦X⟧ := 1 + 245 * xSeries + 2401 * xSeries ^ 2
abbrev Tx : ℚ⟦X⟧ := 1 - 490 * xSeries - 21609 * xSeries ^ 2 - 235298 * xSeries ^ 3 -
  823543 * xSeries ^ 4
abbrev Ntx : ℚ⟦X⟧ := 1 + 5 * xSeries + xSeries ^ 2
abbrev Ttx : ℚ⟦X⟧ := 1 + 14 * xSeries + 63 * xSeries ^ 2 + 70 * xSeries ^ 3 - 7 * xSeries ^ 4

theorem E6_formal : E6Q * Px ^ 2 = ASeries ^ 3 * Tx := by
  have h := Zeta7LevelSeven.actual_E6_quotient
  simp only [map_ofNat] at h
  linear_combination h

theorem Px_ne : Px ≠ 0 := by
  intro h
  have := congrArg (constantCoeff (R := ℚ)) h
  simp [xSeries_constant] at this

theorem ASeries_ne : ASeries ≠ 0 := by
  intro h
  have := congrArg (constantCoeff (R := ℚ)) h
  simp [Zeta7Common.ASeries_constant] at this

/-- `E₄ P(x) = A² N(x)` as `q`-series. -/
theorem E4_formal : E4Q * Px = ASeries ^ 2 * Nx := by
  apply map_injective_rat
  simp only [map_mul, map_add, map_pow, map_ofNat, map_one]
  have hE : Tempered (Zeta7Common.eisensteinFourQ.map (algebraMap ℚ ℂ)) := E4Q_tempered
  have hA : Tempered (ASeries.map (algebraMap ℚ ℂ)) := ASeries_tempered
  have hx : Tempered (xSeries.map (algebraMap ℚ ℂ)) := xSeries_tempered
  let S := temperedSubring
  let ee : S := ⟨Zeta7Common.eisensteinFourQ.map (algebraMap ℚ ℂ), hE⟩
  let aa : S := ⟨ASeries.map (algebraMap ℚ ℂ), hA⟩
  let xx : S := ⟨xSeries.map (algebraMap ℚ ℂ), hx⟩
  have hL : Zeta7Common.eisensteinFourQ.map (algebraMap ℚ ℂ) *
      (1 + 13 * xSeries.map (algebraMap ℚ ℂ) + 49 * xSeries.map (algebraMap ℚ ℂ) ^ 2) =
      ((ee * (1 + 13 * xx + 49 * xx ^ 2) : S) : ℂ⟦X⟧) := rfl
  have hR : ASeries.map (algebraMap ℚ ℂ) ^ 2 * (1 + 245 * xSeries.map (algebraMap ℚ ℂ) +
      2401 * xSeries.map (algebraMap ℚ ℂ) ^ 2) =
      ((aa ^ 2 * (1 + 245 * xx + 2401 * xx ^ 2) : S) : ℂ⟦X⟧) := rfl
  rw [hL, hR]
  apply eq_of_evalQ_eventually (Subtype.prop _) (Subtype.prop _)
  apply eventually_punctured_of_atImInfty
  filter_upwards [Filter.univ_mem] with σ _
  have hq := norm_qParam_one_lt σ
  have e : ∀ f : S, evalQ (f : ℂ⟦X⟧) (Function.Periodic.qParam 1 (σ : ℂ)) =
      evalHom _ hq f := fun _ => rfl
  rw [e, e]
  simp only [map_mul, map_add, map_pow, map_ofNat, map_one]
  have h1 : evalHom _ hq ee = classicalE4 σ := evalQ_E4 σ
  have h2 : evalHom _ hq aa = actualA σ := evalQ_A σ
  have h3 : evalHom _ hq xx = etaCoordinate σ := xFun_qParam σ
  rw [h1, h2, h3]
  have := E4_function σ
  simp only [polyP, polyN] at this
  linear_combination this

/-- **The Katz ratio** `E₆ · T̃(x) = V(E₆) · T(x)`. -/
theorem katz_formal : E6Q * Ttx = vSeven E6Q * Tx := by
  have h1 := E6_formal
  have h2 := VE6_formal
  apply mul_left_cancel₀ (pow_ne_zero 3 ASeries_ne)
  apply mul_left_cancel₀ (pow_ne_zero 2 Px_ne)
  linear_combination (ASeries ^ 3 * Ttx) * h1 - (ASeries ^ 3 * Tx) * h2


/-! ### Polynomials in `x` -/

/-- The polynomials in `x(q)`. -/
def PX : Subalgebra ℚ ℚ⟦X⟧ := (Polynomial.aeval xSeries).range

theorem x_mem_PX : xSeries ∈ PX := ⟨Polynomial.X, by simp⟩

theorem Px_mem : Px ∈ PX := by
  have hx := x_mem_PX
  apply Subalgebra.add_mem _ (Subalgebra.add_mem _ (Subalgebra.one_mem _)
    (Subalgebra.mul_mem _ (Subalgebra.natCast_mem _ 13) hx))
  exact Subalgebra.mul_mem _ (Subalgebra.natCast_mem _ 49) (Subalgebra.pow_mem _ hx 2)

theorem Nx_mem : Nx ∈ PX := by
  have hx := x_mem_PX
  apply Subalgebra.add_mem _ (Subalgebra.add_mem _ (Subalgebra.one_mem _)
    (Subalgebra.mul_mem _ (Subalgebra.natCast_mem _ 245) hx))
  exact Subalgebra.mul_mem _ (Subalgebra.natCast_mem _ 2401) (Subalgebra.pow_mem _ hx 2)

theorem Ntx_mem : Ntx ∈ PX := by
  have hx := x_mem_PX
  apply Subalgebra.add_mem _ (Subalgebra.add_mem _ (Subalgebra.one_mem _)
    (Subalgebra.mul_mem _ (Subalgebra.natCast_mem _ 5) hx))
  exact Subalgebra.pow_mem _ hx 2

theorem Tx_mem : Tx ∈ PX := by
  have hx := x_mem_PX
  refine Subalgebra.sub_mem _ (Subalgebra.sub_mem _ (Subalgebra.sub_mem _ (Subalgebra.sub_mem _
    (Subalgebra.one_mem _) (Subalgebra.mul_mem _ (Subalgebra.natCast_mem _ 490) hx))
    (Subalgebra.mul_mem _ (Subalgebra.natCast_mem _ 21609) (Subalgebra.pow_mem _ hx 2)))
    (Subalgebra.mul_mem _ (Subalgebra.natCast_mem _ 235298) (Subalgebra.pow_mem _ hx 3)))
    (Subalgebra.mul_mem _ (Subalgebra.natCast_mem _ 823543) (Subalgebra.pow_mem _ hx 4))

theorem Ttx_mem : Ttx ∈ PX := by
  have hx := x_mem_PX
  refine Subalgebra.sub_mem _ (Subalgebra.add_mem _ (Subalgebra.add_mem _ (Subalgebra.add_mem _
    (Subalgebra.one_mem _) (Subalgebra.mul_mem _ (Subalgebra.natCast_mem _ 14) hx))
    (Subalgebra.mul_mem _ (Subalgebra.natCast_mem _ 63) (Subalgebra.pow_mem _ hx 2)))
    (Subalgebra.mul_mem _ (Subalgebra.natCast_mem _ 70) (Subalgebra.pow_mem _ hx 3)))
    (Subalgebra.mul_mem _ (Subalgebra.natCast_mem _ 7) (Subalgebra.pow_mem _ hx 4))

/-! ### Monomials -/

/-- A generic form: `A · E₄'^a E₆'^b · T^j = E₆^j · N'^a S^b P^{t+1}` from
`E₄' P = A² N'`, `E₆' P² = A³ S` and `E₆ P² = A³ T`. -/
theorem mono_identity_gen' {R : Type*} [CommRing R] [IsDomain R] (A E4' E6' E6 P N' T S : R)
    (hP : P ≠ 0) (h4 : E4' * P = A ^ 2 * N') (h6 : E6' * P ^ 2 = A ^ 3 * S)
    (h6' : E6 * P ^ 2 = A ^ 3 * T) (t b : ℕ) :
    A * (E4' ^ (3 * t + 1) * E6' ^ b) * T ^ (b + 2 * t + 1) =
      E6 ^ (b + 2 * t + 1) * (N' ^ (3 * t + 1) * S ^ b * P ^ (t + 1)) := by
  apply mul_left_cancel₀ (pow_ne_zero (3 * t + 1 + 2 * b) hP)
  calc P ^ (3 * t + 1 + 2 * b) * (A * (E4' ^ (3 * t + 1) * E6' ^ b) * T ^ (b + 2 * t + 1))
      = A * (E4' * P) ^ (3 * t + 1) * (E6' * P ^ 2) ^ b * T ^ (b + 2 * t + 1) := by ring
    _ = A * (A ^ 2 * N') ^ (3 * t + 1) * (A ^ 3 * S) ^ b * T ^ (b + 2 * t + 1) := by rw [h4, h6]
    _ = (A ^ 3 * T) ^ (b + 2 * t + 1) * (N' ^ (3 * t + 1) * S ^ b) := by ring
    _ = (E6 * P ^ 2) ^ (b + 2 * t + 1) * (N' ^ (3 * t + 1) * S ^ b) := by rw [h6']
    _ = P ^ (3 * t + 1 + 2 * b) *
          (E6 ^ (b + 2 * t + 1) * (N' ^ (3 * t + 1) * S ^ b * P ^ (t + 1))) := by ring

theorem mono_identity (t b : ℕ) :
    ASeries * (E4Q ^ (3 * t + 1) * E6Q ^ b) * Tx ^ (b + 2 * t + 1) =
      E6Q ^ (b + 2 * t + 1) * (Nx ^ (3 * t + 1) * Tx ^ b * Px ^ (t + 1)) :=
  mono_identity_gen' _ _ _ _ _ _ _ _ Px_ne E4_formal E6_formal E6_formal t b

theorem Vmono_identity (t b : ℕ) :
    ASeries * (vSeven E4Q ^ (3 * t + 1) * vSeven E6Q ^ b) * Tx ^ (b + 2 * t + 1) =
      E6Q ^ (b + 2 * t + 1) * (Ntx ^ (3 * t + 1) * Ttx ^ b * Px ^ (t + 1)) :=
  mono_identity_gen' _ _ _ _ _ _ _ _ Px_ne VE4_formal VE6_formal E6_formal t b

/-- The polynomial property of weight `6j - 2` combinations. -/
theorem span_poly (j : ℕ) {F : ℚ⟦X⟧} (hF : F ∈ Submodule.span ℚ (monoSet (6 * j - 2)))
    (hj : 1 ≤ j) :
    (∃ S ∈ PX, ASeries * F * Tx ^ j = E6Q ^ j * S) ∧
      (∃ S ∈ PX, ASeries * vSeven F * Tx ^ j = E6Q ^ j * S) := by
  induction hF using Submodule.span_induction with
  | mem s hs =>
    obtain ⟨a, b, hab, rfl⟩ := hs
    obtain ⟨t, rfl⟩ : ∃ t, a = 3 * t + 1 := ⟨a / 3, by omega⟩
    obtain rfl : j = b + 2 * t + 1 := by omega
    refine ⟨⟨_, ?_, mono_identity t b⟩, ⟨Ntx ^ (3 * t + 1) * Ttx ^ b * Px ^ (t + 1), ?_, ?_⟩⟩
    · exact Subalgebra.mul_mem _ (Subalgebra.mul_mem _ (Subalgebra.pow_mem _ Nx_mem _)
        (Subalgebra.pow_mem _ Tx_mem _)) (Subalgebra.pow_mem _ Px_mem _)
    · exact Subalgebra.mul_mem _ (Subalgebra.mul_mem _ (Subalgebra.pow_mem _ Ntx_mem _)
        (Subalgebra.pow_mem _ Ttx_mem _)) (Subalgebra.pow_mem _ Px_mem _)
    · have hV : vSeven (E4Q ^ (3 * t + 1) * E6Q ^ b) = vSeven E4Q ^ (3 * t + 1) * vSeven E6Q ^ b := by
        simp only [vSeven, map_mul, map_pow]
      rw [hV]; exact Vmono_identity t b
  | zero =>
    refine ⟨⟨0, Subalgebra.zero_mem _, by simp⟩, ⟨0, Subalgebra.zero_mem _, ?_⟩⟩
    simp [vSeven]
  | add x y _ _ hx hy =>
    obtain ⟨⟨S1, hS1, e1⟩, ⟨V1, hV1, f1⟩⟩ := hx
    obtain ⟨⟨S2, hS2, e2⟩, ⟨V2, hV2, f2⟩⟩ := hy
    refine ⟨⟨S1 + S2, Subalgebra.add_mem _ hS1 hS2, ?_⟩, ⟨V1 + V2, Subalgebra.add_mem _ hV1 hV2, ?_⟩⟩
    · linear_combination e1 + e2
    · have : vSeven (x + y) = vSeven x + vSeven y := map_add (vSevenHom ℚ) x y
      rw [this]; linear_combination f1 + f2
  | smul c x _ hx =>
    obtain ⟨⟨S1, hS1, e1⟩, ⟨V1, hV1, f1⟩⟩ := hx
    refine ⟨⟨c • S1, Subalgebra.smul_mem _ hS1 c, ?_⟩, ⟨c • V1, Subalgebra.smul_mem _ hV1 c, ?_⟩⟩
    · rw [smul_eq_C_mul, smul_eq_C_mul]; linear_combination C c * e1
    · have : vSeven (c • x) = c • vSeven x := map_smul (vSevenHom ℚ) c x
      rw [this, smul_eq_C_mul, smul_eq_C_mul]; linear_combination C c * f1

/-! ### The stabilized Serre series -/

/-- `F_r` (the level-one Eisenstein series of weight `k_r = 6·7^r - 2`). -/
abbrev Fr (r : ℕ) : ℚ⟦X⟧ := classicalRationalSeries r

/-- The `7`-stabilization `F_r - 7^{k_r - 1} V(F_r)`. -/
def Fst (r : ℕ) : ℚ⟦X⟧ := Fr r - C ((7 : ℚ) ^ (serreWeight r - 1)) * vSeven (Fr r)

theorem serreWeight_eq (r : ℕ) : serreWeight r = 6 * 7 ^ r - 2 := rfl

theorem Fr_span (r : ℕ) : Fr r ∈ Submodule.span ℚ (monoSet (6 * 7 ^ r - 2)) := by
  have h := span_of_qExpansion (serreWeight r)
    (by rw [serreWeight_eq]; have := Nat.one_le_pow r 7 (by norm_num); omega)
    (classicalEisensteinForm r) (Fr r) (classicalEisensteinForm_qExpansion r)
  exact h

/-- **Polynomial structure of the approximants.** -/
theorem approx_poly (r : ℕ) :
    ∃ S ∈ PX, ASeries * Fst r * Tx ^ (7 ^ r) = E6Q ^ (7 ^ r) * S := by
  have hj : 1 ≤ 7 ^ r := Nat.one_le_pow r 7 (by norm_num)
  obtain ⟨⟨S1, hS1, e1⟩, ⟨V1, hV1, f1⟩⟩ := span_poly (7 ^ r) (Fr_span r) hj
  refine ⟨S1 - C ((7 : ℚ) ^ (serreWeight r - 1)) * V1, ?_, ?_⟩
  · apply Subalgebra.sub_mem _ hS1
    rw [← smul_eq_C_mul]; exact Subalgebra.smul_mem _ hV1 _
  · rw [Fst]; linear_combination e1 - C ((7 : ℚ) ^ (serreWeight r - 1)) * f1


/-! ### `U₇`-fixedness of the stabilized series -/

/-- The prime-to-`7` divisor power sum over `ℚ`. -/
def sStar (k m : ℕ) : ℚ := ∑ d ∈ m.divisors.filter (fun d => ¬ 7 ∣ d), (d : ℚ) ^ k

theorem full_split (k m : ℕ) (hm : m ≠ 0) :
    (∑ d ∈ m.divisors, (d : ℚ) ^ k) =
      sStar k m + if 7 ∣ m then (7 : ℚ) ^ k * ∑ d ∈ (m / 7).divisors, (d : ℚ) ^ k else 0 := by
  split_ifs with h7
  · have h := PadicLFunctions.sigmaP_add_pow_mul_sigma_div (p := 7) h7 hm k
    have hc := congrArg (fun n : ℕ => (n : ℚ)) h
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, PadicLFunctions.sigmaP,
      ArithmeticFunction.sigma_apply, Nat.cast_sum] at hc
    rw [sStar, ← hc]
    push_cast
    ring
  · rw [sStar, add_zero]
    apply (Finset.sum_filter_of_ne _).symm
    intro d hd _ h7d
    exact h7 (h7d.trans (Nat.mem_divisors.mp hd).1)

theorem sStar_seven (k n : ℕ) : sStar k (7 * n) = sStar k n := by
  rw [sStar, sStar, divisors_filter_seven]

theorem coeff_Fst (r m : ℕ) :
    coeff m (Fst r) = fullEisensteinCoeff (serreWeight r) m -
      (7 : ℚ) ^ (serreWeight r - 1) *
        (if 7 ∣ m then fullEisensteinCoeff (serreWeight r) (m / 7) else 0) := by
  rw [Fst, map_sub, coeff_C_mul, coeff_vSeven, Fr, classicalRationalSeries, coeff_mk]
  split_ifs <;> simp [coeff_mk]

/-- **The stabilized series is `U₇`-fixed.** -/
theorem uSeven_Fst (r : ℕ) : uSeven (Fst r) = Fst r := by
  ext n
  rw [coeff_uSeven, coeff_Fst, coeff_Fst]
  have h7n : 7 ∣ 7 * n := dvd_mul_right 7 n
  rw [if_pos h7n, Nat.mul_div_cancel_left n (by norm_num)]
  set k := serreWeight r
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hn0 : n ≠ 0 := hn.ne'
    have h7n0 : 7 * n ≠ 0 := by omega
    have eF : ∀ m : ℕ, m ≠ 0 → fullEisensteinCoeff k m = ∑ d ∈ m.divisors, (d : ℚ) ^ (k - 1) :=
      fun m hm => by simp [fullEisensteinCoeff, hm]
    rw [eF (7 * n) h7n0, eF n hn0, full_split (k - 1) (7 * n) h7n0, if_pos h7n,
      Nat.mul_div_cancel_left n (by norm_num), full_split (k - 1) n hn0, sStar_seven]
    by_cases h7 : 7 ∣ n
    · rw [if_pos h7, if_pos h7, eF (n / 7) (by omega)]; ring
    · rw [if_neg h7, if_neg h7]; ring

end Zeta7Radius49
