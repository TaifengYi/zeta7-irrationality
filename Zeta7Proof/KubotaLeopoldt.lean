import PadicLFunctions.Interpolation.BranchContinuity

/-!
# The genuine Kubota–Leopoldt value at 3, for p = 7

The imported construction is the Mahler-transform measure construction of
Rodrigues Jacinto–Williams, adapted from Chris Birkbeck's formalization.
See KL_CONSTRUCTION_PROVENANCE.md for the exact upstream revision and changes.

Our convention is branch 4: its weight character at s = 3 is x ↦ x⁻².
The proofs below exclude a zero denominator at this specialization. The
interpolation theorem retains the Euler factor and mathlib's B₁ = -1/2.
No irrationality or manuscript-specific identification is assumed here.
-/

set_option autoImplicit false

namespace PadicLFunctions

open PadicInt

/-- Negative integral powers of a principal unit cancel positive powers.
This uses the constructed continuous additive character, over any prime. -/
theorem onePAdicPow_neg_nat_mul (p : ℕ) [Fact p.Prime]
    (y : ℤ_[p]) (hy : y - 1 ∈ Ideal.span {(p : ℤ_[p])}) (n : ℕ) :
    onePAdicPow p y hy (-(n : ℤ_[p])) * y ^ n = 1 := by
  rw [← onePAdicPow_natCast p y hy n, ← AddChar.map_add_eq_mul]
  simp

end PadicLFunctions

namespace Zeta7Main

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

open PadicInt PadicLFunctions
open Filter Topology

/-- The fourth branch, whose interpolation weights are 4 modulo 6. -/
noncomputable def zetaSevenBranch (s : ℤ_[7]) : ℚ_[7] :=
  zetaPBranch 7 (by decide) 4 s

/-- The actual Kubota–Leopoldt weight-minus-two specialization.
The source defines the measure via a convergent Mahler series, not by
assuming an interpolation or irrationality theorem. -/
noncomputable def zeta7Three : ℚ_[7] := zetaSevenBranch 3

/-- At s = 3 the character is the inverse square on every seven-adic unit,
expressed without partial inversion in the integer ring. -/
theorem branch_four_neg_two_mul_square (x : ℤ_[7]ˣ) :
    branchChar 7 4 (-2) x * (x : ℤ_[7]) ^ 2 = 1 := by
  have ht : (teichmuller 7 x : ℤ_[7]) ^ 6 = 1 := by
    simpa only [teichmuller_coe] using teichmullerFun_pow_card_sub_one 7 x
  have hx : (x : ℤ_[7]) =
      (teichmuller 7 x : ℤ_[7]) * (angleUnit 7 x : ℤ_[7]) :=
    (congrArg Units.val (teichmuller_mul_angleUnit 7 x)).symm
  have he := onePAdicPow_neg_nat_mul 7 (angleUnit 7 x : ℤ_[7])
    (angleUnit_sub_one_mem 7 x) 2
  norm_num only [Nat.cast_ofNat] at he
  rw [branchChar_apply, hx]
  calc
    _ = (teichmuller 7 x : ℤ_[7]) ^ 6 *
        (onePAdicPow 7 (angleUnit 7 x : ℤ_[7]) (angleUnit_sub_one_mem 7 x) (-2) *
          (angleUnit 7 x : ℤ_[7]) ^ 2) := by ring
    _ = 1 := by rw [ht, one_mul, he]

/-- Field-valued version of the exact weight-character normalization. -/
theorem branch_four_neg_two_eq_inv_square (x : ℤ_[7]ˣ) :
    ((branchChar 7 4 (-2) x : ℤ_[7]) : ℚ_[7]) =
      ((((x : ℤ_[7]) : ℚ_[7]) ^ 2))⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  have h := congrArg (fun a : ℤ_[7] => (a : ℚ_[7])) (branch_four_neg_two_mul_square x)
  simpa only [PadicInt.coe_mul, PadicInt.coe_pow, PadicInt.coe_one] using h

/-- The canonical integer topological generator supplied by the proved
existence theorem of the measure construction. -/
noncomputable def zetaSevenGenerator : ℤ_[7]ˣ :=
  (PadicMeasure.exists_nat_topological_generator 7 (by decide)).choose_spec.choose

/-- The Mellin-pairing denominator at the intended value is nonzero. -/
theorem zeta7Three_denominator_ne_zero :
    ((branchChar 7 4 (1 - (3 : ℤ_[7])) zetaSevenGenerator : ℤ_[7]) : ℚ_[7]) - 1 ≠ 0 := by
  intro h
  rw [show 1 - (3 : ℤ_[7]) = -2 by ring] at h
  have hb : branchChar 7 4 (-2) zetaSevenGenerator = 1 := by
    apply Subtype.coe_injective
    exact sub_eq_zero.mp h
  have hs := branch_four_neg_two_mul_square zetaSevenGenerator
  rw [hb, one_mul] at hs
  exact PadicMeasure.topGen_pow_ne_one 7
    (PadicMeasure.exists_nat_topological_generator 7 (by decide)).choose_spec.choose_spec.2.2
    2 (by decide) hs

/-- Euler-corrected interpolation for all positive weights on this branch. -/
theorem zetaSevenBranch_interpolation {k : ℕ} (hk : 0 < k)
    (hbranch : (k : ZMod 6) = 4) :
    zetaSevenBranch (1 - (k : ℤ_[7])) =
      (1 - (7 : ℚ_[7]) ^ ((k : ℤ) - 1)) * ((zetaNeg (k - 1) : ℚ) : ℚ_[7]) :=
  zetaPBranch_interpolation 7 (by decide) hk hbranch

/-- The sign and Bernoulli normalization on the fourth branch. -/
theorem zetaSevenBranch_interpolation_bernoulli {k : ℕ} (hk : 0 < k)
    (hbranch : (k : ZMod 6) = 4) :
    zetaSevenBranch (1 - (k : ℤ_[7])) =
      -(1 - (7 : ℚ_[7]) ^ ((k : ℤ) - 1)) * (bernoulli k : ℚ_[7]) / k := by
  have hmod : k % 6 = 4 := (ZMod.natCast_eq_natCast_iff k 4 6).mp hbranch
  have he : Odd (k - 1) := by rw [Nat.odd_iff]; omega
  rw [zetaSevenBranch_interpolation hk hbranch, zetaNeg,
    show k - 1 + 1 = k by omega, he.neg_one_pow]
  push_cast
  rw [Nat.cast_sub (show 1 ≤ k by omega)]
  push_cast
  ring

/-- Continuity at the actual specialization, justified by its nonzero denominator. -/
theorem continuousAt_zetaSevenBranch_three : ContinuousAt zetaSevenBranch 3 := by
  have hden : Continuous (fun s : ℤ_[7] =>
      ((branchChar 7 4 (1 - s) zetaSevenGenerator : ℤ_[7]) : ℚ_[7]) - 1) := by
    refine (continuous_subtype_val.comp ?_).sub continuous_const
    exact continuous_const.mul ((continuous_onePAdicPow 7 _ _).comp
      (continuous_const.sub continuous_id))
  exact (hden.continuousAt.inv₀ zeta7Three_denominator_ne_zero).mul
    (continuous_zetaNum_branch_pairing 7
      (PadicMeasure.exists_nat_topological_generator 7 (by decide)).choose 4).continuousAt

/-- The positive classical weights fixed in the master ledger. -/
def interpolationWeight (n : ℕ) : ℕ := 6 * 7 ^ (n + 1) - 2

theorem interpolationWeight_pos (n : ℕ) : 0 < interpolationWeight n := by
  have h : 0 < 7 ^ (n + 1) := pow_pos (by decide) _
  unfold interpolationWeight
  omega

theorem interpolationWeight_branch (n : ℕ) : (interpolationWeight n : ZMod 6) = 4 := by
  have h : 0 < 7 ^ (n + 1) := pow_pos (by decide) _
  rw [interpolationWeight, Nat.cast_sub (by omega)]
  push_cast
  rw [show (6 : ZMod 6) = 0 from by decide, zero_mul]
  decide

theorem interpolationWeight_cast (n : ℕ) :
    (interpolationWeight n : ℤ_[7]) = 6 * (7 : ℤ_[7]) ^ (n + 1) - 2 := by
  have h : 0 < 7 ^ (n + 1) := pow_pos (by decide) _
  rw [interpolationWeight, Nat.cast_sub (by omega)]
  push_cast
  rfl

/-- The arguments 1-w(n) converge to 3 in the seven-adic topology. -/
theorem interpolationArgument_tendsto :
    Tendsto (fun n => 1 - (interpolationWeight n : ℤ_[7])) atTop (𝓝 3) := by
  have hp : Tendsto (fun n : ℕ => (7 : ℤ_[7]) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one (by
      change ‖((7 : ℕ) : ℤ_[7])‖ < 1
      rw [PadicInt.norm_p]
      norm_num)
  have hs := hp.comp (tendsto_add_atTop_nat 1)
  have ht := (tendsto_const_nhds (x := (3 : ℤ_[7]))).sub
    ((tendsto_const_nhds (x := (6 : ℤ_[7]))).mul hs)
  convert ht using 1
  · funext n
    rw [interpolationWeight_cast]
    simp only [Function.comp_apply]
    ring
  · simp

/-- The planned Euler-corrected Bernoulli sequence converges to the actual
constructed KL value. This is a theorem about zeta7Three, not a definition
using an unproved limit or an arbitrary parameter. -/
theorem bernoulli_approximants_tendsto_zeta7Three :
    Tendsto (fun n =>
      -(1 - (7 : ℚ_[7]) ^ ((interpolationWeight n : ℤ) - 1)) *
        (bernoulli (interpolationWeight n) : ℚ_[7]) / interpolationWeight n)
      atTop (𝓝 zeta7Three) := by
  have ht := continuousAt_zetaSevenBranch_three.tendsto.comp interpolationArgument_tendsto
  change Tendsto _ atTop (𝓝 (zetaSevenBranch 3))
  convert ht using 1
  funext n
  exact (zetaSevenBranch_interpolation_bernoulli
    (interpolationWeight_pos n) (interpolationWeight_branch n)).symm

end Zeta7Main
