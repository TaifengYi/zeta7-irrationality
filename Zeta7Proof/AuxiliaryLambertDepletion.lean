import Zeta7Proof.AuxiliaryTransportCaps

/-! The exact prime-depleted decomposition of the original Lambert series. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
namespace Zeta7Auxiliary
open PowerSeries Zeta7Main
variable {p : ℕ} [Fact p.Prime]

def depletedLambert (p : ℕ) : PowerSeries ℚ :=
  mk (fun n => ∑ a ∈ n.divisors.filter (fun a => ¬7 ∣ a ∧ ¬p ∣ a), (a : ℚ)⁻¹^3)

theorem depletedLambert_integral (n : ℕ) :
    Integral ((coeff n (depletedLambert p) : ℚ) : ℚ_[p]) := by
  simp only [depletedLambert, coeff_mk, Rat.cast_sum, Rat.cast_pow, Rat.cast_inv,
    Rat.cast_natCast]
  apply integral_sum
  intro a ha
  exact (integral_nat_inv (Finset.mem_filter.mp ha).2.2).pow 3

theorem depletedLambert_cap_zero (N : ℕ) :
    Cap N 0 ((depletedLambert p).map (algebraMap ℚ ℚ_[p])) := by
  intro n _
  rw [pow_zero, one_mul, coeff_map]
  change Integral ((coeff n (depletedLambert p) : ℚ) : ℚ_[p])
  exact depletedLambert_integral n

theorem prime_divisor_sum (hp7 : p ≠ 7) (m : ℕ) :
    (∑ a ∈ (p*m).divisors.filter (fun a => ¬7 ∣ a ∧ p ∣ a), (a : ℚ)⁻¹^3) =
      (p : ℚ)⁻¹^3 * coeff m GSeries := by
  classical
  have hp0 := (Fact.out : p.Prime).ne_zero
  have h7p : ¬7 ∣ p := by
    intro h
    exact hp7 ((Nat.dvd_prime (Fact.out : p.Prime)).mp h |>.resolve_left (by decide)).symm
  rw [GSeries_coeff, Finset.mul_sum]
  symm
  apply Finset.sum_bij (fun a _ => p*a)
  · intro a ha
    obtain ⟨⟨ha, hm⟩, h7a⟩ := Finset.mem_filter.mp ha |>.imp_left Nat.mem_divisors.mp
    exact Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr
      ⟨Nat.mul_dvd_mul_left p ha, mul_ne_zero hp0 hm⟩,
      ⟨fun h => ((Nat.Prime.dvd_mul (by decide : Nat.Prime 7)).mp h).elim h7p h7a,
        dvd_mul_right p a⟩⟩
  · intro a _ b _ h
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hp0) h
  · intro b hb
    obtain ⟨⟨hb, hm⟩, h7b, hpb⟩ := Finset.mem_filter.mp hb |>.imp_left Nat.mem_divisors.mp
    obtain ⟨a, rfl⟩ := hpb
    refine ⟨a, Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨?_, ?_⟩, ?_⟩, rfl⟩
    · exact (Nat.mul_dvd_mul_iff_left (Nat.pos_of_ne_zero hp0)).mp hb
    · exact fun h => hm (by simp [h])
    · exact fun h => h7b (h.trans (dvd_mul_left a p))
  · intro a _
    push_cast
    simp only [mul_inv, mul_pow, inv_pow]

theorem GSeries_depletion (hp7 : p ≠ 7) :
    GSeries = depletedLambert p + C ((p : ℚ)⁻¹^3) *
      expand p (Fact.out : p.Prime).ne_zero GSeries := by
  classical
  ext n
  rw [map_add, coeff_C_mul, coeff_expand]
  have hs := Finset.sum_filter_add_sum_filter_not
    (n.divisors.filter (fun a => ¬7 ∣ a)) (fun a => p ∣ a) (fun a => (a : ℚ)⁻¹^3)
  simp only [Finset.filter_filter] at hs
  rw [GSeries_coeff, depletedLambert, coeff_mk]
  by_cases hpn : p ∣ n
  · obtain ⟨m, rfl⟩ := hpn
    rw [if_pos (dvd_mul_right p m), Nat.mul_div_right _ (Fact.out : p.Prime).pos,
      prime_divisor_sum hp7] at *
    simpa only [inv_pow] using hs.symm.trans (add_comm _ _)
  · rw [if_neg hpn, mul_zero, add_zero]
    have hz : n.divisors.filter (fun a => ¬7 ∣ a ∧ p ∣ a) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro a ha
      exact hpn ((Finset.mem_filter.mp ha).2.2.trans
        (Nat.dvd_of_mem_divisors (Finset.mem_filter.mp ha).1))
    simpa [hz] using hs.symm

end Zeta7Auxiliary
