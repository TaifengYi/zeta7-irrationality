import Mathlib

/-! Exact characteristic-p multiplicity restrictions, with all size bounds explicit. -/
noncomputable section
set_option autoImplicit false
namespace Zeta7Auxiliary

theorem bounded_mod (p a : ℕ) (hp : 0 < p) (ha : a < 2*p) :
    a%p = if a<p then a else a-p := by
  split_ifs with h
  · exact Nat.mod_eq_of_lt h
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

theorem multiplicity_congruence_impossible (p m r : ℕ) [Fact p.Prime]
    (hp : 11 ≤ p) (hm : 0 < m) (hm' : m ≤ 2*((p-1)/3))
    (hr : r=1 ∨ r=2) : (3*m)%p ≠ (3*((p-1)/3)+r)%p := by
  have hp3 : p%3 ≠ 0 := by
    intro h
    have hd : 3 ∣ p := Nat.dvd_of_mod_eq_zero h
    have he := (Nat.dvd_prime (Fact.out : p.Prime)).mp hd
    rcases he with he | he <;> omega
  rw [bounded_mod p (3*m) (by omega) (by omega),
    bounded_mod p (3*((p-1)/3)+r) (by omega) (by rcases hr with rfl | rfl <;> omega)]
  split_ifs <;> rcases hr with rfl | rfl <;> omega

theorem small_natCast_ne_zero {K : Type*} [Field K] (p m : ℕ) [CharP K p]
    (hm : 0 < m) (hmp : m<p) : (m:K) ≠ 0 := by
  intro h
  have hd := (CharP.cast_eq_zero_iff K p m).mp h
  have := Nat.le_of_dvd hm hd
  omega

theorem ordinary_multiplicity_one {K : Type*} [Field K] (p m : ℕ) [CharP K p]
    (hp : 1 < p) (hm : 0 < m) (hmp : m < p) (he : (m:K)^2-(m:K)=0) : m=1 := by
  have hm0 := small_natCast_ne_zero (K := K) p m hm hmp
  have hf : (m:K)*((m:K)-1)=0 := by linear_combination he
  have h1 := sub_eq_zero.mp ((mul_eq_zero.mp hf).resolve_left hm0)
  have hc : (m:K)=(1:ℕ) := by simpa using h1
  have hh := (CharP.cast_eq_iff_mod_eq K p).mp hc
  simpa [Nat.mod_eq_of_lt hmp, Nat.mod_eq_of_lt hp] using hh

theorem singular_multiplicity_impossible {K : Type*} [Field K] (p m : ℕ)
    [Fact p.Prime] [CharP K p] (hp : 11 ≤ p) (hm : 0 < m)
    (hm' : m ≤ 2*((p-1)/3)) :
    9*((m:K)-((p-1)/3:ℕ))^2-9*((m:K)-((p-1)/3:ℕ))+2 ≠ 0 := by
  intro he
  have hf : (3*((m:K)-((p-1)/3:ℕ))-1)*(3*((m:K)-((p-1)/3:ℕ))-2)=0 := by
    linear_combination he
  rcases mul_eq_zero.mp hf with h | h
  · have hc : ((3*m:ℕ):K)=((3*((p-1)/3)+1:ℕ):K) := by
      push_cast; linear_combination h
    exact multiplicity_congruence_impossible p m 1 hp hm hm' (Or.inl rfl)
      ((CharP.cast_eq_iff_mod_eq K p).mp hc)
  · have hc : ((3*m:ℕ):K)=((3*((p-1)/3)+2:ℕ):K) := by
      push_cast; linear_combination h
    exact multiplicity_congruence_impossible p m 2 hp hm hm' (Or.inr rfl)
      ((CharP.cast_eq_iff_mod_eq K p).mp hc)

end Zeta7Auxiliary
