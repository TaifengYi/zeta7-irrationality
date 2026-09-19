import Zeta7Proof.CommonRationalGerms
import Mathlib.NumberTheory.Padics.RingHoms

/-! Zero-safe integral caps for actual finite coefficient problems. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
namespace Zeta7Auxiliary
variable {p : ℕ} [Fact p.Prime]

def Integral (z : ℚ_[p]) : Prop := ‖z‖ ≤ 1

theorem integral_iff_lift (z : ℚ_[p]) : Integral z ↔ ∃ a : ℤ_[p], (a : ℚ_[p]) = z := by
  constructor
  · intro h; exact ⟨⟨z, h⟩, rfl⟩
  · rintro ⟨a, rfl⟩; exact a.property

theorem integral_zero : Integral (0 : ℚ_[p]) := by simp [Integral]
theorem integral_one : Integral (1 : ℚ_[p]) := by simp [Integral]
theorem integral_coe (a : ℤ_[p]) : Integral (a : ℚ_[p]) := a.property
theorem integral_nat (a : ℕ) : Integral (a : ℚ_[p]) := by
  simpa [Integral] using Padic.norm_int_le_one (p := p) (a : ℤ)

theorem Integral.add {x y : ℚ_[p]} (hx : Integral x) (hy : Integral y) : Integral (x + y) :=
  (IsUltrametricDist.norm_add_le_max x y).trans (max_le hx hy)

theorem Integral.neg {x : ℚ_[p]} (hx : Integral x) : Integral (-x) := by
  simpa [Integral] using hx

theorem Integral.mul {x y : ℚ_[p]} (hx : Integral x) (hy : Integral y) : Integral (x * y) := by
  change ‖x * y‖ ≤ 1
  rw [norm_mul]
  exact (mul_le_mul hx hy (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)

theorem Integral.pow {x : ℚ_[p]} (hx : Integral x) (n : ℕ) : Integral (x ^ n) := by
  induction n with
  | zero => simpa using (integral_one (p := p))
  | succ n ih => simpa only [pow_succ] using ih.mul hx

theorem integral_sum {ι : Type*} (s : Finset ι) (f : ι → ℚ_[p])
    (h : ∀ i ∈ s, Integral (f i)) : Integral (∑ i ∈ s, f i) :=
  IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one h

theorem integral_prod {ι : Type*} (s : Finset ι) (f : ι → ℚ_[p])
    (h : ∀ i ∈ s, Integral (f i)) : Integral (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (integral_one (p := p))
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi]
    exact (h i (Finset.mem_insert_self _ _)).mul
      (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

def Cap (N e : ℕ) (F : PowerSeries ℚ_[p]) : Prop :=
  ∀ n : ℕ, n < N → Integral ((p : ℚ_[p]) ^ e * PowerSeries.coeff n F)

theorem Cap.mono_range {N M e : ℕ} {F : PowerSeries ℚ_[p]}
    (h : Cap N e F) (hMN : M ≤ N) : Cap M e F := fun n hn => h n (hn.trans_le hMN)

theorem Cap.mono {N e f : ℕ} {F : PowerSeries ℚ_[p]}
    (h : Cap N e F) (hef : e ≤ f) : Cap N f F := by
  intro n hn
  have hh := ((integral_nat (p := p) p).pow (f - e)).mul (h n hn)
  simpa only [← mul_assoc, ← pow_add, Nat.sub_add_cancel hef] using hh

theorem Cap.add {N e : ℕ} {F G : PowerSeries ℚ_[p]}
    (hF : Cap N e F) (hG : Cap N e G) : Cap N e (F + G) := by
  intro n hn
  simpa only [map_add, mul_add] using (hF n hn).add (hG n hn)

theorem Cap.neg {N e : ℕ} {F : PowerSeries ℚ_[p]} (hF : Cap N e F) : Cap N e (-F) := by
  intro n hn
  simpa only [map_neg, mul_neg] using (hF n hn).neg

theorem Cap.const_mul {N e : ℕ} {F : PowerSeries ℚ_[p]}
    (hF : Cap N e F) (a : ℤ_[p]) : Cap N e (PowerSeries.C (a : ℚ_[p]) * F) := by
  intro n hn
  rw [PowerSeries.coeff_C_mul, mul_left_comm]
  exact (integral_coe a).mul (hF n hn)

theorem Cap.shift {N e : ℕ} {F : PowerSeries ℚ_[p]} (hF : Cap N e F) (m : ℕ) :
    Cap (N + m) e (PowerSeries.X ^ m * F) := by
  intro n hn
  rw [PowerSeries.coeff_X_pow_mul']
  split_ifs with hmn
  · exact hF (n - m) (by omega)
  · simpa using (integral_zero (p := p))

theorem Cap.sum {ι : Type*} (s : Finset ι) (F : ι → PowerSeries ℚ_[p]) {N e : ℕ}
    (h : ∀ i ∈ s, Cap N e (F i)) : Cap N e (∑ i ∈ s, F i) := by
  intro n hn
  simp only [map_sum, Finset.mul_sum]
  exact integral_sum s _ (fun i hi => h i hi n hn)

/-- Lifts are unique: residue layers never depend on a choice of integral representative. -/
theorem integral_lift_unique {z : ℚ_[p]} {a b : ℤ_[p]}
    (ha : (a : ℚ_[p]) = z) (hb : (b : ℚ_[p]) = z) : a = b :=
  Subtype.coe_injective (ha.trans hb.symm)

def layerCoefficient {N e : ℕ} {F : PowerSeries ℚ_[p]} (h : Cap N e F) (n : Fin N) : ZMod p :=
  PadicInt.toZMod (⟨(p : ℚ_[p]) ^ e * PowerSeries.coeff n.val F, h n.val n.isLt⟩ : ℤ_[p])

theorem Cap.improve {N e : ℕ} {F : PowerSeries ℚ_[p]} (h : Cap N (e + 1) F)
    (hz : ∀ n : Fin N, layerCoefficient h n = 0) : Cap N e F := by
  intro n hn
  let a : ℤ_[p] := ⟨(p : ℚ_[p]) ^ (e + 1) * PowerSeries.coeff n F, h n hn⟩
  have ha : a ∈ Ideal.span ({(p : ℤ_[p])} : Set ℤ_[p]) := by
    rw [← PadicInt.maximalIdeal_eq_span_p, ← PadicInt.ker_toZMod, RingHom.mem_ker]
    exact hz ⟨n, hn⟩
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp ha
  have he := congrArg (fun z : ℤ_[p] => (z : ℚ_[p])) hb
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have he' : (p : ℚ_[p]) * ((p : ℚ_[p]) ^ e * PowerSeries.coeff n F) = p * (b : ℚ_[p]) := by
    simpa only [a, PadicInt.coe_mul, PadicInt.coe_natCast, pow_succ, mul_assoc, mul_comm,
      mul_left_comm] using he
  rw [mul_left_cancel₀ hp0 he']
  exact integral_coe b

end Zeta7Auxiliary
