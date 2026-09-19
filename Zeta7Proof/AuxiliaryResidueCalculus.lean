import Zeta7Proof.AuxiliaryTransportCaps

/-! Coefficientwise reduction with explicit integrality witnesses. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
namespace Zeta7Auxiliary
open PowerSeries Zeta7Common
variable {p : ℕ} [Fact p.Prime]

def integralResidue (x : ℚ_[p]) (hx : Integral x) : ZMod p :=
  PadicInt.toZMod (⟨x, hx⟩ : ℤ_[p])

theorem integralResidue_congr {x y : ℚ_[p]} (hx : Integral x) (hy : Integral y)
    (h : x = y) : integralResidue x hx = integralResidue y hy := by subst y; rfl

theorem integralResidue_mul {x y : ℚ_[p]} (hx : Integral x) (hy : Integral y) :
    integralResidue (x*y) (hx.mul hy) = integralResidue x hx * integralResidue y hy := by
  let a : ℤ_[p] := ⟨x, hx⟩
  let b : ℤ_[p] := ⟨y, hy⟩
  have h : PadicInt.toZMod (a*b) = PadicInt.toZMod a * PadicInt.toZMod b :=
    map_mul (PadicInt.toZMod (p := p)) a b
  exact h

theorem integralResidue_nat (n : ℕ) :
    integralResidue (n : ℚ_[p]) (integral_nat n) = (n : ZMod p) := by
  change PadicInt.toZMod (n : ℤ_[p]) = _
  exact map_natCast _ n

theorem integralResidue_add {x y : ℚ_[p]} (hx : Integral x) (hy : Integral y) :
    integralResidue (x+y) (hx.add hy) = integralResidue x hx + integralResidue y hy := by
  let a : ℤ_[p] := ⟨x, hx⟩
  let b : ℤ_[p] := ⟨y, hy⟩
  have h : PadicInt.toZMod (a+b) = PadicInt.toZMod a + PadicInt.toZMod b :=
    map_add (PadicInt.toZMod (p := p)) a b
  exact h

theorem integralResidue_nat_mul_eq {x y : ℚ_[p]} (hx : Integral x) (hy : Integral y)
    (a : ℕ) (h : (a : ℚ_[p])*x = y) :
    (a : ZMod p)*integralResidue x hx = integralResidue y hy := by
  rw [← integralResidue_nat (p := p) a, ← integralResidue_mul (integral_nat a) hx]
  exact integralResidue_congr _ _ h

theorem integralResidue_nat_mul_eq_nat_mul {x y : ℚ_[p]}
    (hx : Integral x) (hy : Integral y) (a b : ℕ)
    (h : (a : ℚ_[p])*x = (b : ℚ_[p])*y) :
    (a : ZMod p)*integralResidue x hx = (b : ZMod p)*integralResidue y hy := by
  rw [← integralResidue_nat (p := p) b, ← integralResidue_mul (integral_nat b) hy]
  exact integralResidue_nat_mul_eq hx _ a h

theorem integralResidue_prime_mul {x : ℚ_[p]} (hx : Integral x) :
    integralResidue ((p : ℚ_[p])*x) ((integral_nat p).mul hx) = 0 := by
  rw [integralResidue_mul (integral_nat p) hx, integralResidue_nat, ZMod.natCast_self, zero_mul]

theorem integralResidue_congr_mod_prime {x y z : ℚ_[p]}
    (hx : Integral x) (hy : Integral y) (hz : Integral z)
    (h : x = y + (p : ℚ_[p])*z) : integralResidue x hx = integralResidue y hy := by
  rw [integralResidue_congr hx (hy.add ((integral_nat p).mul hz)) h,
    integralResidue_add hy ((integral_nat p).mul hz), integralResidue_prime_mul hz, add_zero]

theorem layerCoefficient_eq_residue {N e : ℕ} {F : PowerSeries ℚ_[p]}
    (h : Cap N e F) (n : Fin N) :
    layerCoefficient h n = integralResidue _ (h n n.isLt) := rfl

theorem layerCoefficient_mono_succ {N e : ℕ} {F : PowerSeries ℚ_[p]}
    (h : Cap N e F) (h' : Cap N (e+1) F) (n : Fin N) :
    layerCoefficient h' n = 0 := by
  rw [layerCoefficient_eq_residue]
  have he : (p : ℚ_[p])^(e+1)*coeff n.val F =
      p*((p : ℚ_[p])^e*coeff n.val F) := by ring
  exact (integralResidue_congr _ _ he).trans (integralResidue_prime_mul (h n n.isLt))

theorem layerCoefficient_euler {N e : ℕ} {F : PowerSeries ℚ_[p]}
    (h : Cap N e F) (n : Fin N) :
    layerCoefficient h.euler n = (n.val : ZMod p)*layerCoefficient h n := by
  simp only [layerCoefficient_eq_residue]
  have he : (p : ℚ_[p])^e*coeff n.val (euler F) =
      n.val*((p : ℚ_[p])^e*coeff n.val F) := by rw [euler_coeff]; ring
  rw [integralResidue_congr _ ((integral_nat n.val).mul (h n n.isLt)) he,
    integralResidue_mul (integral_nat n.val) (h n n.isLt), integralResidue_nat]

theorem integralResidue_div_nat {x : ℚ_[p]} (hx : Integral x) {n : ℕ}
    (hn : ¬p ∣ n) :
    integralResidue (x / (n : ℚ_[p])) (by simpa [div_eq_mul_inv] using hx.mul (integral_nat_inv hn)) =
      integralResidue x hx / (n : ZMod p) := by
  have hnZ : (n : ZMod p) ≠ 0 := (ZMod.natCast_eq_zero_iff n p).not.mpr hn
  have hnQ : (n : ℚ_[p]) ≠ 0 := by
    exact_mod_cast (show n ≠ 0 from fun h => hn (h ▸ dvd_zero p))
  apply (eq_div_iff hnZ).mpr
  rw [← integralResidue_nat (p := p) n, ← integralResidue_mul
    (show Integral (x / (n : ℚ_[p])) from by simpa [div_eq_mul_inv] using hx.mul (integral_nat_inv hn))
    (integral_nat n)]
  exact integralResidue_congr _ _ (div_mul_cancel₀ _ hnQ)

theorem short_index_unit {N m r : ℕ} (hN : N+p < p^2)
    (hn : m*p+r < N) (hm : 0 < m) : m < p ∧ (m : ZMod p) ≠ 0 := by
  have hp0 := (Fact.out : p.Prime).pos
  have hmp : m < p := by nlinarith
  exact ⟨hmp, (ZMod.natCast_eq_zero_iff m p).not.mpr
    (Nat.not_dvd_of_pos_of_lt hm hmp)⟩

end Zeta7Auxiliary
