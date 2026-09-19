import Zeta7Proof.Radius49Bridge
import Zeta7Proof.Radius49FromPublishedGeometry
import Zeta7Proof.EisensteinSpecialization

/-! Phase VI, R3 (formal part): the `U₇` operator on q-expansions and the eigenvalue `1` of the
weight `-2` Eisenstein specialization, and the R1 equivalence.

* `uSeven f = ∑ aₙ₇ qⁿ`.
* `uSeven_GSeries`: `U₇ G = G`, because the divisors of `7n` prime to `7` are those of `n`.
* `uSeven_eisensteinMinusTwo`: `U₇ E₋₂* = E₋₂*` for the actual specialization `G + η`.
* `hasRadius49_iff_HSeries_decay`: the geometric continuation statement is equivalent to
  coefficient decay of `HSeries` on every disc of radius `< 49`.

No declaration here uses the published radius input. -/

set_option autoImplicit false
noncomputable section
namespace Zeta7Main
open PowerSeries Filter Topology Zeta7Radius49
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

/-- **R1 equivalence.** -/
theorem hasRadius49_iff_HSeries_decay :
    HasRadius49GeometricContinuation ↔
      ∀ ρ : ℝ, 0 < ρ → ρ < 49 →
        Tendsto (fun n : ℕ => ‖coeff n HSeries‖ * ρ ^ n) atTop (𝓝 0) :=
  ⟨HSeries_radius49_of_geometric_continuation, hasRadius49_of_HSeries_decay⟩

/-- The Atkin operator `U₇` on formal q-expansions. -/
def uSeven {R : Type*} [CommRing R] (f : R⟦X⟧) : R⟦X⟧ := mk fun n => coeff (7 * n) f

theorem coeff_uSeven {R : Type*} [CommRing R] (f : R⟦X⟧) (n : ℕ) :
    coeff n (uSeven f) = coeff (7 * n) f := coeff_mk _ _

theorem uSeven_add {R : Type*} [CommRing R] (f g : R⟦X⟧) :
    uSeven (f + g) = uSeven f + uSeven g := by
  ext n; simp only [coeff_uSeven, map_add]

theorem uSeven_C {R : Type*} [CommRing R] (c : R) : uSeven (C c) = C c := by
  ext n
  rw [coeff_uSeven, coeff_C, coeff_C]
  by_cases h : n = 0 <;> simp [h]

theorem uSeven_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (f : R⟦X⟧) :
    uSeven (f.map φ) = (uSeven f).map φ := by
  ext n; simp only [coeff_uSeven, coeff_map]

/-- Divisors of `7n` prime to `7` are the divisors of `n` prime to `7`. -/
theorem divisors_filter_seven (n : ℕ) :
    (7 * n).divisors.filter (fun a => ¬ 7 ∣ a) = n.divisors.filter (fun a => ¬ 7 ∣ a) := by
  ext a
  simp only [Finset.mem_filter, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨ha, hn⟩, h7⟩
    refine ⟨⟨?_, by omega⟩, h7⟩
    have hc : Nat.Coprime a 7 :=
      (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd (by decide : Nat.Prime 7)).mpr h7))
    exact hc.dvd_of_dvd_mul_left ha
  · rintro ⟨⟨ha, hn⟩, h7⟩
    exact ⟨⟨Dvd.dvd.mul_left ha 7, by omega⟩, h7⟩

theorem uSeven_GSeries : uSeven GSeries = GSeries := by
  ext n
  rw [coeff_uSeven, GSeries_coeff, GSeries_coeff, divisors_filter_seven]

/-- **`U₇`-eigenvalue `1`** of the weight `-2` Eisenstein specialization. -/
theorem uSeven_eisensteinMinusTwo : uSeven eisensteinMinusTwo = eisensteinMinusTwo := by
  rw [eisensteinMinusTwo_eq_G_add_eta, uSeven_add, uSeven_C, uSeven_map, uSeven_GSeries]

end Zeta7Main
