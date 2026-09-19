import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.NumberTheory.Bernoulli
import Zeta7Proof.FinalTheorem

/-!
# Solution: irrationality of `ζ₇(3)`

The declarations of `Challenge.lean` are restated verbatim and proved from the project's final
theorems `Zeta7Main.zeta7Three_irrational` and `Zeta7Main.eta_irrational`. Those depend only on
`propext`, `Classical.choice` and `Quot.sound`.

The project defines `Zeta7Main.zeta7Three` as the value at `3` of the fourth branch of the
Kubota–Leopoldt `7`-adic zeta function, constructed from a `p`-adic measure. It proves
(`Zeta7Main.bernoulli_approximants_tendsto_zeta7Three`) that the Euler-corrected Bernoulli
approximants of the Challenge converge to that value. Hence the Challenge's `zeta7Three`, defined
as their limit, is the same number (`zeta7Three_eq`). This file only bridges the two definitions.
It does not import the archived module `Zeta7Proof.PublishedRadius49GeometricInput`.
-/

namespace Zeta7Challenge

open Filter Topology

/-- `7` is prime. This fixes the field and norm structure on the `7`-adic numbers `ℚ_[7]`. -/
instance (priority := high) fact_prime_seven : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩

/-- The interpolation weights `w_n = 6 · 7^(n+1) - 2`. Each is `≡ 4 (mod 6)`, and `w_n → -2`
`7`-adically. -/
def weight (n : ℕ) : ℕ := 6 * 7 ^ (n + 1) - 2

/-- The `n`-th approximant `-(1 - 7^(w_n - 1)) · B_{w_n} / w_n = (1 - 7^(w_n - 1)) · ζ(1 - w_n)`,
the value `L_7(1 - w_n, ω^{-2})` of the Kubota–Leopoldt `7`-adic `L`-function. Here
`bernoulli` is Mathlib's Bernoulli number; the weights are even, so the convention for `B₁`
plays no role. -/
noncomputable def approximant (n : ℕ) : ℚ_[7] :=
  -(1 - (7 : ℚ_[7]) ^ ((weight n : ℤ) - 1)) * (bernoulli (weight n) : ℚ_[7]) / (weight n : ℚ_[7])

/-- The `7`-adic zeta value `ζ₇(3) = L_7(3, ω^{-2})`, the `7`-adic limit of the approximants
(see `approximant_tendsto`). -/
noncomputable def zeta7Three : ℚ_[7] := limUnder atTop approximant

/-- `η = ζ₇(3) / 2`. -/
noncomputable def eta : ℚ_[7] := zeta7Three / 2

/-- The approximants are the project's Euler-corrected Bernoulli sequence, which converges to the
constructed Kubota–Leopoldt value `Zeta7Main.zeta7Three`. -/
theorem approximant_tendsto_main : Tendsto approximant atTop (𝓝 Zeta7Main.zeta7Three) :=
  Zeta7Main.bernoulli_approximants_tendsto_zeta7Three

/-- The limit definition agrees with the constructed Kubota–Leopoldt value. -/
theorem zeta7Three_eq : zeta7Three = Zeta7Main.zeta7Three :=
  approximant_tendsto_main.limUnder_eq

/-- The approximants converge to `ζ₇(3)` in `ℚ_[7]`. -/
theorem approximant_tendsto : Tendsto approximant atTop (𝓝 zeta7Three) := by
  rw [zeta7Three_eq]
  exact approximant_tendsto_main

/-- **`ζ₇(3)` is irrational**: it is not the image of any rational number in `ℚ_[7]`. -/
theorem zeta7Three_irrational : ¬ ∃ q : ℚ, (q : ℚ_[7]) = zeta7Three := by
  rintro ⟨q, hq⟩
  exact Zeta7Main.zeta7Three_irrational ⟨q, hq.trans zeta7Three_eq⟩

/-- **`η = ζ₇(3)/2` is irrational.** -/
theorem eta_irrational : ¬ ∃ q : ℚ, (q : ℚ_[7]) = eta := by
  rintro ⟨q, hq⟩
  have he : eta = Zeta7Main.eta := by
    rw [eta, zeta7Three_eq]
    rfl
  exact Zeta7Main.eta_irrational ⟨q, hq.trans he⟩

end Zeta7Challenge
