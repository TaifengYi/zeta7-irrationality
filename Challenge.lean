import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.NumberTheory.Bernoulli

/-!
# Irrationality of the 7-adic zeta value `ζ₇(3)`

This file states the result. It imports only Mathlib.

## The number `ζ₇(3)`

For a prime `p` and an odd integer `k ≥ 3`, the `p`-adic zeta value `ζ_p(k)` is the value at
`s = k` of the Kubota–Leopoldt `p`-adic `L`-function `L_p(s, ω^{1-k})`, where `ω` is the
Teichmüller character. Equivalently (Lai–Lupu–Sprang, *On the irrationality of certain `p`-adic
zeta values*, 2025) it is the `p`-adic limit of `ζ(m)` over negative integers `m → k`
`p`-adically with `m ≡ k (mod p - 1)`.

For `p = 7`, `k = 3`, take the weights `w_n = 6·7^{n+1} - 2`. They satisfy `w_n ≡ 4 (mod 6)` and
`w_n → -2` in `ℤ₇`, so `1 - w_n ≡ 3 (mod 6)` and `1 - w_n → 3`. Since
`ζ(1 - w) = -B_w / w` for even `w ≥ 2`, the interpolation property gives
`L_7(1 - w_n, ω^{-2}) = -(1 - 7^{w_n - 1}) · B_{w_n} / w_n`, and
`ζ₇(3) = lim_{n → ∞} -(1 - 7^{w_n - 1}) · B_{w_n} / w_n`.
The Euler factor `1 - 7^{w_n - 1}` tends to `1` in `ℚ₇`. It is kept because it gives the exact
values of the Kubota–Leopoldt function at `1 - w_n`.

Below, `zeta7Three` is defined as this limit (`limUnder`), and `approximant_tendsto` states that
the sequence really converges to it. The definition therefore does not rely on the junk value
that `limUnder` assigns to a divergent sequence.

## The theorems

* `approximant_tendsto`: the Bernoulli approximants converge in `ℚ₇` to `zeta7Three`.
* `zeta7Three_irrational`: `ζ₇(3)` is not in the image of `ℚ → ℚ₇`, i.e. `ζ₇(3)` is irrational.
* `eta_irrational`: the same for `η = ζ₇(3)/2` (an immediate consequence, stated for completeness).
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

/-- The approximants converge to `ζ₇(3)` in `ℚ_[7]`. -/
theorem approximant_tendsto : Tendsto approximant atTop (𝓝 zeta7Three) := sorry

/-- **`ζ₇(3)` is irrational**: it is not the image of any rational number in `ℚ_[7]`. -/
theorem zeta7Three_irrational : ¬ ∃ q : ℚ, (q : ℚ_[7]) = zeta7Three := sorry

/-- **`η = ζ₇(3)/2` is irrational.** -/
theorem eta_irrational : ¬ ∃ q : ℚ, (q : ℚ_[7]) = eta := sorry

end Zeta7Challenge
