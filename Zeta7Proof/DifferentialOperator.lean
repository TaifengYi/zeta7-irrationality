import Mathlib

/-!
# Clearing a third-order operator over a commutative differential ring

These lemmas have no analytic or modular inputs. The inverse denominator
is supplied by a unit. The doubled identity works without dividing by two.
The weighted identity permits any coefficient in front of D V; specializing
it to one half gives the desired operator. An additive map with the Leibniz
rule is the full operator interface.
-/

set_option autoImplicit false

namespace Zeta7Differential

variable {A : Type*} [CommRing A]

theorem unit_potential_relation (u : Aˣ) (N : A) :
    (u : A) ^ 2 * (N * (↑u⁻¹ : A) ^ 2) = N := by
  calc
    _ = N * ((u : A) * (↑u⁻¹ : A)) ^ 2 := by ring
    _ = N := by simp

theorem unit_potential_derivative
    (D : A →+ A)
    (leibniz : ∀ a b : A, D (a * b) = D a * b + a * D b)
    (u : Aˣ) (N : A) :
    (u : A) ^ 3 * D (N * (↑u⁻¹ : A) ^ 2) =
      (u : A) * D N - 2 * N * D (u : A) := by
  have h := unit_potential_relation u N
  have hd := congrArg D h
  rw [leibniz, show D ((u : A) ^ 2) = 2 * (u : A) * D (u : A) by
    rw [pow_two, leibniz]
    ring] at hd
  linear_combination (u : A) * hd - 2 * D (u : A) * h

/-- Denominator clearing without a characteristic assumption. -/
theorem twice_cleared_operator
    (D : A →+ A)
    (leibniz : ∀ a b : A, D (a * b) = D a * b + a * D b)
    (u : Aˣ) (N f : A) :
    let P : A := u
    let V := N * (↑u⁻¹ : A) ^ 2
    2 * P ^ 3 * D (D (D f)) - 2 * N * P * D f +
      (2 * N * D P - P * D N) * f =
      P ^ 3 * (2 * D (D (D f)) - 2 * V * D f - D V * f) := by
  dsimp
  have h := unit_potential_relation u N
  have hd := unit_potential_derivative D leibniz u N
  linear_combination 2 * (u : A) * D f * h + f * hd

/-- The exact weighted identity, with no restriction on the coefficient `half`. -/
theorem cleared_operator
    (D : A →+ A)
    (leibniz : ∀ a b : A, D (a * b) = D a * b + a * D b)
    (u : Aˣ) (N half f : A) :
    let P : A := u
    let V := N * (↑u⁻¹ : A) ^ 2
    P ^ 3 * D (D (D f)) - N * P * D f +
      half * (2 * N * D P - P * D N) * f =
      P ^ 3 * (D (D (D f)) - V * D f - half * D V * f) := by
  dsimp
  have h := unit_potential_relation u N
  have hd := unit_potential_derivative D leibniz u N
  linear_combination (u : A) * D f * h + half * f * hd

#print axioms unit_potential_relation
#print axioms unit_potential_derivative
#print axioms twice_cleared_operator
#print axioms cleared_operator

end Zeta7Differential
