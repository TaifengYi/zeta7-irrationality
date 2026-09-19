import Mathlib

/-! Flag-adapted independent families over a field: for a chain `S₁ ≤ S₂ ≤ S₃` and a fixed
independent family in `S₁`, extend by `n₂` vectors of `S₂`, `n₃` vectors of `S₃` and `n₄` further
vectors to one independent family. The given family is kept unchanged. -/
noncomputable section
set_option autoImplicit false
namespace Zeta7Auxiliary

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- An `n`-element independent family in `S`, whose span meets `W` trivially. -/
theorem exists_disjoint_family (W S : Submodule K V) (hWS : W ≤ S) (n : ℕ)
    (hn : Module.finrank K W + n ≤ Module.finrank K S) :
    ∃ f : Fin n → V, LinearIndependent K f ∧ (∀ i, f i ∈ S) ∧
      Disjoint W (Submodule.span K (Set.range f)) := by
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl (W.comap S.subtype)
  have hW' : Module.finrank K (W.comap S.subtype) = Module.finrank K W :=
    (Submodule.comapSubtypeEquivOfLe hWS).finrank_eq
  have hsum := Submodule.finrank_add_eq_of_isCompl hC
  have hle : n ≤ Module.finrank K C := by omega
  let b := Module.finBasis K C
  refine ⟨fun i => ((b (Fin.castLE hle i) : S) : V), ?_, fun i => (b _ : S).2, ?_⟩
  · have h1 := b.linearIndependent.comp (Fin.castLE hle) (Fin.castLE_injective hle)
    have h2 := h1.map' C.subtype (Submodule.ker_subtype C)
    exact h2.map' S.subtype (Submodule.ker_subtype S)
  · rw [Submodule.disjoint_def]
    intro x hxW hxf
    have hspan : Submodule.span K (Set.range fun i => ((b (Fin.castLE hle i) : S) : V)) ≤
        C.map S.subtype := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact ⟨_, (b _).2, rfl⟩
    obtain ⟨y, hyC, rfl⟩ := hspan hxf
    have hyW : y ∈ W.comap S.subtype := hxW
    have h0 := Submodule.disjoint_def.mp hC.disjoint y hyW hyC
    rw [h0]
    rfl

theorem span_range_le {ι : Type*} (f : ι → V) (S : Submodule K V) (h : ∀ i, f i ∈ S) :
    Submodule.span K (Set.range f) ≤ S := by
  rw [Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  exact h i

/-- Extension of an independent family along the flag `S₁ ≤ S₂ ≤ S₃ ≤ ⊤`. -/
theorem flag_family (S₁ S₂ S₃ : Submodule K V) (h12 : S₁ ≤ S₂) (h23 : S₂ ≤ S₃)
    {κ : Type*} [Fintype κ] (f₁ : κ → V) (hf₁ : LinearIndependent K f₁) (hf₁S : ∀ i, f₁ i ∈ S₁)
    (n₂ n₃ n₄ : ℕ) (h2 : Fintype.card κ + n₂ ≤ Module.finrank K S₂)
    (h3 : Fintype.card κ + n₂ + n₃ ≤ Module.finrank K S₃)
    (h4 : Fintype.card κ + n₂ + n₃ + n₄ ≤ Module.finrank K V) :
    ∃ (f₂ : Fin n₂ → V) (f₃ : Fin n₃ → V) (f₄ : Fin n₄ → V),
      (∀ i, f₂ i ∈ S₂) ∧ (∀ i, f₃ i ∈ S₃) ∧
      LinearIndependent K (Sum.elim (Sum.elim (Sum.elim f₁ f₂) f₃) f₄) := by
  classical
  -- second block
  let W₂ := Submodule.span K (Set.range f₁)
  have hW₂ : Module.finrank K W₂ = Fintype.card κ := finrank_span_eq_card hf₁
  obtain ⟨f₂, hf₂, hf₂S, hd₂⟩ := exists_disjoint_family W₂ S₂
    ((span_range_le f₁ S₁ hf₁S).trans h12) n₂ (by omega)
  have hg₂ : LinearIndependent K (Sum.elim f₁ f₂) := hf₁.sum_type hf₂ hd₂
  have hg₂S : ∀ i, Sum.elim f₁ f₂ i ∈ S₃ := by
    rintro (i | i)
    · exact h23 (h12 (hf₁S i))
    · exact h23 (hf₂S i)
  -- third block
  let W₃ := Submodule.span K (Set.range (Sum.elim f₁ f₂))
  have hW₃ : Module.finrank K W₃ = Fintype.card κ + n₂ := by
    rw [finrank_span_eq_card hg₂, Fintype.card_sum, Fintype.card_fin]
  obtain ⟨f₃, hf₃, hf₃S, hd₃⟩ := exists_disjoint_family W₃ S₃
    (span_range_le _ S₃ hg₂S) n₃ (by omega)
  have hg₃ : LinearIndependent K (Sum.elim (Sum.elim f₁ f₂) f₃) := hg₂.sum_type hf₃ hd₃
  -- fourth block
  let W₄ := Submodule.span K (Set.range (Sum.elim (Sum.elim f₁ f₂) f₃))
  have hW₄ : Module.finrank K W₄ = Fintype.card κ + n₂ + n₃ := by
    rw [finrank_span_eq_card hg₃, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_fin]
  obtain ⟨f₄, hf₄, -, hd₄⟩ := exists_disjoint_family W₄ ⊤ le_top n₄
    (by rw [finrank_top]; omega)
  exact ⟨f₂, f₃, f₄, hf₂S, hf₃S, hg₃.sum_type hf₄ hd₄⟩

end Zeta7Auxiliary
