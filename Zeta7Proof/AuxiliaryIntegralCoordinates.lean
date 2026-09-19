import Zeta7Proof.AuxiliaryCaps

/-! Integral lifts of the original Euler-product coordinate and its inverse. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
namespace Zeta7Auxiliary
open PowerSeries Zeta7Main
open scoped PowerSeries.WithPiTopology

def IntegerSeries (f : PowerSeries ℚ) : Prop :=
  ∃ g : PowerSeries ℤ, g.map (Int.castRingHom ℚ) = f

theorem IntegerSeries.one : IntegerSeries 1 := ⟨1, by simp⟩
theorem IntegerSeries.X : IntegerSeries X := ⟨PowerSeries.X, by simp⟩
theorem IntegerSeries.add {f g : PowerSeries ℚ} (hf : IntegerSeries f) (hg : IntegerSeries g) :
    IntegerSeries (f + g) := by
  obtain ⟨f, rfl⟩ := hf
  obtain ⟨g, rfl⟩ := hg
  exact ⟨f + g, by simp⟩
theorem IntegerSeries.mul {f g : PowerSeries ℚ} (hf : IntegerSeries f) (hg : IntegerSeries g) :
    IntegerSeries (f * g) := by
  obtain ⟨f, rfl⟩ := hf
  obtain ⟨g, rfl⟩ := hg
  exact ⟨f * g, by simp⟩
theorem IntegerSeries.pow {f : PowerSeries ℚ} (hf : IntegerSeries f) (n : ℕ) :
    IntegerSeries (f ^ n) := by
  obtain ⟨f, rfl⟩ := hf
  exact ⟨f ^ n, by simp⟩
theorem IntegerSeries.derivative {f : PowerSeries ℚ} (hf : IntegerSeries f) :
    IntegerSeries (derivative ℚ f) := by
  obtain ⟨f, rfl⟩ := hf
  refine ⟨PowerSeries.derivative ℤ f, ?_⟩
  ext n
  simp [coeff_derivative]

theorem IntegerSeries.inv {f : PowerSeries ℚ} (hf : IntegerSeries f)
    (h0 : constantCoeff f = 1) : IntegerSeries f⁻¹ := by
  obtain ⟨g, hg⟩ := hf
  have hg0 : constantCoeff g = 1 := by
    have := congrArg constantCoeff hg
    rw [h0] at this
    change ((constantCoeff g : ℤ) : ℚ) = 1 at this
    exact_mod_cast this
  refine ⟨g.invOfUnit 1, ?_⟩
  apply (eq_inv_iff_mul_eq_one (by rw [h0]; norm_num)).mpr
  rw [← hg, ← map_mul]
  simp [invOfUnit_mul g 1 (by simpa using hg0)]

theorem IntegerSeries.subst {f g : PowerSeries ℚ} (hf : IntegerSeries f)
    (hg : IntegerSeries g) (h0 : constantCoeff g = 0) : IntegerSeries (f.subst g) := by
  obtain ⟨f, rfl⟩ := hf
  obtain ⟨g, rfl⟩ := hg
  have hg0 : constantCoeff g = 0 := by
    change ((constantCoeff g : ℤ) : ℚ) = 0 at h0
    exact_mod_cast h0
  exact ⟨f.subst g, map_subst (HasSubst.of_constantCoeff_zero hg0) f⟩

theorem integerSevenProduct_multipliable :
    Multipliable (fun n : SevenProductIndex => (1 : PowerSeries ℤ) - X ^ (n.val + 1)) := by
  classical
  apply (multipliable_subtype_iff_mulIndicator
    (f := fun n : ℕ => (1 : PowerSeries ℤ) - X ^ (n + 1))
    (s := {n : ℕ | ¬ 7 ∣ n + 1})).mpr
  have h : Multipliable (fun n : ℕ => (1 : PowerSeries ℤ) +
      (if ¬ 7 ∣ n + 1 then -(X ^ (n + 1)) else 0)) := by
    apply WithPiTopology.multipliable_one_add_of_tendsto_order_atTop_nhds_top
    refine ENat.tendsto_nhds_top_iff_natCast_lt.mpr fun n =>
      Filter.eventually_atTop.mpr ⟨n, ?_⟩
    intro m hm
    by_cases hd : 7 ∣ m + 1
    · simp [hd]
    · simp only [hd, not_false_eq_true, ite_true, order_neg, order_X_pow]
      exact_mod_cast Nat.lt_add_one_of_le hm
  convert h using 1
  funext n
  by_cases hd : 7 ∣ n + 1 <;> simp [Set.mulIndicator, hd, sub_eq_add_neg]

theorem sevenEulerProduct_integer : IntegerSeries sevenEulerProduct := by
  refine ⟨∏' n : SevenProductIndex, (1 - (X : PowerSeries ℤ) ^ (n.val + 1)), ?_⟩
  have hc : Continuous (PowerSeries.map (Int.castRingHom ℚ)) := by
    apply continuous_iff_continuousAt.mpr
    intro f
    apply (WithPiTopology.tendsto_iff_coeff_tendsto ℚ _ _ _).mpr
    intro n
    simp only [coeff_map]
    exact (continuous_of_discreteTopology (f := fun z : ℤ => (z : ℚ))).continuousAt.comp
      (WithPiTopology.continuous_coeff ℤ n).continuousAt
  rw [integerSevenProduct_multipliable.map_tprod (PowerSeries.map (Int.castRingHom ℚ)) hc]
  simp only [map_sub, map_one, map_pow, map_X]
  rfl

theorem xUnit_integer : IntegerSeries xUnit :=
  (sevenEulerProduct_integer.inv sevenEulerProduct_constant).pow 4

theorem xSeries_integer : IntegerSeries xSeries := IntegerSeries.X.mul xUnit_integer

theorem ASeries_integer : IntegerSeries ASeries :=
  IntegerSeries.one.add ((IntegerSeries.X.mul xUnit_integer.derivative).mul
    (xUnit_integer.inv xUnit_constant))

theorem qSeries_integer : IntegerSeries qSeries := by
  obtain ⟨f, hf⟩ := xSeries_integer
  have h0 : constantCoeff f = 0 := by
    have h := congrArg constantCoeff hf
    rw [xSeries_constant] at h
    change ((constantCoeff f : ℤ) : ℚ) = 0 at h
    exact_mod_cast h
  have h1 : coeff 1 f = 1 := by
    have h := congrArg (coeff 1) hf
    rw [xSeries_linear] at h
    change ((coeff 1 f : ℤ) : ℚ) = 1 at h
    exact_mod_cast h
  let g := f.substInvOfIsUnit (h1 ▸ isUnit_one)
  have hg0 : constantCoeff g = 0 := by simp [g]
  have hg : xSeries.subst (g.map (Int.castRingHom ℚ)) = X := by
    calc
      xSeries.subst (g.map (Int.castRingHom ℚ)) = (f.subst g).map (Int.castRingHom ℚ) := by
        rw [← hf]
        exact (map_subst (h := Int.castRingHom ℚ) (HasSubst.of_constantCoeff_zero hg0) f).symm
      _ = X := by
        change PowerSeries.map (Int.castRingHom ℚ) (f.subst g) = X
        rw [show f.subst g = X from subst_substInvOfIsUnit_right f h0 (h1 ▸ isUnit_one)]
        exact map_X _
  refine ⟨g, ?_⟩
  have he := congrArg (fun z : PowerSeries ℚ => qSeries.subst z) hg
  have hgm : constantCoeff (g.map (Int.castRingHom ℚ)) = 0 := by
    change ((constantCoeff g : ℤ) : ℚ) = 0
    rw [hg0, Int.cast_zero]
  rw [← subst_comp_subst_apply (HasSubst.of_constantCoeff_zero xSeries_constant)
    (HasSubst.of_constantCoeff_zero hgm), q_subst_x,
    subst_X (HasSubst.of_constantCoeff_zero hgm)] at he
  simpa using he

theorem BSeries_integer : IntegerSeries BSeries :=
  ASeries_integer.subst qSeries_integer qSeries_constant

theorem IntegerSeries.integral_coeff {p : ℕ} [Fact p.Prime]
    {f : PowerSeries ℚ} (hf : IntegerSeries f) (n : ℕ) :
    Integral ((coeff n f : ℚ) : ℚ_[p]) := by
  obtain ⟨g, rfl⟩ := hf
  simpa [Integral] using Padic.norm_int_le_one (p := p) (coeff n g)

end Zeta7Auxiliary
