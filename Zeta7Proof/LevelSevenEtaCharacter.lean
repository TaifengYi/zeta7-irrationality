import Zeta7Proof.LevelSevenGenerators
import Zeta7Proof.LevelSevenEtaTransforms
import LeanModularForms.HeckeRIngs.GL2.LevelRaise

/-! The correlated eta-square multipliers on Γ₀(7) and its integer conjugate. -/
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open Matrix.SpecialLinearGroup ModularGroup ModularForm
open scoped MatrixGroups ModularForm
namespace Zeta7LevelSeven
open HeckeRing.GL2

def sevenConj (γ : CongruenceSubgroup.Gamma0 7) : SL(2, ℤ) :=
  levelRaiseConjOfDvd 7 γ.val
    ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (CongruenceSubgroup.Gamma0_mem.mp γ.property))

theorem sevenConj_mapGL (γ : CongruenceSubgroup.Gamma0 7) :
    mapGL ℝ (sevenConj γ) = levelRaiseMatrix 7 * mapGL ℝ γ.val * (levelRaiseMatrix 7)⁻¹ := by
  apply (eq_mul_inv_iff_mul_eq).mpr
  exact levelRaiseMatrix_mul_mapGL 7 γ.val _

def sevenConjHom : CongruenceSubgroup.Gamma0 7 →* SL(2, ℤ) where
  toFun := sevenConj
  map_one' := by
    apply mapGL_injective (S := ℝ)
    simp [sevenConj_mapGL]
  map_mul' γ δ := by
    apply mapGL_injective (S := ℝ)
    simp [sevenConj_mapGL, map_mul, mul_assoc]

def repExponent (i : Fin 8) : ℤ := if i = 0 then 0 else i.val - 4

theorem etaEigen_cosetRep (i : Fin 8) : EtaEigen (cosetRep i) (repExponent i) := by
  by_cases hi : i = 0
  · subst i; simpa [cosetRep, repExponent] using etaEigen_one
  · have h := etaEigen_S.mul (etaEigen_T_zpow ((i.val : ℤ) - 1))
    convert h using 1 <;> simp [cosetRep, repExponent, hi] <;> omega

def sExponent (i : Fin 8) : ℤ := repExponent i - 3 - repExponent (nextS i)
def tExponent (i : Fin 8) : ℤ := repExponent i + 1 - repExponent (nextT i)

theorem etaEigen_schreierS (i : Fin 8) : EtaEigen (schreierS i) (sExponent i) := by
  exact ((etaEigen_cosetRep i).mul etaEigen_S).mul (etaEigen_cosetRep (nextS i)).inv

theorem etaEigen_schreierT (i : Fin 8) : EtaEigen (schreierT i) (tExponent i) := by
  exact ((etaEigen_cosetRep i).mul etaEigen_T).mul (etaEigen_cosetRep (nextT i)).inv

def liftedSWord : Fin 8 → SL(2, ℤ) :=
  ![1, S * S, T ^ (-6 : ℤ) * S * T, T ^ (-3 : ℤ) * S * T ^ (2 : ℤ),
    T ^ (-2 : ℤ) * S * T ^ (3 : ℤ),
    S * S * T ^ (-2 : ℤ) * S * T ^ (-3 : ℤ) * S * T,
    T ^ (-1 : ℤ) * S * T ^ (3 : ℤ) * S * T ^ (2 : ℤ),
    T ^ (-1 : ℤ) * S * T ^ (6 : ℤ)]
def liftedSExponent : Fin 8 → ℤ := ![0, -6, -8, -4, -2, -16, -2, 2]

theorem sevenConj_schreierS (i : Fin 8) :
    sevenConj ⟨schreierS i, schreierS_mem i⟩ = liftedSWord i := by
  fin_cases i <;> apply Matrix.SpecialLinearGroup.ext <;> intro a b <;>
    fin_cases a <;> fin_cases b <;> decide

theorem etaEigen_liftedSWord (i : Fin 8) : EtaEigen (liftedSWord i) (liftedSExponent i) := by
  fin_cases i
  · exact etaEigen_one
  · exact etaEigen_S.mul etaEigen_S
  · exact ((etaEigen_T_zpow (-6)).mul etaEigen_S).mul etaEigen_T
  · exact ((etaEigen_T_zpow (-3)).mul etaEigen_S).mul (etaEigen_T_zpow 2)
  · exact ((etaEigen_T_zpow (-2)).mul etaEigen_S).mul (etaEigen_T_zpow 3)
  · exact (((((etaEigen_S.mul etaEigen_S).mul (etaEigen_T_zpow (-2))).mul
      etaEigen_S).mul (etaEigen_T_zpow (-3))).mul etaEigen_S).mul etaEigen_T
  · exact ((((etaEigen_T_zpow (-1)).mul etaEigen_S).mul (etaEigen_T_zpow 3)).mul
      etaEigen_S).mul (etaEigen_T_zpow 2)
  · exact ((etaEigen_T_zpow (-1)).mul etaEigen_S).mul (etaEigen_T_zpow 6)

def liftedTWord : Fin 8 → SL(2, ℤ) := ![T ^ (7 : ℤ), 1, 1, 1, 1, 1, 1, S * T * S⁻¹]
def liftedTExponent : Fin 8 → ℤ := ![7, 0, 0, 0, 0, 0, 0, 1]

theorem sevenConj_schreierT (i : Fin 8) :
    sevenConj ⟨schreierT i, schreierT_mem i⟩ = liftedTWord i := by
  fin_cases i <;> apply Matrix.SpecialLinearGroup.ext <;> intro a b <;>
    fin_cases a <;> fin_cases b <;> decide

theorem etaEigen_liftedTWord (i : Fin 8) : EtaEigen (liftedTWord i) (liftedTExponent i) := by
  fin_cases i
  · exact etaEigen_T_zpow 7
  · exact etaEigen_one
  · exact etaEigen_one
  · exact etaEigen_one
  · exact etaEigen_one
  · exact etaEigen_one
  · exact etaEigen_one
  · exact (etaEigen_S.mul etaEigen_T).mul etaEigen_S.inv

theorem etaRoot_zpow_congr {a b : ℤ} (h : 12 ∣ a - b) : etaRoot ^ a = etaRoot ^ b := by
  obtain ⟨k, hk⟩ := h
  have ha : a = b + 12 * k := by omega
  rw [ha, zpow_add₀ etaRoot_ne_zero, zpow_mul]
  norm_num [etaRoot_pow_twelve]

theorem etaRoot_zpow_pow_twelve (a : ℤ) : (etaRoot ^ a) ^ 12 = 1 := by
  rw [← zpow_natCast, ← zpow_mul]
  have h := etaRoot_zpow_congr (a := a * 12) (b := 0) (by exact ⟨a, by ring⟩)
  simpa using h

def Correlated (γ : CongruenceSubgroup.Gamma0 7) : Prop :=
  ∃ μ : ℂ, μ ^ 12 = 1 ∧ etaTwo ∣[(1 : ℤ)] γ.val = μ • etaTwo ∧
    etaTwo ∣[(1 : ℤ)] sevenConjHom γ = μ ^ 7 • etaTwo

theorem correlated_schreierS (i : Fin 8) : Correlated ⟨schreierS i, schreierS_mem i⟩ := by
  refine ⟨etaRoot ^ sExponent i, etaRoot_zpow_pow_twelve _, etaEigen_schreierS i, ?_⟩
  change etaTwo ∣[(1 : ℤ)] sevenConj ⟨schreierS i, schreierS_mem i⟩ = _
  rw [sevenConj_schreierS]
  have h := etaEigen_liftedSWord i
  change etaTwo ∣[(1 : ℤ)] liftedSWord i = etaRoot ^ liftedSExponent i • etaTwo at h
  rw [h, ← zpow_natCast, ← zpow_mul]
  congr 1
  apply etaRoot_zpow_congr
  fin_cases i <;> decide

theorem correlated_schreierT (i : Fin 8) : Correlated ⟨schreierT i, schreierT_mem i⟩ := by
  refine ⟨etaRoot ^ tExponent i, etaRoot_zpow_pow_twelve _, etaEigen_schreierT i, ?_⟩
  change etaTwo ∣[(1 : ℤ)] sevenConj ⟨schreierT i, schreierT_mem i⟩ = _
  rw [sevenConj_schreierT]
  have h := etaEigen_liftedTWord i
  change etaTwo ∣[(1 : ℤ)] liftedTWord i = etaRoot ^ liftedTExponent i • etaTwo at h
  rw [h, ← zpow_natCast, ← zpow_mul]
  congr 1
  apply etaRoot_zpow_congr
  fin_cases i <;> decide

theorem scalar_slash_inv {f : UpperHalfPlane → ℂ} {γ : SL(2, ℤ)} {μ : ℂ}
    (hμ : μ ≠ 0) (h : f ∣[(1 : ℤ)] γ = μ • f) : f ∣[(1 : ℤ)] γ⁻¹ = μ⁻¹ • f := by
  have ht := congrArg (fun g : UpperHalfPlane → ℂ ↦ g ∣[(1 : ℤ)] γ⁻¹) h
  simp only [← SlashAction.slash_mul, mul_inv_cancel, SlashAction.slash_one,
    SL_smul_slash] at ht
  conv_rhs => rw [ht]
  rw [smul_smul, inv_mul_cancel₀ hμ, one_smul]

def correlatedGroup : Subgroup (CongruenceSubgroup.Gamma0 7) where
  carrier := {γ | Correlated γ}
  one_mem' := by
    refine ⟨1, by norm_num, ?_, ?_⟩ <;> simp
  mul_mem' := by
    rintro γ δ ⟨μ, hμ, hγ, hγ7⟩ ⟨ν, hν, hδ, hδ7⟩
    refine ⟨μ * ν, by rw [mul_pow, hμ, hν, one_mul], ?_, ?_⟩
    · change etaTwo ∣[(1 : ℤ)] (γ.val * δ.val) = _
      rw [SlashAction.slash_mul, hγ, SL_smul_slash, hδ, smul_smul]
    · rw [map_mul, SlashAction.slash_mul, hγ7, SL_smul_slash, hδ7, smul_smul, mul_pow]
  inv_mem' := by
    rintro γ ⟨μ, hμ, hγ, hγ7⟩
    have hn : μ ≠ 0 := by intro hz; simpa [hz] using hμ
    refine ⟨μ⁻¹, by rw [inv_pow, hμ, inv_one], scalar_slash_inv hn hγ, ?_⟩
    rw [map_inv, inv_pow]
    exact scalar_slash_inv (pow_ne_zero _ hn) hγ7

/-- The complete generator bridge: the property holds on the entire Γ₀(7). -/
theorem correlatedGroup_eq_top : correlatedGroup = ⊤ := by
  have hle : schreierGroup ≤ correlatedGroup.map (CongruenceSubgroup.Gamma0 7).subtype := by
    apply (Subgroup.closure_le _).mpr
    rintro g (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · exact ⟨⟨schreierS i, schreierS_mem i⟩, correlated_schreierS i, rfl⟩
    · exact ⟨⟨schreierT i, schreierT_mem i⟩, correlated_schreierT i, rfl⟩
  apply top_unique
  intro γ _
  have hγ : γ.val ∈ schreierGroup := by rw [schreierGroup_eq_Gamma0]; exact γ.property
  obtain ⟨δ, hδ, he⟩ := hle hγ
  have : δ = γ := Subtype.ext he
  rwa [this] at hδ

theorem etaTwo_correlated (γ : CongruenceSubgroup.Gamma0 7) :
    ∃ μ : ℂ, μ ^ 12 = 1 ∧ etaTwo ∣[(1 : ℤ)] γ.val = μ • etaTwo ∧
      etaTwo ∣[(1 : ℤ)] sevenConjHom γ = μ ^ 7 • etaTwo := by
  change γ ∈ correlatedGroup
  rw [correlatedGroup_eq_top]
  trivial

end Zeta7LevelSeven
