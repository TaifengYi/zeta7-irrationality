import Zeta7Proof.AuxiliaryThresholdCount

/-! Exact integer counts from P4--P8. These arithmetic results do not assert
the existence of the compatible source basis. -/
noncomputable section
set_option autoImplicit false
namespace Zeta7Auxiliary

def derivativeBudget (d p : ℕ) : ℕ := d + 4*((p-1)/3) + 4
def derivativeThree (d p : ℕ) : ℕ := min (3*d) (derivativeBudget d p)
def derivativeTwo (d p : ℕ) : ℕ := min (3*d-derivativeThree d p) (d+2)
def derivativeOne (d p : ℕ) : ℕ := 3*d-derivativeThree d p-derivativeTwo d p
def primitiveShifts (d : ℕ) : ℕ := d-2
def resonanceShifts (d p : ℕ) : ℕ := min (d-4) ((d-p-2)+(d-p-4))
def jointThirdRank (d p : ℕ) : ℕ :=
  min (derivativeThree d p + primitiveShifts d - resonanceShifts d p) (derivativeBudget d p)
def jointFourthRank (d p N : ℕ) : ℕ :=
  min (2*d+2) (min (d+2) (N-2*p) + min (d+1) (N-3*p))
def simultaneousOne (d p : ℕ) : ℕ := derivativeOne d p + resonanceShifts d p
def simultaneousTwo (d p : ℕ) : ℕ :=
  derivativeTwo d p + derivativeThree d p + primitiveShifts d -
    resonanceShifts d p - jointThirdRank d p
def simultaneousThree (d p N : ℕ) : ℕ :=
  3*d-primitiveShifts d-jointFourthRank d p N+jointThirdRank d p

theorem derivative_counts_sum (d p : ℕ) :
    derivativeOne d p + derivativeTwo d p + derivativeThree d p = 3*d := by
  unfold derivativeOne derivativeTwo derivativeThree
  omega

theorem resonanceShifts_le_primitiveShifts (d p : ℕ) :
    resonanceShifts d p ≤ primitiveShifts d := by
  unfold resonanceShifts primitiveShifts
  omega

theorem jointFourthRank_le_complement (d p N : ℕ) (hd : 2 ≤ d) :
    jointFourthRank d p N ≤ 3*d-primitiveShifts d := by
  unfold jointFourthRank primitiveShifts
  omega

theorem simultaneous_counts_sum (d p N : ℕ) (hd : 2 ≤ d) :
    simultaneousOne d p + simultaneousTwo d p + simultaneousThree d p N +
      jointFourthRank d p N = 6*d := by
  have hc := derivative_counts_sum d p
  have ht := resonanceShifts_le_primitiveShifts d p
  have hq := jointFourthRank_le_complement d p N hd
  have hs : primitiveShifts d ≤ 3*d := by unfold primitiveShifts; omega
  have hb : jointThirdRank d p ≤
      derivativeThree d p + primitiveShifts d - resonanceShifts d p := min_le_left _ _
  unfold simultaneousOne simultaneousTwo simultaneousThree
  omega

def sharpThreshold (d p N : ℕ) : ℕ :=
  let r := min (6*d) (N-p)
  r + min r (6*d-simultaneousOne d p) +
    min r (jointFourthRank d p N+simultaneousThree d p N) + min r (jointFourthRank d p N)

/-- Threshold counts for any actual four-cap list with these multiplicities. -/
theorem thresholdMass_eq_four_counts {ι : Type*} [Fintype ι]
    (e : ι → ℕ) (he : ∀ i, 1 ≤ e i ∧ e i ≤ 4) (r : ℕ) :
    thresholdMass r e =
      min r (Fintype.card ι) +
      min r ((Finset.univ.filter (fun i => e i = 2)).card +
        (Finset.univ.filter (fun i => e i = 3)).card +
        (Finset.univ.filter (fun i => e i = 4)).card) +
      min r ((Finset.univ.filter (fun i => e i = 3)).card +
        (Finset.univ.filter (fun i => e i = 4)).card) +
      min r (Finset.univ.filter (fun i => e i = 4)).card := by
  classical
  have h0 : Finset.univ.filter (fun i => 0 < e i) = Finset.univ := by
    ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨fun _ => trivial, fun _ => (he i).1⟩
  have h1 : (Finset.univ.filter (fun i => 1 < e i)).card =
      (Finset.univ.filter (fun i => e i = 2)).card +
      (Finset.univ.filter (fun i => e i = 3)).card +
      (Finset.univ.filter (fun i => e i = 4)).card := by
    simp only [Finset.card_filter]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    obtain ⟨hlo, hhi⟩ := he i
    interval_cases h : e i <;> simp_all
  have h2 : (Finset.univ.filter (fun i => 2 < e i)).card =
      (Finset.univ.filter (fun i => e i = 3)).card +
      (Finset.univ.filter (fun i => e i = 4)).card := by
    simp only [Finset.card_filter]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    obtain ⟨hlo, hhi⟩ := he i
    interval_cases h : e i <;> simp_all
  have h3 : Finset.univ.filter (fun i => 3 < e i) =
      Finset.univ.filter (fun i => e i = 4) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have := he i
    omega
  simp only [thresholdMass, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ,
    add_zero]
  simp only [h0, h1, h2, h3, Finset.card_univ]
  omega

/-- Identifies the existing determinant bridge's threshold with paper (35),
once an actual cap list has the simultaneous multiplicities. -/
theorem thresholdMass_eq_sharpThreshold {ι : Type*} [Fintype ι]
    (d p N : ℕ) (hd : 2 ≤ d) (e : ι → ℕ) (he : ∀ i, 1 ≤ e i ∧ e i ≤ 4)
    (hcard : Fintype.card ι = 6*d)
    (h2 : (Finset.univ.filter (fun i => e i = 2)).card = simultaneousTwo d p)
    (h3 : (Finset.univ.filter (fun i => e i = 3)).card = simultaneousThree d p N)
    (h4 : (Finset.univ.filter (fun i => e i = 4)).card = jointFourthRank d p N) :
    thresholdMass (min (6*d) (N-p)) e = sharpThreshold d p N := by
  have hc := simultaneous_counts_sum d p N hd
  have h23 : simultaneousTwo d p + simultaneousThree d p N + jointFourthRank d p N =
      6*d-simultaneousOne d p := by omega
  rw [thresholdMass_eq_four_counts e he, hcard, h2, h3, h4, h23]
  unfold sharpThreshold
  rw [min_eq_left (min_le_left (6*d) (N-p))]
  congr 2
  omega

end Zeta7Auxiliary
