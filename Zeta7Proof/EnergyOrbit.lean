import Zeta7Proof.EnergyCircle
import Zeta7Proof.CertEnergyDefs

/-! Averaging the orbit terms over `u ∈ [0, 1]`.

For rational heights `y, t > 0`:

`Σ_{p ∈ box} ∫_0^1 orbitTerm(y, t, u, p) du ≤ 2π (y - t)₊ + Σ_{m ∈ mSet y t} eTerm y t m`.

The row `(0, 1)` gives `2π (y - t)₊`. For each `c > 0` the rows `(c, d)` are averaged with
`average_le` (at most `φ(c)` of `c` consecutive integers are prime to `c`), and the integral is
evaluated by `integral_posPart`; rows with `c² y t ≥ 1` contribute nothing. -/
noncomputable section
set_option autoImplicit false
namespace Zeta7Valence
open Real MeasureTheory Zeta7Cert

theorem orbitTerm_zero_one (y t u : ℝ) : orbitTerm y t u (0, 1) = 2 * π * max 0 (y - t) := by
  simp [orbitTerm]

theorem bottom_zero {p : ℤ × ℤ} (hp : bottomShape p) (h0 : p.1 = 0) : p = (0, 1) := by
  rcases hp with ⟨h1, h2⟩ | ⟨h1, _⟩
  · exact Prod.ext h1 h2
  · omega

/-- The profile `f_c(v) = 2π (y/(v² + c²y²) - t)₊`. -/
def profile (y t c : ℝ) (v : ℝ) : ℝ := 2 * π * max 0 (y / (v ^ 2 + c ^ 2 * y ^ 2) - t)

theorem profile_continuous {y t c : ℝ} (hy : 0 < y) (hc : 0 < c) : Continuous (profile y t c) := by
  unfold profile
  refine continuous_const.mul (continuous_const.max ((continuous_const.div (by fun_prop)
    (fun v => by positivity)).sub continuous_const))

theorem profile_nonneg (y t c v : ℝ) : 0 ≤ profile y t c v := by
  unfold profile; have := pi_pos; positivity

theorem orbitTerm_eq_profile (y t u : ℝ) (p : ℤ × ℤ) :
    orbitTerm y t u p = profile y t p.1 (p.1 * u + p.2) := rfl

theorem eTerm_nonneg {y t : ℚ} (hy : 0 < y) (ht : 0 < t) {m : ℕ} (hm : m ∈ mSet y t) :
    0 ≤ eTerm y t m := by
  have hyt : 0 < y * t := mul_pos hy ht
  rw [mem_mSet hyt] at hm
  obtain ⟨h7, _, hlt⟩ := hm
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le (by norm_num) h7)
  have hy' : (0 : ℝ) < y := by exact_mod_cast hy
  have ht' : (0 : ℝ) < t := by exact_mod_cast ht
  have hlt' : (m : ℝ) ^ 2 * y * t < 1 := by exact_mod_cast hlt
  have hI := integral_posPart hm0 hy' ht' hlt' (le_refl _)
  have hI0 : 0 ≤ ∫ v in (-√((y : ℝ) / t - (m : ℝ) ^ 2 * y ^ 2))..√((y : ℝ) / t - (m : ℝ) ^ 2 * y ^ 2),
      max 0 ((y : ℝ) / (v ^ 2 + (m : ℝ) ^ 2 * y ^ 2) - t) :=
    intervalIntegral.integral_nonneg (by
      have := Real.sqrt_nonneg ((y : ℝ) / t - (m : ℝ) ^ 2 * y ^ 2); linarith)
      (fun v _ => le_max_left _ _)
  rw [hI] at hI0
  have hg : 0 ≤ arccos ((m : ℝ) * √((y : ℝ) * t)) - m * √((y : ℝ) * t) * √(1 - (m : ℝ) ^ 2 * y * t) := by
    have h2 : (0 : ℝ) < 2 / m := by positivity
    exact nonneg_of_mul_nonneg_right (by linarith) h2
  unfold eTerm
  have := pi_pos
  positivity


/-- The averaged contribution of the rows `(c, d)` with a fixed `c > 0`. -/
theorem row_average_le {y t : ℚ} (hy : 0 < y) (ht : 0 < t) {n : ℕ} (hn : 0 < n)
    (D : Finset ℤ) (hD : ∀ d ∈ D, IsCoprime d (n : ℤ) ∧ |(d : ℝ)| ≤ boxN y t)
    (hnM : (n : ℝ) ≤ boxM y t) :
    ∑ d ∈ D, ∫ u in (0 : ℝ)..1, profile y t n (n * u + d) ≤
      if (n : ℝ) ^ 2 * y * t < 1 then eTerm y t n else 0 := by
  have hy' : (0 : ℝ) < y := by exact_mod_cast hy
  have ht' : (0 : ℝ) < t := by exact_mod_cast ht
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set B : ℝ := (boxN y t : ℝ) + boxM y t with hB
  have hB0 : 0 ≤ B := by positivity
  have havg := average_le hn (profile_continuous hy' hn') (profile_nonneg y t n) hB0 D (fun d hd => by
    obtain ⟨hcop, habs⟩ := hD d hd
    rw [abs_le] at habs
    refine ⟨hcop, by linarith [habs.1, (by positivity : (0 : ℝ) ≤ boxM y t)], by linarith [habs.2]⟩)
  refine havg.trans ?_
  have hprof : ∫ v in (-B)..B, profile y t n v =
      2 * π * ∫ v in (-B)..B, max 0 ((y : ℝ) / (v ^ 2 + (n : ℝ) ^ 2 * y ^ 2) - t) := by
    unfold profile
    rw [intervalIntegral.integral_const_mul]
  rw [hprof]
  split_ifs with hlt
  · -- the explicit integral
    have hVB : √((y : ℝ) / t - (n : ℝ) ^ 2 * y ^ 2) ≤ B := by
      have h1 : √((y : ℝ) / t - (n : ℝ) ^ 2 * y ^ 2) ≤ √((y : ℝ) / t) :=
        Real.sqrt_le_sqrt (by nlinarith)
      have h2 : √((y : ℝ) / t) ≤ 1 + (y : ℝ) / t := by
        rw [Real.sqrt_le_left (by positivity)]
        nlinarith [div_pos hy' ht']
      have h3 := Nat.le_ceil ((y : ℝ) / t)
      have h4 : (1 : ℝ) + (y : ℝ) / t ≤ boxN y t := by
        unfold boxN; push_cast; linarith [(by positivity : (0 : ℝ) ≤ boxM y t)]
      linarith [(by positivity : (0 : ℝ) ≤ boxM y t)]
    rw [integral_posPart hn' hy' ht' hlt hVB, eTerm]
    push_cast
    field_simp
    ring_nf
    rfl
  · -- the integrand vanishes
    push Not at hlt
    have hz : ∫ v in (-B)..B, max 0 ((y : ℝ) / (v ^ 2 + (n : ℝ) ^ 2 * y ^ 2) - t) = 0 := by
      rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) (fun v _ =>
        posPart_eq_zero hn' hy' ht' hlt v)]
      simp
    rw [hz]; simp

/-- **Averaging the orbit terms.** -/
theorem orbit_integral_le {y t : ℚ} (hy : 0 < y) (ht : 0 < t) :
    ∑ p ∈ cosetBox y t, ∫ u in (0 : ℝ)..1, orbitTerm y t u p ≤
      2 * π * max 0 ((y : ℝ) - t) + ∑ m ∈ mSet y t, eTerm y t m := by
  have hy' : (0 : ℝ) < y := by exact_mod_cast hy
  have ht' : (0 : ℝ) < t := by exact_mod_cast ht
  set box := cosetBox (y : ℝ) (t : ℝ) with hbox
  have hint_nonneg : ∀ p, 0 ≤ ∫ u in (0 : ℝ)..1, orbitTerm y t u p :=
    fun p => intervalIntegral.integral_nonneg zero_le_one (fun u _ => orbitTerm_nonneg _ _ _ _)
  rw [← Finset.sum_filter_add_sum_filter_not box (fun p => p.1 = 0)]
  gcongr
  · -- the row `(0, 1)`
    have hsub : box.filter (fun p => p.1 = 0) ⊆ {(0, 1)} := by
      intro p hp
      rw [Finset.mem_filter, hbox, cosetBox, Finset.mem_filter] at hp
      rw [Finset.mem_singleton]
      exact bottom_zero hp.1.2 hp.2
    refine (Finset.sum_le_sum_of_subset_of_nonneg hsub fun p _ _ => hint_nonneg p).trans ?_
    rw [Finset.sum_singleton]
    simp only [orbitTerm_zero_one, intervalIntegral.integral_const, sub_zero, one_smul]
    exact le_refl _
  · -- the rows with `c > 0`, grouped by `c`
    set S := box.filter (fun p => ¬ p.1 = 0) with hS
    have hSprop : ∀ p ∈ S, 0 < p.1 ∧ (7 : ℤ) ∣ p.1 ∧ IsCoprime p.1 p.2 ∧
        p.1 ≤ boxM y t ∧ |(p.2 : ℝ)| ≤ boxN y t := by
      intro p hp
      rw [hS, Finset.mem_filter, hbox, cosetBox, Finset.mem_filter, Finset.mem_product,
        Finset.mem_Icc, Finset.mem_Icc] at hp
      obtain ⟨⟨⟨⟨_, hcM⟩, hd1, hd2⟩, hsh⟩, hne⟩ := hp
      rcases hsh with ⟨h0, _⟩ | ⟨hc, h7, hcop⟩
      · exact absurd h0 hne
      · refine ⟨hc, h7, hcop, hcM, ?_⟩
        rw [abs_le]
        constructor
        · have : (-(boxN y t : ℤ) : ℝ) ≤ p.2 := by exact_mod_cast hd1
          push_cast at this; linarith
        · exact_mod_cast hd2
    set C := S.image Prod.fst with hC
    rw [← Finset.sum_fiberwise_of_maps_to (g := Prod.fst) (t := C)
      (fun p hp => Finset.mem_image_of_mem _ hp)]
    -- each fibre
    have hfib : ∀ c ∈ C, ∑ p ∈ S with p.1 = c, ∫ u in (0 : ℝ)..1, orbitTerm y t u p ≤
        if ((c.toNat : ℕ) : ℝ) ^ 2 * y * t < 1 then eTerm y t c.toNat else 0 := by
      intro c hc
      obtain ⟨p0, hp0, hp0c⟩ := Finset.mem_image.mp hc
      have hc0 : 0 < c := by rw [← hp0c]; exact (hSprop p0 hp0).1
      set n := c.toNat with hn
      have hnc : (n : ℤ) = c := Int.toNat_of_nonneg hc0.le
      have hn0 : 0 < n := by omega
      set F := S.filter (fun p => p.1 = c) with hF
      have hinj : Set.InjOn Prod.snd (F : Set (ℤ × ℤ)) := by
        intro p hp q hq he
        rw [Finset.mem_coe, hF, Finset.mem_filter] at hp hq
        exact Prod.ext (hp.2.trans hq.2.symm) he
      have hsum : ∑ p ∈ F, ∫ u in (0 : ℝ)..1, orbitTerm y t u p =
          ∑ d ∈ F.image Prod.snd, ∫ u in (0 : ℝ)..1, profile y t n (n * u + d) := by
        rw [Finset.sum_image hinj]
        refine Finset.sum_congr rfl fun p hp => ?_
        rw [hF, Finset.mem_filter] at hp
        congr 1
        funext u
        rw [orbitTerm_eq_profile, hp.2, ← hnc]
        push_cast
        rfl
      rw [hsum]
      refine row_average_le hy ht hn0 _ (fun d hd => ?_) ?_
      · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hd
        rw [hF, Finset.mem_filter] at hp
        obtain ⟨_, _, hcop, _, hd⟩ := hSprop p hp.1
        refine ⟨?_, hd⟩
        rw [hnc, ← hp.2]; exact hcop.symm
      · have := (hSprop p0 hp0).2.2.2.1
        rw [hp0c, ← hnc] at this
        exact_mod_cast this
    refine (Finset.sum_le_sum hfib).trans ?_
    -- compare with the cutoff set
    rw [← Finset.sum_filter]
    set C' := C.filter (fun c : ℤ => ((c.toNat : ℕ) : ℝ) ^ 2 * y * t < 1) with hC'
    have hinj : Set.InjOn Int.toNat (C' : Set ℤ) := by
      intro a ha b hb he
      rw [Finset.mem_coe, hC', Finset.mem_filter, hC] at ha hb
      obtain ⟨pa, hpa, rfl⟩ := Finset.mem_image.mp ha.1
      obtain ⟨pb, hpb, rfl⟩ := Finset.mem_image.mp hb.1
      have h1 := (hSprop pa hpa).1
      have h2 := (hSprop pb hpb).1
      omega
    rw [← Finset.sum_image hinj]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun m hm _ => eTerm_nonneg hy ht hm
    intro m hm
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hm
    rw [hC', Finset.mem_filter] at hc
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hc.1
    obtain ⟨hc0, h7, _⟩ := hSprop p hp
    rw [mem_mSet (mul_pos hy ht)]
    refine ⟨?_, ?_, ?_⟩
    · obtain ⟨k, hk⟩ := h7
      omega
    · obtain ⟨k, hk⟩ := h7
      exact ⟨k.toNat, by omega⟩
    · have := hc.2
      exact_mod_cast this

end Zeta7Valence
