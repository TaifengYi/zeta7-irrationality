import Zeta7Proof.CertEnergyDefs

/-! Generated certificates (38 summands of the explicit energy (48) for the six C5 circles).
Each bound `eTerm (cy i) (cy j) m ≤ π K` is proved from exact rational witnesses: bounds for
`m√(y_i y_j)` and `√(1 - a²)`, two half-angle reductions of the arctangent and a Taylor sum
with its alternating remainder. Every side condition is decided by `norm_num`. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace Zeta7Cert
open Real

theorem eTerm_0_4_7 : eTerm (cy 0) (cy 4) 7 ≤ π * (56285825878889223 / 3062500000000000000 : ℝ) := by
  have hg : arccos (((7 : ℕ) : ℝ) * √((1 / 2 : ℝ) * (7 / 200 : ℝ))) - ((7 : ℕ) : ℝ) * √((1 / 2 : ℝ) * (7 / 200 : ℝ)) *
      √(1 - ((7 : ℕ) : ℝ) ^ 2 * (1 / 2 : ℝ) * (7 / 200 : ℝ)) ≤ (18761941959629741 / 500000000000000000 : ℝ) :=
    term_le' (a := (463006479436303353 / 500000000000000000 : ℝ)) (b := (926012958872606707 / 1000000000000000000 : ℝ)) (s := (94372930440884371 / 250000000000000000 : ℝ))
      (shi := (377491721763537487 / 1000000000000000000 : ℝ)) (u := (20382637097385897 / 50000000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (atan_up_direct (q1 := (1079898494312077793 / 1000000000000000000 : ℝ)) (r1 := (6124889373545911 / 31250000000000000 : ℝ)) (q2 := (1019026305997196441 / 1000000000000000000 : ℝ)) (r2 := (19414948618677513 / 200000000000000000 : ℝ)) 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (by norm_num [atanPoly, Finset.sum_range_succ])
  have ht : ((Nat.totient 7 : ℕ) : ℝ) = 6 := by rw [show Nat.totient 7 = 6 by decide]; norm_num
  unfold eTerm
  rw [cy_0, cy_4, ht]
  refine (mul_le_mul_of_nonneg_left hg (by positivity)).trans (le_of_eq ?_)
  push_cast
  ring

theorem eTerm_0_5_7 : eTerm (cy 0) (cy 5) 7 ≤ π * (677324566039673787 / 6125000000000000000 : ℝ) := by
  have hg : arccos (((7 : ℕ) : ℝ) * √((1 / 2 : ℝ) * (23 / 1000 : ℝ))) - ((7 : ℕ) : ℝ) * √((1 / 2 : ℝ) * (23 / 1000 : ℝ)) *
      √(1 - ((7 : ℕ) : ℝ) ^ 2 * (1 / 2 : ℝ) * (23 / 1000 : ℝ)) ≤ (225774855346557929 / 1000000000000000000 : ℝ) :=
    term_le' (a := (750666370633452581 / 1000000000000000000 : ℝ)) (b := (375333185316726291 / 500000000000000000 : ℝ)) (s := (330340733183178607 / 500000000000000000 : ℝ))
      (shi := (20646295823948663 / 31250000000000000 : ℝ)) (u := (17602532688625407 / 20000000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (atan_up_direct (q1 := (266429945211518219 / 200000000000000000 : ℝ)) (r1 := (188694281631542239 / 500000000000000000 : ℝ)) (q2 := (13360518607085481 / 12500000000000000 : ℝ)) (r2 := (182415407535410179 / 1000000000000000000 : ℝ)) 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (by norm_num [atanPoly, Finset.sum_range_succ])
  have ht : ((Nat.totient 7 : ℕ) : ℝ) = 6 := by rw [show Nat.totient 7 = 6 by decide]; norm_num
  unfold eTerm
  rw [cy_0, cy_5, ht]
  refine (mul_le_mul_of_nonneg_left hg (by positivity)).trans (le_of_eq ?_)
  push_cast
  ring

theorem eTerm_1_2_7 : eTerm (cy 1) (cy 2) 7 ≤ π * (7405808768879037 / 1225000000000000000 : ℝ) := by
  have hg : arccos (((7 : ℕ) : ℝ) * √((1 / 5 : ℝ) * (19 / 200 : ℝ))) - ((7 : ℕ) : ℝ) * √((1 / 5 : ℝ) * (19 / 200 : ℝ)) *
      √(1 - ((7 : ℕ) : ℝ) ^ 2 * (1 / 5 : ℝ) * (19 / 200 : ℝ)) ≤ (2468602922959679 / 200000000000000000 : ℝ) :=
    term_le' (a := (964883412646315523 / 1000000000000000000 : ℝ)) (b := (241220853161578881 / 250000000000000000 : ℝ)) (s := (131339255365636971 / 500000000000000000 : ℝ))
      (shi := (131339255365636973 / 500000000000000000 : ℝ)) (u := (272238601356867261 / 1000000000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (atan_up_direct (q1 := (1036394643014302389 / 1000000000000000000 : ℝ)) (r1 := (66843281652395121 / 500000000000000000 : ℝ)) (q2 := (1008896474970670957 / 1000000000000000000 : ℝ)) (r2 := (66547263619814959 / 1000000000000000000 : ℝ)) 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (by norm_num [atanPoly, Finset.sum_range_succ])
  have ht : ((Nat.totient 7 : ℕ) : ℝ) = 6 := by rw [show Nat.totient 7 = 6 by decide]; norm_num
  unfold eTerm
  rw [cy_1, cy_2, ht]
  refine (mul_le_mul_of_nonneg_left hg (by positivity)).trans (le_of_eq ?_)
  push_cast
  ring

theorem eTerm_1_3_7 : eTerm (cy 1) (cy 3) 7 ≤ π * (185911371930039177 / 1531250000000000000 : ℝ) := by
  have hg : arccos (((7 : ℕ) : ℝ) * √((1 / 5 : ℝ) * (11 / 200 : ℝ))) - ((7 : ℕ) : ℝ) * √((1 / 5 : ℝ) * (11 / 200 : ℝ)) *
      √(1 - ((7 : ℕ) : ℝ) ^ 2 * (1 / 5 : ℝ) * (11 / 200 : ℝ)) ≤ (61970457310013059 / 250000000000000000 : ℝ) :=
    term_le' (a := (367083096859553041 / 500000000000000000 : ℝ)) (b := (734166193719106083 / 1000000000000000000 : ℝ)) (s := (67896980787071821 / 100000000000000000 : ℝ))
      (shi := (169742451967679553 / 250000000000000000 : ℝ)) (u := (924817587188567617 / 1000000000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (atan_up_direct (q1 := (42565294162749657 / 31250000000000000 : ℝ)) (r1 := (15661008969724969 / 40000000000000000 : ℝ)) (q2 := (1073914336070912459 / 1000000000000000000 : ℝ)) (r2 := (188785629875571183 / 1000000000000000000 : ℝ)) 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (by norm_num [atanPoly, Finset.sum_range_succ])
  have ht : ((Nat.totient 7 : ℕ) : ℝ) = 6 := by rw [show Nat.totient 7 = 6 by decide]; norm_num
  unfold eTerm
  rw [cy_1, cy_3, ht]
  refine (mul_le_mul_of_nonneg_left hg (by positivity)).trans (le_of_eq ?_)
  push_cast
  ring

theorem eTerm_1_4_7 : eTerm (cy 1) (cy 4) 7 ≤ π * (1411164814731281811 / 6125000000000000000 : ℝ) := by
  have hg : arccos (((7 : ℕ) : ℝ) * √((1 / 5 : ℝ) * (7 / 200 : ℝ))) - ((7 : ℕ) : ℝ) * √((1 / 5 : ℝ) * (7 / 200 : ℝ)) *
      √(1 - ((7 : ℕ) : ℝ) ^ 2 * (1 / 5 : ℝ) * (7 / 200 : ℝ)) ≤ (470388271577093937 / 1000000000000000000 : ℝ) :=
    term_le' (a := (585662018573852883 / 1000000000000000000 : ℝ)) (b := (146415504643463221 / 250000000000000000 : ℝ)) (s := (810555365166377761 / 1000000000000000000 : ℝ))
      (shi := (810555365166377763 / 1000000000000000000 : ℝ)) (u := (86499907312173331 / 62500000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (atan_up_inv (v := (722544126832887729 / 1000000000000000000 : ℝ)) (q1 := (1233722016996008769 / 1000000000000000000 : ℝ)) (r1 := (64694184982300667 / 200000000000000000 : ℝ)) (q2 := (1051015432457156373 / 1000000000000000000 : ℝ)) (r2 := (31542514970155917 / 200000000000000000 : ℝ)) 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (by norm_num [atanPoly, Finset.sum_range_succ])
  have ht : ((Nat.totient 7 : ℕ) : ℝ) = 6 := by rw [show Nat.totient 7 = 6 by decide]; norm_num
  unfold eTerm
  rw [cy_1, cy_4, ht]
  refine (mul_le_mul_of_nonneg_left hg (by positivity)).trans (le_of_eq ?_)
  push_cast
  ring

theorem eTerm_1_5_7 : eTerm (cy 1) (cy 5) 7 ≤ π * (1974768035782550013 / 6125000000000000000 : ℝ) := by
  have hg : arccos (((7 : ℕ) : ℝ) * √((1 / 5 : ℝ) * (23 / 1000 : ℝ))) - ((7 : ℕ) : ℝ) * √((1 / 5 : ℝ) * (23 / 1000 : ℝ)) *
      √(1 - ((7 : ℕ) : ℝ) ^ 2 * (1 / 5 : ℝ) * (23 / 1000 : ℝ)) ≤ (658256011927516671 / 1000000000000000000 : ℝ) :=
    term_le' (a := (474763098818768769 / 1000000000000000000 : ℝ)) (b := (47476309881876877 / 100000000000000000 : ℝ)) (s := (440056814513762529 / 500000000000000000 : ℝ))
      (shi := (44005681451376253 / 50000000000000000 : ℝ)) (u := (926897679302883937 / 500000000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (atan_up_inv (v := (21577354703317329 / 40000000000000000 : ℝ)) (q1 := (1136216923608991813 / 1000000000000000000 : ℝ)) (r1 := (126259150374952733 / 500000000000000000 : ℝ)) (q2 := (515695038810152727 / 500000000000000000 : ℝ)) (r2 := (124308129458681241 / 1000000000000000000 : ℝ)) 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (by norm_num [atanPoly, Finset.sum_range_succ])
  have ht : ((Nat.totient 7 : ℕ) : ℝ) = 6 := by rw [show Nat.totient 7 = 6 by decide]; norm_num
  unfold eTerm
  rw [cy_1, cy_5, ht]
  refine (mul_le_mul_of_nonneg_left hg (by positivity)).trans (le_of_eq ?_)
  push_cast
  ring

theorem eTerm_1_5_14 : eTerm (cy 1) (cy 5) 14 ≤ π * (649579459584597 / 250000000000000000 : ℝ) := by
  have hg : arccos (((14 : ℕ) : ℝ) * √((1 / 5 : ℝ) * (23 / 1000 : ℝ))) - ((14 : ℕ) : ℝ) * √((1 / 5 : ℝ) * (23 / 1000 : ℝ)) *
      √(1 - ((14 : ℕ) : ℝ) ^ 2 * (1 / 5 : ℝ) * (23 / 1000 : ℝ)) ≤ (10609797839881751 / 500000000000000000 : ℝ) :=
    term_le' (a := (949526197637537539 / 1000000000000000000 : ℝ)) (b := (47476309881876877 / 50000000000000000 : ℝ)) (s := (313687742827162437 / 1000000000000000000 : ℝ))
      (shi := (313687742827162441 / 1000000000000000000 : ℝ)) (u := (165181194372325473 / 500000000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (atan_up_direct (q1 := (263289207419459167 / 250000000000000000 : ℝ)) (r1 := (80452302515168437 / 500000000000000000 : ℝ)) (q2 := (1012862424971905407 / 1000000000000000000 : ℝ)) (r2 := (4996137684142233 / 62500000000000000 : ℝ)) 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (by norm_num [atanPoly, Finset.sum_range_succ])
  have ht : ((Nat.totient 14 : ℕ) : ℝ) = 6 := by rw [show Nat.totient 14 = 6 by decide]; norm_num
  unfold eTerm
  rw [cy_1, cy_5, ht]
  refine (mul_le_mul_of_nonneg_left hg (by positivity)).trans (le_of_eq ?_)
  push_cast
  ring

theorem eTerm_2_2_7 : eTerm (cy 2) (cy 2) 7 ≤ π * (1039955029025244093 / 6125000000000000000 : ℝ) := by
  have hg : arccos (((7 : ℕ) : ℝ) * √((19 / 200 : ℝ) * (19 / 200 : ℝ))) - ((7 : ℕ) : ℝ) * √((19 / 200 : ℝ) * (19 / 200 : ℝ)) *
      √(1 - ((7 : ℕ) : ℝ) ^ 2 * (19 / 200 : ℝ) * (19 / 200 : ℝ)) ≤ (346651676341748031 / 1000000000000000000 : ℝ) :=
    term_le' (a := (133 / 200 : ℝ)) (b := (133 / 200 : ℝ)) (s := (746843357070276149 / 1000000000000000000 : ℝ))
      (shi := (14936867141405523 / 20000000000000000 : ℝ)) (u := (70192044837431969 / 62500000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (atan_up_inv (v := (44520714665567087 / 50000000000000000 : ℝ)) (q1 := (1338968862122318407 / 1000000000000000000 : ℝ)) (r1 := (190343340548664549 / 500000000000000000 : ℝ)) (q2 := (1070010443484034199 / 1000000000000000000 : ℝ)) (r2 := (91952840695961759 / 500000000000000000 : ℝ)) 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (by norm_num [atanPoly, Finset.sum_range_succ])
  have ht : ((Nat.totient 7 : ℕ) : ℝ) = 6 := by rw [show Nat.totient 7 = 6 by decide]; norm_num
  unfold eTerm
  rw [cy_2, ht]
  refine (mul_le_mul_of_nonneg_left hg (by positivity)).trans (le_of_eq ?_)
  push_cast
  ring

theorem eTerm_2_3_7 : eTerm (cy 2) (cy 3) 7 ≤ π * (181149657375926811 / 612500000000000000 : ℝ) := by
  have hg : arccos (((7 : ℕ) : ℝ) * √((19 / 200 : ℝ) * (11 / 200 : ℝ))) - ((7 : ℕ) : ℝ) * √((19 / 200 : ℝ) * (11 / 200 : ℝ)) *
      √(1 - ((7 : ℕ) : ℝ) ^ 2 * (19 / 200 : ℝ) * (11 / 200 : ℝ)) ≤ (60383219125308937 / 100000000000000000 : ℝ) :=
    term_le' (a := (50598913031803361 / 100000000000000000 : ℝ)) (b := (505989130318033611 / 1000000000000000000 : ℝ)) (s := (53908740884479949 / 62500000000000000 : ℝ))
      (shi := (431269927075839593 / 500000000000000000 : ℝ)) (u := (1704660836507574277 / 1000000000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (atan_up_inv (v := (293313478723647771 / 500000000000000000 : ℝ)) (q1 := (1159366718171550367 / 1000000000000000000 : ℝ)) (r1 := (135833101554890943 / 500000000000000000 : ℝ)) (q2 := (259061108369252001 / 250000000000000000 : ℝ)) (r2 := (66707660102941509 / 500000000000000000 : ℝ)) 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (by norm_num [atanPoly, Finset.sum_range_succ])
  have ht : ((Nat.totient 7 : ℕ) : ℝ) = 6 := by rw [show Nat.totient 7 = 6 by decide]; norm_num
  unfold eTerm
  rw [cy_2, cy_3, ht]
  refine (mul_le_mul_of_nonneg_left hg (by positivity)).trans (le_of_eq ?_)
  push_cast
  ring

theorem eTerm_2_4_7 : eTerm (cy 2) (cy 4) 7 ≤ π * (1179011346282089451 / 3062500000000000000 : ℝ) := by
  have hg : arccos (((7 : ℕ) : ℝ) * √((19 / 200 : ℝ) * (7 / 200 : ℝ))) - ((7 : ℕ) : ℝ) * √((19 / 200 : ℝ) * (7 / 200 : ℝ)) *
      √(1 - ((7 : ℕ) : ℝ) ^ 2 * (19 / 200 : ℝ) * (7 / 200 : ℝ)) ≤ (393003782094029817 / 500000000000000000 : ℝ) :=
    term_le' (a := (12613740337921183 / 31250000000000000 : ℝ)) (b := (403639690813477857 / 1000000000000000000 : ℝ)) (s := (914918029115177071 / 1000000000000000000 : ℝ))
      (shi := (57182376819698567 / 62500000000000000 : ℝ)) (u := (70833441459207957 / 31250000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (atan_up_inv (v := (220587898570454621 / 500000000000000000 : ℝ)) (q1 := (1092994091467523307 / 1000000000000000000 : ℝ)) (r1 := (210786929088545353 / 1000000000000000000 : ℝ)) (q2 := (510987066733244103 / 500000000000000000 : ℝ)) (r2 := (5212404194488151 / 50000000000000000 : ℝ)) 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (by norm_num [atanPoly, Finset.sum_range_succ])
  have ht : ((Nat.totient 7 : ℕ) : ℝ) = 6 := by rw [show Nat.totient 7 = 6 by decide]; norm_num
  unfold eTerm
  rw [cy_2, cy_4, ht]
  refine (mul_le_mul_of_nonneg_left hg (by positivity)).trans (le_of_eq ?_)
  push_cast
  ring

theorem eTerm_2_4_14 : eTerm (cy 2) (cy 4) 14 ≤ π * (58063914745193163 / 3062500000000000000 : ℝ) := by
  have hg : arccos (((14 : ℕ) : ℝ) * √((19 / 200 : ℝ) * (7 / 200 : ℝ))) - ((14 : ℕ) : ℝ) * √((19 / 200 : ℝ) * (7 / 200 : ℝ)) *
      √(1 - ((14 : ℕ) : ℝ) ^ 2 * (19 / 200 : ℝ) * (7 / 200 : ℝ)) ≤ (19354638248397721 / 125000000000000000 : ℝ) :=
    term_le' (a := (12613740337921183 / 15625000000000000 : ℝ)) (b := (807279381626955713 / 1000000000000000000 : ℝ)) (s := (590169467187180057 / 1000000000000000000 : ℝ))
      (shi := (29508473359359003 / 50000000000000000 : ℝ)) (u := (18276493882383637 / 25000000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (atan_up_direct (q1 := (1238728527891599989 / 1000000000000000000 : ℝ)) (r1 := (326551319727830639 / 1000000000000000000 : ℝ)) (q2 := (1051967568138860387 / 1000000000000000000 : ℝ)) (r2 := (159140585259840869 / 1000000000000000000 : ℝ)) 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (by norm_num [atanPoly, Finset.sum_range_succ])
  have ht : ((Nat.totient 14 : ℕ) : ℝ) = 6 := by rw [show Nat.totient 14 = 6 by decide]; norm_num
  unfold eTerm
  rw [cy_2, cy_4, ht]
  refine (mul_le_mul_of_nonneg_left hg (by positivity)).trans (le_of_eq ?_)
  push_cast
  ring

theorem eTerm_2_5_7 : eTerm (cy 2) (cy 5) 7 ≤ π * (2227807601844183 / 4900000000000000 : ℝ) := by
  have hg : arccos (((7 : ℕ) : ℝ) * √((19 / 200 : ℝ) * (23 / 1000 : ℝ))) - ((7 : ℕ) : ℝ) * √((19 / 200 : ℝ) * (23 / 1000 : ℝ)) *
      √(1 - ((7 : ℕ) : ℝ) ^ 2 * (19 / 200 : ℝ) * (23 / 1000 : ℝ)) ≤ (742602533948061 / 800000000000000 : ℝ) :=
    term_le' (a := (65441576998113363 / 200000000000000000 : ℝ)) (b := (10225246405955213 / 31250000000000000 : ℝ)) (s := (3691220233408383 / 3906250000000000 : ℝ))
      (shi := (944952379752546049 / 1000000000000000000 : ℝ)) (u := (72198166906933523 / 25000000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (atan_up_inv (v := (173134589637338387 / 500000000000000000 : ℝ)) (q1 := (1058254385540432449 / 1000000000000000000 : ℝ)) (r1 := (16823439401235987 / 100000000000000000 : ℝ)) (q2 := (40562106677611427 / 40000000000000000 : ℝ)) (r2 := (41765142683169919 / 500000000000000000 : ℝ)) 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (by norm_num [atanPoly, Finset.sum_range_succ])
  have ht : ((Nat.totient 7 : ℕ) : ℝ) = 6 := by rw [show Nat.totient 7 = 6 by decide]; norm_num
  unfold eTerm
  rw [cy_2, cy_5, ht]
  refine (mul_le_mul_of_nonneg_left hg (by positivity)).trans (le_of_eq ?_)
  push_cast
  ring

theorem eTerm_2_5_14 : eTerm (cy 2) (cy 5) 14 ≤ π * (108768002891993229 / 2450000000000000000 : ℝ) := by
  have hg : arccos (((14 : ℕ) : ℝ) * √((19 / 200 : ℝ) * (23 / 1000 : ℝ))) - ((14 : ℕ) : ℝ) * √((19 / 200 : ℝ) * (23 / 1000 : ℝ)) *
      √(1 - ((14 : ℕ) : ℝ) ^ 2 * (19 / 200 : ℝ) * (23 / 1000 : ℝ)) ≤ (36256000963997743 / 100000000000000000 : ℝ) :=
    term_le' (a := (65441576998113363 / 100000000000000000 : ℝ)) (b := (654415769981133631 / 1000000000000000000 : ℝ)) (s := (30245396343906621 / 40000000000000000 : ℝ))
      (shi := (756134908597665527 / 1000000000000000000 : ℝ)) (u := (1155435035771623279 / 1000000000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (atan_up_inv (v := (865474880924118277 / 1000000000000000000 : ℝ)) (q1 := (1322515319196952331 / 1000000000000000000 : ℝ)) (r1 := (93161374843306779 / 250000000000000000 : ℝ)) (q2 := (1067176024938305017 / 1000000000000000000 : ℝ)) (r2 := (9013395445710743 / 50000000000000000 : ℝ)) 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (by norm_num [atanPoly, Finset.sum_range_succ])
  have ht : ((Nat.totient 14 : ℕ) : ℝ) = 6 := by rw [show Nat.totient 14 = 6 by decide]; norm_num
  unfold eTerm
  rw [cy_2, cy_5, ht]
  refine (mul_le_mul_of_nonneg_left hg (by positivity)).trans (le_of_eq ?_)
  push_cast
  ring

theorem eTerm_2_5_21 : eTerm (cy 2) (cy 5) 21 ≤ π * (312284507025079 / 612500000000000000 : ℝ) := by
  have hg : arccos (((21 : ℕ) : ℝ) * √((19 / 200 : ℝ) * (23 / 1000 : ℝ))) - ((21 : ℕ) : ℝ) * √((19 / 200 : ℝ) * (23 / 1000 : ℝ)) *
      √(1 - ((21 : ℕ) : ℝ) ^ 2 * (19 / 200 : ℝ) * (23 / 1000 : ℝ)) ≤ (936853521075237 / 200000000000000000 : ℝ) :=
    term_le' (a := (196324730994340089 / 200000000000000000 : ℝ)) (b := (490811827485850223 / 500000000000000000 : ℝ)) (s := (190827146915736279 / 1000000000000000000 : ℝ))
      (shi := (38165429383147257 / 200000000000000000 : ℝ)) (u := (9719974959305443 / 50000000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (atan_up_direct (q1 := (254680089190808399 / 250000000000000000 : ℝ)) (r1 := (48149189791151713 / 500000000000000000 : ℝ)) (q2 := (502312994533830817 / 500000000000000000 : ℝ)) (r2 := (48038077979369693 / 1000000000000000000 : ℝ)) 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (by norm_num [atanPoly, Finset.sum_range_succ])
  have ht : ((Nat.totient 21 : ℕ) : ℝ) = 12 := by rw [show Nat.totient 21 = 12 by decide]; norm_num
  unfold eTerm
  rw [cy_2, cy_5, ht]
  refine (mul_le_mul_of_nonneg_left hg (by positivity)).trans (le_of_eq ?_)
  push_cast
  ring

theorem eTerm_3_3_7 : eTerm (cy 3) (cy 3) 7 ≤ π * (2460796871357752707 / 6125000000000000000 : ℝ) := by
  have hg : arccos (((7 : ℕ) : ℝ) * √((11 / 200 : ℝ) * (11 / 200 : ℝ))) - ((7 : ℕ) : ℝ) * √((11 / 200 : ℝ) * (11 / 200 : ℝ)) *
      √(1 - ((7 : ℕ) : ℝ) ^ 2 * (11 / 200 : ℝ) * (11 / 200 : ℝ)) ≤ (820265623785917569 / 1000000000000000000 : ℝ) :=
    term_le' (a := (77 / 200 : ℝ)) (b := (77 / 200 : ℝ)) (s := (92291657261098091 / 100000000000000000 : ℝ))
      (shi := (922916572610980911 / 1000000000000000000 : ℝ)) (u := (37456029732588511 / 15625000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (atan_up_inv (v := (417155798720586599 / 1000000000000000000 : ℝ)) (q1 := (33860048597450211 / 31250000000000000 : ℝ)) (r1 := (100108347258466349 / 500000000000000000 : ℝ)) (q2 := (254961605536412917 / 250000000000000000 : ℝ)) (r2 := (19824942364107623 / 200000000000000000 : ℝ)) 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (by norm_num [atanPoly, Finset.sum_range_succ])
  have ht : ((Nat.totient 7 : ℕ) : ℝ) = 6 := by rw [show Nat.totient 7 = 6 by decide]; norm_num
  unfold eTerm
  rw [cy_3, ht]
  refine (mul_le_mul_of_nonneg_left hg (by positivity)).trans (le_of_eq ?_)
  push_cast
  ring

theorem eTerm_3_3_14 : eTerm (cy 3) (cy 3) 14 ≤ π * (601984149555238131 / 24500000000000000000 : ℝ) := by
  have hg : arccos (((14 : ℕ) : ℝ) * √((11 / 200 : ℝ) * (11 / 200 : ℝ))) - ((14 : ℕ) : ℝ) * √((11 / 200 : ℝ) * (11 / 200 : ℝ)) *
      √(1 - ((14 : ℕ) : ℝ) ^ 2 * (11 / 200 : ℝ) * (11 / 200 : ℝ)) ≤ (200661383185079377 / 1000000000000000000 : ℝ) :=
    term_le' (a := (77 / 100 : ℝ)) (b := (77 / 100 : ℝ)) (s := (63804388563797083 / 100000000000000000 : ℝ))
      (shi := (638043885637970831 / 1000000000000000000 : ℝ)) (u := (1325805476650329 / 1600000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (atan_up_direct (q1 := (1298701298701298701 / 1000000000000000000 : ℝ)) (r1 := (22529798221679761 / 62500000000000000 : ℝ)) (q2 := (132873500863183469 / 125000000000000000 : ℝ)) (r2 := (174735272498069493 / 1000000000000000000 : ℝ)) 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (by norm_num [atanPoly, Finset.sum_range_succ])
  have ht : ((Nat.totient 14 : ℕ) : ℝ) = 6 := by rw [show Nat.totient 14 = 6 by decide]; norm_num
  unfold eTerm
  rw [cy_3, ht]
  refine (mul_le_mul_of_nonneg_left hg (by positivity)).trans (le_of_eq ?_)
  push_cast
  ring

theorem eTerm_3_4_7 : eTerm (cy 3) (cy 4) 7 ≤ π * (724760066490912873 / 1531250000000000000 : ℝ) := by
  have hg : arccos (((7 : ℕ) : ℝ) * √((11 / 200 : ℝ) * (7 / 200 : ℝ))) - ((7 : ℕ) : ℝ) * √((11 / 200 : ℝ) * (7 / 200 : ℝ)) *
      √(1 - ((7 : ℕ) : ℝ) ^ 2 * (11 / 200 : ℝ) * (7 / 200 : ℝ)) ≤ (241586688830304291 / 250000000000000000 : ℝ) :=
    term_le' (a := (19195234597420267 / 62500000000000000 : ℝ)) (b := (307123753558724273 / 1000000000000000000 : ℝ)) (s := (951669585517998993 / 1000000000000000000 : ℝ))
      (shi := (475834792758999497 / 500000000000000000 : ℝ)) (u := (309865184470673943 / 100000000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (atan_up_inv (v := (40340124113501421 / 125000000000000000 : ℝ)) (q1 := (1050784868212105881 / 1000000000000000000 : ℝ)) (r1 := (157364625568630539 / 1000000000000000000 : ℝ)) (q2 := (1012306092731025347 / 1000000000000000000 : ℝ)) (r2 := (3128045502363137 / 40000000000000000 : ℝ)) 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (by norm_num [atanPoly, Finset.sum_range_succ])
  have ht : ((Nat.totient 7 : ℕ) : ℝ) = 6 := by rw [show Nat.totient 7 = 6 by decide]; norm_num
  unfold eTerm
  rw [cy_3, cy_4, ht]
  refine (mul_le_mul_of_nonneg_left hg (by positivity)).trans (le_of_eq ?_)
  push_cast
  ring

theorem eTerm_3_4_14 : eTerm (cy 3) (cy 4) 14 ≤ π * (79622503558328799 / 1531250000000000000 : ℝ) := by
  have hg : arccos (((14 : ℕ) : ℝ) * √((11 / 200 : ℝ) * (7 / 200 : ℝ))) - ((14 : ℕ) : ℝ) * √((11 / 200 : ℝ) * (7 / 200 : ℝ)) *
      √(1 - ((14 : ℕ) : ℝ) ^ 2 * (11 / 200 : ℝ) * (7 / 200 : ℝ)) ≤ (26540834519442933 / 62500000000000000 : ℝ) :=
    term_le' (a := (19195234597420267 / 31250000000000000 : ℝ)) (b := (122849501423489709 / 200000000000000000 : ℝ)) (s := (394556713287202857 / 500000000000000000 : ℝ))
      (shi := (197278356643601429 / 250000000000000000 : ℝ)) (u := (160585394615106177 / 125000000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (atan_up_inv (v := (38920102385276737 / 50000000000000000 : ℝ)) (q1 := (1267244943912647687 / 1000000000000000000 : ℝ)) (r1 := (343325078216835569 / 1000000000000000000 : ℝ)) (q2 := (528647356309618809 / 500000000000000000 : ℝ)) (r2 := (166881816256520893 / 1000000000000000000 : ℝ)) 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (by norm_num [atanPoly, Finset.sum_range_succ])
  have ht : ((Nat.totient 14 : ℕ) : ℝ) = 6 := by rw [show Nat.totient 14 = 6 by decide]; norm_num
  unfold eTerm
  rw [cy_3, cy_4, ht]
  refine (mul_le_mul_of_nonneg_left hg (by positivity)).trans (le_of_eq ?_)
  push_cast
  ring

theorem eTerm_3_4_21 : eTerm (cy 3) (cy 4) 21 ≤ π * (5135066917625063 / 1148437500000000000 : ℝ) := by
  have hg : arccos (((21 : ℕ) : ℝ) * √((11 / 200 : ℝ) * (7 / 200 : ℝ))) - ((21 : ℕ) : ℝ) * √((11 / 200 : ℝ) * (7 / 200 : ℝ)) *
      √(1 - ((21 : ℕ) : ℝ) ^ 2 * (11 / 200 : ℝ) * (7 / 200 : ℝ)) ≤ (5135066917625063 / 125000000000000000 : ℝ) :=
    term_le' (a := (57585703792260801 / 62500000000000000 : ℝ)) (b := (921371260676172817 / 1000000000000000000 : ℝ)) (s := (15547347040572549 / 40000000000000000 : ℝ))
      (shi := (1518295609430913 / 3906250000000000 : ℝ)) (u := (421853483609927089 / 1000000000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (atan_up_direct (q1 := (542669411712561661 / 500000000000000000 : ℝ)) (r1 := (202294935897775109 / 1000000000000000000 : ℝ)) (q2 := (255064114622417649 / 250000000000000000 : ℝ)) (r2 := (25033323745566611 / 250000000000000000 : ℝ)) 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (by norm_num [atanPoly, Finset.sum_range_succ])
  have ht : ((Nat.totient 21 : ℕ) : ℝ) = 12 := by rw [show Nat.totient 21 = 12 by decide]; norm_num
  unfold eTerm
  rw [cy_3, cy_4, ht]
  refine (mul_le_mul_of_nonneg_left hg (by positivity)).trans (le_of_eq ?_)
  push_cast
  ring

theorem eTerm_3_5_7 : eTerm (cy 3) (cy 5) 7 ≤ π * (1617080399184385731 / 3062500000000000000 : ℝ) := by
  have hg : arccos (((7 : ℕ) : ℝ) * √((11 / 200 : ℝ) * (23 / 1000 : ℝ))) - ((7 : ℕ) : ℝ) * √((11 / 200 : ℝ) * (23 / 1000 : ℝ)) *
      √(1 - ((7 : ℕ) : ℝ) ^ 2 * (11 / 200 : ℝ) * (23 / 1000 : ℝ)) ≤ (539026799728128577 / 500000000000000000 : ℝ) :=
    term_le' (a := (124483934706451177 / 500000000000000000 : ℝ)) (b := (49793573882580471 / 200000000000000000 : ℝ)) (s := (968511744895228413 / 1000000000000000000 : ℝ))
      (shi := (484255872447614207 / 500000000000000000 : ℝ)) (u := (778021474963095677 / 200000000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (atan_up_inv (v := (257062313105800467 / 1000000000000000000 : ℝ)) (q1 := (516256000647765981 / 500000000000000000 : ℝ)) (r1 := (12647517600975927 / 100000000000000000 : ℝ)) (q2 := (251991563617055887 / 250000000000000000 : ℝ)) (r2 := (62986703948993463 / 1000000000000000000 : ℝ)) 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (by norm_num [atanPoly, Finset.sum_range_succ])
  have ht : ((Nat.totient 7 : ℕ) : ℝ) = 6 := by rw [show Nat.totient 7 = 6 by decide]; norm_num
  unfold eTerm
  rw [cy_3, cy_5, ht]
  refine (mul_le_mul_of_nonneg_left hg (by positivity)).trans (le_of_eq ?_)
  push_cast
  ring

theorem eTerm_3_5_14 : eTerm (cy 3) (cy 5) 14 ≤ π * (264755447236583283 / 3500000000000000000 : ℝ) := by
  have hg : arccos (((14 : ℕ) : ℝ) * √((11 / 200 : ℝ) * (23 / 1000 : ℝ))) - ((14 : ℕ) : ℝ) * √((11 / 200 : ℝ) * (23 / 1000 : ℝ)) *
      √(1 - ((14 : ℕ) : ℝ) ^ 2 * (11 / 200 : ℝ) * (23 / 1000 : ℝ)) ≤ (617762710218694327 / 1000000000000000000 : ℝ) :=
    term_le' (a := (497935738825804709 / 1000000000000000000 : ℝ)) (b := (49793573882580471 / 100000000000000000 : ℝ)) (s := (105861075412283 / 122070312500000 : ℝ))
      (shi := (433606964888711169 / 500000000000000000 : ℝ)) (u := (435404542272072191 / 250000000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (atan_up_inv (v := (574178667717669219 / 1000000000000000000 : ℝ)) (q1 := (144139751113179523 / 125000000000000000 : ℝ)) (r1 := (266673106324330059 / 1000000000000000000 : ℝ)) (q2 := (103494663902863487 / 100000000000000000 : ℝ)) (r2 := (131046731747041919 / 1000000000000000000 : ℝ)) 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (by norm_num [atanPoly, Finset.sum_range_succ])
  have ht : ((Nat.totient 14 : ℕ) : ℝ) = 6 := by rw [show Nat.totient 14 = 6 by decide]; norm_num
  unfold eTerm
  rw [cy_3, cy_5, ht]
  refine (mul_le_mul_of_nonneg_left hg (by positivity)).trans (le_of_eq ?_)
  push_cast
  ring

theorem eTerm_3_5_21 : eTerm (cy 3) (cy 5) 21 ≤ π * (9615118982204101 / 382812500000000000 : ℝ) := by
  have hg : arccos (((21 : ℕ) : ℝ) * √((11 / 200 : ℝ) * (23 / 1000 : ℝ))) - ((21 : ℕ) : ℝ) * √((11 / 200 : ℝ) * (23 / 1000 : ℝ)) *
      √(1 - ((21 : ℕ) : ℝ) ^ 2 * (11 / 200 : ℝ) * (23 / 1000 : ℝ)) ≤ (28845356946612303 / 125000000000000000 : ℝ) :=
    term_le' (a := (93362951029838383 / 125000000000000000 : ℝ)) (b := (149380721647741413 / 200000000000000000 : ℝ)) (s := (664932327383772189 / 1000000000000000000 : ℝ))
      (shi := (20779135230742881 / 31250000000000000 : ℝ)) (u := (6955092665753317 / 7812500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (atan_up_direct (q1 := (267772170055015843 / 200000000000000000 : ℝ)) (r1 := (38063481250358261 / 100000000000000000 : ℝ)) (q2 := (534995995426516601 / 500000000000000000 : ℝ)) (r2 := (183882263402731783 / 1000000000000000000 : ℝ)) 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (by norm_num [atanPoly, Finset.sum_range_succ])
  have ht : ((Nat.totient 21 : ℕ) : ℝ) = 12 := by rw [show Nat.totient 21 = 12 by decide]; norm_num
  unfold eTerm
  rw [cy_3, cy_5, ht]
  refine (mul_le_mul_of_nonneg_left hg (by positivity)).trans (le_of_eq ?_)
  push_cast
  ring

theorem eTerm_3_5_28 : eTerm (cy 3) (cy 5) 28 ≤ π * (299935459574379 / 9800000000000000000 : ℝ) := by
  have hg : arccos (((28 : ℕ) : ℝ) * √((11 / 200 : ℝ) * (23 / 1000 : ℝ))) - ((28 : ℕ) : ℝ) * √((11 / 200 : ℝ) * (23 / 1000 : ℝ)) *
      √(1 - ((28 : ℕ) : ℝ) ^ 2 * (11 / 200 : ℝ) * (23 / 1000 : ℝ)) ≤ (99978486524793 / 200000000000000000 : ℝ) :=
    term_le' (a := (995871477651609419 / 1000000000000000000 : ℝ)) (b := (49793573882580471 / 50000000000000000 : ℝ)) (s := (18154889148656347 / 200000000000000000 : ℝ))
      (shi := (90774445743281747 / 1000000000000000000 : ℝ)) (u := (45575381854162217 / 500000000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (atan_up_direct (q1 := (100414563770630941 / 100000000000000000 : ℝ)) (r1 := (2842569234783881 / 62500000000000000 : ℝ)) (q2 := (100103373128120023 / 100000000000000000 : ℝ)) (r2 := (2272880613932577 / 100000000000000000 : ℝ)) 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (by norm_num [atanPoly, Finset.sum_range_succ])
  have ht : ((Nat.totient 28 : ℕ) : ℝ) = 12 := by rw [show Nat.totient 28 = 12 by decide]; norm_num
  unfold eTerm
  rw [cy_3, cy_5, ht]
  refine (mul_le_mul_of_nonneg_left hg (by positivity)).trans (le_of_eq ?_)
  push_cast
  ring

theorem eTerm_4_4_7 : eTerm (cy 4) (cy 4) 7 ≤ π * (814307609997187281 / 1531250000000000000 : ℝ) := by
  have hg : arccos (((7 : ℕ) : ℝ) * √((7 / 200 : ℝ) * (7 / 200 : ℝ))) - ((7 : ℕ) : ℝ) * √((7 / 200 : ℝ) * (7 / 200 : ℝ)) *
      √(1 - ((7 : ℕ) : ℝ) ^ 2 * (7 / 200 : ℝ) * (7 / 200 : ℝ)) ≤ (271435869999062427 / 250000000000000000 : ℝ) :=
    term_le' (a := (49 / 200 : ℝ)) (b := (49 / 200 : ℝ)) (s := (242380769657990813 / 250000000000000000 : ℝ))
      (shi := (969523078631963253 / 1000000000000000000 : ℝ)) (u := (3957237055640666339 / 1000000000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (atan_up_inv (v := (63175391437227319 / 250000000000000000 : ℝ)) (q1 := (515717481120223013 / 500000000000000000 : ℝ)) (r1 := (15549449677569769 / 125000000000000000 : ℝ)) (q2 := (251926857522379099 / 250000000000000000 : ℝ)) (r2 := (7744878284818857 / 125000000000000000 : ℝ)) 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (by norm_num [atanPoly, Finset.sum_range_succ])
  have ht : ((Nat.totient 7 : ℕ) : ℝ) = 6 := by rw [show Nat.totient 7 = 6 by decide]; norm_num
  unfold eTerm
  rw [cy_4, ht]
  refine (mul_le_mul_of_nonneg_left hg (by positivity)).trans (le_of_eq ?_)
  push_cast
  ring

theorem eTerm_4_4_14 : eTerm (cy 4) (cy 4) 14 ≤ π * (1894687745237032989 / 24500000000000000000 : ℝ) := by
  have hg : arccos (((14 : ℕ) : ℝ) * √((7 / 200 : ℝ) * (7 / 200 : ℝ))) - ((14 : ℕ) : ℝ) * √((7 / 200 : ℝ) * (7 / 200 : ℝ)) *
      √(1 - ((14 : ℕ) : ℝ) ^ 2 * (7 / 200 : ℝ) * (7 / 200 : ℝ)) ≤ (631562581745677663 / 1000000000000000000 : ℝ) :=
    term_le' (a := (49 / 100 : ℝ)) (b := (49 / 100 : ℝ)) (s := (87172243288790039 / 100000000000000000 : ℝ))
      (shi := (871722432887900391 / 1000000000000000000 : ℝ)) (u := (1779025373240613043 / 1000000000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (atan_up_inv (v := (562105529826386617 / 1000000000000000000 : ℝ)) (q1 := (1147154142502829833 / 1000000000000000000 : ℝ)) (r1 := (130895476644999601 / 500000000000000000 : ℝ)) (q2 := (1033699425957316929 / 1000000000000000000 : ℝ)) (r2 := (128726472530112049 / 1000000000000000000 : ℝ)) 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (by norm_num [atanPoly, Finset.sum_range_succ])
  have ht : ((Nat.totient 14 : ℕ) : ℝ) = 6 := by rw [show Nat.totient 14 = 6 by decide]; norm_num
  unfold eTerm
  rw [cy_4, ht]
  refine (mul_le_mul_of_nonneg_left hg (by positivity)).trans (le_of_eq ?_)
  push_cast
  ring

theorem eTerm_4_4_21 : eTerm (cy 4) (cy 4) 21 ≤ π * (246750323028723877 / 9187500000000000000 : ℝ) := by
  have hg : arccos (((21 : ℕ) : ℝ) * √((7 / 200 : ℝ) * (7 / 200 : ℝ))) - ((21 : ℕ) : ℝ) * √((7 / 200 : ℝ) * (7 / 200 : ℝ)) *
      √(1 - ((21 : ℕ) : ℝ) ^ 2 * (7 / 200 : ℝ) * (7 / 200 : ℝ)) ≤ (246750323028723877 / 1000000000000000000 : ℝ) :=
    term_le' (a := (147 / 200 : ℝ)) (b := (147 / 200 : ℝ)) (s := (339033552911802521 / 500000000000000000 : ℝ))
      (shi := (678067105823605043 / 1000000000000000000 : ℝ)) (u := (184508056006423141 / 200000000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (atan_up_direct (q1 := (136054421768707483 / 100000000000000000 : ℝ)) (r1 := (195408387845419321 / 500000000000000000 : ℝ)) (q2 := (67103515886877369 / 62500000000000000 : ℝ)) (r2 := (188467483413006733 / 1000000000000000000 : ℝ)) 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (by norm_num [atanPoly, Finset.sum_range_succ])
  have ht : ((Nat.totient 21 : ℕ) : ℝ) = 12 := by rw [show Nat.totient 21 = 12 by decide]; norm_num
  unfold eTerm
  rw [cy_4, ht]
  refine (mul_le_mul_of_nonneg_left hg (by positivity)).trans (le_of_eq ?_)
  push_cast
  ring

theorem eTerm_4_4_28 : eTerm (cy 4) (cy 4) 28 ≤ π * (3987978487666563 / 12250000000000000000 : ℝ) := by
  have hg : arccos (((28 : ℕ) : ℝ) * √((7 / 200 : ℝ) * (7 / 200 : ℝ))) - ((28 : ℕ) : ℝ) * √((7 / 200 : ℝ) * (7 / 200 : ℝ)) *
      √(1 - ((28 : ℕ) : ℝ) ^ 2 * (7 / 200 : ℝ) * (7 / 200 : ℝ)) ≤ (1329326162555521 / 250000000000000000 : ℝ) :=
    term_le' (a := (49 / 50 : ℝ)) (b := (49 / 50 : ℝ)) (s := (19899748742132399 / 100000000000000000 : ℝ))
      (shi := (198997487421323991 / 1000000000000000000 : ℝ)) (u := (203058660634004073 / 1000000000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (atan_up_direct (q1 := (510204081632653061 / 500000000000000000 : ℝ)) (r1 := (12562972690740151 / 125000000000000000 : ℝ)) (q2 := (40201512610368483 / 40000000000000000 : ℝ)) (r2 := (50125628933800453 / 1000000000000000000 : ℝ)) 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (by norm_num [atanPoly, Finset.sum_range_succ])
  have ht : ((Nat.totient 28 : ℕ) : ℝ) = 12 := by rw [show Nat.totient 28 = 12 by decide]; norm_num
  unfold eTerm
  rw [cy_4, ht]
  refine (mul_le_mul_of_nonneg_left hg (by positivity)).trans (le_of_eq ?_)
  push_cast
  ring

theorem eTerm_4_5_7 : eTerm (cy 4) (cy 5) 7 ≤ π * (126022291314066453 / 218750000000000000 : ℝ) := by
  have hg : arccos (((7 : ℕ) : ℝ) * √((7 / 200 : ℝ) * (23 / 1000 : ℝ))) - ((7 : ℕ) : ℝ) * √((7 / 200 : ℝ) * (23 / 1000 : ℝ)) *
      √(1 - ((7 : ℕ) : ℝ) ^ 2 * (7 / 200 : ℝ) * (23 / 1000 : ℝ)) ≤ (294052013066155057 / 250000000000000000 : ℝ) :=
    term_le' (a := (39721530685511101 / 200000000000000000 : ℝ)) (b := (99303826713777753 / 500000000000000000 : ℝ)) (s := (19601581568842857 / 20000000000000000 : ℝ))
      (shi := (245019769610535713 / 250000000000000000 : ℝ)) (u := (2467374901037331649 / 500000000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (atan_up_inv (v := (202644518994576149 / 1000000000000000000 : ℝ)) (q1 := (25508145770990283 / 25000000000000000 : ℝ)) (r1 := (50151444856387523 / 500000000000000000 : ℝ)) (q2 := (1005017745955131439 / 1000000000000000000 : ℝ)) (r2 := (10005187227407177 / 200000000000000000 : ℝ)) 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (by norm_num [atanPoly, Finset.sum_range_succ])
  have ht : ((Nat.totient 7 : ℕ) : ℝ) = 6 := by rw [show Nat.totient 7 = 6 by decide]; norm_num
  unfold eTerm
  rw [cy_4, cy_5, ht]
  refine (mul_le_mul_of_nonneg_left hg (by positivity)).trans (le_of_eq ?_)
  push_cast
  ring

theorem eTerm_4_5_14 : eTerm (cy 4) (cy 5) 14 ≤ π * (1196671840482472887 / 12250000000000000000 : ℝ) := by
  have hg : arccos (((14 : ℕ) : ℝ) * √((7 / 200 : ℝ) * (23 / 1000 : ℝ))) - ((14 : ℕ) : ℝ) * √((7 / 200 : ℝ) * (23 / 1000 : ℝ)) *
      √(1 - ((14 : ℕ) : ℝ) ^ 2 * (7 / 200 : ℝ) * (23 / 1000 : ℝ)) ≤ (398890613494157629 / 500000000000000000 : ℝ) :=
    term_le' (a := (39721530685511101 / 100000000000000000 : ℝ)) (b := (397215306855111011 / 1000000000000000000 : ℝ)) (s := (229431362285106959 / 250000000000000000 : ℝ))
      (shi := (917725449140427837 / 1000000000000000000 : ℝ)) (u := (288799749563521689 / 125000000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (atan_up_inv (v := (216412930047410187 / 500000000000000000 : ℝ)) (q1 := (54482525298640963 / 50000000000000000 : ℝ)) (r1 := (207128349385545659 / 1000000000000000000 : ℝ)) (q2 := (1021225809074163907 / 1000000000000000000 : ℝ)) (r2 := (102476600316330907 / 1000000000000000000 : ℝ)) 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (by norm_num [atanPoly, Finset.sum_range_succ])
  have ht : ((Nat.totient 14 : ℕ) : ℝ) = 6 := by rw [show Nat.totient 14 = 6 by decide]; norm_num
  unfold eTerm
  rw [cy_4, cy_5, ht]
  refine (mul_le_mul_of_nonneg_left hg (by positivity)).trans (le_of_eq ?_)
  push_cast
  ring

theorem eTerm_4_5_21 : eTerm (cy 4) (cy 5) 21 ≤ π * (45399151998592529 / 918750000000000000 : ℝ) := by
  have hg : arccos (((21 : ℕ) : ℝ) * √((7 / 200 : ℝ) * (23 / 1000 : ℝ))) - ((21 : ℕ) : ℝ) * √((7 / 200 : ℝ) * (23 / 1000 : ℝ)) *
      √(1 - ((21 : ℕ) : ℝ) ^ 2 * (7 / 200 : ℝ) * (23 / 1000 : ℝ)) ≤ (45399151998592529 / 100000000000000000 : ℝ) :=
    term_le' (a := (119164592056533303 / 200000000000000000 : ℝ)) (b := (148955740070666629 / 250000000000000000 : ℝ)) (s := (803115807340385997 / 1000000000000000000 : ℝ))
      (shi := (803115807340385999 / 1000000000000000000 : ℝ)) (u := (1347910135855417419 / 1000000000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (atan_up_inv (v := (370944610252290683 / 500000000000000000 : ℝ)) (q1 := (622575219451612801 / 500000000000000000 : ℝ)) (r1 := (82610190351765507 / 250000000000000000 : ℝ)) (q2 := (526590708425262403 / 500000000000000000 : ℝ)) (r2 := (6437633980029709 / 40000000000000000 : ℝ)) 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (by norm_num [atanPoly, Finset.sum_range_succ])
  have ht : ((Nat.totient 21 : ℕ) : ℝ) = 12 := by rw [show Nat.totient 21 = 12 by decide]; norm_num
  unfold eTerm
  rw [cy_4, cy_5, ht]
  refine (mul_le_mul_of_nonneg_left hg (by positivity)).trans (le_of_eq ?_)
  push_cast
  ring

theorem eTerm_4_5_28 : eTerm (cy 4) (cy 5) 28 ≤ π * (510676396824976197 / 49000000000000000000 : ℝ) := by
  have hg : arccos (((28 : ℕ) : ℝ) * √((7 / 200 : ℝ) * (23 / 1000 : ℝ))) - ((28 : ℕ) : ℝ) * √((7 / 200 : ℝ) * (23 / 1000 : ℝ)) *
      √(1 - ((28 : ℕ) : ℝ) ^ 2 * (7 / 200 : ℝ) * (23 / 1000 : ℝ)) ≤ (170225465608325399 / 1000000000000000000 : ℝ) :=
    term_le' (a := (39721530685511101 / 50000000000000000 : ℝ)) (b := (794430613710222021 / 1000000000000000000 : ℝ)) (s := (121470984189640943 / 200000000000000000 : ℝ))
      (shi := (303677460474102359 / 500000000000000000 : ℝ)) (u := (764516007397651247 / 1000000000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (atan_up_direct (q1 := (251752634589371917 / 200000000000000000 : ℝ)) (r1 := (169233325687756267 / 500000000000000000 : ℝ)) (q2 := (527863541574276737 / 500000000000000000 : ℝ)) (r2 := (164645713018051357 / 1000000000000000000 : ℝ)) 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (by norm_num [atanPoly, Finset.sum_range_succ])
  have ht : ((Nat.totient 28 : ℕ) : ℝ) = 12 := by rw [show Nat.totient 28 = 12 by decide]; norm_num
  unfold eTerm
  rw [cy_4, cy_5, ht]
  refine (mul_le_mul_of_nonneg_left hg (by positivity)).trans (le_of_eq ?_)
  push_cast
  ring

theorem eTerm_4_5_35 : eTerm (cy 4) (cy 5) 35 ≤ π * (820610356268607 / 9570312500000000000 : ℝ) := by
  have hg : arccos (((35 : ℕ) : ℝ) * √((7 / 200 : ℝ) * (23 / 1000 : ℝ))) - ((35 : ℕ) : ℝ) * √((7 / 200 : ℝ) * (23 / 1000 : ℝ)) *
      √(1 - ((35 : ℕ) : ℝ) ^ 2 * (7 / 200 : ℝ) * (23 / 1000 : ℝ)) ≤ (273536785422869 / 250000000000000000 : ℝ) :=
    term_le' (a := (39721530685511101 / 40000000000000000 : ℝ)) (b := (496519133568888763 / 500000000000000000 : ℝ)) (s := (117792189893897463 / 1000000000000000000 : ℝ))
      (shi := (460125741773037 / 3906250000000000 : ℝ)) (u := (14827247069920139 / 125000000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (atan_up_direct (q1 := (251752634589371917 / 250000000000000000 : ℝ)) (r1 := (472814563919277 / 8000000000000000 : ℝ)) (q2 := (500872495048695377 / 500000000000000000 : ℝ)) (r2 := (29525149698031291 / 1000000000000000000 : ℝ)) 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (by norm_num [atanPoly, Finset.sum_range_succ])
  have ht : ((Nat.totient 35 : ℕ) : ℝ) = 24 := by rw [show Nat.totient 35 = 24 by decide]; norm_num
  unfold eTerm
  rw [cy_4, cy_5, ht]
  refine (mul_le_mul_of_nonneg_left hg (by positivity)).trans (le_of_eq ?_)
  push_cast
  ring

theorem eTerm_5_5_7 : eTerm (cy 5) (cy 5) 7 ≤ π * (3750578639863932753 / 6125000000000000000 : ℝ) := by
  have hg : arccos (((7 : ℕ) : ℝ) * √((23 / 1000 : ℝ) * (23 / 1000 : ℝ))) - ((7 : ℕ) : ℝ) * √((23 / 1000 : ℝ) * (23 / 1000 : ℝ)) *
      √(1 - ((7 : ℕ) : ℝ) ^ 2 * (23 / 1000 : ℝ) * (23 / 1000 : ℝ)) ≤ (1250192879954644251 / 1000000000000000000 : ℝ) :=
    term_le' (a := (161 / 1000 : ℝ)) (b := (161 / 1000 : ℝ)) (s := (986954406241747319 / 1000000000000000000 : ℝ))
      (shi := (24673860156043683 / 25000000000000000 : ℝ)) (u := (6130151591563647951 / 1000000000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (atan_up_inv (v := (8156405148089699 / 50000000000000000 : ℝ)) (q1 := (1013218030818596151 / 1000000000000000000 : ℝ)) (r1 := (40514266329977269 / 500000000000000000 : ℝ)) (q2 := (25081936018589969 / 25000000000000000 : ℝ)) (r2 := (20223991697794357 / 500000000000000000 : ℝ)) 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (by norm_num [atanPoly, Finset.sum_range_succ])
  have ht : ((Nat.totient 7 : ℕ) : ℝ) = 6 := by rw [show Nat.totient 7 = 6 by decide]; norm_num
  unfold eTerm
  rw [cy_5, ht]
  refine (mul_le_mul_of_nonneg_left hg (by positivity)).trans (le_of_eq ?_)
  push_cast
  ring

theorem eTerm_5_5_14 : eTerm (cy 5) (cy 5) 14 ≤ π * (43973667650665377 / 382812500000000000 : ℝ) := by
  have hg : arccos (((14 : ℕ) : ℝ) * √((23 / 1000 : ℝ) * (23 / 1000 : ℝ))) - ((14 : ℕ) : ℝ) * √((23 / 1000 : ℝ) * (23 / 1000 : ℝ)) *
      √(1 - ((14 : ℕ) : ℝ) ^ 2 * (23 / 1000 : ℝ) * (23 / 1000 : ℝ)) ≤ (14657889216888459 / 15625000000000000 : ℝ) :=
    term_le' (a := (161 / 500 : ℝ)) (b := (161 / 500 : ℝ)) (s := (946739668546744691 / 1000000000000000000 : ℝ))
      (shi := (236684917136686173 / 250000000000000000 : ℝ)) (u := (2940185306045790969 / 1000000000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (atan_up_inv (v := (42514327155831731 / 125000000000000000 : ℝ)) (q1 := (1056256575300167231 / 1000000000000000000 : ℝ)) (r1 := (82702378033005137 / 500000000000000000 : ℝ)) (q2 := (1013587062530523997 / 1000000000000000000 : ℝ)) (r2 := (41072163986329471 / 500000000000000000 : ℝ)) 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (by norm_num [atanPoly, Finset.sum_range_succ])
  have ht : ((Nat.totient 14 : ℕ) : ℝ) = 6 := by rw [show Nat.totient 14 = 6 by decide]; norm_num
  unfold eTerm
  rw [cy_5, ht]
  refine (mul_le_mul_of_nonneg_left hg (by positivity)).trans (le_of_eq ?_)
  push_cast
  ring

theorem eTerm_5_5_21 : eTerm (cy 5) (cy 5) 21 ≤ π * (643794066958127509 / 9187500000000000000 : ℝ) := by
  have hg : arccos (((21 : ℕ) : ℝ) * √((23 / 1000 : ℝ) * (23 / 1000 : ℝ))) - ((21 : ℕ) : ℝ) * √((23 / 1000 : ℝ) * (23 / 1000 : ℝ)) *
      √(1 - ((21 : ℕ) : ℝ) ^ 2 * (23 / 1000 : ℝ) * (23 / 1000 : ℝ)) ≤ (643794066958127509 / 1000000000000000000 : ℝ) :=
    term_le' (a := (483 / 1000 : ℝ)) (b := (483 / 1000 : ℝ)) (s := (875620351522279317 / 1000000000000000000 : ℝ))
      (shi := (437810175761139659 / 500000000000000000 : ℝ)) (u := (453219643645072111 / 250000000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (atan_up_inv (v := (275804462036713253 / 500000000000000000 : ℝ)) (q1 := (3568898318280451 / 3125000000000000 : ℝ)) (r1 := (51502960032182477 / 200000000000000000 : ℝ)) (q2 := (516312374513219139 / 500000000000000000 : ℝ)) (r2 := (126690772748021331 / 1000000000000000000 : ℝ)) 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (by norm_num [atanPoly, Finset.sum_range_succ])
  have ht : ((Nat.totient 21 : ℕ) : ℝ) = 12 := by rw [show Nat.totient 21 = 12 by decide]; norm_num
  unfold eTerm
  rw [cy_5, ht]
  refine (mul_le_mul_of_nonneg_left hg (by positivity)).trans (le_of_eq ?_)
  push_cast
  ring

theorem eTerm_5_5_28 : eTerm (cy 5) (cy 5) 28 ≤ π * (227042696683895367 / 9800000000000000000 : ℝ) := by
  have hg : arccos (((28 : ℕ) : ℝ) * √((23 / 1000 : ℝ) * (23 / 1000 : ℝ))) - ((28 : ℕ) : ℝ) * √((23 / 1000 : ℝ) * (23 / 1000 : ℝ)) *
      √(1 - ((28 : ℕ) : ℝ) ^ 2 * (23 / 1000 : ℝ) * (23 / 1000 : ℝ)) ≤ (75680898894631789 / 200000000000000000 : ℝ) :=
    term_le' (a := (161 / 250 : ℝ)) (b := (161 / 250 : ℝ)) (s := (153005097954283863 / 200000000000000000 : ℝ))
      (shi := (191256372442854829 / 250000000000000000 : ℝ)) (u := (14849097239352083 / 12500000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (atan_up_inv (v := (841802016547735789 / 1000000000000000000 : ℝ)) (q1 := (326786497107040291 / 250000000000000000 : ℝ)) (r1 := (364867251907733981 / 1000000000000000000 : ℝ)) (q2 := (266121226078771971 / 250000000000000000 : ℝ)) (r2 := (88367624085094023 / 500000000000000000 : ℝ)) 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (by norm_num [atanPoly, Finset.sum_range_succ])
  have ht : ((Nat.totient 28 : ℕ) : ℝ) = 12 := by rw [show Nat.totient 28 = 12 by decide]; norm_num
  unfold eTerm
  rw [cy_5, ht]
  refine (mul_le_mul_of_nonneg_left hg (by positivity)).trans (le_of_eq ?_)
  push_cast
  ring

theorem eTerm_5_5_35 : eTerm (cy 5) (cy 5) 35 ≤ π * (472603909966575663 / 38281250000000000000 : ℝ) := by
  have hg : arccos (((35 : ℕ) : ℝ) * √((23 / 1000 : ℝ) * (23 / 1000 : ℝ))) - ((35 : ℕ) : ℝ) * √((23 / 1000 : ℝ) * (23 / 1000 : ℝ)) *
      √(1 - ((35 : ℕ) : ℝ) ^ 2 * (23 / 1000 : ℝ) * (23 / 1000 : ℝ)) ≤ (157534636655525221 / 1000000000000000000 : ℝ) :=
    term_le' (a := (161 / 200 : ℝ)) (b := (161 / 200 : ℝ)) (s := (593274809847847829 / 1000000000000000000 : ℝ))
      (shi := (59327480984784783 / 100000000000000000 : ℝ)) (u := (368493670712948963 / 500000000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (atan_up_direct (q1 := (1242236024844720497 / 1000000000000000000 : ℝ)) (r1 := (41085513147357883 / 125000000000000000 : ℝ)) (q2 := (1052631578947368421 / 1000000000000000000 : ℝ)) (r2 := (80064076902543567 / 500000000000000000 : ℝ)) 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (by norm_num [atanPoly, Finset.sum_range_succ])
  have ht : ((Nat.totient 35 : ℕ) : ℝ) = 24 := by rw [show Nat.totient 35 = 24 by decide]; norm_num
  unfold eTerm
  rw [cy_5, ht]
  refine (mul_le_mul_of_nonneg_left hg (by positivity)).trans (le_of_eq ?_)
  push_cast
  ring

theorem eTerm_5_5_42 : eTerm (cy 5) (cy 5) 42 ≤ π * (392033773390081 / 1225000000000000000 : ℝ) := by
  have hg : arccos (((42 : ℕ) : ℝ) * √((23 / 1000 : ℝ) * (23 / 1000 : ℝ))) - ((42 : ℕ) : ℝ) * √((23 / 1000 : ℝ) * (23 / 1000 : ℝ)) *
      √(1 - ((42 : ℕ) : ℝ) ^ 2 * (23 / 1000 : ℝ) * (23 / 1000 : ℝ)) ≤ (1176101320170243 / 100000000000000000 : ℝ) :=
    term_le' (a := (483 / 500 : ℝ)) (b := (483 / 500 : ℝ)) (s := (12927103310486847 / 50000000000000000 : ℝ))
      (shi := (258542066209736941 / 1000000000000000000 : ℝ)) (u := (133820945243135063 / 500000000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (atan_up_direct (q1 := (517598343685300207 / 500000000000000000 : ℝ)) (r1 := (5260265843534831 / 40000000000000000 : ℝ)) (q2 := (504304966752611907 / 500000000000000000 : ℝ)) (r2 := (32735735270132469 / 500000000000000000 : ℝ)) 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (by norm_num [atanPoly, Finset.sum_range_succ])
  have ht : ((Nat.totient 42 : ℕ) : ℝ) = 12 := by rw [show Nat.totient 42 = 12 by decide]; norm_num
  unfold eTerm
  rw [cy_5, ht]
  refine (mul_le_mul_of_nonneg_left hg (by positivity)).trans (le_of_eq ?_)
  push_cast
  ring

end Zeta7Cert
