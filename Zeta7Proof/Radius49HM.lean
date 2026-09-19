import Zeta7Proof.Radius49U7Jacobian
import Zeta7Proof.Radius49U7Norm

/-! Radius internalization, **HM**: the twisted `U₇` matrix estimate.

* `sdiv_cert_n`: `Σ_k a_k uP(n+k) = T · qP n` (`n ≤ 6`), exact polynomial identities, so the
  spurious poles of the Jacobian formula at the zeros of `T` (`j = 1728`) cancel.
* `Fcol_rec`: the twisted columns `Fₙ = twistLin (Xⁿ)` satisfy the `e_k` recurrence.
* `eK_bnd`: `‖e_k‖ ≤ (7^s)^k` at radius `7^{improve s}` (from `v₇(e_{k,j}) ≥ (7j-k)/4`).
* `twistMatrix_bound`: **HM**. No published radius input is used. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option linter.style.longLine false
open PowerSeries
namespace Zeta7Radius49
open Zeta7Main
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

theorem norm_49 : ‖(49 : ℚ_[7])‖ = (49 : ℝ)⁻¹ := by
  have h := Padic.norm_p (p := 7)
  rw [show (49 : ℚ_[7]) = 7 ^ 2 by norm_num, norm_pow]
  simp only [Nat.cast_ofNat] at h
  rw [h]; norm_num

/-- Scaled weight-zero columns `uP m = 7 colX m` (explicit for `m ≤ 7`, recurrence beyond). -/
def uP {R : Type*} [CommRing R] : ℕ → R → R
  | 0, _ => 7
  | 1, X => pM 1 X
  | 2, X => pM 2 X
  | 3, X => pM 3 X
  | 4, X => pM 4 X
  | 5, X => pM 5 X
  | 6, X => pM 6 X
  | 7, X => pM 7 X
  | m + 8, X => eK 1 X * uP (m + 7) X - eK 2 X * uP (m + 6) X + eK 3 X * uP (m + 5) X -
      eK 4 X * uP (m + 4) X + eK 5 X * uP (m + 3) X - eK 6 X * uP (m + 2) X + eK 7 X * uP (m + 1) X

/-- The quotients `(Σ_k a_k uP (n+k)) / T` for `n ≤ 6`. -/
def qP {R : Type*} [CommRing R] : ℕ → R → R
  | 0, X => 49 * X + (-23030) * X ^ 2 + (-972405) * X ^ 3 + (-10117814) * X ^ 4 + (-33765263) * X ^ 5
  | 1, X => 7546 * X ^ 2 + 2007236 * X ^ 3 + 284525703 * X ^ 4 + 16828277662 * X ^ 5 + 517535009775 * X ^ 6 + 9431848564110 * X ^ 7 + 108377278783830 * X ^ 8 + 798946779816122 * X ^ 9 + 3688855293225711 * X ^ 10 + 9770481587462694 * X ^ 11 + 11398895185373143 * X ^ 12
  | 2, X => 27440 * X ^ 2 + 27850914 * X ^ 3 + 10812077556 * X ^ 4 + 2077537102326 * X ^ 5 + 217533382182760 * X ^ 6 + 13687754841287275 * X ^ 7 + 563044047121726590 * X ^ 8 + 16084501695834459699 * X ^ 9 + 332402750472568818210 * X ^ 10 + 5102090816802231813155 * X ^ 11 + 59055852132188594180120 * X ^ 12 + 518470198335308379497750 * X ^ 13 + 3440689440605612478976588 * X ^ 14 + 17017202877378811759168825 * X ^ 15 + 60924747391333925443662010 * X ^ 16 + 149495624377040487317460325 * X ^ 17 + 225393402906922580878632490 * X ^ 18 + 157775382034845806615042743 * X ^ 19
  | 3, X => 45619 * X ^ 2 + 160211870 * X ^ 3 + 142021418945 * X ^ 4 + 58647206486470 * X ^ 5 + 13554860002205669 * X ^ 6 + 1922523917674184300 * X ^ 7 + 179220011359674885726 * X ^ 8 + 11628203206606615861820 * X ^ 9 + 549723226120142836724417 * X ^ 10 + 19616515769181285300375974 * X ^ 11 + 542688286087632753478232795 * X ^ 12 + 11873552271255661670693155146 * X ^ 13 + 208457907809971487630431627263 * X ^ 14 + 2966550802439889693939637083392 * X ^ 15 + 34436872701437500948858828616762 * X ^ 16 + 327017731640292512138079279984920 * X ^ 17 + 2538878961048290765142772198131635 * X ^ 18 + 16046226839133046442945173020559626 * X ^ 19 + 81844590218337445364226177479897885 * X ^ 20 + 332065646903620965656999981984366826 * X ^ 21 + 1047645822582231893630456557602923080 * X ^ 22 + 2479416072034001469875878884217803818 * X ^ 23 + 4144790550351777218717674275634824651 * X ^ 24 + 4367628751983593198218624505507664686 * X ^ 25 + 2183814375991796599109312252753832343 * X ^ 26
  | 4, X => 27440 * X ^ 2 + 453380144 * X ^ 3 + 923141080316 * X ^ 4 + 742298281837210 * X ^ 5 + 319251177517043744 * X ^ 6 + 83832773441371863118 * X ^ 7 + 14508794925150898510404 * X ^ 8 + 1748325302191017504657066 * X ^ 9 + 153279125709099252020987780 * X ^ 10 + 10134791498818323708361099620 * X ^ 11 + 520321912591766493860098679204 * X ^ 12 + 21234158504804482113197777127637 * X ^ 13 + 701856515539856906546548478502794 * X ^ 14 + 19072032597041496827323694610187087 * X ^ 15 + 431129289550247081498974849325316886 * X ^ 16 + 8182369102935817456839604173445752769 * X ^ 17 + 131296801296879612610530005499262857220 * X ^ 18 + 1790356998634753074968303432201463261044 * X ^ 19 + 20815424615328663366256310773678292551460 * X ^ 20 + 206692427013633483028476022249399339941222 * X ^ 21 + 1752989820675134057057891433177045409502356 * X ^ 22 + 12677265296291273154588225422387099710484858 * X ^ 23 + 77895314631595141576240818323942606703718880 * X ^ 24 + 404308115086363534429681260694682538811289066 * X ^ 25 + 1757494597227262594263440894205473821832849092 * X ^ 26 + 6320069610861697181581788465973295530095083820 * X ^ 27 + 18476223880346658444540834083507239165372557336 * X ^ 28 + 42814442322105380033069599938656232576576177699 * X ^ 29 + 75697393645029577251247599534576541109985070410 * X ^ 30 + 95967893140708559555804779253137058925395897889 * X ^ 31 + 77726062213135858152635275758739105575940479282 * X ^ 32 + 30226801971775055948247051683954096612865741943 * X ^ 33
  | 5, X => 7546 * X ^ 2 + 677014772 * X ^ 3 + 3399248470828 * X ^ 4 + 5239739143210544 * X ^ 5 + 3940122828941526206 * X ^ 6 + 1745681361873042878480 * X ^ 7 + 503382613647728689472213 * X ^ 8 + 100595830697011724737669006 * X ^ 9 + 14581020837221434514906636943 * X ^ 10 + 1589115224578327539199120651406 * X ^ 11 + 134120253680397068156758754029486 * X ^ 12 + 8982811080690918610010721231505690 * X ^ 13 + 487196342041528328405637368471457417 * X ^ 14 + 21760014549231752448009995402498889370 * X ^ 15 + 811552453704146925636359919146105242852 * X ^ 16 + 25566686597912525191644496922636932312570 * X ^ 17 + 686847727895039007747478159876073506567075 * X ^ 18 + 15858695893485256490688090585161205417285822 * X ^ 19 + 316708478729715550408833622104384891249805930 * X ^ 20 + 5498632722280217501697595724886085864497785310 * X ^ 21 + 83326882658886506498785437958080620299937800715 * X ^ 22 + 1105459868789388108953572426500620979825451021242 * X ^ 23 + 12864977167919513147794859115792808929597044896019 * X ^ 24 + 131482570508659645550037666868566216216213927730464 * X ^ 25 + 1180351509561460533062615276000087914165464487649616 * X ^ 26 + 9300851205318342374671142279013889466415037215107380 * X ^ 27 + 64217057221942444372184238641939829634564053307031203 * X ^ 28 + 387397686129537380162021617872705529274476089117112466 * X ^ 29 + 2033493017070636746103164774581286460854142139911924281 * X ^ 30 + 9234858966221575818180555393474939496519727395163604638 * X ^ 31 + 36007601862398119413627020623166921070369768705882575740 * X ^ 32 + 119316650171800694195098142932988718507223194072875076118 * X ^ 33 + 331439405654189607467872075603808023438031948083905498091 * X ^ 34 + 757495575296617937475680501943921713907536207022044769926 * X ^ 35 + 1387303049176599048281639597019486909741153565815002514794 * X ^ 36 + 1957840048011397506446914985521994565355696793539222453850 * X ^ 37 + 1999187439235134712527122560740710814218453467081099739239 * X ^ 38 + 1314901805671430884749382623842883622774553287073474996278 * X ^ 39 + 418377847259091645147530834859099334519176045887014771543 * X ^ 40
  | 6, X => 980 * X ^ 2 + 591024035 * X ^ 3 + 7647344738530 * X ^ 4 + 22913237985129905 * X ^ 5 + 29534948124327294446 * X ^ 6 + 21152839299026071627123 * X ^ 7 + 9585970346643777867892300 * X ^ 8 + 2969572388132339213872144672 * X ^ 9 + 662361075953190777159920184464 * X ^ 10 + 110545959059387788965800842913234 * X ^ 11 + 14231899879542778273856621409260184 * X ^ 12 + 1449177156194057863189710098264597030 * X ^ 13 + 119180848333927234780116727739801447976 * X ^ 14 + 8057074132821878904555378791846307805850 * X ^ 15 + 454478720889920951695560058115011458077408 * X ^ 16 + 21662461352995434736605377792284211140322840 * X ^ 17 + 881907354569841518340331898212469096497396100 * X ^ 18 + 30947131776628638881713819165081520453906960991 * X ^ 19 + 943332867263742789163073542103529932709776981402 * X ^ 20 + 25142615108129224324526784904995892990322005958013 * X ^ 21 + 589208178935022621869690284819823226778521513073030 * X ^ 22 + 12197352269416289387475186079005938108944261800879141 * X ^ 23 + 223915661907002542038386978064748576943335081427299080 * X ^ 24 + 3656805007837839944014315360301159582620683583148955674 * X ^ 25 + 53261467896763184797889303566477615188178625675638620076 * X ^ 26 + 693190629524931265256007700408058422811321826324084619556 * X ^ 27 + 8072467200385850694298647604334097167219645467816328173536 * X ^ 28 + 84181807159681837047702958868499992836419447864779639319426 * X ^ 29 + 786306994616442927926703634914483496744204413771735805601512 * X ^ 30 + 6576356647167440975641786051528887432480237285304379996317840 * X ^ 31 + 49203564199448531204611530759314530072010546051954411537192252 * X ^ 32 + 328809930025204020562278068685454033038222747653364479126191134 * X ^ 33 + 1958119305990691669951983193945733773486737959235874223170315832 * X ^ 34 + 10359369288349377962664616018568500253817575700303962664088362097 * X ^ 35 + 48491419946184640506559730233265237846560288873343237199977925778 * X ^ 36 + 199787298121840652815314977582030655791761066451169762885156440269 * X ^ 37 + 719696590549854421966119699157190099207549014451614182456860104406 * X ^ 38 + 2247562783313562595131838799056519626797749454132147140164975879053 * X ^ 39 + 6018481427654113546269659757484447308814484477207328584600980923984 * X ^ 40 + 13621529436014363077329708367710380905188202892034191587875902111618 * X ^ 41 + 25558267547647065533133473399442028112049809952846038777882460815076 * X ^ 42 + 38698726026388452223150810087456900769516549232161047313847256855485 * X ^ 43 + 45445739146377362615711341431266574649914916951814225551898378709402 * X ^ 44 + 38847910074564445689539174475988074308960385839058227696788353887901 * X ^ 45 + 21509012357668450155790051404784357526995015888292126069408241135674 * X ^ 46 + 5790887942449198118866552301288096257267888893001726249456064921143 * X ^ 47
  | _, _ => 0

theorem sdiv_cert_0 {R : Type*} [CommRing R] (X : R) :
    ∑ k ∈ Finset.range 7, aJ k X * uP (0 + k) X = polyTg X * qP 0 X := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, uP, pM, eK, aJ, qP, polyTg]
  ring

theorem sdiv_cert_1 {R : Type*} [CommRing R] (X : R) :
    ∑ k ∈ Finset.range 7, aJ k X * uP (1 + k) X = polyTg X * qP 1 X := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, uP, pM, eK, aJ, qP, polyTg]
  ring

theorem sdiv_cert_2 {R : Type*} [CommRing R] (X : R) :
    ∑ k ∈ Finset.range 7, aJ k X * uP (2 + k) X = polyTg X * qP 2 X := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, uP, pM, eK, aJ, qP, polyTg]
  ring

theorem sdiv_cert_3 {R : Type*} [CommRing R] (X : R) :
    ∑ k ∈ Finset.range 7, aJ k X * uP (3 + k) X = polyTg X * qP 3 X := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, uP, pM, eK, aJ, qP, polyTg]
  ring

theorem sdiv_cert_4 {R : Type*} [CommRing R] (X : R) :
    ∑ k ∈ Finset.range 7, aJ k X * uP (4 + k) X = polyTg X * qP 4 X := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, uP, pM, eK, aJ, qP, polyTg]
  ring

theorem sdiv_cert_5 {R : Type*} [CommRing R] (X : R) :
    ∑ k ∈ Finset.range 7, aJ k X * uP (5 + k) X = polyTg X * qP 5 X := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, uP, pM, eK, aJ, qP, polyTg]
  ring

theorem sdiv_cert_6 {R : Type*} [CommRing R] (X : R) :
    ∑ k ∈ Finset.range 7, aJ k X * uP (6 + k) X = polyTg X * qP 6 X := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, uP, pM, eK, aJ, qP, polyTg]
  ring

/-- Coefficient table of `e_k`. -/
def eKc : ℕ → ℕ → ℤ
  | 1, 1 => 4018
  | 1, 2 => 422576
  | 1, 3 => 14201915
  | 1, 4 => 224003696
  | 1, 5 => 1856265922
  | 1, 6 => 7909306972
  | 1, 7 => 13841287201
  | 2, 1 => (-8624)
  | 2, 2 => (-289835)
  | 2, 3 => (-4571504)
  | 2, 4 => (-37882978)
  | 2, 5 => (-161414428)
  | 2, 6 => (-282475249)
  | 3, 1 => 5915
  | 3, 2 => 93296
  | 3, 3 => 773122
  | 3, 4 => 3294172
  | 3, 5 => 5764801
  | 4, 1 => (-1904)
  | 4, 2 => (-15778)
  | 4, 3 => (-67228)
  | 4, 4 => (-117649)
  | 5, 1 => 322
  | 5, 2 => 1372
  | 5, 3 => 2401
  | 6, 1 => (-28)
  | 6, 2 => (-49)
  | 7, 1 => 1
  | _, _ => 0

theorem eK_eq_sum (k : ℕ) (hk : 1 ≤ k ∧ k ≤ 7) :
    eK k (X : ℚ_[7]⟦X⟧) = ∑ j ∈ Finset.range 8, C ((eKc k j : ℤ) : ℚ_[7]) * X ^ j := by
  obtain ⟨h1, h7⟩ := hk
  interval_cases k <;>
    simp only [eK, eKc, Finset.sum_range_succ, Finset.sum_range_zero, Int.cast_zero, map_zero,
      zero_mul, zero_add, add_zero, map_intCast, Int.cast_ofNat, Int.cast_neg, map_neg, map_ofNat,
      pow_zero, pow_one, mul_one] <;> ring

theorem eK_term_bound {s : ℝ} (hs : 0 < s) (k j : ℕ) (hk : 1 ≤ k ∧ k ≤ 7) (hj : j < 8) :
    ‖((eKc k j : ℤ) : ℚ_[7])‖ * ((7 : ℝ) ^ improve s) ^ j ≤ ((7 : ℝ) ^ s) ^ k := by
  have hR : 0 ≤ ((7 : ℝ) ^ s) ^ k := by positivity
  have hρ : 0 ≤ ((7 : ℝ) ^ improve s) ^ j := by positivity
  obtain ⟨h1, h7⟩ := hk
  interval_cases k <;> interval_cases j
  · simp [eKc]; positivity
  · calc ‖((eKc 1 1 : ℤ) : ℚ_[7])‖ * ((7 : ℝ) ^ improve s) ^ 1
        ≤ (7 : ℝ) ^ (-((2 : ℕ) : ℤ)) * ((7 : ℝ) ^ improve s) ^ 1 :=
          mul_le_mul_of_nonneg_right (norm_int_le_of_dvd _ 2 (by norm_num [eKc])) hρ
      _ ≤ ((7 : ℝ) ^ s) ^ 1 := expo_le hs 2 1 1 (by norm_num) (by norm_num) (by norm_num)
  · calc ‖((eKc 1 2 : ℤ) : ℚ_[7])‖ * ((7 : ℝ) ^ improve s) ^ 2
        ≤ (7 : ℝ) ^ (-((4 : ℕ) : ℤ)) * ((7 : ℝ) ^ improve s) ^ 2 :=
          mul_le_mul_of_nonneg_right (norm_int_le_of_dvd _ 4 (by norm_num [eKc])) hρ
      _ ≤ ((7 : ℝ) ^ s) ^ 1 := expo_le hs 4 2 1 (by norm_num) (by norm_num) (by norm_num)
  · calc ‖((eKc 1 3 : ℤ) : ℚ_[7])‖ * ((7 : ℝ) ^ improve s) ^ 3
        ≤ (7 : ℝ) ^ (-((5 : ℕ) : ℤ)) * ((7 : ℝ) ^ improve s) ^ 3 :=
          mul_le_mul_of_nonneg_right (norm_int_le_of_dvd _ 5 (by norm_num [eKc])) hρ
      _ ≤ ((7 : ℝ) ^ s) ^ 1 := expo_le hs 5 3 1 (by norm_num) (by norm_num) (by norm_num)
  · calc ‖((eKc 1 4 : ℤ) : ℚ_[7])‖ * ((7 : ℝ) ^ improve s) ^ 4
        ≤ (7 : ℝ) ^ (-((7 : ℕ) : ℤ)) * ((7 : ℝ) ^ improve s) ^ 4 :=
          mul_le_mul_of_nonneg_right (norm_int_le_of_dvd _ 7 (by norm_num [eKc])) hρ
      _ ≤ ((7 : ℝ) ^ s) ^ 1 := expo_le hs 7 4 1 (by norm_num) (by norm_num) (by norm_num)
  · calc ‖((eKc 1 5 : ℤ) : ℚ_[7])‖ * ((7 : ℝ) ^ improve s) ^ 5
        ≤ (7 : ℝ) ^ (-((9 : ℕ) : ℤ)) * ((7 : ℝ) ^ improve s) ^ 5 :=
          mul_le_mul_of_nonneg_right (norm_int_le_of_dvd _ 9 (by norm_num [eKc])) hρ
      _ ≤ ((7 : ℝ) ^ s) ^ 1 := expo_le hs 9 5 1 (by norm_num) (by norm_num) (by norm_num)
  · calc ‖((eKc 1 6 : ℤ) : ℚ_[7])‖ * ((7 : ℝ) ^ improve s) ^ 6
        ≤ (7 : ℝ) ^ (-((11 : ℕ) : ℤ)) * ((7 : ℝ) ^ improve s) ^ 6 :=
          mul_le_mul_of_nonneg_right (norm_int_le_of_dvd _ 11 (by norm_num [eKc])) hρ
      _ ≤ ((7 : ℝ) ^ s) ^ 1 := expo_le hs 11 6 1 (by norm_num) (by norm_num) (by norm_num)
  · calc ‖((eKc 1 7 : ℤ) : ℚ_[7])‖ * ((7 : ℝ) ^ improve s) ^ 7
        ≤ (7 : ℝ) ^ (-((12 : ℕ) : ℤ)) * ((7 : ℝ) ^ improve s) ^ 7 :=
          mul_le_mul_of_nonneg_right (norm_int_le_of_dvd _ 12 (by norm_num [eKc])) hρ
      _ ≤ ((7 : ℝ) ^ s) ^ 1 := expo_le hs 12 7 1 (by norm_num) (by norm_num) (by norm_num)
  · simp [eKc]; positivity
  · calc ‖((eKc 2 1 : ℤ) : ℚ_[7])‖ * ((7 : ℝ) ^ improve s) ^ 1
        ≤ (7 : ℝ) ^ (-((2 : ℕ) : ℤ)) * ((7 : ℝ) ^ improve s) ^ 1 :=
          mul_le_mul_of_nonneg_right (norm_int_le_of_dvd _ 2 (by norm_num [eKc])) hρ
      _ ≤ ((7 : ℝ) ^ s) ^ 2 := expo_le hs 2 1 2 (by norm_num) (by norm_num) (by norm_num)
  · calc ‖((eKc 2 2 : ℤ) : ℚ_[7])‖ * ((7 : ℝ) ^ improve s) ^ 2
        ≤ (7 : ℝ) ^ (-((3 : ℕ) : ℤ)) * ((7 : ℝ) ^ improve s) ^ 2 :=
          mul_le_mul_of_nonneg_right (norm_int_le_of_dvd _ 3 (by norm_num [eKc])) hρ
      _ ≤ ((7 : ℝ) ^ s) ^ 2 := expo_le hs 3 2 2 (by norm_num) (by norm_num) (by norm_num)
  · calc ‖((eKc 2 3 : ℤ) : ℚ_[7])‖ * ((7 : ℝ) ^ improve s) ^ 3
        ≤ (7 : ℝ) ^ (-((5 : ℕ) : ℤ)) * ((7 : ℝ) ^ improve s) ^ 3 :=
          mul_le_mul_of_nonneg_right (norm_int_le_of_dvd _ 5 (by norm_num [eKc])) hρ
      _ ≤ ((7 : ℝ) ^ s) ^ 2 := expo_le hs 5 3 2 (by norm_num) (by norm_num) (by norm_num)
  · calc ‖((eKc 2 4 : ℤ) : ℚ_[7])‖ * ((7 : ℝ) ^ improve s) ^ 4
        ≤ (7 : ℝ) ^ (-((7 : ℕ) : ℤ)) * ((7 : ℝ) ^ improve s) ^ 4 :=
          mul_le_mul_of_nonneg_right (norm_int_le_of_dvd _ 7 (by norm_num [eKc])) hρ
      _ ≤ ((7 : ℝ) ^ s) ^ 2 := expo_le hs 7 4 2 (by norm_num) (by norm_num) (by norm_num)
  · calc ‖((eKc 2 5 : ℤ) : ℚ_[7])‖ * ((7 : ℝ) ^ improve s) ^ 5
        ≤ (7 : ℝ) ^ (-((9 : ℕ) : ℤ)) * ((7 : ℝ) ^ improve s) ^ 5 :=
          mul_le_mul_of_nonneg_right (norm_int_le_of_dvd _ 9 (by norm_num [eKc])) hρ
      _ ≤ ((7 : ℝ) ^ s) ^ 2 := expo_le hs 9 5 2 (by norm_num) (by norm_num) (by norm_num)
  · calc ‖((eKc 2 6 : ℤ) : ℚ_[7])‖ * ((7 : ℝ) ^ improve s) ^ 6
        ≤ (7 : ℝ) ^ (-((10 : ℕ) : ℤ)) * ((7 : ℝ) ^ improve s) ^ 6 :=
          mul_le_mul_of_nonneg_right (norm_int_le_of_dvd _ 10 (by norm_num [eKc])) hρ
      _ ≤ ((7 : ℝ) ^ s) ^ 2 := expo_le hs 10 6 2 (by norm_num) (by norm_num) (by norm_num)
  · simp [eKc]; positivity
  · simp [eKc]; positivity
  · calc ‖((eKc 3 1 : ℤ) : ℚ_[7])‖ * ((7 : ℝ) ^ improve s) ^ 1
        ≤ (7 : ℝ) ^ (-((1 : ℕ) : ℤ)) * ((7 : ℝ) ^ improve s) ^ 1 :=
          mul_le_mul_of_nonneg_right (norm_int_le_of_dvd _ 1 (by norm_num [eKc])) hρ
      _ ≤ ((7 : ℝ) ^ s) ^ 3 := expo_le hs 1 1 3 (by norm_num) (by norm_num) (by norm_num)
  · calc ‖((eKc 3 2 : ℤ) : ℚ_[7])‖ * ((7 : ℝ) ^ improve s) ^ 2
        ≤ (7 : ℝ) ^ (-((3 : ℕ) : ℤ)) * ((7 : ℝ) ^ improve s) ^ 2 :=
          mul_le_mul_of_nonneg_right (norm_int_le_of_dvd _ 3 (by norm_num [eKc])) hρ
      _ ≤ ((7 : ℝ) ^ s) ^ 3 := expo_le hs 3 2 3 (by norm_num) (by norm_num) (by norm_num)
  · calc ‖((eKc 3 3 : ℤ) : ℚ_[7])‖ * ((7 : ℝ) ^ improve s) ^ 3
        ≤ (7 : ℝ) ^ (-((5 : ℕ) : ℤ)) * ((7 : ℝ) ^ improve s) ^ 3 :=
          mul_le_mul_of_nonneg_right (norm_int_le_of_dvd _ 5 (by norm_num [eKc])) hρ
      _ ≤ ((7 : ℝ) ^ s) ^ 3 := expo_le hs 5 3 3 (by norm_num) (by norm_num) (by norm_num)
  · calc ‖((eKc 3 4 : ℤ) : ℚ_[7])‖ * ((7 : ℝ) ^ improve s) ^ 4
        ≤ (7 : ℝ) ^ (-((7 : ℕ) : ℤ)) * ((7 : ℝ) ^ improve s) ^ 4 :=
          mul_le_mul_of_nonneg_right (norm_int_le_of_dvd _ 7 (by norm_num [eKc])) hρ
      _ ≤ ((7 : ℝ) ^ s) ^ 3 := expo_le hs 7 4 3 (by norm_num) (by norm_num) (by norm_num)
  · calc ‖((eKc 3 5 : ℤ) : ℚ_[7])‖ * ((7 : ℝ) ^ improve s) ^ 5
        ≤ (7 : ℝ) ^ (-((8 : ℕ) : ℤ)) * ((7 : ℝ) ^ improve s) ^ 5 :=
          mul_le_mul_of_nonneg_right (norm_int_le_of_dvd _ 8 (by norm_num [eKc])) hρ
      _ ≤ ((7 : ℝ) ^ s) ^ 3 := expo_le hs 8 5 3 (by norm_num) (by norm_num) (by norm_num)
  · simp [eKc]; positivity
  · simp [eKc]; positivity
  · simp [eKc]; positivity
  · calc ‖((eKc 4 1 : ℤ) : ℚ_[7])‖ * ((7 : ℝ) ^ improve s) ^ 1
        ≤ (7 : ℝ) ^ (-((1 : ℕ) : ℤ)) * ((7 : ℝ) ^ improve s) ^ 1 :=
          mul_le_mul_of_nonneg_right (norm_int_le_of_dvd _ 1 (by norm_num [eKc])) hρ
      _ ≤ ((7 : ℝ) ^ s) ^ 4 := expo_le hs 1 1 4 (by norm_num) (by norm_num) (by norm_num)
  · calc ‖((eKc 4 2 : ℤ) : ℚ_[7])‖ * ((7 : ℝ) ^ improve s) ^ 2
        ≤ (7 : ℝ) ^ (-((3 : ℕ) : ℤ)) * ((7 : ℝ) ^ improve s) ^ 2 :=
          mul_le_mul_of_nonneg_right (norm_int_le_of_dvd _ 3 (by norm_num [eKc])) hρ
      _ ≤ ((7 : ℝ) ^ s) ^ 4 := expo_le hs 3 2 4 (by norm_num) (by norm_num) (by norm_num)
  · calc ‖((eKc 4 3 : ℤ) : ℚ_[7])‖ * ((7 : ℝ) ^ improve s) ^ 3
        ≤ (7 : ℝ) ^ (-((5 : ℕ) : ℤ)) * ((7 : ℝ) ^ improve s) ^ 3 :=
          mul_le_mul_of_nonneg_right (norm_int_le_of_dvd _ 5 (by norm_num [eKc])) hρ
      _ ≤ ((7 : ℝ) ^ s) ^ 4 := expo_le hs 5 3 4 (by norm_num) (by norm_num) (by norm_num)
  · calc ‖((eKc 4 4 : ℤ) : ℚ_[7])‖ * ((7 : ℝ) ^ improve s) ^ 4
        ≤ (7 : ℝ) ^ (-((6 : ℕ) : ℤ)) * ((7 : ℝ) ^ improve s) ^ 4 :=
          mul_le_mul_of_nonneg_right (norm_int_le_of_dvd _ 6 (by norm_num [eKc])) hρ
      _ ≤ ((7 : ℝ) ^ s) ^ 4 := expo_le hs 6 4 4 (by norm_num) (by norm_num) (by norm_num)
  · simp [eKc]; positivity
  · simp [eKc]; positivity
  · simp [eKc]; positivity
  · simp [eKc]; positivity
  · calc ‖((eKc 5 1 : ℤ) : ℚ_[7])‖ * ((7 : ℝ) ^ improve s) ^ 1
        ≤ (7 : ℝ) ^ (-((1 : ℕ) : ℤ)) * ((7 : ℝ) ^ improve s) ^ 1 :=
          mul_le_mul_of_nonneg_right (norm_int_le_of_dvd _ 1 (by norm_num [eKc])) hρ
      _ ≤ ((7 : ℝ) ^ s) ^ 5 := expo_le hs 1 1 5 (by norm_num) (by norm_num) (by norm_num)
  · calc ‖((eKc 5 2 : ℤ) : ℚ_[7])‖ * ((7 : ℝ) ^ improve s) ^ 2
        ≤ (7 : ℝ) ^ (-((3 : ℕ) : ℤ)) * ((7 : ℝ) ^ improve s) ^ 2 :=
          mul_le_mul_of_nonneg_right (norm_int_le_of_dvd _ 3 (by norm_num [eKc])) hρ
      _ ≤ ((7 : ℝ) ^ s) ^ 5 := expo_le hs 3 2 5 (by norm_num) (by norm_num) (by norm_num)
  · calc ‖((eKc 5 3 : ℤ) : ℚ_[7])‖ * ((7 : ℝ) ^ improve s) ^ 3
        ≤ (7 : ℝ) ^ (-((4 : ℕ) : ℤ)) * ((7 : ℝ) ^ improve s) ^ 3 :=
          mul_le_mul_of_nonneg_right (norm_int_le_of_dvd _ 4 (by norm_num [eKc])) hρ
      _ ≤ ((7 : ℝ) ^ s) ^ 5 := expo_le hs 4 3 5 (by norm_num) (by norm_num) (by norm_num)
  · simp [eKc]; positivity
  · simp [eKc]; positivity
  · simp [eKc]; positivity
  · simp [eKc]; positivity
  · simp [eKc]; positivity
  · calc ‖((eKc 6 1 : ℤ) : ℚ_[7])‖ * ((7 : ℝ) ^ improve s) ^ 1
        ≤ (7 : ℝ) ^ (-((1 : ℕ) : ℤ)) * ((7 : ℝ) ^ improve s) ^ 1 :=
          mul_le_mul_of_nonneg_right (norm_int_le_of_dvd _ 1 (by norm_num [eKc])) hρ
      _ ≤ ((7 : ℝ) ^ s) ^ 6 := expo_le hs 1 1 6 (by norm_num) (by norm_num) (by norm_num)
  · calc ‖((eKc 6 2 : ℤ) : ℚ_[7])‖ * ((7 : ℝ) ^ improve s) ^ 2
        ≤ (7 : ℝ) ^ (-((2 : ℕ) : ℤ)) * ((7 : ℝ) ^ improve s) ^ 2 :=
          mul_le_mul_of_nonneg_right (norm_int_le_of_dvd _ 2 (by norm_num [eKc])) hρ
      _ ≤ ((7 : ℝ) ^ s) ^ 6 := expo_le hs 2 2 6 (by norm_num) (by norm_num) (by norm_num)
  · simp [eKc]; positivity
  · simp [eKc]; positivity
  · simp [eKc]; positivity
  · simp [eKc]; positivity
  · simp [eKc]; positivity
  · simp [eKc]; positivity
  · calc ‖((eKc 7 1 : ℤ) : ℚ_[7])‖ * ((7 : ℝ) ^ improve s) ^ 1
        ≤ (7 : ℝ) ^ (-((0 : ℕ) : ℤ)) * ((7 : ℝ) ^ improve s) ^ 1 :=
          mul_le_mul_of_nonneg_right (norm_int_le_of_dvd _ 0 (by norm_num [eKc])) hρ
      _ ≤ ((7 : ℝ) ^ s) ^ 7 := expo_le hs 0 1 7 (by norm_num) (by norm_num) (by norm_num)
  · simp [eKc]; positivity
  · simp [eKc]; positivity
  · simp [eKc]; positivity
  · simp [eKc]; positivity
  · simp [eKc]; positivity
  · simp [eKc]; positivity

/-! ### Bounds for `e_k` -/

theorem eK_bnd {s : ℝ} (hs : 0 < s) (k : ℕ) (hk : 1 ≤ k ∧ k ≤ 7) :
    Bnd ((7 : ℝ) ^ improve s) (eK k (X : ℚ_[7]⟦X⟧)) (((7 : ℝ) ^ s) ^ k) := by
  rw [eK_eq_sum k hk]
  apply Bnd.sum (by positivity) (by positivity)
  intro j hj
  exact (Bnd_C_mul_X_pow (by positivity) _ j).mono
    (eK_term_bound hs k j hk (Finset.mem_range.mp hj))

/-! ### The weight-zero columns and the twisted columns -/

theorem seven_colX_small (m : ℕ) (hm : m ≤ 7) : 7 * colX m = uP m (X : ℚ_[7]⟦X⟧) := by
  interval_cases m
  · rw [colX_zero, mul_one]; rfl
  all_goals exact colX_small _ ⟨by norm_num, by norm_num⟩

theorem seven_colX (m : ℕ) : 7 * colX m = uP m (X : ℚ_[7]⟦X⟧) := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    by_cases hm : m ≤ 7
    · exact seven_colX_small m hm
    · obtain ⟨j, rfl⟩ : ∃ j, m = j + 8 := ⟨m - 8, by omega⟩
      have h : colX (j + 8) =
          eK 1 X * colX (j + 7) - eK 2 X * colX (j + 6) + eK 3 X * colX (j + 5) -
            eK 4 X * colX (j + 4) + eK 5 X * colX (j + 3) - eK 6 X * colX (j + 2) +
            eK 7 X * colX (j + 1) := colX_rec (j + 1)
      rw [h, uP, ← ih (j + 7) (by omega), ← ih (j + 6) (by omega), ← ih (j + 5) (by omega),
        ← ih (j + 4) (by omega), ← ih (j + 3) (by omega), ← ih (j + 2) (by omega),
        ← ih (j + 1) (by omega)]
      ring

/-- The twisted columns `Fₙ = twistLin (Xⁿ)`. -/
def Fcol (n : ℕ) : ℚ_[7]⟦X⟧ := twistLin (X ^ n)

/-- The Jacobian denominator `7 X T N²`. -/
def Dq : ℚ_[7]⟦X⟧ := 7 * (X * (polyTg X * polyNg X ^ 2))

theorem polyTg_ne : polyTg (X : ℚ_[7]⟦X⟧) ≠ 0 := by
  intro h
  have := congrArg (constantCoeff (R := ℚ_[7])) h
  simp [polyTg] at this

theorem polyNg_ne : polyNg (X : ℚ_[7]⟦X⟧) ≠ 0 := by
  intro h
  have := congrArg (constantCoeff (R := ℚ_[7])) h
  simp [polyNg] at this

theorem Dq_ne : Dq ≠ 0 := by
  unfold Dq
  refine mul_ne_zero (by
    intro h
    have := congrArg (constantCoeff (R := ℚ_[7])) h
    rw [map_ofNat, map_zero] at this
    norm_num at this) (mul_ne_zero X_ne_zero (mul_ne_zero polyTg_ne (pow_ne_zero 2 polyNg_ne)))

theorem Fcol_jac (n : ℕ) : Dq * Fcol n = ∑ k ∈ Finset.range 7, aJ k X * colX (n + k) :=
  twistLin_jacobian n

/-- **The recurrence for the twisted columns.** -/
theorem Fcol_rec (n : ℕ) :
    Fcol (n + 7) =
      eK 1 X * Fcol (n + 6) - eK 2 X * Fcol (n + 5) + eK 3 X * Fcol (n + 4) -
        eK 4 X * Fcol (n + 3) + eK 5 X * Fcol (n + 2) - eK 6 X * Fcol (n + 1) +
        eK 7 X * Fcol n := by
  apply mul_left_cancel₀ Dq_ne
  have hL : Dq * Fcol (n + 7) = ∑ k ∈ Finset.range 7, aJ k X *
      (eK 1 X * colX (n + k + 6) - eK 2 X * colX (n + k + 5) + eK 3 X * colX (n + k + 4) -
        eK 4 X * colX (n + k + 3) + eK 5 X * colX (n + k + 2) - eK 6 X * colX (n + k + 1) +
        eK 7 X * colX (n + k)) := by
    rw [Fcol_jac]
    apply Finset.sum_congr rfl
    intro k _
    rw [show n + 7 + k = n + k + 7 by ring, colX_rec]
  have hR : Dq * (eK 1 X * Fcol (n + 6) - eK 2 X * Fcol (n + 5) + eK 3 X * Fcol (n + 4) -
        eK 4 X * Fcol (n + 3) + eK 5 X * Fcol (n + 2) - eK 6 X * Fcol (n + 1) +
        eK 7 X * Fcol n) =
      eK 1 X * (Dq * Fcol (n + 6)) - eK 2 X * (Dq * Fcol (n + 5)) +
        eK 3 X * (Dq * Fcol (n + 4)) - eK 4 X * (Dq * Fcol (n + 3)) +
        eK 5 X * (Dq * Fcol (n + 2)) - eK 6 X * (Dq * Fcol (n + 1)) + eK 7 X * (Dq * Fcol n) := by
    ring
  rw [hL, hR, Fcol_jac, Fcol_jac, Fcol_jac, Fcol_jac, Fcol_jac, Fcol_jac, Fcol_jac]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, add_zero, add_assoc,
    Nat.reduceAdd]
  ring

/-- **The base columns.** `49 X N² Fₙ = qPₙ` for `n ≤ 6`. -/
theorem Fcol_base (n : ℕ) (hn : n ≤ 6) :
    C (49 : ℚ_[7]) * X * (polyNg X ^ 2 * Fcol n) = qP n (X : ℚ_[7]⟦X⟧) := by
  have hc : ∑ k ∈ Finset.range 7, aJ k (X : ℚ_[7]⟦X⟧) * uP (n + k) X =
      polyTg X * qP n X := by
    interval_cases n
    exacts [sdiv_cert_0 _, sdiv_cert_1 _, sdiv_cert_2 _, sdiv_cert_3 _, sdiv_cert_4 _,
      sdiv_cert_5 _, sdiv_cert_6 _]
  have h7 : 7 * (Dq * Fcol n) = polyTg X * qP n (X : ℚ_[7]⟦X⟧) := by
    rw [Fcol_jac, Finset.mul_sum, ← hc]
    apply Finset.sum_congr rfl
    intro k _
    rw [← seven_colX]; ring
  apply mul_left_cancel₀ polyTg_ne
  rw [← h7, Dq, show (C (49 : ℚ_[7]) : ℚ_[7]⟦X⟧) = 49 from map_ofNat C 49]
  ring

theorem qP_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (n : ℕ) (X : R) :
    φ (qP n X) = qP n (φ X) := by
  rcases n with _ | _ | _ | _ | _ | _ | _ | n <;> simp [qP, map_ofNat]

theorem qP_bdd {ρ : ℝ} (hρ : 0 < ρ) (n : ℕ) : ∃ B, Bnd ρ (qP n (X : ℚ_[7]⟦X⟧)) B := by
  have h := qP_map (bddSubring ρ hρ).subtype n ⟨X, X_mem_bddSubring hρ⟩
  simp only [Subring.coe_subtype] at h
  rw [← h]
  exact (qP n (⟨X, X_mem_bddSubring hρ⟩ : bddSubring ρ hρ)).2

/-- `N² = 1 + N'` with `N'` explicit. -/
theorem polyNg_sq_eq : polyNg (X : ℚ_[7]⟦X⟧) ^ 2 =
    1 + (C (490 : ℚ_[7]) * X ^ 1 + C (64827 : ℚ_[7]) * X ^ 2 + C (1176490 : ℚ_[7]) * X ^ 3 +
      C (5764801 : ℚ_[7]) * X ^ 4) := by
  simp only [polyNg, map_ofNat]; ring

theorem norm_nat_seven_pow {c : ℕ} {v : ℕ} (h : 7 ^ v ∣ c) :
    ‖(c : ℚ_[7])‖ ≤ (7 : ℝ) ^ (-(v : ℤ)) := by
  have := norm_int_le_of_dvd (c : ℤ) v (by exact_mod_cast h)
  simpa using this

theorem improve_lt_two {s : ℝ} (hs : s < 2) : improve s < 2 := by
  unfold improve
  exact (min_le_right _ _).trans_lt (by linarith)

theorem mono_le_one {s : ℝ} (hs : s < 2) (j : ℕ) {c : ℕ} (h : 7 ^ (2 * j) ∣ c) :
    ‖(c : ℚ_[7])‖ * ((7 : ℝ) ^ improve s) ^ j ≤ 1 := by
  have hn := norm_nat_seven_pow h
  have hρ : ((7 : ℝ) ^ improve s) ^ j ≤ (49 : ℝ) ^ j := by
    apply pow_le_pow_left₀ (by positivity)
    calc (7 : ℝ) ^ improve s ≤ (7 : ℝ) ^ (2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (improve_lt_two hs).le
      _ = 49 := by norm_num
  calc ‖(c : ℚ_[7])‖ * ((7 : ℝ) ^ improve s) ^ j ≤ (7 : ℝ) ^ (-((2 * j : ℕ) : ℤ)) * 49 ^ j :=
        mul_le_mul hn hρ (by positivity) (by positivity)
    _ = 1 := by
      rw [show (49 : ℝ) ^ j = (7 : ℝ) ^ ((2 * j : ℕ) : ℤ) by push_cast; rw [zpow_mul]; norm_num,
        ← zpow_add₀ (by norm_num)]
      simp

theorem Nprime_bnd {s : ℝ} (hs : s < 2) :
    Bnd ((7 : ℝ) ^ improve s)
      (C (490 : ℚ_[7]) * X ^ 1 + C (64827 : ℚ_[7]) * X ^ 2 + C (1176490 : ℚ_[7]) * X ^ 3 +
        C (5764801 : ℚ_[7]) * X ^ 4) 1 := by
  have hρ : 0 ≤ (7 : ℝ) ^ improve s := by positivity
  have t : ∀ (c j : ℕ), 7 ^ (2 * j) ∣ c → Bnd ((7 : ℝ) ^ improve s) (C (c : ℚ_[7]) * X ^ j) 1 :=
    fun c j h => (Bnd_C_mul_X_pow hρ _ j).mono (mono_le_one hs j h)
  have h := (((t 490 1 (by norm_num)).add hρ (t 64827 2 (by norm_num))).add hρ
    (t 1176490 3 (by norm_num))).add hρ (t 5764801 4 (by norm_num))
  simpa using h

/-- **Bounds for the base twisted columns.** -/
theorem Fcol_base_bnd {s : ℝ} (hs2 : s < 2) (n : ℕ) (hn : n ≤ 6) :
    ∃ B, Bnd ((7 : ℝ) ^ improve s) (Fcol n) B := by
  have hρ : 0 < (7 : ℝ) ^ improve s := by positivity
  obtain ⟨B, hB⟩ := qP_bdd hρ n
  have hG := Bnd_of_X_mul hρ norm_49 hB (Fcol_base n hn)
  refine ⟨49 * B / (7 : ℝ) ^ improve s, ?_⟩
  apply Bnd_of_mul_dominant hρ (D := polyNg X ^ 2) (G := polyNg X ^ 2 * Fcol n)
  · rw [polyNg_sq_eq]; simp
  · intro l hl
    rw [polyNg_sq_eq, map_add, coeff_one, ite_cond_eq_false _ _ (eq_false (by omega)), zero_add]
    exact Nprime_bnd hs2 l
  · exact hG
  · rfl

/-- **HM: the twisted matrix estimate.** -/
theorem twistMatrix_bound :
    ∀ s : ℝ, 0 < s → s < 2 → ∃ K : ℝ, 0 ≤ K ∧ ∀ i n,
      ‖Zeta7Main.twistMatrix i n‖ * ((7 : ℝ) ^ improve s) ^ i ≤ K * ((7 : ℝ) ^ s) ^ n := by
  intro s hs0 hs2
  set ρ : ℝ := (7 : ℝ) ^ improve s with hρdef
  set R : ℝ := (7 : ℝ) ^ s with hRdef
  have hρ : 0 < ρ := by positivity
  have hR1 : 1 ≤ R := Real.one_le_rpow (by norm_num) hs0.le
  -- base bounds
  choose B hB using fun n : Fin 7 => Fcol_base_bnd hs2 n.1 (by omega)
  set C0 : ℝ := ∑ n : Fin 7, B n with hC0
  have hB0 : ∀ n : Fin 7, 0 ≤ B n := fun n => (hB n).nonneg
  have hC0nn : 0 ≤ C0 := Finset.sum_nonneg (fun n _ => hB0 n)
  have hbase : ∀ n, n ≤ 6 → Bnd ρ (Fcol n) (C0 * R ^ n) := by
    intro n hn
    have hle : B ⟨n, by omega⟩ ≤ C0 :=
      Finset.single_le_sum (fun m _ => hB0 m) (Finset.mem_univ _)
    exact (hB ⟨n, by omega⟩).mono (hle.trans (le_mul_of_one_le_right hC0nn (one_le_pow₀ hR1)))
  have hall : ∀ n, Bnd ρ (Fcol n) (C0 * R ^ n) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      by_cases hn : n ≤ 6
      · exact hbase n hn
      · obtain ⟨m, rfl⟩ : ∃ m, n = m + 7 := ⟨n - 7, by omega⟩
        rw [Fcol_rec]
        have term : ∀ j : ℕ, 1 ≤ j → j ≤ 7 →
            Bnd ρ (eK j X * Fcol (m + 7 - j)) (C0 * R ^ (m + 7)) := by
          intro j hj1 hj7
          have := (eK_bnd hs0 j ⟨hj1, hj7⟩).mul hρ (ih (m + 7 - j) (by omega))
          refine this.mono (le_of_eq ?_)
          rw [← mul_assoc, mul_comm (R ^ j) C0, mul_assoc, ← pow_add]
          congr 2; omega
        have t1 := term 1 le_rfl (by norm_num)
        have t2 := term 2 (by norm_num) (by norm_num)
        have t3 := term 3 (by norm_num) (by norm_num)
        have t4 := term 4 (by norm_num) (by norm_num)
        have t5 := term 5 (by norm_num) (by norm_num)
        have t6 := term 6 (by norm_num) (by norm_num)
        have t7 := term 7 (by norm_num) (by norm_num)
        simp only [show m + 7 - 1 = m + 6 by omega, show m + 7 - 2 = m + 5 by omega,
          show m + 7 - 3 = m + 4 by omega, show m + 7 - 4 = m + 3 by omega,
          show m + 7 - 5 = m + 2 by omega, show m + 7 - 6 = m + 1 by omega,
          show m + 7 - 7 = m by omega] at t1 t2 t3 t4 t5 t6 t7
        exact (((((t1.sub hρ.le t2).add hρ.le t3).sub hρ.le t4).add hρ.le t5).sub hρ.le t6).add
          hρ.le t7
  refine ⟨C0, hC0nn, fun i n => ?_⟩
  exact hall n i

end Zeta7Radius49
