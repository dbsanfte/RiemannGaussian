/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaBlockCacheCheck

/-!
# Kernel-checked batch examples with original finite sums

The checks exercise a direct block, all thirty-one compressed moments, and
phase resets at sample indices 8 and 256. Conclusions pay the analytic
polynomial error. A small full-zeta check also exercises the exact cached
prefix and the analytic correction. These are not new zero counts.
-/

namespace RiemannGaussian.ZetaBlockBatchValidation
open LeanCert.Core LeanCert.Engine CertifiedComplexInterval ZetaBlockEnclosure
open ZetaBlockBatchEnclosure ZetaBlockBatchPacket

private def cfg : DyadicConfig := {precision := -48, taylorDepth := 24}
private def center : Box := rational cfg.precision (1 / 2) 21900
private def initial : Box := rational cfg.precision 0 (-64)
private def step : Box := rational cfg.precision 0 (1 / 2)
private def delta (j : ℕ) : ℚ := -64 + (j : ℚ) / 2
private def shiftBox (j : ℕ) : Box := rational cfg.precision 0 (delta j)

private def checkedPacket (v K : ℕ) (js : List ℕ) (margin : ℚ) : Bool :=
  match prepare cfg center initial step (lookup cfg.precision (coefficients cfg.precision center)) v K with
  | .error _ => false
  | .ok P => js.all fun j =>
      let D := shiftCoefficients cfg.precision (shiftBox j)
      let Z := evaluate cfg.precision P (lookup cfg.precision D) j
      decide (Z.re.hi.toRat ≤ margin - 1 / 1000000000)

private theorem checked_direct : checkedPacket 6000 20 [0] (-1 / 100) = true := by
  decide +kernel

private theorem checked_compressed : checkedPacket 10000 32 [0, 8, 256] (-1 / 1000) = true := by
  decide +kernel

private theorem original_sum_bound {v K j : ℕ} {js : List ℕ} {margin : ℚ}
    (hv : 0 < v) (hK : K ≤ 32) (hKv : ∀ k < K, 300 * k ≤ v) (hj : j ≤ 256)
    (hmem : j ∈ js) (hc : checkedPacket v K js margin = true) :
    (∑ k ∈ Finset.range K,
      (v + k : ℂ) ^ (-(1 / 2 + (21836 + (j : ℂ) / 2) * Complex.I))).re < (margin : ℝ) := by
  let s : ℂ := 1 / 2 + 21900 * Complex.I
  let d : ℂ := -64 * Complex.I
  let q : ℂ := (1 / 2) * Complex.I
  have hp : cfg.precision ≤ 0 := by decide
  have hs : Mem s center := by simpa [s, center] using mem_rational hp (1 / 2) 21900
  have hd : Mem d initial := by simpa [d, initial] using mem_rational hp 0 (-64)
  have hq : Mem q step := by simpa [q, step] using mem_rational hp 0 (1 / 2)
  have hshift : d + j * q = (delta j : ℂ) * Complex.I := by
    dsimp [d, q, delta]
    push_cast
    ring
  have hD : Mem (d + j * q) (shiftBox j) := by
    rw [hshift]
    simpa only [shiftBox, Rat.cast_zero, zero_add] using mem_rational hp 0 (delta j)
  have hs0 : 0 < s.re := by norm_num [s]
  have hn : ‖s‖ ≤ 22500 := by
    have hh := Complex.norm_le_abs_re_add_abs_im s
    norm_num [s] at hh
    linarith
  have hd0 : (d + j * q).re = 0 := by simp [d, q]
  have hnD : ‖d + j * q‖ ≤ 64 := by
    rw [hshift, norm_mul, Complex.norm_I, mul_one]
    rw [← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs]
    apply abs_le.mpr
    have hjR : (j : ℝ) ≤ 256 := by exact_mod_cast hj
    have hj0 := Nat.cast_nonneg (α := ℝ) j
    dsimp [delta]
    push_cast
    constructor <;> linarith
  have herr := ZetaBlockBatch.norm_block_error_le hs0.le hn hd0 hnD
    (show 1 ≤ v by omega) hKv
  have hr := (Complex.re_le_norm _).trans herr
  simp only [Complex.sub_re] at hr
  cases he : prepare cfg center initial step
      (lookup cfg.precision (coefficients cfg.precision center)) v K with
  | error err => simp only [checkedPacket, he, Bool.false_eq_true] at hc
  | ok P =>
    simp only [checkedPacket, he, List.all_eq_true] at hc
    have hcheck := of_decide_eq_true (hc j hmem)
    have hP := sound_prepare hp hs0 hs hd hq (fun l hl => mem_coefficients hp hs hl) hv he
    have hb := (mem_evaluate hp hv hP j (fun l hl => mem_shiftCoefficients hp hD hl)).1.2
    have hcast :
        ((evaluate cfg.precision P (lookup cfg.precision (shiftCoefficients cfg.precision (shiftBox j))) j).re.hi.toRat : ℝ)
          ≤ (margin : ℝ) - 1 / 1000000000 := by
      simpa only [Rat.cast_sub, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using
        (Rat.cast_le (K := ℝ)).mpr hcheck
    have hKR : (K : ℝ) ≤ 32 := by exact_mod_cast hK
    have heq : s + (d + j * q) = 1 / 2 + (21836 + (j : ℂ) / 2) * Complex.I := by
      dsimp [s, d, q]
      ring
    rw [heq] at hr
    linarith

/-- A direct cached block bounds the original sum at the first shifted height. -/
theorem direct_sum_negative :
    (∑ k ∈ Finset.range 20, (6000 + k : ℂ) ^ (-(1 / 2 + 21836 * Complex.I))).re < -(1 / 100) := by
  convert! original_sum_bound (j := 0) (by norm_num : 0 < (6000 : ℕ))
    (by norm_num : 20 ≤ 32) (fun k hk => by omega) (by norm_num) (by simp) checked_direct using 1 <;>
    norm_num

/-- The same compressed packet controls three original sums, including two phase resets. -/
theorem compressed_sums_negative {j : ℕ} (hj : j ∈ [0, 8, 256]) :
    (∑ k ∈ Finset.range 32,
      (10000 + k : ℂ) ^ (-(1 / 2 + (21836 + (j : ℂ) / 2) * Complex.I))).re < -(1 / 1000) := by
  have hj' : j ≤ 256 := by simp only [List.mem_cons, List.not_mem_nil, or_false] at hj; omega
  convert! original_sum_bound (by norm_num : 0 < (10000 : ℕ)) le_rfl
    (fun k hk => by omega) hj' hj checked_compressed using 1
  norm_num

private def smallCfg : DyadicConfig := {precision := -32, taylorDepth := 12}

private def smallCenter : Box := rational smallCfg.precision (1 / 2) 20
private def smallInitial : Box := rational smallCfg.precision 0 (-6)
private def smallPoint : Box := rational smallCfg.precision (1 / 2) 18
private def smallStep : Box := rational smallCfg.precision 0 (1 / 2)
private def smallShift : Box := rational smallCfg.precision 0 (-2)

-- Exact dyadic candidate data; every numerical inclusion is checked below.
private def dataInterval (a b : ℤ) (hab : a ≤ b) : IntervalDyadic :=
  ⟨⟨a, -32⟩, ⟨b, -32⟩, by
    change (a : ℚ) / 4294967296 ≤ (b : ℚ) / 4294967296
    exact div_le_div_of_nonneg_right (by exact_mod_cast hab) (by norm_num)⟩

private def dataBox (a b c d : ℤ) (hab : a ≤ b) (hcd : c ≤ d) : Box :=
  ⟨dataInterval a b hab, dataInterval c d hcd⟩

private def pair40 : Box × Box :=
  (dataBox (129443862) (129694247) (-666742616) (-666495099) (by decide) (by decide),
    dataBox (-1160715601) (-1160634723) (-4135197243) (-4135125749) (by decide) (by decide))

private theorem checked_pair40 :
    (ZetaBlockCacheCheck.powerCheck smallCfg 40
        (neg (add smallCfg.precision smallCenter smallInitial)) pair40.1 &&
      ZetaBlockCacheCheck.powerCheck smallCfg 40 (neg smallStep) pair40.2) = true := by
  decide +kernel

private def pair39 : Box × Box :=
  (dataBox (357281514) (357471044) (-587711860) (-587491754) (by decide) (by decide),
    dataBox (-1108276925) (-1108196975) (-4149558190) (-4149487465) (by decide) (by decide))

private theorem checked_pair39 :
    (ZetaBlockCacheCheck.powerCheck smallCfg 39
        (neg (add smallCfg.precision smallCenter smallInitial)) pair39.1 &&
      ZetaBlockCacheCheck.powerCheck smallCfg 39 (neg smallStep) pair39.2) = true := by
  decide +kernel

private def pair38 : Box × Box :=
  (dataBox (550046540) (550173057) (-427675280) (-427474057) (by decide) (by decide),
    dataBox (-1054291571) (-1054212547) (-4163601093) (-4163531127) (by decide) (by decide))

private theorem checked_pair38 :
    (ZetaBlockCacheCheck.powerCheck smallCfg 38
        (neg (add smallCfg.precision smallCenter smallInitial)) pair38.1 &&
      ZetaBlockCacheCheck.powerCheck smallCfg 38 (neg smallStep) pair38.2) = true := by
  decide +kernel

private def pair37 : Box × Box :=
  (dataBox (677105533) (677165362) (-200216434) (-200025967) (by decide) (by decide),
    dataBox (-998681530) (-998603424) (-4177287848) (-4177218626) (by decide) (by decide))

private theorem checked_pair37 :
    (ZetaBlockCacheCheck.powerCheck smallCfg 37
        (neg (add smallCfg.precision smallCenter smallInitial)) pair37.1 &&
      ZetaBlockCacheCheck.powerCheck smallCfg 37 (neg smallStep) pair37.2) = true := by
  decide +kernel

private def pair36 : Box × Box :=
  (dataBox (712504196) (712529049) (68679405) (68868921) (by decide) (by decide),
    dataBox (-941362925) (-941285736) (-4190576105) (-4190507617) (by decide) (by decide))

private theorem checked_pair36 :
    (ZetaBlockCacheCheck.powerCheck smallCfg 36
        (neg (add smallCfg.precision smallCenter smallInitial)) pair36.1 &&
      ZetaBlockCacheCheck.powerCheck smallCfg 36 (neg smallStep) pair36.2) = true := by
  decide +kernel

private def pair35 : Box × Box :=
  (dataBox (640297025) (640396901) (341960091) (342162332) (by decide) (by decide),
    dataBox (-882245421) (-882169146) (-4203418709) (-4203350944) (by decide) (by decide))

private theorem checked_pair35 :
    (ZetaBlockCacheCheck.powerCheck smallCfg 35
        (neg (add smallCfg.precision smallCenter smallInitial)) pair35.1 &&
      ZetaBlockCacheCheck.powerCheck smallCfg 35 (neg smallStep) pair35.2) = true := by
  decide +kernel

private def pair34 : Box × Box :=
  (dataBox (459826462) (460005055) (575238006) (575464523) (by decide) (by decide),
    dataBox (-821231551) (-821156187) (-4215763042) (-4215695991) (by decide) (by decide))

private theorem checked_pair34 :
    (ZetaBlockCacheCheck.powerCheck smallCfg 34
        (neg (add smallCfg.precision smallCenter smallInitial)) pair34.1 &&
      ZetaBlockCacheCheck.powerCheck smallCfg 34 (neg smallStep) pair34.2) = true := by
  decide +kernel

private def pair33 : Box × Box :=
  (dataBox (189483437) (189746263) (723081380) (723346976) (by decide) (by decide),
    dataBox (-758215941) (-758141492) (-4227550261) (-4227483916) (by decide) (by decide))

private theorem checked_pair33 :
    (ZetaBlockCacheCheck.powerCheck smallCfg 33
        (neg (add smallCfg.precision smallCenter smallInitial)) pair33.1 &&
      ZetaBlockCacheCheck.powerCheck smallCfg 33 (neg smallStep) pair33.2) = true := by
  decide +kernel

private def pair32 : Box × Box :=
  (dataBox (-131916112) (-131556450) (747571374) (747896934) (by decide) (by decide),
    dataBox (-693084456) (-693010920) (-4238714401) (-4238648751) (by decide) (by decide))

private theorem checked_pair32 :
    (ZetaBlockCacheCheck.powerCheck smallCfg 32
        (neg (add smallCfg.precision smallCenter smallInitial)) pair32.1 &&
      ZetaBlockCacheCheck.powerCheck smallCfg 32 (neg smallStep) pair32.2) = true := by
  decide +kernel

private def pair31 : Box × Box :=
  (dataBox (-447722057) (-447280110) (628134537) (628519504) (by decide) (by decide),
    dataBox (-625710137) (-625643823) (-4249178496) (-4249119159) (by decide) (by decide))

private theorem checked_pair31 :
    (ZetaBlockCacheCheck.powerCheck smallCfg 31
        (neg (add smallCfg.precision smallCenter smallInitial)) pair31.1 &&
      ZetaBlockCacheCheck.powerCheck smallCfg 31 (neg smallStep) pair31.2) = true := by
  decide +kernel

private def pair30 : Box × Box :=
  (dataBox (-691123350) (-690503423) (370708353) (371261952) (by decide) (by decide),
    dataBox (-555962535) (-555900773) (-4258863009) (-4258807615) (by decide) (by decide))

private theorem checked_pair30 :
    (ZetaBlockCacheCheck.powerCheck smallCfg 30
        (neg (add smallCfg.precision smallCenter smallInitial)) pair30.1 &&
      ZetaBlockCacheCheck.powerCheck smallCfg 30 (neg smallStep) pair30.2) = true := by
  decide +kernel

private def pair29 : Box × Box :=
  (dataBox (-797558694) (-796655555) (13560534) (14882985) (by decide) (by decide),
    dataBox (-483694157) (-483635275) (-4267673057) (-4267620113) (by decide) (by decide))

private theorem checked_pair29 :
    (ZetaBlockCacheCheck.powerCheck smallCfg 29
        (neg (add smallCfg.precision smallCenter smallInitial)) pair29.1 &&
      ZetaBlockCacheCheck.powerCheck smallCfg 29 (neg smallStep) pair29.2) = true := by
  decide +kernel

private def pair28 : Box × Box :=
  (dataBox (-722848378) (-722221832) (-370025213) (-369463918) (by decide) (by decide),
    dataBox (-408743952) (-408686956) (-4275501255) (-4275449865) (by decide) (by decide))

private theorem checked_pair28 :
    (ZetaBlockCacheCheck.powerCheck smallCfg 28
        (neg (add smallCfg.precision smallCenter smallInitial)) pair28.1 &&
      ZetaBlockCacheCheck.powerCheck smallCfg 28 (neg smallStep) pair28.2) = true := by
  decide +kernel

private def pair27 : Box × Box :=
  (dataBox (-459124268) (-458713034) (-687640038) (-687281557) (by decide) (by decide),
    dataBox (-330935526) (-330879856) (-4282225575) (-4282175230) (by decide) (by decide))

private theorem checked_pair27 :
    (ZetaBlockCacheCheck.powerCheck smallCfg 27
        (neg (add smallCfg.precision smallCenter smallInitial)) pair27.1 &&
      ZetaBlockCacheCheck.powerCheck smallCfg 27 (neg smallStep) pair27.2) = true := by
  decide +kernel

private def pair26 : Box × Box :=
  (dataBox (-50868659) (-50572062) (-840921342) (-840646713) (by decide) (by decide),
    dataBox (-250075067) (-250020437) (-4287706774) (-4287657206) (by decide) (by decide))

private theorem checked_pair26 :
    (ZetaBlockCacheCheck.powerCheck smallCfg 26
        (neg (add smallCfg.precision smallCenter smallInitial)) pair26.1 &&
      ZetaBlockCacheCheck.powerCheck smallCfg 26 (neg smallStep) pair26.2) = true := by
  decide +kernel

private def pair25 : Box × Box :=
  (dataBox (403283681) (403483527) (-758499799) (-758275392) (by decide) (by decide),
    dataBox (-165948953) (-165895230) (-4291785299) (-4291736374) (by decide) (by decide))

private theorem checked_pair25 :
    (ZetaBlockCacheCheck.powerCheck smallCfg 25
        (neg (add smallCfg.precision smallCenter smallInitial)) pair25.1 &&
      ZetaBlockCacheCheck.powerCheck smallCfg 25 (neg smallStep) pair25.2) = true := by
  decide +kernel

private def pair24 : Box × Box :=
  (dataBox (764898023) (764998143) (-428431006) (-428234830) (by decide) (by decide),
    dataBox (-78320927) (-78268062) (-4294277496) (-4294229156) (by decide) (by decide))

private theorem checked_pair24 :
    (ZetaBlockCacheCheck.powerCheck smallCfg 24
        (neg (add smallCfg.precision smallCenter smallInitial)) pair24.1 &&
      ZetaBlockCacheCheck.powerCheck smallCfg 24 (neg smallStep) pair24.2) = true := by
  decide +kernel

private def pair23 : Box × Box :=
  (dataBox (892288814) (892311651) (76279171) (76468731) (by decide) (by decide),
    dataBox (13071211) (13123226) (-4294967296) (-4294923202) (by decide) (by decide))

private theorem checked_pair23 :
    (ZetaBlockCacheCheck.powerCheck smallCfg 23
        (neg (add smallCfg.precision smallCenter smallInitial)) pair23.1 &&
      ZetaBlockCacheCheck.powerCheck smallCfg 23 (neg smallStep) pair23.2) = true := by
  decide +kernel

private def pair22 : Box × Box :=
  (dataBox (695719403) (695861317) (595178227) (595392215) (by decide) (by decide),
    dataBox (108519532) (108570687) (-4293618884) (-4293571660) (by decide) (by decide))

private theorem checked_pair22 :
    (ZetaBlockCacheCheck.powerCheck smallCfg 22
        (neg (add smallCfg.precision smallCenter smallInitial)) pair22.1 &&
      ZetaBlockCacheCheck.powerCheck smallCfg 22 (neg smallStep) pair22.2) = true := by
  decide +kernel

private def pair21 : Box × Box :=
  (dataBox (196896843) (197169324) (916158454) (916429564) (by decide) (by decide),
    dataBox (208350666) (208400939) (-4289932684) (-4289886015) (by decide) (by decide))

private theorem checked_pair21 :
    (ZetaBlockCacheCheck.powerCheck smallCfg 21
        (neg (add smallCfg.precision smallCenter smallInitial)) pair21.1 &&
      ZetaBlockCacheCheck.powerCheck smallCfg 21 (neg smallStep) pair21.2) = true := by
  decide +kernel

private def pair20 : Box × Box :=
  (dataBox (-436238757) (-435798808) (855507235) (855892482) (by decide) (by decide),
    dataBox (312931430) (312980795) (-4283573153) (-4283527041) (by decide) (by decide))

private theorem checked_pair20 :
    (ZetaBlockCacheCheck.powerCheck smallCfg 20
        (neg (add smallCfg.precision smallCenter smallInitial)) pair20.1 &&
      ZetaBlockCacheCheck.powerCheck smallCfg 20 (neg smallStep) pair20.2) = true := by
  decide +kernel

private def pair19 : Box × Box :=
  (dataBox (-914924594) (-914080175) (366327975) (367093677) (by decide) (by decide),
    dataBox (422675637) (422724064) (-4274138828) (-4274093277) (by decide) (by decide))

private theorem checked_pair19 :
    (ZetaBlockCacheCheck.powerCheck smallCfg 19
        (neg (add smallCfg.precision smallCenter smallInitial)) pair19.1 &&
      ZetaBlockCacheCheck.powerCheck smallCfg 19 (neg smallStep) pair19.2) = true := by
  decide +kernel

private def pair18 : Box × Box :=
  (dataBox (-942216716) (-941341865) (-371576455) (-370782513) (by decide) (by decide),
    dataBox (538052392) (538099845) (-4261151154) (-4261106171) (by decide) (by decide))

private theorem checked_pair18 :
    (ZetaBlockCacheCheck.powerCheck smallCfg 18
        (neg (add smallCfg.precision smallCenter smallInitial)) pair18.1 &&
      ZetaBlockCacheCheck.powerCheck smallCfg 18 (neg smallStep) pair18.2) = true := by
  decide +kernel

private def pair17 : Box × Box :=
  (dataBox (-401145171) (-400690419) (-961639619) (-961239266) (by decide) (by decide),
    dataBox (659596273) (659642711) (-4244035124) (-4243990717) (by decide) (by decide))

private theorem checked_pair17 :
    (ZetaBlockCacheCheck.powerCheck smallCfg 17
        (neg (add smallCfg.precision smallCenter smallInitial)) pair17.1 &&
      ZetaBlockCacheCheck.powerCheck smallCfg 17 (neg smallStep) pair17.2) = true := by
  decide +kernel

private def pair16 : Box × Box :=
  (dataBox (470459208) (470716645) (-965268244) (-964984588) (by decide) (by decide),
    dataBox (787919927) (787965300) (-4222093691) (-4222049869) (by decide) (by decide))

private theorem checked_pair16 :
    (ZetaBlockCacheCheck.powerCheck smallCfg 16
        (neg (add smallCfg.precision smallCenter smallInitial)) pair16.1 &&
      ZetaBlockCacheCheck.powerCheck smallCfg 16 (neg smallStep) pair16.2) = true := by
  decide +kernel

private def pair15 : Box × Box :=
  (dataBox (1083733352) (1083781176) (-235158437) (-234963063) (by decide) (by decide),
    dataBox (923733512) (923769965) (-4194469675) (-4194434070) (by decide) (by decide))

private theorem checked_pair15 :
    (ZetaBlockCacheCheck.powerCheck smallCfg 15
        (neg (add smallCfg.precision smallCenter smallInitial)) pair15.1 &&
      ZetaBlockCacheCheck.powerCheck smallCfg 15 (neg smallStep) pair15.2) = true := by
  decide +kernel

private def pair14 : Box × Box :=
  (dataBox (838004967) (838149501) (784275699) (784483752) (by decide) (by decide),
    dataBox (1067850531) (1067883572) (-4160112959) (-4160080267) (by decide) (by decide))

private theorem checked_pair14 :
    (ZetaBlockCacheCheck.powerCheck smallCfg 14
        (neg (add smallCfg.precision smallCenter smallInitial)) pair14.1 &&
      ZetaBlockCacheCheck.powerCheck smallCfg 14 (neg smallStep) pair14.2) = true := by
  decide +kernel

private def pair13 : Box × Box :=
  (dataBox (-259003388) (-258653279) (1162592773) (1162907431) (by decide) (by decide),
    dataBox (1221231183) (1221262663) (-4117697179) (-4117665567) (by decide) (by decide))

private theorem checked_pair13 :
    (ZetaBlockCacheCheck.powerCheck smallCfg 13
        (neg (add smallCfg.precision smallCenter smallInitial)) pair13.1 &&
      ZetaBlockCacheCheck.powerCheck smallCfg 13 (neg smallStep) pair13.2) = true := by
  decide +kernel

private def pair12 : Box × Box :=
  (dataBox (-1207386896) (-1206265900) (283340620) (284387159) (by decide) (by decide),
    dataBox (1385005026) (1385035385) (-4065536757) (-4065505738) (by decide) (by decide))

private theorem checked_pair12 :
    (ZetaBlockCacheCheck.powerCheck smallCfg 12
        (neg (add smallCfg.precision smallCenter smallInitial)) pair12.1 &&
      ZetaBlockCacheCheck.powerCheck smallCfg 12 (neg smallStep) pair12.2) = true := by
  decide +kernel

private def pair11 : Box × Box :=
  (dataBox (-714038539) (-713557984) (-1080699733) (-1080280490) (by decide) (by decide),
    dataBox (1560512551) (1560541803) (-4001452362) (-4001421859) (by decide) (by decide))

private theorem checked_pair11 :
    (ZetaBlockCacheCheck.powerCheck smallCfg 11
        (neg (add smallCfg.precision smallCenter smallInitial)) pair11.1 &&
      ZetaBlockCacheCheck.powerCheck smallCfg 11 (neg smallStep) pair11.2) = true := by
  decide +kernel

private def pair10 : Box × Box :=
  (dataBox (926235471) (926417017) (-993397320) (-993152134) (by decide) (by decide),
    dataBox (1749358175) (1749386236) (-3922570397) (-3922540419) (by decide) (by decide))

private theorem checked_pair10 :
    (ZetaBlockCacheCheck.powerCheck smallCfg 10
        (neg (add smallCfg.precision smallCenter smallInitial)) pair10.1 &&
      ZetaBlockCacheCheck.powerCheck smallCfg 10 (neg smallStep) pair10.2) = true := by
  decide +kernel

private def pair9 : Box × Box :=
  (dataBox (1135480271) (1135634932) (871740692) (871988430) (by decide) (by decide),
    dataBox (1953477619) (1953504369) (-3825013669) (-3824984237) (by decide) (by decide))

private theorem checked_pair9 :
    (ZetaBlockCacheCheck.powerCheck smallCfg 9
        (neg (add smallCfg.precision smallCenter smallInitial)) pair9.1 &&
      ZetaBlockCacheCheck.powerCheck smallCfg 9 (neg smallStep) pair9.2) = true := by
  decide +kernel

private def pair8 : Box × Box :=
  (dataBox (-1016290678) (-1015663370) (1128266169) (1128813998) (by decide) (by decide),
    dataBox (2175221575) (2175246869) (-3703404788) (-3703375928) (by decide) (by decide))

private theorem checked_pair8 :
    (ZetaBlockCacheCheck.powerCheck smallCfg 8
        (neg (add smallCfg.precision smallCenter smallInitial)) pair8.1 &&
      ZetaBlockCacheCheck.powerCheck smallCfg 8 (neg smallStep) pair8.2) = true := by
  decide +kernel

private def pair7 : Box × Box :=
  (dataBox (-833710211) (-833304643) (-1393196433) (-1392841883) (by decide) (by decide),
    dataBox (2417455248) (2417471549) (-3550025905) (-3550006429) (by decide) (by decide))

private theorem checked_pair7 :
    (ZetaBlockCacheCheck.powerCheck smallCfg 7
        (neg (add smallCfg.precision smallCenter smallInitial)) pair7.1 &&
      ZetaBlockCacheCheck.powerCheck smallCfg 7 (neg smallStep) pair7.2) = true := by
  decide +kernel

private def pair6 : Box × Box :=
  (dataBox (1751376547) (1751392038) (84234439) (84419698) (by decide) (by decide),
    dataBox (2683626954) (2683641470) (-3353343597) (-3353325171) (by decide) (by decide))

private theorem checked_pair6 :
    (ZetaBlockCacheCheck.powerCheck smallCfg 6
        (neg (add smallCfg.precision smallCenter smallInitial)) pair6.1 &&
      ZetaBlockCacheCheck.powerCheck smallCfg 6 (neg smallStep) pair6.2) = true := by
  decide +kernel

private def pair5 : Box × Box :=
  (dataBox (-1646854535) (-1646100889) (988734983) (989413659) (by decide) (by decide),
    dataBox (2977753884) (2977766908) (-3095115945) (-3095097977) (by decide) (by decide))

private theorem checked_pair5 :
    (ZetaBlockCacheCheck.powerCheck smallCfg 5
        (neg (add smallCfg.precision smallCenter smallInitial)) pair5.1 &&
      ZetaBlockCacheCheck.powerCheck smallCfg 5 (neg smallStep) pair5.2) = true := by
  decide +kernel

private def pair4 : Box × Box :=
  (dataBox (1821038344) (1821171636) (-1138217752) (-1137975217) (by decide) (by decide),
    dataBox (3303850611) (3303861823) (-2744326178) (-2744308687) (by decide) (by decide))

private theorem checked_pair4 :
    (ZetaBlockCacheCheck.powerCheck smallCfg 4
        (neg (add smallCfg.precision smallCenter smallInitial)) pair4.1 &&
      ZetaBlockCacheCheck.powerCheck smallCfg 4 (neg smallStep) pair4.2) = true := by
  decide +kernel

private def pair3 : Box × Box :=
  (dataBox (-2348430357) (-2347439791) (-797614599) (-796673755) (by decide) (by decide),
    dataBox (3663119610) (3663124057) (-2242387474) (-2242378968) (by decide) (by decide))

private theorem checked_pair3 :
    (ZetaBlockCacheCheck.powerCheck smallCfg 3
        (neg (add smallCfg.precision smallCenter smallInitial)) pair3.1 &&
      ZetaBlockCacheCheck.powerCheck smallCfg 3 (neg smallStep) pair3.2) = true := by
  decide +kernel

private def pair2 : Box × Box :=
  (dataBox (-2919942441) (-2918547957) (836120721) (837454348) (by decide) (by decide),
    dataBox (4039596257) (4039599059) (-1458906051) (-1458897804) (by decide) (by decide))

private theorem checked_pair2 :
    (ZetaBlockCacheCheck.powerCheck smallCfg 2
        (neg (add smallCfg.precision smallCenter smallInitial)) pair2.1 &&
      ZetaBlockCacheCheck.powerCheck smallCfg 2 (neg smallStep) pair2.2) = true := by
  decide +kernel

private def pair1 : Box × Box :=
  (dataBox (4294967296) (4294967296) (0) (0) (by decide) (by decide),
    dataBox (4294967296) (4294967296) (0) (0) (by decide) (by decide))

private theorem checked_pair1 :
    (ZetaBlockCacheCheck.powerCheck smallCfg 1
        (neg (add smallCfg.precision smallCenter smallInitial)) pair1.1 &&
      ZetaBlockCacheCheck.powerCheck smallCfg 1 (neg smallStep) pair1.2) = true := by
  decide +kernel

private def prefixData : List (Box × Box) :=
  [pair40, pair39, pair38, pair37, pair36, pair35, pair34, pair33, pair32, pair31, pair30, pair29, pair28, pair27, pair26, pair25, pair24, pair23, pair22, pair21, pair20, pair19, pair18, pair17, pair16, pair15, pair14, pair13, pair12, pair11, pair10, pair9, pair8, pair7, pair6, pair5, pair4, pair3, pair2, pair1]

private def smallBatch : ZetaBlockBatchCertificate.Batch := ⟨prefixData, []⟩

private theorem checked_prefix :
    ZetaBlockCacheCheck.prefixCheck smallCfg (add smallCfg.precision smallCenter smallInitial) smallStep
      40 prefixData = true := by
  exact ZetaBlockCacheCheck.prefixCheck_cons checked_pair40 <|
    ZetaBlockCacheCheck.prefixCheck_cons checked_pair39 <|
    ZetaBlockCacheCheck.prefixCheck_cons checked_pair38 <|
    ZetaBlockCacheCheck.prefixCheck_cons checked_pair37 <|
    ZetaBlockCacheCheck.prefixCheck_cons checked_pair36 <|
    ZetaBlockCacheCheck.prefixCheck_cons checked_pair35 <|
    ZetaBlockCacheCheck.prefixCheck_cons checked_pair34 <|
    ZetaBlockCacheCheck.prefixCheck_cons checked_pair33 <|
    ZetaBlockCacheCheck.prefixCheck_cons checked_pair32 <|
    ZetaBlockCacheCheck.prefixCheck_cons checked_pair31 <|
    ZetaBlockCacheCheck.prefixCheck_cons checked_pair30 <|
    ZetaBlockCacheCheck.prefixCheck_cons checked_pair29 <|
    ZetaBlockCacheCheck.prefixCheck_cons checked_pair28 <|
    ZetaBlockCacheCheck.prefixCheck_cons checked_pair27 <|
    ZetaBlockCacheCheck.prefixCheck_cons checked_pair26 <|
    ZetaBlockCacheCheck.prefixCheck_cons checked_pair25 <|
    ZetaBlockCacheCheck.prefixCheck_cons checked_pair24 <|
    ZetaBlockCacheCheck.prefixCheck_cons checked_pair23 <|
    ZetaBlockCacheCheck.prefixCheck_cons checked_pair22 <|
    ZetaBlockCacheCheck.prefixCheck_cons checked_pair21 <|
    ZetaBlockCacheCheck.prefixCheck_cons checked_pair20 <|
    ZetaBlockCacheCheck.prefixCheck_cons checked_pair19 <|
    ZetaBlockCacheCheck.prefixCheck_cons checked_pair18 <|
    ZetaBlockCacheCheck.prefixCheck_cons checked_pair17 <|
    ZetaBlockCacheCheck.prefixCheck_cons checked_pair16 <|
    ZetaBlockCacheCheck.prefixCheck_cons checked_pair15 <|
    ZetaBlockCacheCheck.prefixCheck_cons checked_pair14 <|
    ZetaBlockCacheCheck.prefixCheck_cons checked_pair13 <|
    ZetaBlockCacheCheck.prefixCheck_cons checked_pair12 <|
    ZetaBlockCacheCheck.prefixCheck_cons checked_pair11 <|
    ZetaBlockCacheCheck.prefixCheck_cons checked_pair10 <|
    ZetaBlockCacheCheck.prefixCheck_cons checked_pair9 <|
    ZetaBlockCacheCheck.prefixCheck_cons checked_pair8 <|
    ZetaBlockCacheCheck.prefixCheck_cons checked_pair7 <|
    ZetaBlockCacheCheck.prefixCheck_cons checked_pair6 <|
    ZetaBlockCacheCheck.prefixCheck_cons checked_pair5 <|
    ZetaBlockCacheCheck.prefixCheck_cons checked_pair4 <|
    ZetaBlockCacheCheck.prefixCheck_cons checked_pair3 <|
    ZetaBlockCacheCheck.prefixCheck_cons checked_pair2 <|
    ZetaBlockCacheCheck.prefixCheck_cons checked_pair1 <| rfl

private theorem checked_zeta :
    ZetaBlockBatchCertificate.check smallCfg 40 [] smallBatch smallCenter smallPoint smallShift 8 = true := by
  decide +kernel

/-- End-to-end cached evaluation, including a phase reset and the analytic
tail, certifies actual zeta at a small sample height. -/
theorem cached_zeta_nonzero : riemannZeta (1 / 2 + 18 * Complex.I) ≠ 0 := by
  let s : ℂ := 1 / 2 + 20 * Complex.I
  let d : ℂ := -6 * Complex.I
  let q : ℂ := (1 / 2) * Complex.I
  have hp : smallCfg.precision ≤ 0 := by decide
  have hs : Mem s smallCenter := by simpa [s, smallCenter] using mem_rational hp (1 / 2) 20
  have hd : Mem d smallInitial := by simpa [d, smallInitial] using mem_rational hp 0 (-6)
  have hq : Mem q smallStep := by simpa [q, smallStep] using mem_rational hp 0 (1 / 2)
  have ht : Mem (s + (d + 8 * q)) smallPoint := by
    convert! mem_rational hp (1 / 2) 18 using 1
    norm_num [s, d, q, smallPoint]
    ring
  have hD : Mem (d + 8 * q) smallShift := by
    convert! mem_rational hp 0 (-2) using 1
    norm_num [d, q, smallShift]
    ring
  have hB : ZetaBlockBatchCertificate.Sound smallCfg.precision s d q 40 [] smallBatch :=
    ⟨ZetaBlockCacheCheck.sound_prefix_of_check hp (mem_add hs hd smallCfg.precision) hq
      40 checked_prefix, trivial⟩
  have hn := ZetaBlockBatchCertificate.nonzero_of_check hB 8 checked_zeta hs ht hD
  have heq : s + (d + 8 * q) = 1 / 2 + 18 * Complex.I := by
    dsimp [s, d, q]
    ring
  simpa only [Nat.cast_ofNat, heq] using hn

end RiemannGaussian.ZetaBlockBatchValidation
