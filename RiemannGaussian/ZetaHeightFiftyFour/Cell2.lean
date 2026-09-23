/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaHorizontalCertificate

/-!
# Checked height-fifty-four contour cell 2

Every literal prefix checkpoint is checked in the kernel. This independent
module bounds compiler memory while retaining the complete original
Euler--Maclaurin expression, rounding errors and analytic tail.
-/

namespace RiemannGaussian.ZetaHeightFiftyFour.Cell2
open LeanCert.Core LeanCert.Engine CertifiedComplexInterval ZetaHorizontalCertificate
open ZetaEulerMaclaurinEnclosure

private def cfg : DyadicConfig := {precision := -40, taylorDepth := 20}

@[instance_reducible] private def intervalEq : DecidableEq IntervalDyadic := fun A B =>
  decidable_of_iff (A.lo = B.lo ∧ A.hi = B.hi) (by
    constructor
    · intro h
      cases A
      cases B
      cases h.1
      cases h.2
      rfl
    · intro h
      cases h
      exact ⟨rfl, rfl⟩)
attribute [local instance] intervalEq

@[instance_reducible] private def boxEq : DecidableEq Box := fun A B =>
  decidable_of_iff (A.re = B.re ∧ A.im = B.im) (by
    constructor
    · intro h
      cases A
      cases B
      cases h.1
      cases h.2
      rfl
    · intro h
      cases h
      exact ⟨rfl, rfl⟩)

attribute [local instance] boxEq

private def dataInterval (a b : ℤ) (hab : a ≤ b) : IntervalDyadic :=
  ⟨⟨a, -40⟩, ⟨b, -40⟩, by
    change (a : ℚ) / 1099511627776 ≤ (b : ℚ) / 1099511627776
    exact div_le_div_of_nonneg_right (by exact_mod_cast hab) (by norm_num)⟩
private def dataBox (a b c d : ℤ) (hab : a ≤ b) (hcd : c ≤ d) : Box :=
  ⟨dataInterval a b hab, dataInterval c d hcd⟩


private def cell2 : Box := input cfg (3 / 4) (1) 54 (by norm_num)

private def prefix2_1 : Box :=
  dataBox (1099511627776) (1099511627776) (0) (0) (by decide) (by decide)

private theorem checked_prefix2_1 : prefixBox cfg cell2 1 = .ok prefix2_1 := by
  decide +kernel

private def prefix2_2 : Box :=
  dataBox (1629472668713) (1729745074113) (146194202567) (173855206496) (by decide) (by decide)

private theorem checked_prefix2_2 : prefixBox cfg cell2 2 = .ok prefix2_2 := by
  rw [prefixBox, checked_prefix2_1]
  decide +kernel

private def prefix2_3 : Box :=
  dataBox (1178935470502) (1387410870270) (-26067647254) (42964538608) (by decide) (by decide)

private theorem checked_prefix2_3 : prefixBox cfg cell2 3 = .ok prefix2_3 := by
  rw [prefixBox, checked_prefix2_2]
  decide +kernel

private def prefix2_4 : Box :=
  dataBox (1414936571671) (1721166841601) (114862616352) (242270054250) (by decide) (by decide)

private theorem checked_prefix2_4 : prefixBox cfg cell2 4 = .ok prefix2_4 := by
  rw [prefixBox, checked_prefix2_3]
  decide +kernel

private def prefix2_5 : Box :=
  dataBox (1523408621900) (1883370411468) (306149945680) (528311353714) (by decide) (by decide)

private theorem checked_prefix2_5 : prefixBox cfg cell2 5 = .ok prefix2_5 := by
  rw [prefixBox, checked_prefix2_4]
  decide +kernel

private def prefix2_6 : Box :=
  dataBox (1292401507967) (1735770040774) (136171372432) (419704744195) (by decide) (by decide)

private theorem checked_prefix2_6 : prefixBox cfg cell2 6 = .ok prefix2_6 := by
  rw [prefixBox, checked_prefix2_5]
  decide +kernel

private def prefix2_7 : Box :=
  dataBox (1250636591434) (1710093482352) (291131583353) (671759416781) (by decide) (by decide)

private theorem checked_prefix2_7 : prefixBox cfg cell2 7 = .ok prefix2_7 := by
  rw [prefixBox, checked_prefix2_6]
  decide +kernel

private def prefix2_8 : Box :=
  dataBox (1345649862651) (1869886138316) (390438893244) (838773762744) (by decide) (by decide)

private theorem checked_prefix2_8 : prefixBox cfg cell2 8 = .ok prefix2_8 := by
  rw [prefixBox, checked_prefix2_7]
  decide +kernel

private def prefix2_9 : Box :=
  dataBox (1436654215259) (2027510315365) (471944820230) (979946191089) (by decide) (by decide)

private theorem checked_prefix2_9 : prefixBox cfg cell2 9 = .ok prefix2_9 := by
  rw [prefixBox, checked_prefix2_8]
  decide +kernel

private def prefix2_10 : Box :=
  dataBox (1463503277205) (2075255473755) (578567445616) (1169551034723) (by decide) (by decide)

private theorem checked_prefix2_10 : prefixBox cfg cell2 10 = .ok prefix2_10 := by
  rw [prefixBox, checked_prefix2_9]
  decide +kernel

private def prefix2_11 : Box :=
  dataBox (1322077466546) (1997598517613) (641500078502) (1284161486646) (by decide) (by decide)

private theorem checked_prefix2_11 : prefixBox cfg cell2 11 = .ok prefix2_11 := by
  rw [prefixBox, checked_prefix2_10]
  decide +kernel

private def prefix2_12 : Box :=
  dataBox (1216542648356) (1940896266910) (507542451234) (1212188085197) (by decide) (by decide)

private theorem checked_prefix2_12 : prefixBox cfg cell2 12 = .ok prefix2_12 := by
  rw [prefixBox, checked_prefix2_11]
  decide +kernel

private def prefix2_13 : Box :=
  dataBox (1297892011098) (2095364794058) (463594163729) (1189043150026) (by decide) (by decide)

private theorem checked_prefix2_13 : prefixBox cfg cell2 13 = .ok prefix2_13 := by
  rw [prefixBox, checked_prefix2_12]
  decide +kernel

private def prefix2_14 : Box :=
  dataBox (1234097627148) (2062384825601) (534870450727) (1326915493877) (by decide) (by decide)

private theorem checked_prefix2_14 : prefixBox cfg cell2 14 = .ok prefix2_14 := by
  rw [prefixBox, checked_prefix2_13]
  decide +kernel

private def prefix2_15 : Box :=
  dataBox (1212447331679) (2051383614070) (392249196880) (1254444975552) (by decide) (by decide)

private theorem checked_prefix2_15 : prefixBox cfg cell2 15 = .ok prefix2_15 := by
  rw [prefixBox, checked_prefix2_14]
  decide +kernel

private def prefix2_16 : Box :=
  dataBox (1245039233603) (2116567436465) (452748233898) (1375443070362) (by decide) (by decide)

private theorem checked_prefix2_16 : prefixBox cfg cell2 16 = .ok prefix2_16 := by
  rw [prefixBox, checked_prefix2_15]
  decide +kernel

private def prefix2_17 : Box :=
  dataBox (1168062603344) (2078658076748) (346342832140) (1323040654390) (by decide) (by decide)

private theorem checked_prefix2_17 : prefixBox cfg cell2 17 = .ok prefix2_17 := by
  rw [prefixBox, checked_prefix2_16]
  decide +kernel

private def prefix2_18 : Box :=
  dataBox (1201089142716) (2146685073192) (397728623081) (1428883436772) (by decide) (by decide)

private theorem checked_prefix2_18 : prefixBox cfg cell2 18 = .ok prefix2_18 := by
  rw [prefixBox, checked_prefix2_17]
  decide +kernel

private def prefix2_19 : Box :=
  dataBox (1159742811434) (2126881285337) (284204727819) (1374508497665) (by decide) (by decide)

private theorem checked_prefix2_19 : prefixBox cfg cell2 19 = .ok prefix2_19 := by
  rw [prefixBox, checked_prefix2_18]
  decide +kernel

private def prefix2_20 : Box :=
  dataBox (1157129642044) (2125645604883) (339166415091) (1490738336661) (by decide) (by decide)

private theorem checked_prefix2_20 : prefixBox cfg cell2 20 = .ok prefix2_20 := by
  rw [prefixBox, checked_prefix2_19]
  decide +kernel

private def prefix2_21 : Box :=
  dataBox (1183571211433) (2182248958680) (242427551999) (1445547947611) (by decide) (by decide)

private theorem checked_prefix2_21 : prefixBox cfg cell2 21 = .ok prefix2_21 := by
  rw [prefixBox, checked_prefix2_20]
  decide +kernel

private def prefix2_22 : Box :=
  dataBox (1084384535407) (2136450856705) (262435381131) (1488879676477) (by decide) (by decide)

private theorem checked_prefix2_22 : prefixBox cfg cell2 22 = .ok prefix2_22 := by
  rw [prefixBox, checked_prefix2_21]
  decide +kernel

private def prefix2_23 : Box :=
  dataBox (1129620540681) (2235514939905) (277895253280) (1522735862127) (by decide) (by decide)

private theorem checked_prefix2_23 : prefixBox cfg cell2 23 = .ok prefix2_23 := by
  rw [prefixBox, checked_prefix2_22]
  decide +kernel

private def prefix2_24 : Box :=
  dataBox (1090310044743) (2217754430148) (184424343706) (1480505621759) (by decide) (by decide)

private theorem checked_prefix2_24 : prefixBox cfg cell2 24 = .ok prefix2_24 := by
  rw [prefixBox, checked_prefix2_23]
  decide +kernel

private def prefix2_25 : Box :=
  dataBox (1039824322748) (2195176541080) (222167151787) (1564901129941) (by decide) (by decide)

private theorem checked_prefix2_25 : prefixBox cfg cell2 25 = .ok prefix2_25 := by
  rw [prefixBox, checked_prefix2_24]
  decide +kernel

private def prefix2_26 : Box :=
  dataBox (1082111869917) (2290666088185) (221400878328) (1564561790974) (by decide) (by decide)

private theorem checked_prefix2_26 : prefixBox cfg cell2 26 = .ok prefix2_26 := by
  rw [prefixBox, checked_prefix2_25]
  decide +kernel

private def prefix2_27 : Box :=
  dataBox (1039641247790) (2272034605035) (138858721227) (1528351271131) (by decide) (by decide)

private theorem checked_prefix2_27 : prefixBox cfg cell2 27 = .ok prefix2_27 := by
  rw [prefixBox, checked_prefix2_26]
  decide +kernel

private def prefix2_28 : Box :=
  dataBox (981274260539) (2246661269433) (168828546776) (1597291682947) (by decide) (by decide)

private theorem checked_prefix2_28 : prefixBox cfg cell2 28 = .ok prefix2_28 := by
  rw [prefixBox, checked_prefix2_27]
  decide +kernel

private def prefix2_29 : Box :=
  dataBox (1016506299503) (2328420594968) (182835309673) (1629795729284) (by decide) (by decide)

private theorem checked_prefix2_29 : prefixBox cfg cell2 29 = .ok prefix2_29 := by
  rw [prefixBox, checked_prefix2_28]
  decide +kernel

private def prefix2_30 : Box :=
  dataBox (1020839632853) (2338562116267) (97662313546) (1593402421361) (by decide) (by decide)

private theorem checked_prefix2_30 : prefixBox cfg cell2 30 = .ok prefix2_30 := by
  rw [prefixBox, checked_prefix2_29]
  decide +kernel

private def prefix2_31 : Box :=
  dataBox (937425371847) (2303211282982) (100544189153) (1600202566611) (by decide) (by decide)

private theorem checked_prefix2_31 : prefixBox cfg cell2 31 = .ok prefix2_31 := by
  rw [prefixBox, checked_prefix2_30]
  decide +kernel

private def prefix2_32 : Box :=
  dataBox (945090435907) (2321441997663) (134038041091) (1679864837729) (by decide) (by decide)

private theorem checked_prefix2_32 : prefixBox cfg cell2 32 = .ok prefix2_32 := by
  rw [prefixBox, checked_prefix2_31]
  decide +kernel

private def prefix2_33 : Box :=
  dataBox (976760800315) (2397348952464) (109232480564) (1669515314616) (by decide) (by decide)

private theorem checked_prefix2_33 : prefixBox cfg cell2 33 = .ok prefix2_33 := by
  rw [prefixBox, checked_prefix2_32]
  decide +kernel

private def prefix2_34 : Box :=
  dataBox (949463118163) (2386044340570) (36069972939) (1639216982161) (by decide) (by decide)

private theorem checked_prefix2_34 : prefixBox cfg cell2 34 = .ok prefix2_34 := by
  rw [prefixBox, checked_prefix2_33]
  decide +kernel

private def prefix2_35 : Box :=
  dataBox (877729018682) (2356552056765) (46890453120) (1665535662788) (by decide) (by decide)

private theorem checked_prefix2_35 : prefixBox cfg cell2 35 = .ok prefix2_35 := by
  rw [prefixBox, checked_prefix2_34]
  decide +kernel

private def prefix2_36 : Box :=
  dataBox (886815300145) (2378808824877) (76049540656) (1736960563758) (by decide) (by decide)

private theorem checked_prefix2_36 : prefixBox cfg cell2 36 = .ok prefix2_36 := by
  rw [prefixBox, checked_prefix2_35]
  decide +kernel

private def prefix2_37 : Box :=
  dataBox (915873878531) (2450476746554) (60712404262) (1730741950854) (by decide) (by decide)

private theorem checked_prefix2_37 : prefixBox cfg cell2 37 = .ok prefix2_37 := by
  rw [prefixBox, checked_prefix2_36]
  decide +kernel

private def prefix2_38 : Box :=
  dataBox (910124848992) (2448161233560) (-10896505092) (1701900237497) (by decide) (by decide)

private theorem checked_prefix2_38 : prefixBox cfg cell2 38 = .ok prefix2_38 := by
  rw [prefixBox, checked_prefix2_37]
  decide +kernel

private def prefix2_39 : Box :=
  dataBox (839944193590) (2420077747955) (-17088997596) (1699422263850) (by decide) (by decide)

private theorem checked_prefix2_39 : prefixBox cfg cell2 39 = .ok prefix2_39 := by
  rw [prefixBox, checked_prefix2_38]
  decide +kernel

private def prefix2_40 : Box :=
  dataBox (820068032416) (2412174291584) (9238056141) (1765631317042) (by decide) (by decide)

private theorem checked_prefix2_40 : prefixBox cfg cell2 40 = .ok prefix2_40 := by
  rw [prefixBox, checked_prefix2_39]
  decide +kernel

private def prefix2_41 : Box :=
  dataBox (843219264393) (2470757089964) (22772862031) (1799880336056) (by decide) (by decide)

private theorem checked_prefix2_41 : prefixBox cfg cell2 41 = .ok prefix2_41 := by
  rw [prefixBox, checked_prefix2_40]
  decide +kernel

private def prefix2_42 : Box :=
  dataBox (861972659170) (2518498175785) (-23727130010) (1781614462433) (by decide) (by decide)

private theorem checked_prefix2_42 : prefixBox cfg cell2 42 = .ok prefix2_42 := by
  rw [prefixBox, checked_prefix2_41]
  decide +kernel

private def prefix2_43 : Box :=
  dataBox (832196981586) (2506870464996) (-82043851979) (1758841168650) (by decide) (by decide)

private theorem checked_prefix2_43 : prefixBox cfg cell2 43 = .ok prefix2_43 := by
  rw [prefixBox, checked_prefix2_42]
  decide +kernel

private def prefix2_44 : Box :=
  dataBox (768492143507) (2482135631263) (-78489593382) (1767995229029) (by decide) (by decide)

private theorem checked_prefix2_44 : prefixBox cfg cell2 44 = .ok prefix2_44 := by
  rw [prefixBox, checked_prefix2_43]
  decide +kernel

private def prefix2_45 : Box :=
  dataBox (755018935734) (2476933667804) (-54616181469) (1829827860955) (by decide) (by decide)

private theorem checked_prefix2_45 : prefixBox cfg cell2 45 = .ok prefix2_45 := by
  rw [prefixBox, checked_prefix2_44]
  decide +kernel

private def prefix2_46 : Box :=
  dataBox (774766953891) (2528363253487) (-41149864889) (1864898074139) (by decide) (by decide)

private theorem checked_prefix2_46 : prefixBox cfg cell2 46 = .ok prefix2_46 := by
  rw [prefixBox, checked_prefix2_45]
  decide +kernel

private def prefix2_47 : Box :=
  dataBox (794551961254) (2580166947160) (-73834599208) (1852415034183) (by decide) (by decide)

private theorem checked_prefix2_47 : prefixBox cfg cell2 47 = .ok prefix2_47 := by
  rw [prefixBox, checked_prefix2_46]
  decide +kernel

private def prefix2_48 : Box :=
  dataBox (786799074938) (2577221493496) (-133627351031) (1829698706474) (by decide) (by decide)

private theorem checked_prefix2_48 : prefixBox cfg cell2 48 = .ok prefix2_48 := by
  rw [prefixBox, checked_prefix2_47]
  decide +kernel

private def prefix2_49 : Box :=
  dataBox (730603888166) (2555981720905) (-152775935687) (1822461232049) (by decide) (by decide)

private theorem checked_prefix2_49 : prefixBox cfg cell2 49 = .ok prefix2_49 := by
  rw [prefixBox, checked_prefix2_48]
  decide +kernel

private def prefix2_50 : Box :=
  dataBox (688321124436) (2540080860570) (-137586047266) (1862853413163) (by decide) (by decide)

private theorem checked_prefix2_50 : prefixBox cfg cell2 50 = .ok prefix2_50 := by
  rw [prefixBox, checked_prefix2_49]
  decide +kernel

private def prefix2_51 : Box :=
  dataBox (693886034037) (2554952231403) (-116757596372) (1918514234073) (by decide) (by decide)

private theorem checked_prefix2_51 : prefixBox cfg cell2 51 = .ok prefix2_51 := by
  rw [prefixBox, checked_prefix2_50]
  decide +kernel

private def prefix2_52 : Box :=
  dataBox (714313614213) (2609807428386) (-111298486337) (1933173862038) (by decide) (by decide)

private theorem checked_prefix2_52 : prefixBox cfg cell2 52 = .ok prefix2_52 := by
  rw [prefixBox, checked_prefix2_51]
  decide +kernel

private def prefix2_53 : Box :=
  dataBox (729243622702) (2650091104454) (-150162476338) (1918770021311) (by decide) (by decide)

private theorem checked_prefix2_53 : prefixBox cfg cell2 53 = .ok prefix2_53 := by
  rw [prefixBox, checked_prefix2_52]
  decide +kernel

private def prefix2_54 : Box :=
  dataBox (717951312674) (2645925445118) (-204190613433) (1898839372304) (by decide) (by decide)

private theorem checked_prefix2_54 : prefixBox cfg cell2 54 = .ok prefix2_54 := by
  rw [prefixBox, checked_prefix2_53]
  decide +kernel

private def prefix2_55 : Box :=
  dataBox (667271451584) (2627315524998) (-224075266901) (1891537624565) (by decide) (by decide)

private theorem checked_prefix2_55 : prefixBox cfg cell2 55 = .ok prefix2_55 := by
  rw [prefixBox, checked_prefix2_54]
  decide +kernel

private def prefix2_56 : Box :=
  dataBox (622914959780) (2611100786458) (-213003621437) (1921824848983) (by decide) (by decide)

private theorem checked_prefix2_56 : prefixBox cfg cell2 56 = .ok prefix2_56 := by
  rw [prefixBox, checked_prefix2_55]
  decide +kernel

private def prefix2_57 : Box :=
  dataBox (622071143045) (2610793691591) (-193716390696) (1974820312017) (by decide) (by decide)

private theorem checked_prefix2_57 : prefixBox cfg cell2 57 = .ok prefix2_57 := by
  rw [prefixBox, checked_prefix2_56]
  decide +kernel

private def prefix2_58 : Box :=
  dataBox (637190491596) (2652518094813) (-182280623960) (2006379252055) (by decide) (by decide)

private theorem checked_prefix2_58 : prefixBox cfg cell2 58 = .ok prefix2_58 := by
  rw [prefixBox, checked_prefix2_57]
  decide +kernel

private def prefix2_59 : Box :=
  dataBox (655123329230) (2702218741537) (-196332372676) (2001309145156) (by decide) (by decide)

private theorem checked_prefix2_59 : prefixBox cfg cell2 59 = .ok prefix2_59 := by
  rw [prefixBox, checked_prefix2_58]
  decide +kernel

private def prefix2_60 : Box :=
  dataBox (662050940559) (2721499385958) (-243549441903) (1984343861723) (by decide) (by decide)

private theorem checked_prefix2_60 : prefixBox cfg cell2 60 = .ok prefix2_60 := by
  rw [prefixBox, checked_prefix2_59]
  decide +kernel

private def prefix2_61 : Box :=
  dataBox (637683957764) (2712780339765) (-287637360325) (1968568221899) (by decide) (by decide)

private theorem checked_prefix2_61 : prefixBox cfg cell2 61 = .ok prefix2_61 := by
  rw [prefixBox, checked_prefix2_60]
  decide +kernel

private def prefix2_62 : Box :=
  dataBox (588796164828) (2695358169950) (-296929074030) (1965256936324) (by decide) (by decide)

private theorem checked_prefix2_62 : prefixBox cfg cell2 62 = .ok prefix2_62 := by
  rw [prefixBox, checked_prefix2_61]
  decide +kernel

private def prefix2_63 : Box :=
  dataBox (550446105067) (2681745897216) (-286006717069) (1996028657711) (by decide) (by decide)

private theorem checked_prefix2_63 : prefixBox cfg cell2 63 = .ok prefix2_63 := by
  rw [prefixBox, checked_prefix2_62]
  decide +kernel

private def prefix2_64 : Box :=
  dataBox (548299601331) (2680986998803) (-268843620280) (2044573239873) (by decide) (by decide)

private theorem checked_prefix2_64 : prefixBox cfg cell2 64 = .ok prefix2_64 := by
  rw [prefixBox, checked_prefix2_63]
  decide +kernel

private def prefix2_65 : Box :=
  dataBox (560351738810) (2715207983792) (-256974239540) (2078275306178) (by decide) (by decide)

private theorem checked_prefix2_65 : prefixBox cfg cell2 65 = .ok prefix2_65 := by
  rw [prefixBox, checked_prefix2_64]
  decide +kernel

private def prefix2_66 : Box :=
  dataBox (576992854741) (2762639655905) (-259190202044) (2077497852198) (by decide) (by decide)

private theorem checked_prefix2_66 : prefixBox cfg cell2 66 = .ok prefix2_66 := by
  rw [prefixBox, checked_prefix2_65]
  decide +kernel

private def prefix2_67 : Box :=
  dataBox (587715538770) (2793317322054) (-294732661097) (2065074790290) (by decide) (by decide)

private theorem checked_prefix2_67 : prefixBox cfg cell2 67 = .ok prefix2_67 := by
  rw [prefixBox, checked_prefix2_66]
  decide +kernel

private def prefix2_68 : Box :=
  dataBox (583637153210) (2791897089400) (-340985288363) (2048967998169) (by decide) (by decide)

private theorem checked_prefix2_68 : prefixBox cfg cell2 68 = .ok prefix2_68 := by
  rw [prefixBox, checked_prefix2_67]
  decide +kernel

private def prefix2_69 : Box :=
  dataBox (548348816578) (2779653221629) (-370378736468) (2038769459055) (by decide) (by decide)

private theorem checked_prefix2_69 : prefixBox cfg cell2 69 = .ok prefix2_69 := by
  rw [prefixBox, checked_prefix2_68]
  decide +kernel

private def prefix2_70 : Box :=
  dataBox (503069740642) (2763999315171) (-369084681218) (2042512553110) (by decide) (by decide)

private theorem checked_prefix2_70 : prefixBox cfg cell2 70 = .ok prefix2_70 := by
  rw [prefixBox, checked_prefix2_69]
  decide +kernel

private def prefix2_71 : Box :=
  dataBox (473349363498) (2753760742292) (-357466155872) (2076238630199) (by decide) (by decide)

private theorem checked_prefix2_71 : prefixBox cfg cell2 71 = .ok prefix2_71 := by
  rw [prefixBox, checked_prefix2_70]
  decide +kernel

private def prefix2_72 : Box :=
  dataBox (473851844877) (2755224458664) (-342203432328) (2120698202442) (by decide) (by decide)

private theorem checked_prefix2_72 : prefixBox cfg cell2 72 = .ok prefix2_72 := by
  rw [prefixBox, checked_prefix2_71]
  decide +kernel

private def prefix2_73 : Box :=
  dataBox (484420378554) (2786116424321) (-331471985474) (2152066367972) (by decide) (by decide)

private theorem checked_prefix2_73 : prefixBox cfg cell2 73 = .ok prefix2_73 := by
  rw [prefixBox, checked_prefix2_72]
  decide +kernel

private def prefix2_74 : Box :=
  dataBox (499253364236) (2829621157908) (-330605627482) (2154607379896) (by decide) (by decide)

private theorem checked_prefix2_74 : prefixBox cfg cell2 74 = .ok prefix2_74 := by
  rw [prefixBox, checked_prefix2_73]
  decide +kernel

private def prefix2_75 : Box :=
  dataBox (510776087161) (2863530589089) (-357277971837) (2145543884223) (by decide) (by decide)

private theorem checked_prefix2_75 : prefixBox cfg cell2 75 = .ok prefix2_75 := by
  rw [prefixBox, checked_prefix2_74]
  decide +kernel

private def prefix2_76 : Box :=
  dataBox (513494890862) (2871558117508) (-399232805200) (2131334394244) (by decide) (by decide)

private theorem checked_prefix2_76 : prefixBox cfg cell2 76 = .ok prefix2_76 := by
  rw [prefixBox, checked_prefix2_75]
  decide +kernel

private def prefix2_77 : Box :=
  dataBox (492593366820) (2864502176972) (-436007068928) (2118920125950) (by decide) (by decide)

private theorem checked_prefix2_77 : prefixBox cfg cell2 77 = .ok prefix2_77 := by
  rw [prefixBox, checked_prefix2_76]
  decide +kernel

private def prefix2_78 : Box :=
  dataBox (453345393295) (2851295507604) (-450653557393) (2113991689137) (by decide) (by decide)

private theorem checked_prefix2_78 : prefixBox cfg cell2 78 = .ok prefix2_78 := by
  rw [prefixBox, checked_prefix2_77]
  decide +kernel

private def prefix2_79 : Box :=
  dataBox (414100716552) (2838131937222) (-446133896303) (2127466211428) (by decide) (by decide)

private theorem checked_prefix2_79 : prefixBox cfg cell2 79 = .ok prefix2_79 := by
  rw [prefixBox, checked_prefix2_78]
  decide +kernel

private def prefix2_80 : Box :=
  dataBox (392238818749) (2830821976904) (-434495209147) (2162274019740) (by decide) (by decide)

private theorem checked_prefix2_80 : prefixBox cfg cell2 80 = .ok prefix2_80 := by
  rw [prefixBox, checked_prefix2_79]
  decide +kernel

private theorem checked_2 : positiveCheck cfg 80
    (input cfg (3 / 4) (1) 54 (by norm_num)) false = true := by
  change positiveCheck cfg 80 cell2 false = true
  unfold positiveCheck evaluate
  rw [checked_prefix2_80]
  decide +kernel

/-- Actual zeta has positive real part throughout this closed contour cell. -/
theorem positive {x : ℝ} (hx : x ∈ Set.Icc (3 / 4 : ℝ) (1)) :
    0 < (riemannZeta ((x : ℂ) + 54 * Complex.I)).re := by
  simpa using positive_of_check checked_2
    (mem_input (by decide) (by norm_num : (3 / 4 : ℚ) ≤ 1)
      (x := x) (by simpa using hx.1) (by simpa using hx.2))

end RiemannGaussian.ZetaHeightFiftyFour.Cell2
