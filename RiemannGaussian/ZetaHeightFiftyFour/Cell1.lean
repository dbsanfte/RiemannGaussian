/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaHorizontalCertificate

/-!
# Checked height-fifty-four contour cell 1

Every literal prefix checkpoint is checked in the kernel. This independent
module bounds compiler memory while retaining the complete original
Euler--Maclaurin expression, rounding errors and analytic tail.
-/

namespace RiemannGaussian.ZetaHeightFiftyFour.Cell1
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


private def cell1 : Box := input cfg (5 / 8) (3 / 4) 54 (by norm_num)

private def prefix1_1 : Box :=
  dataBox (1099511627776) (1099511627776) (0) (0) (by decide) (by decide)

private theorem checked_prefix1_1 : prefixBox cfg cell1 1 = .ok prefix1_1 := by
  decide +kernel

private def prefix1_2 : Box :=
  dataBox (1729745068376) (1786786074365) (173855185877) (189590447041) (by decide) (by decide)

private theorem checked_prefix1_2 : prefixBox cfg cell1 2 = .ok prefix1_2 := by
  rw [prefixBox, checked_prefix1_1]
  decide +kernel

private def prefix1_3 : Box :=
  dataBox (1212887582464) (1336248924911) (-23764071690) (17328640483) (by decide) (by decide)

private theorem checked_prefix1_3 : prefixBox cfg cell1 3 = .ok prefix1_3 := by
  rw [prefixBox, checked_prefix1_2]
  decide +kernel

private def prefix1_4 : Box :=
  dataBox (1546643540519) (1733153900663) (175541418479) (254344177726) (by decide) (by decide)

private theorem checked_prefix1_4 : prefixBox cfg cell1 4 = .ok prefix1_4 := by
  rw [prefixBox, checked_prefix1_3]
  decide +kernel

private def prefix1_5 : Box :=
  dataBox (1708847088648) (1931503651238) (461582693292) (604128220392) (by decide) (by decide)

private theorem checked_prefix1_5 : prefixBox cfg cell1 5 = .ok prefix1_5 := by
  rw [prefixBox, checked_prefix1_4]
  decide +kernel

private def prefix1_6 : Box :=
  dataBox (1419849472379) (1700496587019) (248933820064) (434149690516) (by decide) (by decide)

private theorem checked_prefix1_6 : prefixBox cfg cell1 6 = .ok prefix1_6 := by
  rw [prefixBox, checked_prefix1_5]
  decide +kernel

private def prefix1_7 : Box :=
  dataBox (1366583621026) (1658731698898) (500988467179) (755613441366) (by decide) (by decide)

private theorem checked_prefix1_7 : prefixBox cfg cell1 7 = .ok prefix1_7 := by
  rw [prefixBox, checked_prefix1_6]
  decide +kernel

private def prefix1_8 : Box :=
  dataBox (1526376259396) (1865957135672) (668002789005) (972204251381) (by decide) (by decide)

private theorem checked_prefix1_8 : prefixBox cfg cell1 8 = .ok prefix1_8 := by
  rw [prefixBox, checked_prefix1_7]
  decide +kernel

private def prefix1_9 : Box :=
  dataBox (1684000421856) (2073402218876) (809175195693) (1157997615651) (by decide) (by decide)

private theorem checked_prefix1_9 : prefixBox cfg cell1 9 = .ok prefix1_9 := by
  rw [prefixBox, checked_prefix1_8]
  decide +kernel

private def prefix1_10 : Box :=
  dataBox (1731745555903) (2137071410864) (998780015100) (1410839738251) (by decide) (by decide)

private theorem checked_prefix1_10 : prefixBox cfg cell1 10 = .ok prefix1_10 := by
  rw [prefixBox, checked_prefix1_9]
  decide +kernel

private def prefix1_11 : Box :=
  dataBox (1540890898517) (1995645646312) (1113390426882) (1565506969308) (by decide) (by decide)

private theorem checked_prefix1_11 : prefixBox cfg cell1 11 = .ok prefix1_11 := by
  rw [prefixBox, checked_prefix1_10]
  decide +kernel

private def prefix1_12 : Box :=
  dataBox (1396913798422) (1890110866237) (930637179750) (1431549375052) (by decide) (by decide)

private theorem checked_prefix1_12 : prefixBox cfg cell1 12 = .ok prefix1_12 := by
  rw [prefixBox, checked_prefix1_11]
  decide +kernel

private def prefix1_13 : Box :=
  dataBox (1551382321226) (2102965409589) (870077317875) (1387601102739) (by decide) (by decide)

private theorem checked_prefix1_13 : prefixBox cfg cell1 13 = .ok prefix1_13 := by
  rw [prefixBox, checked_prefix1_12]
  decide +kernel

private def prefix1_14 : Box :=
  dataBox (1462656821865) (2039171055449) (1007949635747) (1579354542443) (by decide) (by decide)

private theorem checked_prefix1_14 : prefixBox cfg cell1 14 = .ok prefix1_14 := by
  rw [prefixBox, checked_prefix1_13]
  decide +kernel

private def prefix1_15 : Box :=
  dataBox (1432284692919) (2017520784779) (807873331083) (1436733310876) (by decide) (by decide)

private theorem checked_prefix1_15 : prefixBox cfg cell1 15 = .ok prefix1_15 := by
  rw [prefixBox, checked_prefix1_14]
  decide +kernel

private def prefix1_16 : Box :=
  dataBox (1497468496785) (2109704630443) (928871405154) (1607850457552) (by decide) (by decide)

private theorem checked_prefix1_16 : prefixBox cfg cell1 16 = .ok prefix1_16 := by
  rw [prefixBox, checked_prefix1_15]
  decide +kernel

private def prefix1_17 : Box :=
  dataBox (1387779008478) (2032728038404) (777246762289) (1501445088898) (by decide) (by decide)

private theorem checked_prefix1_17 : prefixBox cfg cell1 17 = .ok prefix1_17 := by
  rw [prefixBox, checked_prefix1_16]
  decide +kernel

private def prefix1_18 : Box :=
  dataBox (1455805989173) (2130359627761) (883089526163) (1653349474011) (by decide) (by decide)

private theorem checked_prefix1_18 : prefixBox cfg cell1 18 = .ok prefix1_18 := by
  rw [prefixBox, checked_prefix1_17]
  decide +kernel

private def prefix1_19 : Box :=
  dataBox (1396063793480) (2089013326402) (719056429244) (1539825604984) (by decide) (by decide)

private theorem checked_prefix1_19 : prefixBox cfg cell1 19 = .ok prefix1_19 := by
  rw [prefixBox, checked_prefix1_18]
  decide +kernel

private def prefix1_20 : Box :=
  dataBox (1392263682223) (2086400180395) (835286246703) (1708848830653) (by decide) (by decide)

private theorem checked_prefix1_20 : prefixBox cfg cell1 20 = .ok prefix1_20 := by
  rw [prefixBox, checked_prefix1_19]
  decide +kernel

private def prefix1_21 : Box :=
  dataBox (1448867021402) (2169217195970) (693746507556) (1612109984278) (by decide) (by decide)

private theorem checked_prefix1_21 : prefixBox cfg cell1 21 = .ok prefix1_21 := by
  rw [prefixBox, checked_prefix1_20]
  decide +kernel

private def prefix1_22 : Box :=
  dataBox (1302899520914) (2070030562468) (737078198821) (1675878873486) (by decide) (by decide)

private theorem checked_prefix1_22 : prefixBox cfg cell1 22 = .ok prefix1_22 := by
  rw [prefixBox, checked_prefix1_21]
  decide +kernel

private def prefix1_23 : Box :=
  dataBox (1401963599667) (2216629966271) (770934371195) (1725980751694) (by decide) (by decide)

private theorem checked_prefix1_23 : prefixBox cfg cell1 23 = .ok prefix1_23 := by
  rw [prefixBox, checked_prefix1_22]
  decide +kernel

private def prefix1_24 : Box :=
  dataBox (1343479887905) (2177319496193) (631874163398) (1632509864706) (by decide) (by decide)

private theorem checked_prefix1_24 : prefixBox cfg cell1 24 = .ok prefix1_24 := by
  rw [prefixBox, checked_prefix1_23]
  decide +kernel

private def prefix1_25 : Box :=
  dataBox (1267986125062) (2126833801435) (716269647952) (1758710584988) (by decide) (by decide)

private theorem checked_prefix1_25 : prefixBox cfg cell1 25 = .ok prefix1_25 := by
  rw [prefixBox, checked_prefix1_24]
  decide +kernel

private def prefix1_26 : Box :=
  dataBox (1363475671905) (2270325739687) (715118170465) (1757944323372) (by decide) (by decide)

private theorem checked_prefix1_26 : prefixBox cfg cell1 26 = .ok prefix1_26 := by
  rw [prefixBox, checked_prefix1_25]
  decide +kernel

private def prefix1_27 : Box :=
  dataBox (1299353371675) (2227855142353) (590495720540) (1675402187830) (by decide) (by decide)

private theorem checked_prefix1_27 : prefixBox cfg cell1 27 = .ok prefix1_27 := by
  rw [prefixBox, checked_prefix1_26]
  decide +kernel

private def prefix1_28 : Box :=
  dataBox (1210829167616) (2169488182662) (659436108481) (1779962922776) (by decide) (by decide)

private theorem checked_prefix1_28 : prefixBox cfg cell1 28 = .ok prefix1_28 := by
  rw [prefixBox, checked_prefix1_27]
  decide +kernel

private def prefix1_29 : Box :=
  dataBox (1292588488831) (2294036266348) (691940143461) (1829477967779) (by decide) (by decide)

private theorem checked_prefix1_29 : prefixBox cfg cell1 29 = .ok prefix1_29 := by
  rw [prefixBox, checked_prefix1_28]
  decide +kernel

private def prefix1_30 : Box :=
  dataBox (1302729993924) (2309550962118) (561640843802) (1744304987115) (by decide) (by decide)

private theorem checked_prefix1_30 : prefixBox cfg cell1 30 = .ok prefix1_30 := by
  rw [prefixBox, checked_prefix1_29]
  decide +kernel

private def prefix1_31 : Box :=
  dataBox (1174597134428) (2226136744827) (568440949367) (1754750707610) (by decide) (by decide)

private theorem checked_prefix1_31 : prefixBox cfg cell1 31 = .ok prefix1_31 := by
  rw [prefixBox, checked_prefix1_30]
  decide +kernel

private def prefix1_32 : Box :=
  dataBox (1192827831869) (2254252350358) (648103203461) (1877606724482) (by decide) (by decide)

private theorem checked_prefix1_32 : prefixBox cfg cell1 32 = .ok prefix1_32 := by
  rw [prefixBox, checked_prefix1_31]
  decide +kernel

private def prefix1_33 : Box :=
  dataBox (1268734782596) (2371768028574) (609700368352) (1852801176593) (by decide) (by decide)

private theorem checked_prefix1_33 : prefixBox cfg cell1 33 = .ok prefix1_33 := by
  rw [prefixBox, checked_prefix1_32]
  decide +kernel

private def prefix1_34 : Box :=
  dataBox (1226315761978) (2344470370704) (496010059332) (1779638690243) (by decide) (by decide)

private theorem checked_prefix1_34 : prefixBox cfg cell1 34 = .ok prefix1_34 := by
  rw [prefixBox, checked_prefix1_33]
  decide +kernel

private def prefix1_35 : Box :=
  dataBox (1114440476589) (2272736310040) (522328705485) (1820684858349) (by decide) (by decide)

private theorem checked_prefix1_35 : prefixBox cfg cell1 35 = .ok prefix1_35 := by
  rw [prefixBox, checked_prefix1_34]
  decide +kernel

private def prefix1_36 : Box :=
  dataBox (1136697229840) (2307570034607) (593753591339) (1932470869469) (by decide) (by decide)

private theorem checked_prefix1_36 : prefixBox cfg cell1 36 = .ok prefix1_36 := by
  rw [prefixBox, checked_prefix1_35]
  decide +kernel

private def prefix1_37 : Box :=
  dataBox (1208365148967) (2420121207678) (569667324397) (1917133744548) (by decide) (by decide)

private theorem checked_prefix1_37 : prefixBox cfg cell1 37 = .ok prefix1_37 := by
  rw [prefixBox, checked_prefix1_36]
  decide +kernel

private def prefix1_38 : Box :=
  dataBox (1199306415336) (2414372196913) (456833318052) (1845524852277) (by decide) (by decide)

private theorem checked_prefix1_38 : prefixBox cfg cell1 38 = .ok prefix1_38 := by
  rw [prefixBox, checked_prefix1_37]
  decide +kernel

private def prefix1_39 : Box :=
  dataBox (1088363264602) (2344191583226) (447044087311) (1839332397620) (by decide) (by decide)

private theorem checked_prefix1_39 : prefixBox cfg cell1 39 = .ok prefix1_39 := by
  rw [prefixBox, checked_prefix1_38]
  decide +kernel

private def prefix1_40 : Box :=
  dataBox (1056842988823) (2324315442717) (513253122284) (1944328910646) (by decide) (by decide)

private theorem checked_prefix1_40 : prefixBox cfg cell1 40 = .ok prefix1_40 := by
  rw [prefixBox, checked_prefix1_39]
  decide +kernel

private def prefix1_41 : Box :=
  dataBox (1115425781512) (2417505181676) (547502130212) (1998810042134) (by decide) (by decide)

private theorem checked_prefix1_41 : prefixBox cfg cell1 41 = .ok prefix1_41 := by
  rw [prefixBox, checked_prefix1_40]
  decide +kernel

private def prefix1_42 : Box :=
  dataBox (1163166859247) (2493677724488) (473309795169) (1952310061577) (by decide) (by decide)

private theorem checked_prefix1_42 : prefixBox cfg cell1 42 = .ok prefix1_42 := by
  rw [prefixBox, checked_prefix1_41]
  decide +kernel

private def prefix1_43 : Box :=
  dataBox (1115518800661) (2463902068700) (379989380306) (1893993358564) (by decide) (by decide)

private theorem checked_prefix1_43 : prefixBox cfg cell1 43 = .ok prefix1_43 := by
  rw [prefixBox, checked_prefix1_42]
  decide +kernel

private def prefix1_44 : Box :=
  dataBox (1013282765030) (2400197267514) (389143407366) (1908684155546) (by decide) (by decide)

private theorem checked_prefix1_44 : prefixBox cfg cell1 44 = .ok prefix1_44 := by
  rw [prefixBox, checked_prefix1_43]
  decide +kernel

private def prefix1_45 : Box :=
  dataBox (991599605188) (2386724077776) (450976023242) (2008194744566) (by decide) (by decide)

private theorem checked_prefix1_45 : prefixBox cfg cell1 45 = .ok prefix1_45 := by
  rw [prefixBox, checked_prefix1_44]
  decide +kernel

private def prefix1_46 : Box :=
  dataBox (1043029184982) (2469720191008) (486046226115) (2064790405329) (by decide) (by decide)

private theorem checked_prefix1_46 : prefixBox cfg cell1 46 = .ok prefix1_46 := by
  rw [prefixBox, checked_prefix1_45]
  decide +kernel

private def prefix1_47 : Box :=
  dataBox (1094832873197) (2553545074561) (433158220377) (2032105681084) (by decide) (by decide)

private theorem checked_prefix1_47 : prefixBox cfg cell1 47 = .ok prefix1_47 := by
  rw [prefixBox, checked_prefix1_46]
  decide +kernel

private def prefix1_48 : Box :=
  dataBox (1082254671042) (2545792204509) (336151081467) (1972312943927) (by decide) (by decide)

private theorem checked_prefix1_48 : prefixBox cfg cell1 48 = .ok prefix1_48 := by
  rw [prefixBox, checked_prefix1_47]
  decide +kernel

private def prefix1_49 : Box :=
  dataBox (990848897375) (2489597048308) (305004442483) (1953164386471) (by decide) (by decide)

private theorem checked_prefix1_49 : prefixBox cfg cell1 49 = .ok prefix1_49 := by
  rw [prefixBox, checked_prefix1_48]
  decide +kernel

private def prefix1_50 : Box :=
  dataBox (921898842392) (2447314308155) (345396603131) (2019031488406) (by decide) (by decide)

private theorem checked_prefix1_50 : prefixBox cfg cell1 50 = .ok prefix1_50 := by
  rw [prefixBox, checked_prefix1_49]
  decide +kernel

private def prefix1_51 : Box :=
  dataBox (936770201402) (2471624997587) (401057412209) (2110021952289) (by decide) (by decide)

private theorem checked_prefix1_51 : prefixBox cfg cell1 51 = .ok prefix1_51 := by
  rw [prefixBox, checked_prefix1_50]
  decide +kernel

private def prefix1_52 : Box :=
  dataBox (991625395967) (2561516408447) (415717031241) (2134044737967) (by decide) (by decide)

private theorem checked_prefix1_52 : prefixBox cfg cell1 52 = .ok prefix1_52 := by
  rw [prefixBox, checked_prefix1_51]
  decide +kernel

private def prefix1_53 : Box :=
  dataBox (1031909065280) (2627686780821) (351878649511) (2095180757607) (by decide) (by decide)

private theorem checked_prefix1_53 : prefixBox cfg cell1 53 = .ok prefix1_53 := by
  rw [prefixBox, checked_prefix1_52]
  decide +kernel

private def prefix1_54 : Box :=
  dataBox (1013316812604) (2616394486450) (262923885249) (2041152634461) (by decide) (by decide)

private theorem checked_prefix1_54 : prefixBox cfg cell1 54 = .ok prefix1_54 := by
  rw [prefixBox, checked_prefix1_53]
  decide +kernel

private def prefix1_55 : Box :=
  dataBox (929683220192) (2565714652704) (230109568721) (2021268005237) (by decide) (by decide)

private theorem checked_prefix1_55 : prefixBox cfg cell1 55 = .ok prefix1_55 := by
  rw [prefixBox, checked_prefix1_54]
  decide +kernel

private def prefix1_56 : Box :=
  dataBox (856319610214) (2521358184700) (260396772339) (2071361690043) (by decide) (by decide)

private theorem checked_prefix1_56 : prefixBox cfg cell1 56 = .ok prefix1_56 := by
  rw [prefixBox, checked_prefix1_55]
  decide +kernel

private def prefix1_57 : Box :=
  dataBox (854920884719) (2520514381299) (313392223073) (2159207903826) (by decide) (by decide)

private theorem checked_prefix1_57 : prefixBox cfg cell1 57 = .ok prefix1_57 := by
  rw [prefixBox, checked_prefix1_56]
  decide +kernel

private def prefix1_58 : Box :=
  dataBox (896645282550) (2589828009565) (344951154278) (2211634408925) (by decide) (by decide)

private theorem checked_prefix1_58 : prefixBox cfg cell1 58 = .ok prefix1_58 := by
  rw [prefixBox, checked_prefix1_57]
  decide +kernel

private def prefix1_59 : Box :=
  dataBox (946345926922) (2672568585836) (321558102819) (2197582668478) (by decide) (by decide)

private theorem checked_prefix1_59 : prefixBox cfg cell1 59 = .ok prefix1_59 := by
  rw [prefixBox, checked_prefix1_58]
  decide +kernel

private def prefix1_60 : Box :=
  dataBox (965626561631) (2704734096561) (242786817302) (2150365609518) (by decide) (by decide)

private theorem checked_prefix1_60 : prefixBox cfg cell1 60 = .ok prefix1_60 := by
  rw [prefixBox, checked_prefix1_59]
  decide +kernel

private def prefix1_61 : Box :=
  dataBox (924891536747) (2680367131676) (169083705633) (2106277706651) (by decide) (by decide)

private theorem checked_prefix1_61 : prefixBox cfg cell1 61 = .ok prefix1_61 := by
  rw [prefixBox, checked_prefix1_60]
  decide +kernel

private def prefix1_62 : Box :=
  dataBox (842998044331) (2631479368707) (153518861321) (2096986019907) (by decide) (by decide)

private theorem checked_prefix1_62 : prefixBox cfg cell1 62 = .ok prefix1_62 := by
  rw [prefixBox, checked_prefix1_61]
  decide +kernel

private def prefix1_63 : Box :=
  dataBox (778628028842) (2593129332392) (184290562293) (2148635905062) (by decide) (by decide)

private theorem checked_prefix1_63 : prefixBox cfg cell1 63 = .ok prefix1_63 := by
  rw [prefixBox, checked_prefix1_62]
  decide +kernel

private def prefix1_64 : Box :=
  dataBox (775018054250) (2590982843533) (232835130818) (2230277835284) (by decide) (by decide)

private theorem checked_prefix1_64 : prefixBox cfg cell1 64 = .ok prefix1_64 := by
  rw [prefixBox, checked_prefix1_63]
  decide +kernel

private def prefix1_65 : Box :=
  dataBox (809239032196) (2648647097173) (266537187176) (2287067682223) (by decide) (by decide)

private theorem checked_prefix1_65 : prefixBox cfg cell1 65 = .ok prefix1_65 := by
  rw [prefixBox, checked_prefix1_64]
  decide +kernel

private def prefix1_66 : Box :=
  dataBox (856670703772) (2728724766967) (262796034782) (2284851728557) (by decide) (by decide)

private theorem checked_prefix1_66 : prefixBox cfg cell1 66 = .ok prefix1_66 := by
  rw [prefixBox, checked_prefix1_65]
  decide +kernel

private def prefix1_67 : Box :=
  dataBox (887348362332) (2780614527580) (202677716690) (2249309279441) (by decide) (by decide)

private theorem checked_prefix1_67 : prefixBox cfg cell1 67 = .ok prefix1_67 := by
  rw [prefixBox, checked_prefix1_66]
  decide +kernel

private def prefix1_68 : Box :=
  dataBox (880437187262) (2776536156653) (124298662086) (2203056665470) (by decide) (by decide)

private theorem checked_prefix1_68 : prefixBox cfg cell1 68 = .ok prefix1_68 := by
  rw [prefixBox, checked_prefix1_67]
  decide +kernel

private def prefix1_69 : Box :=
  dataBox (820528842010) (2741247843106) (74397958190) (2173663237451) (by decide) (by decide)

private theorem checked_prefix1_69 : prefixBox cfg cell1 69 = .ok prefix1_69 := by
  rw [prefixBox, checked_prefix1_68]
  decide +kernel

private def prefix1_70 : Box :=
  dataBox (743521025413) (2695968799553) (78141022850) (2180029257395) (by decide) (by decide)

private theorem checked_prefix1_70 : prefixBox cfg cell1 70 = .ok prefix1_70 := by
  rw [prefixBox, checked_prefix1_69]
  decide +kernel

private def prefix1_71 : Box :=
  dataBox (692884766750) (2666248443134) (111867081981) (2237490249728) (by decide) (by decide)

private theorem checked_prefix1_71 : prefixBox cfg cell1 71 = .ok prefix1_71 := by
  rw [prefixBox, checked_prefix1_70]
  decide +kernel

private def prefix1_72 : Box :=
  dataBox (694348470200) (2668746621784) (156326642168) (2313371039407) (by decide) (by decide)

private theorem checked_prefix1_72 : prefixBox cfg cell1 72 = .ok prefix1_72 := by
  rw [prefixBox, checked_prefix1_71]
  decide +kernel

private def prefix1_73 : Box :=
  dataBox (725240429278) (2721562061610) (187694798545) (2367000629618) (by decide) (by decide)

private theorem checked_prefix1_73 : prefixBox cfg cell1 73 = .ok prefix1_73 := by
  rw [prefixBox, checked_prefix1_72]
  decide +kernel

private def prefix1_74 : Box :=
  dataBox (768745162279) (2796067929560) (190235802354) (2371352346851) (by decide) (by decide)

private theorem checked_prefix1_74 : prefixBox cfg cell1 74 = .ok prefix1_74 := by
  rw [prefixBox, checked_prefix1_73]
  decide +kernel

private def prefix1_75 : Box :=
  dataBox (802654588020) (2854238478551) (144480245272) (2344680011197) (by decide) (by decide)

private theorem checked_prefix1_75 : prefixBox cfg cell1 75 = .ok prefix1_75 := by
  rw [prefixBox, checked_prefix1_74]
  decide +kernel

private def prefix1_76 : Box :=
  dataBox (810682105332) (2868032266668) (72388805448) (2302725188666) (by decide) (by decide)

private theorem checked_prefix1_76 : prefixBox cfg cell1 76 = .ok prefix1_76 := by
  rw [prefixBox, checked_prefix1_75]
  decide +kernel

private def prefix1_77 : Box :=
  dataBox (774708058596) (2847130759970) (9095857078) (2265950939995) (by decide) (by decide)

private theorem checked_prefix1_77 : prefixBox cfg cell1 77 = .ok prefix1_77 := by
  rw [prefixBox, checked_prefix1_76]
  decide +kernel

private def prefix1_78 : Box :=
  dataBox (707048515115) (2807882811903) (-16153210176) (2251304474131) (by decide) (by decide)

private theorem checked_prefix1_78 : prefixBox cfg cell1 78 = .ok prefix1_78 := by
  rw [prefixBox, checked_prefix1_77]
  decide +kernel

private def prefix1_79 : Box :=
  dataBox (639286838601) (2768638160759) (-2678710656) (2274570208402) (by decide) (by decide)

private theorem checked_prefix1_79 : prefixBox cfg cell1 79 = .ok prefix1_79 := by
  rw [prefixBox, checked_prefix1_78]
  decide +kernel

private def prefix1_80 : Box :=
  dataBox (601479674003) (2746776280243) (32129082668) (2334765556036) (by decide) (by decide)

private theorem checked_prefix1_80 : prefixBox cfg cell1 80 = .ok prefix1_80 := by
  rw [prefixBox, checked_prefix1_79]
  decide +kernel

private theorem checked_1 : positiveCheck cfg 80
    (input cfg (5 / 8) (3 / 4) 54 (by norm_num)) false = true := by
  change positiveCheck cfg 80 cell1 false = true
  unfold positiveCheck evaluate
  rw [checked_prefix1_80]
  decide +kernel

/-- Actual zeta has positive real part throughout this closed contour cell. -/
theorem positive {x : ℝ} (hx : x ∈ Set.Icc (5 / 8 : ℝ) (3 / 4)) :
    0 < (riemannZeta ((x : ℂ) + 54 * Complex.I)).re := by
  simpa using positive_of_check checked_1
    (mem_input (by decide) (by norm_num : (5 / 8 : ℚ) ≤ 3 / 4)
      (x := x) (by simpa using hx.1) (by simpa using hx.2))

end RiemannGaussian.ZetaHeightFiftyFour.Cell1
