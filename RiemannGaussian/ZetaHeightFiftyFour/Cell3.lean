/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaHorizontalCertificate

/-!
# Checked height-fifty-four contour cell 3

Every literal prefix checkpoint is checked in the kernel. This independent
module bounds compiler memory while retaining the complete original
Euler--Maclaurin expression, rounding errors and analytic tail.
-/

namespace RiemannGaussian.ZetaHeightFiftyFour.Cell3
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


private def cell3 : Box := input cfg (1) (3 / 2) 54 (by norm_num)

private def prefix3_1 : Box :=
  dataBox (1099511627776) (1099511627776) (0) (0) (by decide) (by decide)

private theorem checked_prefix3_1 : prefixBox cfg cell3 1 = .ok prefix3_1 := by
  decide +kernel

private def prefix3_2 : Box :=
  dataBox (1474250673534) (1629472673613) (103374911991) (146194219927) (by decide) (by decide)

private theorem checked_prefix3_2 : prefixBox cfg cell3 2 = .ok prefix3_2 := by
  rw [prefixBox, checked_prefix3_1]
  decide +kernel

private def prefix3_3 : Box :=
  dataBox (1131916432594) (1431825928899) (-27515788789) (70624457598) (by decide) (by decide)

private theorem checked_prefix3_3 : prefixBox cfg cell3 3 = .ok prefix3_3 := by
  rw [prefixBox, checked_prefix3_2]
  decide +kernel

private def prefix3_4 : Box :=
  dataBox (1249916983145) (1667827039524) (42949342994) (211554739257) (by decide) (by decide)

private theorem checked_prefix3_4 : prefixBox cfg cell3 4 = .ok prefix3_4 := by
  rw [prefixBox, checked_prefix3_3]
  decide +kernel

private def prefix3_5 : Box :=
  dataBox (1298427158725) (1776299104321) (128495637292) (402842085125) (by decide) (by decide)

private theorem checked_prefix3_5 : prefixBox cfg cell3 5 = .ok prefix3_5 := by
  rw [prefixBox, checked_prefix3_4]
  decide +kernel

private def prefix3_6 : Box :=
  dataBox (1150826756223) (1716041505330) (19889000029) (358503622468) (by decide) (by decide)

private theorem checked_prefix3_6 : prefixBox cfg cell3 6 = .ok prefix3_6 := by
  rw [prefixBox, checked_prefix3_5]
  decide +kernel

private def prefix3_7 : Box :=
  dataBox (1125150180325) (1706336678460) (78458454470) (513463849094) (by decide) (by decide)

private theorem checked_prefix3_7 : prefixBox cfg cell3 7 = .ok prefix3_7 := by
  rw [prefixBox, checked_prefix3_6]
  decide +kernel

private def prefix3_8 : Box :=
  dataBox (1158742444501) (1801349960180) (113568890578) (612771173380) (by decide) (by decide)

private theorem checked_prefix3_8 : prefixBox cfg cell3 8 = .ok prefix3_8 := by
  rw [prefixBox, checked_prefix3_7]
  decide +kernel

private def prefix3_9 : Box :=
  dataBox (1189077228690) (1892354321250) (140737532895) (694277112905) (by decide) (by decide)

private theorem checked_prefix3_9 : prefixBox cfg cell3 9 = .ok prefix3_9 := by
  rw [prefixBox, checked_prefix3_8]
  decide +kernel

private def prefix3_10 : Box :=
  dataBox (1197567647565) (1919203396897) (174454567512) (800899751961) (by decide) (by decide)

private theorem checked_prefix3_10 : prefixBox cfg cell3 10 = .ok prefix3_10 := by
  rw [prefixBox, checked_prefix3_9]
  decide +kernel

private def prefix3_11 : Box :=
  dataBox (1119910666071) (1895788943646) (193429470263) (863832406916) (by decide) (by decide)

private theorem checked_prefix3_11 : prefixBox cfg cell3 11 = .ok prefix3_11 := by
  rw [prefixBox, checked_prefix3_10]
  decide +kernel

private def prefix3_12 : Box :=
  dataBox (1063208394865) (1879420413800) (121456051047) (843055475575) (by decide) (by decide)

private theorem checked_prefix3_12 : prefixBox cfg cell3 12 = .ok prefix3_12 := by
  rw [prefixBox, checked_prefix3_11]
  decide +kernel

private def prefix3_13 : Box :=
  dataBox (1085770648593) (1960769778866) (98311107865) (836636225538) (by decide) (by decide)

private theorem checked_prefix3_13 : prefixBox cfg cell3 13 = .ok prefix3_13 := by
  rw [prefixBox, checked_prefix3_12]
  decide +kernel

private def prefix3_14 : Box :=
  dataBox (1052790664710) (1951955511542) (117360496838) (907912525998) (by decide) (by decide)

private theorem checked_prefix3_14 : prefixBox cfg cell3 14 = .ok prefix3_14 := by
  rw [prefixBox, checked_prefix3_13]
  decide +kernel

private def prefix3_15 : Box :=
  dataBox (1041789440572) (1949115010940) (44889967158) (889200718636) (by decide) (by decide)

private theorem checked_prefix3_15 : prefixBox cfg cell3 15 = .ok prefix3_15 := by
  rw [prefixBox, checked_prefix3_14]
  decide +kernel

private def prefix3_16 : Box :=
  dataBox (1049937416048) (1981706922147) (60014726404) (949699766059) (by decide) (by decide)

private theorem checked_prefix3_16 : prefixBox cfg cell3 16 = .ok prefix3_16 := by
  rw [prefixBox, checked_prefix3_15]
  decide +kernel

private def prefix3_17 : Box :=
  dataBox (1012028037486) (1972512551899) (7612294098) (936990313355) (by decide) (by decide)

private theorem checked_prefix3_17 : prefixBox cfg cell3 17 = .ok prefix3_17 := by
  rw [prefixBox, checked_prefix3_16]
  decide +kernel

private def prefix3_18 : Box :=
  dataBox (1019812467464) (2005539098937) (19724041167) (988376113312) (by decide) (by decide)

private theorem checked_prefix3_18 : prefixBox cfg cell3 18 = .ok prefix3_18 := by
  rw [prefixBox, checked_prefix3_17]
  decide +kernel

private def prefix3_19 : Box :=
  dataBox (1000008665265) (2000995798416) (-34650910538) (975901646760) (by decide) (by decide)

private theorem checked_prefix3_19 : prefixBox cfg cell3 19 = .ok prefix3_19 := by
  rw [prefixBox, checked_prefix3_18]
  decide +kernel

private def prefix3_20 : Box :=
  dataBox (998772973752) (2000719491867) (-22361103655) (1030863344250) (by decide) (by decide)

private theorem checked_prefix3_20 : prefixBox cfg cell3 20 = .ok prefix3_20 := by
  rw [prefixBox, checked_prefix3_19]
  decide +kernel

private def prefix3_21 : Box :=
  dataBox (1004542997235) (2027161068100) (-67551500541) (1021001992898) (by decide) (by decide)

private theorem checked_prefix3_21 : prefixBox cfg cell3 21 = .ok prefix3_21 := by
  rw [prefixBox, checked_prefix3_20]
  decide +kernel

private def prefix3_22 : Box :=
  dataBox (958744875598) (2017396879957) (-63285817040) (1041009839404) (by decide) (by decide)

private theorem checked_prefix3_22 : prefixBox cfg cell3 22 = .ok prefix3_22 := by
  rw [prefixBox, checked_prefix3_21]
  decide +kernel

private def prefix3_23 : Box :=
  dataBox (968177234726) (2062632887290) (-60062210860) (1056469717625) (by decide) (by decide)

private theorem checked_prefix3_23 : prefixBox cfg cell3 23 = .ok prefix3_23 := by
  rw [prefixBox, checked_prefix3_22]
  decide +kernel

private def prefix3_24 : Box :=
  dataBox (950416713274) (2059007538419) (-102292461458) (1047849505912) (by decide) (by decide)

private theorem checked_prefix3_24 : prefixBox cfg cell3 24 = .ok prefix3_24 := by
  rw [prefixBox, checked_prefix3_23]
  decide +kernel

private def prefix3_25 : Box :=
  dataBox (927838812012) (2054491960609) (-94743899847) (1085592324582) (by decide) (by decide)

private theorem checked_prefix3_25 : prefixBox cfg cell3 25 = .ok prefix3_25 := by
  rw [prefixBox, checked_prefix3_24]
  decide +kernel

private def prefix3_26 : Box :=
  dataBox (936132082322) (2096779507919) (-95083244059) (1085525774736) (by decide) (by decide)

private theorem checked_prefix3_26 : prefixBox cfg cell3 26 = .ok prefix3_26 := by
  rw [prefixBox, checked_prefix3_25]
  decide +kernel

private def prefix3_27 : Box :=
  dataBox (917500588284) (2093193877318) (-131293773382) (1078557056948) (by decide) (by decide)

private theorem checked_prefix3_27 : prefixBox cfg cell3 27 = .ok prefix3_27 := by
  rw [prefixBox, checked_prefix3_26]
  decide +kernel

private def prefix3_28 : Box :=
  dataBox (892127240685) (2088398767612) (-125630008726) (1108526892894) (by decide) (by decide)

private theorem checked_prefix3_28 : prefixBox cfg cell3 28 = .ok prefix3_28 := by
  rw [prefixBox, checked_prefix3_27]
  decide +kernel

private def prefix3_29 : Box :=
  dataBox (898669666071) (2123630808459) (-123029018155) (1122533660694) (by decide) (by decide)

private theorem checked_prefix3_29 : prefixBox cfg cell3 29 = .ok prefix3_29 := by
  rw [prefixBox, checked_prefix3_28]
  decide +kernel

private def prefix3_30 : Box :=
  dataBox (899460820878) (2127964148737) (-159422332708) (1115889182135) (by decide) (by decide)

private theorem checked_prefix3_30 : prefixBox cfg cell3 30 = .ok prefix3_30 := by
  rw [prefixBox, checked_prefix3_29]
  decide +kernel

private def prefix3_31 : Box :=
  dataBox (864109969042) (2121614951653) (-158904732570) (1118771074563) (by decide) (by decide)

private theorem checked_prefix3_31 : prefixBox cfg cell3 31 = .ok prefix3_31 := by
  rw [prefixBox, checked_prefix3_30]
  decide +kernel

private def prefix3_32 : Box :=
  dataBox (865464973734) (2129280022968) (-152983800116) (1152264933684) (by decide) (by decide)

private theorem checked_prefix3_32 : prefixBox cfg cell3 32 = .ok prefix3_32 := by
  rw [prefixBox, checked_prefix3_31]
  decide +kernel

private def prefix3_33 : Box :=
  dataBox (870978076529) (2160950389100) (-163333328510) (1150463312962) (by decide) (by decide)

private theorem checked_prefix3_33 : prefixBox cfg cell3 33 = .ok prefix3_33 := by
  rw [prefixBox, checked_prefix3_32]
  decide +kernel

private def prefix3_34 : Box :=
  dataBox (859673454570) (2159011664157) (-193631669799) (1145267191818) (by decide) (by decide)

private theorem checked_prefix3_34 : prefixBox cfg cell3 34 = .ok prefix3_34 := by
  rw [prefixBox, checked_prefix3_33]
  decide +kernel

private def prefix3_35 : Box :=
  dataBox (830181154783) (2154026558334) (-191802674828) (1156087686181) (by decide) (by decide)

private theorem checked_prefix3_35 : prefixBox cfg cell3 35 = .ok prefix3_35 := by
  rw [prefixBox, checked_prefix3_34]
  decide +kernel

private def prefix3_36 : Box :=
  dataBox (831695535025) (2163112845870) (-186942826910) (1185246779910) (by decide) (by decide)

private theorem checked_prefix3_36 : prefixBox cfg cell3 36 = .ok prefix3_36 := by
  rw [prefixBox, checked_prefix3_35]
  decide +kernel

private def prefix3_37 : Box :=
  dataBox (836472735880) (2192171425311) (-193161444471) (1184224446247) (by decide) (by decide)

private theorem checked_prefix3_37 : prefixBox cfg cell3 37 = .ok prefix3_37 := by
  rw [prefixBox, checked_prefix3_36]
  decide +kernel

private def prefix3_38 : Box :=
  dataBox (834157215322) (2191795799503) (-222003164730) (1179545702523) (by decide) (by decide)

private theorem checked_prefix3_38 : prefixBox cfg cell3 38 = .ok prefix3_38 := by
  rw [prefixBox, checked_prefix3_37]
  decide +kernel

private def prefix3_39 : Box :=
  dataBox (806073713003) (2187298842805) (-224481153524) (1179148909179) (by decide) (by decide)

private theorem checked_prefix3_39 : prefixBox cfg cell3 39 = .ok prefix3_39 := by
  rw [prefixBox, checked_prefix3_38]
  decide +kernel

private def prefix3_40 : Box :=
  dataBox (798170248408) (2186049196631) (-220318480834) (1205475970181) (by decide) (by decide)

private theorem checked_prefix3_40 : prefixBox cfg cell3 40 = .ok prefix3_40 := by
  rw [prefixBox, checked_prefix3_39]
  decide +kernel

private def prefix3_41 : Box :=
  dataBox (801785863395) (2209200430875) (-218204699284) (1219010780462) (by decide) (by decide)

private theorem checked_prefix3_41 : prefixBox cfg cell3 41 = .ok prefix3_41 := by
  rw [prefixBox, checked_prefix3_40]
  decide +kernel

private def prefix3_42 : Box :=
  dataBox (804679575030) (2227953828843) (-236470577432) (1216192294975) (by decide) (by decide)

private theorem checked_prefix3_42 : prefixBox cfg cell3 42 = .ok prefix3_42 := by
  rw [prefixBox, checked_prefix3_41]
  decide +kernel

private def prefix3_43 : Box :=
  dataBox (793051855720) (2226180619573) (-259243878635) (1212719400234) (by decide) (by decide)

private theorem checked_prefix3_43 : prefixBox cfg cell3 43 = .ok prefix3_43 := by
  rw [prefixBox, checked_prefix3_42]
  decide +kernel

private def prefix3_44 : Box :=
  dataBox (768317007643) (2222451703088) (-258708053992) (1216273671771) (by decide) (by decide)

private theorem checked_prefix3_44 : prefixBox cfg cell3 44 = .ok prefix3_44 := by
  rw [prefixBox, checked_prefix3_43]
  decide +kernel

private def prefix3_45 : Box :=
  dataBox (763115037216) (2221676240162) (-255149215869) (1240147089899) (by decide) (by decide)

private theorem checked_prefix3_45 : prefixBox cfg cell3 45 = .ok prefix3_45 := by
  rw [prefixBox, checked_prefix3_44]
  decide +kernel

private def prefix3_46 : Box :=
  dataBox (766026723640) (2241424260595) (-253163715812) (1253613410449) (by decide) (by decide)

private theorem checked_prefix3_46 : prefixBox cfg cell3 46 = .ok prefix3_46 := by
  rw [prefixBox, checked_prefix3_45]
  decide +kernel

private def prefix3_47 : Box :=
  dataBox (768912663568) (2261209270058) (-265646759625) (1251792571934) (by decide) (by decide)

private theorem checked_prefix3_47 : prefixBox cfg cell3 47 = .ok prefix3_47 := by
  rw [prefixBox, checked_prefix3_46]
  decide +kernel

private def prefix3_48 : Box :=
  dataBox (765967203722) (2260784130442) (-288363092923) (1248513752457) (by decide) (by decide)

private theorem checked_prefix3_48 : prefixBox cfg cell3 48 = .ok prefix3_48 := by
  rw [prefixBox, checked_prefix3_47]
  decide +kernel

private def prefix3_49 : Box :=
  dataBox (744727419559) (2257749877217) (-295600577635) (1247479827540) (by decide) (by decide)

private theorem checked_prefix3_49 : prefixBox cfg cell3 49 = .ok prefix3_49 := by
  rw [prefixBox, checked_prefix3_48]
  decide +kernel

private def prefix3_50 : Box :=
  dataBox (728826550346) (2255501155985) (-293452403016) (1262669723670) (by decide) (by decide)

private theorem checked_prefix3_50 : prefixBox cfg cell3 50 = .ok prefix3_50 := by
  rw [prefixBox, checked_prefix3_49]
  decide +kernel

private def prefix3_51 : Box :=
  dataBox (729605793553) (2261066070015) (-290535836522) (1283498179008) (by decide) (by decide)

private theorem checked_prefix3_51 : prefixBox cfg cell3 51 = .ok prefix3_51 := by
  rw [prefixBox, checked_prefix3_50]
  decide +kernel

private def prefix3_52 : Box :=
  dataBox (732438589233) (2281493651106) (-289778794171) (1288957292374) (by decide) (by decide)

private theorem checked_prefix3_52 : prefixBox cfg cell3 52 = .ok prefix3_52 := by
  rw [prefixBox, checked_prefix3_51]
  decide +kernel

private def prefix3_53 : Box :=
  dataBox (734489383616) (2296423662109) (-304182638482) (1286978772691) (by decide) (by decide)

private theorem checked_prefix3_53 : prefixBox cfg cell3 53 = .ok prefix3_53 := by
  rw [prefixBox, checked_prefix3_52]
  decide +kernel

private def prefix3_54 : Box :=
  dataBox (730323718501) (2295856787676) (-324113292649) (1284266554899) (by decide) (by decide)

private theorem checked_prefix3_54 : prefixBox cfg cell3 54 = .ok prefix3_54 := by
  rw [prefixBox, checked_prefix3_53]
  decide +kernel

private def prefix3_55 : Box :=
  dataBox (711713788326) (2293347426561) (-331415049296) (1283281987436) (by decide) (by decide)

private theorem checked_prefix3_55 : prefixBox cfg cell3 55 = .ok prefix3_55 := by
  rw [prefixBox, checked_prefix3_54]
  decide +kernel

private def prefix3_56 : Box :=
  dataBox (695499041073) (2291180640983) (-329935538439) (1294353640512) (by decide) (by decide)

private theorem checked_prefix3_56 : prefixBox cfg cell3 56 = .ok prefix3_56 := by
  rw [prefixBox, checked_prefix3_55]
  decide +kernel

private def prefix3_57 : Box :=
  dataBox (695191941353) (2291139965275) (-327380882322) (1313640875745) (by decide) (by decide)

private theorem checked_prefix3_57 : prefixBox cfg cell3 57 = .ok prefix3_57 := by
  rw [prefixBox, checked_prefix3_56]
  decide +kernel

private def prefix3_58 : Box :=
  dataBox (697177209076) (2306259315792) (-325879292587) (1325076645691) (by decide) (by decide)

private theorem checked_prefix3_58 : prefixBox cfg cell3 58 = .ok prefix3_58 := by
  rw [prefixBox, checked_prefix3_57]
  decide +kernel

private def prefix3_59 : Box :=
  dataBox (699511865676) (2324192154289) (-330949402474) (1324416573996) (by decide) (by decide)

private theorem checked_prefix3_59 : prefixBox cfg cell3 59 = .ok prefix3_59 := by
  rw [prefixBox, checked_prefix3_58]
  decide +kernel

private def prefix3_60 : Box :=
  dataBox (700406216452) (2331119769114) (-347914689609) (1322226365325) (by decide) (by decide)

private theorem checked_prefix3_60 : prefixBox cfg cell3 60 = .ok prefix3_60 := by
  rw [prefixBox, checked_prefix3_59]
  decide +kernel

private def prefix3_61 : Box :=
  dataBox (691687163843) (2330003409645) (-363690335012) (1320206501626) (by decide) (by decide)

private theorem checked_prefix3_61 : prefixBox cfg cell3 61 = .ok prefix3_61 := by
  rw [prefixBox, checked_prefix3_60]
  decide +kernel

private def prefix3_62 : Box :=
  dataBox (674264983335) (2327790791868) (-367001630198) (1319785967938) (by decide) (by decide)

private theorem checked_prefix3_62 : prefixBox cfg cell3 62 = .ok prefix3_62 := by
  rw [prefixBox, checked_prefix3_61]
  decide +kernel

private def prefix3_63 : Box :=
  dataBox (660652702267) (2326075806707) (-365625542569) (1330708332156) (by decide) (by decide)

private theorem checked_prefix3_63 : prefixBox cfg cell3 63 = .ok prefix3_63 := by
  rw [prefixBox, checked_prefix3_62]
  decide +kernel

private def prefix3_64 : Box :=
  dataBox (659893798593) (2325980944406) (-363480155473) (1347871433783) (by decide) (by decide)

private theorem checked_prefix3_64 : prefixBox cfg cell3 64 = .ok prefix3_64 := by
  rw [prefixBox, checked_prefix3_63]
  decide +kernel

private def prefix3_65 : Box :=
  dataBox (661388682264) (2338033084376) (-362007939985) (1359740818038) (by decide) (by decide)

private theorem checked_prefix3_65 : prefixBox cfg cell3 65 = .ok prefix3_65 := by
  rw [prefixBox, checked_prefix3_64]
  decide +kernel

private def prefix3_66 : Box :=
  dataBox (663437062033) (2354674200511) (-362785397067) (1359645120069) (by decide) (by decide)

private theorem checked_prefix3_66 : prefixBox cfg cell3 66 = .ok prefix3_66 := by
  rw [prefixBox, checked_prefix3_65]
  decide +kernel

private def prefix3_67 : Box :=
  dataBox (664747046381) (2365396887203) (-375208462460) (1358127401500) (by decide) (by decide)

private theorem checked_prefix3_67 : prefixBox cfg cell3 67 = .ok prefix3_67 := by
  rw [prefixBox, checked_prefix3_66]
  decide +kernel

private def prefix3_68 : Box :=
  dataBox (663326808629) (2365224658696) (-391315259226) (1356174166056) (by decide) (by decide)

private theorem checked_prefix3_68 : prefixBox cfg cell3 68 = .ok prefix3_68 := by
  rw [prefixBox, checked_prefix3_67]
  decide +kernel

private def prefix3_69 : Box :=
  dataBox (651082932837) (2363750670231) (-401513805320) (1354946406226) (by decide) (by decide)

private theorem checked_prefix3_69 : prefixBox cfg cell3 69 = .ok prefix3_69 := by
  rw [prefixBox, checked_prefix3_68]
  decide +kernel

private def prefix3_70 : Box :=
  dataBox (635429015168) (2361879670549) (-401359136135) (1356240471640) (by decide) (by decide)

private theorem checked_prefix3_70 : prefixBox cfg cell3 70 = .ok prefix3_70 := by
  rw [prefixBox, checked_prefix3_69]
  decide +kernel

private def prefix3_71 : Box :=
  dataBox (625190435139) (2360664575501) (-399980270859) (1367859003184) (by decide) (by decide)

private theorem checked_prefix3_71 : prefixBox cfg cell3 71 = .ok prefix3_71 := by
  rw [prefixBox, checked_prefix3_70]
  decide +kernel

private def prefix3_72 : Box :=
  dataBox (625249653137) (2361167061317) (-398181541642) (1383121730881) (by decide) (by decide)

private theorem checked_prefix3_72 : prefixBox cfg cell3 72 = .ok prefix3_72 := by
  rw [prefixBox, checked_prefix3_71]
  decide +kernel

private def prefix3_73 : Box :=
  dataBox (626486606441) (2371735597255) (-396925520793) (1393853180877) (by decide) (by decide)

private theorem checked_prefix3_73 : prefixBox cfg cell3 73 = .ok prefix3_73 := by
  rw [prefixBox, checked_prefix3_72]
  decide +kernel

private def prefix3_74 : Box :=
  dataBox (628210905999) (2386568583151) (-396824808723) (1394719541637) (by decide) (by decide)

private theorem checked_prefix3_74 : prefixBox cfg cell3 74 = .ok prefix3_74 := by
  rw [prefixBox, checked_prefix3_73]
  decide +kernel

private def prefix3_75 : Box :=
  dataBox (629541435434) (2398091307936) (-405888307362) (1393672979305) (by decide) (by decide)

private theorem checked_prefix3_75 : prefixBox cfg cell3 75 = .ok prefix3_75 := by
  rw [prefixBox, checked_prefix3_74]
  decide +kernel

private def prefix3_76 : Box :=
  dataBox (629853303606) (2400810115402) (-420097801023) (1392043039021) (by decide) (by decide)

private theorem checked_prefix3_76 : prefixBox cfg cell3 76 = .ok prefix3_76 := by
  rw [prefixBox, checked_prefix3_75]
  decide +kernel

private def prefix3_77 : Box :=
  dataBox (622797357208) (2400006016352) (-432512074411) (1390628301852) (by decide) (by decide)

private theorem checked_prefix3_77 : prefixBox cfg cell3 77 = .ok prefix3_77 := by
  rw [prefixBox, checked_prefix3_76]
  decide +kernel

private def prefix3_78 : Box :=
  dataBox (609590679260) (2398510655512) (-437440518834) (1390070266271) (by decide) (by decide)

private theorem checked_prefix3_78 : prefixBox cfg cell3 78 = .ok prefix3_78 := by
  rw [prefixBox, checked_prefix3_77]
  decide +kernel

private def prefix3_79 : Box :=
  dataBox (596427100278) (2397029638137) (-436932017234) (1394589935004) (by decide) (by decide)

private theorem checked_prefix3_79 : prefixBox cfg cell3 79 = .ok prefix3_79 := by
  rw [prefixBox, checked_prefix3_78]
  decide +kernel

private def prefix3_80 : Box :=
  dataBox (589117134172) (2396212359729) (-435630772454) (1406228627183) (by decide) (by decide)

private theorem checked_prefix3_80 : prefixBox cfg cell3 80 = .ok prefix3_80 := by
  rw [prefixBox, checked_prefix3_79]
  decide +kernel

private theorem checked_3 : positiveCheck cfg 80
    (input cfg (1) (3 / 2) 54 (by norm_num)) false = true := by
  change positiveCheck cfg 80 cell3 false = true
  unfold positiveCheck evaluate
  rw [checked_prefix3_80]
  decide +kernel

/-- Actual zeta has positive real part throughout this closed contour cell. -/
theorem positive {x : ℝ} (hx : x ∈ Set.Icc (1 : ℝ) (3 / 2)) :
    0 < (riemannZeta ((x : ℂ) + 54 * Complex.I)).re := by
  simpa using positive_of_check checked_3
    (mem_input (by decide) (by norm_num : (1 : ℚ) ≤ 3 / 2)
      (x := x) (by simpa using hx.1) (by simpa using hx.2))

end RiemannGaussian.ZetaHeightFiftyFour.Cell3
