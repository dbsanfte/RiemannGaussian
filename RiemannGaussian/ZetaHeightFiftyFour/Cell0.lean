/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaHorizontalCertificate

/-!
# Checked height-fifty-four contour cell 0

Every literal prefix checkpoint is checked in the kernel. This independent
module bounds compiler memory while retaining the complete original
Euler--Maclaurin expression, rounding errors and analytic tail.
-/

namespace RiemannGaussian.ZetaHeightFiftyFour.Cell0
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


private def cell0 : Box := input cfg (1 / 2) (5 / 8) 54 (by norm_num)

private def prefix0_1 : Box :=
  dataBox (1099511627776) (1099511627776) (0) (0) (by decide) (by decide)

private theorem checked_prefix0_1 : prefixBox cfg cell0 1 = .ok prefix0_1 := by
  decide +kernel

private def prefix0_2 : Box :=
  dataBox (1786786068158) (1848989726216) (189590424570) (206749848530) (by decide) (by decide)

private theorem checked_prefix0_2 : prefixBox cfg cell0 2 = .ok prefix0_2 := by
  rw [prefixBox, checked_prefix0_1]
  decide +kernel

private def prefix0_3 : Box :=
  dataBox (1193845769768) (1332132296201) (-37118919385) (9130640580) (by decide) (by decide)

private theorem checked_prefix0_3 : prefixBox cfg cell0 3 = .ok prefix0_3 := by
  rw [prefixBox, checked_prefix0_2]
  decide +kernel

private def prefix0_4 : Box :=
  dataBox (1590750729788) (1804134517309) (199896587599) (290991203814) (by decide) (by decide)

private theorem checked_prefix0_4 : prefixBox cfg cell0 4 = .ok prefix0_4 := by
  rw [prefixBox, checked_prefix0_3]
  decide +kernel

private def prefix0_5 : Box :=
  dataBox (1789100453810) (2046685427783) (549680600172) (718722712283) (by decide) (by decide)

private theorem checked_prefix0_5 : prefixBox cfg cell0 5 = .ok prefix0_5 := by
  rw [prefixBox, checked_prefix0_4]
  decide +kernel

private def prefix0_6 : Box :=
  dataBox (1427554781960) (1757687873667) (283649756278) (506073893285) (by decide) (by decide)

private theorem checked_prefix0_6 : prefixBox cfg cell0 6 = .ok prefix0_6 := by
  rw [prefixBox, checked_prefix0_5]
  decide +kernel

private def prefix0_7 : Box :=
  dataBox (1359620947636) (1704422058543) (605113474690) (916060115918) (by decide) (by decide)

private theorem checked_prefix0_7 : prefixBox cfg cell0 7 = .ok prefix0_7 := by
  rw [prefixBox, checked_prefix0_6]
  decide +kernel

private def prefix0_8 : Box :=
  dataBox (1566846361638) (1973160201651) (821704253451) (1196943645488) (by decide) (by decide)

private theorem checked_prefix0_8 : prefixBox cfg cell0 8 = .ok prefix0_8 := by
  rw [prefixBox, checked_prefix0_7]
  decide +kernel

private def prefix0_9 : Box :=
  dataBox (1774291425687) (2246173284738) (1007497589258) (1441461463954) (by decide) (by decide)

private theorem checked_prefix0_9 : prefixBox cfg cell0 9 = .ok prefix0_9 := by
  rw [prefixBox, checked_prefix0_8]
  decide +kernel

private def prefix0_10 : Box :=
  dataBox (1837960585227) (2331077516813) (1260339679606) (1778631853357) (by decide) (by decide)

private theorem checked_prefix0_10 : prefixBox cfg cell0 10 = .ok prefix0_10 := by
  rw [prefixBox, checked_prefix0_9]
  decide +kernel

private def prefix0_11 : Box :=
  dataBox (1580401515378) (2140222921608) (1415006856526) (1987355856809) (by decide) (by decide)

private theorem checked_prefix0_11 : prefixBox cfg cell0 11 = .ok prefix0_11 := by
  rw [prefixBox, checked_prefix0_10]
  decide +kernel

private def prefix0_12 : Box :=
  dataBox (1383979086198) (1996245873481) (1165683618884) (1804602654674) (by decide) (by decide)

private theorem checked_prefix0_12 : prefixBox cfg cell0 12 = .ok prefix0_12 := by
  rw [prefixBox, checked_prefix0_11]
  decide +kernel

private def prefix0_13 : Box :=
  dataBox (1596833623612) (2289555180319) (1082233339511) (1744042813720) (by decide) (by decide)

private theorem checked_prefix0_13 : prefixBox cfg cell0 13 = .ok prefix0_13 := by
  rw [prefixBox, checked_prefix0_12]
  decide +kernel

private def prefix0_14 : Box :=
  dataBox (1473433823357) (2200829722399) (1273986743125) (2010734309717) (by decide) (by decide)

private theorem checked_prefix0_14 : prefixBox cfg cell0 14 = .ok prefix0_14 := by
  rw [prefixBox, checked_prefix0_13]
  decide +kernel

private def prefix0_15 : Box :=
  dataBox (1430826265504) (2170457628235) (993309588717) (1810658036263) (by decide) (by decide)

private theorem checked_prefix0_15 : prefixBox cfg cell0 15 = .ok prefix0_15 := by
  rw [prefixBox, checked_prefix0_14]
  decide +kernel

private def prefix0_16 : Box :=
  dataBox (1523010084992) (2300825272985) (1164426706114) (2052654225811) (by decide) (by decide)

private theorem checked_prefix0_16 : prefixBox cfg cell0 16 = .ok prefix0_16 := by
  rw [prefixBox, checked_prefix0_15]
  decide +kernel

private def prefix0_17 : Box :=
  dataBox (1366705713074) (2191135839108) (948365942806) (1901029630075) (by decide) (by decide)

private theorem checked_prefix0_17 : prefixBox cfg cell0 17 = .ok prefix0_17 := by
  rw [prefixBox, checked_prefix0_16]
  decide +kernel

private def prefix0_18 : Box :=
  dataBox (1464337279858) (2331255611238) (1100270301403) (2119041115578) (by decide) (by decide)

private theorem checked_prefix0_18 : prefixBox cfg cell0 18 = .ok prefix0_18 := by
  rw [prefixBox, checked_prefix0_17]
  decide +kernel

private def prefix0_19 : Box :=
  dataBox (1378014507426) (2271513458764) (863255382006) (1955008056517) (by decide) (by decide)

private theorem checked_prefix0_19 : prefixBox cfg cell0 19 = .ok prefix0_19 := by
  rw [prefixBox, checked_prefix0_18]
  decide +kernel

private def prefix0_20 : Box :=
  dataBox (1372488326989) (2267713381510) (1032278576405) (2200804239860) (by decide) (by decide)

private theorem checked_prefix0_20 : prefixBox cfg cell0 20 = .ok prefix0_20 := by
  rw [prefixBox, checked_prefix0_19]
  decide +kernel

private def prefix0_21 : Box :=
  dataBox (1455305321200) (2388883906020) (825190162115) (2059264525130) (by decide) (by decide)

private theorem checked_prefix0_21 : prefixBox cfg cell0 21 = .ok prefix0_21 := by
  rw [prefixBox, checked_prefix0_20]
  decide +kernel

private def prefix0_22 : Box :=
  dataBox (1240493089835) (2242916468068) (888958996006) (2153109643643) (by decide) (by decide)

private theorem checked_prefix0_22 : prefixBox cfg cell0 22 = .ok prefix0_22 := by
  rw [prefixBox, checked_prefix0_21]
  decide +kernel

private def prefix0_23 : Box :=
  dataBox (1387092487100) (2459860737888) (939060854583) (2227252614913) (by decide) (by decide)

private theorem checked_prefix0_23 : prefixBox cfg cell0 23 = .ok prefix0_23 := by
  rw [prefixBox, checked_prefix0_22]
  decide +kernel

private def prefix0_24 : Box :=
  dataBox (1300084056910) (2401377064580) (732175723360) (2088192440676) (by decide) (by decide)

private theorem checked_prefix0_24 : prefixBox cfg cell0 24 = .ok prefix0_24 := by
  rw [prefixBox, checked_prefix0_23]
  decide +kernel

private def prefix0_25 : Box :=
  dataBox (1187194550671) (2325883342443) (858376408347) (2276906533909) (by decide) (by decide)

private theorem checked_prefix0_25 : prefixBox cfg cell0 25 = .ok prefix0_25 := by
  rw [prefixBox, checked_prefix0_24]
  decide +kernel

private def prefix0_26 : Box :=
  dataBox (1330686488572) (2541508371231) (856646085589) (2275755074216) (by decide) (by decide)

private theorem checked_prefix0_26 : prefixBox cfg cell0 26 = .ok prefix0_26 := by
  rw [prefixBox, checked_prefix0_25]
  decide +kernel

private def prefix0_27 : Box :=
  dataBox (1233874405750) (2477386108413) (668490656039) (2151132656804) (by decide) (by decide)

private theorem checked_prefix0_27 : prefixBox cfg cell0 27 = .ok prefix0_27 := by
  rw [prefixBox, checked_prefix0_26]
  decide +kernel

private def prefix0_28 : Box :=
  dataBox (1099611270484) (2388861946127) (773051354806) (2309718122200) (by decide) (by decide)

private theorem checked_prefix0_28 : prefixBox cfg cell0 28 = .ok prefix0_28 := by
  rw [prefixBox, checked_prefix0_27]
  decide +kernel

private def prefix0_29 : Box :=
  dataBox (1224159347626) (2578592292462) (822566382523) (2385146875170) (by decide) (by decide)

private theorem checked_prefix0_29 : prefixBox cfg cell0 29 = .ok prefix0_29 := by
  rw [prefixBox, checked_prefix0_28]
  decide +kernel

private def prefix0_30 : Box :=
  dataBox (1239674018609) (2602326974641) (623231989421) (2254847599127) (by decide) (by decide)

private theorem checked_prefix0_30 : prefixBox cfg cell0 30 = .ok prefix0_30 := by
  rw [prefixBox, checked_prefix0_29]
  decide +kernel

private def prefix0_31 : Box :=
  dataBox (1042848805695) (2474194182256) (633677648960) (2270893297074) (by decide) (by decide)

private theorem checked_prefix0_31 : prefixBox cfg cell0 31 = .ok prefix0_31 := by
  rw [prefixBox, checked_prefix0_30]
  decide +kernel

private def prefix0_32 : Box :=
  dataBox (1070964384648) (2517554373461) (756533639623) (2460363176224) (by decide) (by decide)

private theorem checked_prefix0_32 : prefixBox cfg cell0 32 = .ok prefix0_32 := by
  rw [prefixBox, checked_prefix0_31]
  decide +kernel

private def prefix0_33 : Box :=
  dataBox (1188480056599) (2699486775607) (697080125448) (2421960360666) (by decide) (by decide)

private theorem checked_prefix0_33 : prefixBox cfg cell0 33 = .ok prefix0_33 := by
  rw [prefixBox, checked_prefix0_32]
  decide +kernel

private def prefix0_34 : Box :=
  dataBox (1122563349820) (2657067792706) (520411955034) (2308270084664) (by decide) (by decide)

private theorem checked_prefix0_34 : prefixBox cfg cell0 34 = .ok prefix0_34 := by
  rw [prefixBox, checked_prefix0_33]
  decide +kernel

private def prefix0_35 : Box :=
  dataBox (948084551433) (2545192567814) (561458069390) (2372284992555) (by decide) (by decide)

private theorem checked_prefix0_35 : prefixBox cfg cell0 35 = .ok prefix0_35 := by
  rw [prefixBox, checked_prefix0_34]
  decide +kernel

private def prefix0_36 : Box :=
  dataBox (982918252755) (2599710292990) (673244056893) (2547239554793) (by decide) (by decide)

private theorem checked_prefix0_36 : prefixBox cfg cell0 36 = .ok prefix0_36 := by
  rw [prefixBox, checked_prefix0_35]
  decide +kernel

private def prefix0_37 : Box :=
  dataBox (1095469421863) (2776466731064) (635417683031) (2523153305860) (by decide) (by decide)

private theorem checked_prefix0_37 : prefixBox cfg cell0 37 = .ok prefix0_37 := by
  rw [prefixBox, checked_prefix0_36]
  decide +kernel

private def prefix0_38 : Box :=
  dataBox (1081195594524) (2767408027011) (457625378934) (2410319326391) (by decide) (by decide)

private theorem checked_prefix0_38 : prefixBox cfg cell0 38 = .ok prefix0_38 := by
  rw [prefixBox, checked_prefix0_37]
  decide +kernel

private def prefix0_39 : Box :=
  dataBox (905814178889) (2656464942181) (442150343891) (2400530155475) (by decide) (by decide)

private theorem checked_prefix0_39 : prefixBox cfg cell0 39 = .ok prefix0_39 := by
  rw [prefixBox, checked_prefix0_38]
  decide +kernel

private def prefix0_40 : Box :=
  dataBox (855828279880) (2624944699163) (547146828064) (2567037109073) (by decide) (by decide)

private theorem checked_prefix0_40 : prefixBox cfg cell0 40 = .ok prefix0_40 := by
  rw [prefixBox, checked_prefix0_39]
  decide +kernel

private def prefix0_41 : Box :=
  dataBox (949018009821) (2773184928164) (601627941938) (2653702180767) (by decide) (by decide)

private theorem checked_prefix0_41 : prefixBox cfg cell0 41 = .ok prefix0_41 := by
  rw [prefixBox, checked_prefix0_40]
  decide +kernel

private def prefix0_42 : Box :=
  dataBox (1025190539761) (2894720837513) (483251522125) (2579509864020) (by decide) (by decide)

private theorem checked_prefix0_42 : prefixBox cfg cell0 42 = .ok prefix0_42 := by
  rw [prefixBox, checked_prefix0_41]
  decide +kernel

private def prefix0_43 : Box :=
  dataBox (948942485267) (2847072813788) (333916999607) (2486189479456) (by decide) (by decide)

private theorem checked_prefix0_43 : prefixBox cfg cell0 43 = .ok prefix0_43 := by
  rw [prefixBox, checked_prefix0_42]
  decide +kernel

private def prefix0_44 : Box :=
  dataBox (784870064761) (2744836837328) (348607743124) (2509765849619) (by decide) (by decide)

private theorem checked_prefix0_44 : prefixBox cfg cell0 44 = .ok prefix0_44 := by
  rw [prefixBox, checked_prefix0_43]
  decide +kernel

private def prefix0_45 : Box :=
  dataBox (749974186314) (2723153706503) (448118306353) (2669913606861) (by decide) (by decide)

private theorem checked_prefix0_45 : prefixBox cfg cell0 45 = .ok prefix0_45 := by
  rw [prefixBox, checked_prefix0_44]
  decide +kernel

private def prefix0_46 : Box :=
  dataBox (832970290075) (2857091297488) (504713950498) (2761246636417) (by decide) (by decide)

private theorem checked_prefix0_46 : prefixBox cfg cell0 46 = .ok prefix0_46 := by
  rw [prefixBox, checked_prefix0_45]
  decide +kernel

private def prefix0_47 : Box :=
  dataBox (916795164827) (2992730488526) (419134513822) (2708358646961) (by decide) (by decide)

private theorem checked_prefix0_47 : prefixBox cfg cell0 47 = .ok prefix0_47 := by
  rw [prefixBox, checked_prefix0_46]
  decide +kernel

private def prefix0_48 : Box :=
  dataBox (896388420423) (2980152312753) (261751140208) (2611351531809) (by decide) (by decide)

private theorem checked_prefix0_48 : prefixBox cfg cell0 48 = .ok prefix0_48 := by
  rw [prefixBox, checked_prefix0_47]
  decide +kernel

private def prefix0_49 : Box :=
  dataBox (747709931401) (2888746588780) (211088747270) (2580204937055) (by decide) (by decide)

private theorem checked_prefix0_49 : prefixBox cfg cell0 49 = .ok prefix0_49 := by
  rw [prefixBox, checked_prefix0_48]
  decide +kernel

private def prefix0_50 : Box :=
  dataBox (635273807015) (2819796572218) (276955815855) (2687613722558) (by decide) (by decide)

private theorem checked_prefix0_50 : prefixBox cfg cell0 50 = .ok prefix0_50 := by
  rw [prefixBox, checked_prefix0_49]
  decide +kernel

private def prefix0_51 : Box :=
  dataBox (659584477128) (2859538007442) (367946260431) (2836358645511) (by decide) (by decide)

private theorem checked_prefix0_51 : prefixBox cfg cell0 51 = .ok prefix0_51 := by
  rw [prefixBox, checked_prefix0_50]
  decide +kernel

private def prefix0_52 : Box :=
  dataBox (749475884059) (3006843389445) (391969031480) (2875724871797) (by decide) (by decide)

private theorem checked_prefix0_52 : prefixBox cfg cell0 52 = .ok prefix0_52 := by
  rw [prefixBox, checked_prefix0_51]
  decide +kernel

private def prefix0_53 : Box :=
  dataBox (815646245362) (3115535510113) (287107462150) (2811886505879) (by decide) (by decide)

private theorem checked_prefix0_53 : prefixBox cfg cell0 53 = .ok prefix0_53 := by
  rw [prefixBox, checked_prefix0_52]
  decide +kernel

private def prefix0_54 : Box :=
  dataBox (785034983474) (3096943283207) (140647663415) (2722931764550) (by decide) (by decide)

private theorem checked_prefix0_54 : prefixBox cfg cell0 54 = .ok prefix0_54 := by
  rw [prefixBox, checked_prefix0_53]
  decide +kernel

private def prefix0_55 : Box :=
  dataBox (647020047575) (3013309735887) (86496386857) (2690117488018) (by decide) (by decide)

private theorem checked_prefix0_55 : prefixBox cfg cell0 55 = .ok prefix0_55 := by
  rw [prefixBox, checked_prefix0_54]
  decide +kernel

private def prefix0_56 : Box :=
  dataBox (525679990004) (2939946165244) (136590037280) (2772970152985) (by decide) (by decide)

private theorem checked_prefix0_56 : prefixBox cfg cell0 56 = .ok prefix0_56 := by
  rw [prefixBox, checked_prefix0_55]
  decide +kernel

private def prefix0_57 : Box :=
  dataBox (523361437966) (2938547461850) (224436230706) (2918585585593) (by decide) (by decide)

private theorem checked_prefix0_57 : prefixBox cfg cell0 57 = .ok prefix0_57 := by
  rw [prefixBox, checked_prefix0_56]
  decide +kernel

private def prefix0_58 : Box :=
  dataBox (592675057301) (3053693004801) (276862721150) (3005677814721) (by decide) (by decide)

private theorem checked_prefix0_58 : prefixBox cfg cell0 58 = .ok prefix0_58 := by
  rw [prefixBox, checked_prefix0_57]
  decide +kernel

private def prefix0_59 : Box :=
  dataBox (675415629688) (3191437750857) (237918468186) (2982284777019) (by decide) (by decide)

private theorem checked_prefix0_59 : prefixBox cfg cell0 59 = .ok prefix0_59 := by
  rw [prefixBox, checked_prefix0_58]
  decide +kernel

private def prefix0_60 : Box :=
  dataBox (707581124223) (3245098824502) (106505919216) (2903513508600) (by decide) (by decide)

private theorem checked_prefix0_60 : prefixBox cfg cell0 60 = .ok prefix0_60 := by
  rw [prefixBox, checked_prefix0_59]
  decide +kernel

private def prefix0_61 : Box :=
  dataBox (639483146471) (3204363829543) (-16705810077) (2829810422905) (by decide) (by decide)

private theorem checked_prefix0_61 : prefixBox cfg cell0 61 = .ok prefix0_61 := by
  rw [prefixBox, checked_prefix0_60]
  decide +kernel

private def prefix0_62 : Box :=
  dataBox (502300760084) (3122470387292) (-42778974421) (2814245623750) (by decide) (by decide)

private theorem checked_prefix0_62 : prefixBox cfg cell0 62 = .ok prefix0_62 := by
  rw [prefixBox, checked_prefix0_61]
  decide +kernel

private def prefix0_63 : Box :=
  dataBox (394256628734) (3058100411129) (8870876488) (2900939202017) (by decide) (by decide)

private theorem checked_prefix0_63 : prefixBox cfg cell0 63 = .ok prefix0_63 := by
  rw [prefixBox, checked_prefix0_62]
  decide +kernel

private def prefix0_64 : Box :=
  dataBox (388185399348) (3054490461555) (90512783810) (3038244014902) (by decide) (by decide)

private theorem checked_prefix0_64 : prefixBox cfg cell0 64 = .ok prefix0_64 := by
  rw [prefixBox, checked_prefix0_63]
  decide +kernel

private def prefix0_65 : Box :=
  dataBox (445849641146) (3151657920322) (147302614013) (3133938049984) (by decide) (by decide)

private theorem checked_prefix0_65 : prefixBox cfg cell0 65 = .ok prefix0_65 := by
  rw [prefixBox, checked_prefix0_64]
  decide +kernel

private def prefix0_66 : Box :=
  dataBox (525927310069) (3286850986771) (140986522830) (3130196912509) (by decide) (by decide)

private theorem checked_prefix0_66 : prefixBox cfg cell0 66 = .ok prefix0_66 := by
  rw [prefixBox, checked_prefix0_65]
  decide +kernel

private def prefix0_67 : Box :=
  dataBox (577817057871) (3374619959922) (39299350175) (3070078611195) (by decide) (by decide)

private theorem checked_prefix0_67 : prefixBox cfg cell0 67 = .ok prefix0_67 := by
  rw [prefixBox, checked_prefix0_66]
  decide +kernel

private def prefix0_68 : Box :=
  dataBox (566105477357) (3367708809645) (-93520698412) (2991699579085) (by decide) (by decide)

private theorem checked_prefix0_68 : prefixBox cfg cell0 68 = .ok prefix0_68 := by
  rw [prefixBox, checked_prefix0_67]
  decide +kernel

private def prefix0_69 : Box :=
  dataBox (464400206623) (3307800503555) (-178236184679) (2941798909266) (by decide) (by decide)

private theorem checked_prefix0_69 : prefixBox cfg cell0 69 = .ok prefix0_69 := by
  rw [prefixBox, checked_prefix0_68]
  decide +kernel

private def prefix0_70 : Box :=
  dataBox (333430135030) (3230792742000) (-171870214724) (2952625837292) (by decide) (by decide)

private theorem checked_prefix0_70 : prefixBox cfg cell0 70 = .ok prefix0_70 := by
  rw [prefixBox, checked_prefix0_69]
  decide +kernel

private def prefix0_71 : Box :=
  dataBox (247158326329) (3180156518623) (-114409252960) (3050525324125) (by decide) (by decide)

private theorem checked_prefix0_71 : prefixBox cfg cell0 71 = .ok prefix0_71 := by
  rw [prefixBox, checked_prefix0_70]
  decide +kernel

private def prefix0_72 : Box :=
  dataBox (249656482926) (3184420252148) (-38528483822) (3180033863050) (by decide) (by decide)

private theorem checked_prefix0_72 : prefixBox cfg cell0 72 = .ok prefix0_72 := by
  rw [prefixBox, checked_prefix0_71]
  decide +kernel

private def prefix0_73 : Box :=
  dataBox (302471911526) (3274717862698) (15101090763) (3271723411916) (by decide) (by decide)

private theorem checked_prefix0_73 : prefixBox cfg cell0 73 = .ok prefix0_73 := by
  rw [prefixBox, checked_prefix0_72]
  decide +kernel

private def prefix0_74 : Box :=
  dataBox (376977778504) (3402316031934) (19452794101) (3279176128959) (by decide) (by decide)

private theorem checked_prefix0_74 : prefixBox cfg cell0 74 = .ok prefix0_74 := by
  rw [prefixBox, checked_prefix0_73]
  decide +kernel

private def prefix0_75 : Box :=
  dataBox (435148318189) (3502105755680) (-59039406510) (3233420586783) (by decide) (by decide)

private theorem checked_prefix0_75 : prefixBox cfg cell0 75 = .ok prefix0_75 := by
  rw [prefixBox, checked_prefix0_74]
  decide +kernel

private def prefix0_76 : Box :=
  dataBox (448942087228) (3525807769639) (-182914900210) (3161329165539) (by decide) (by decide)

private theorem checked_prefix0_76 : prefixBox cfg cell0 76 = .ok prefix0_76 := by
  rw [prefixBox, checked_prefix0_75]
  decide +kernel

private def prefix0_77 : Box :=
  dataBox (387026408927) (3489833752737) (-291849706983) (3098036243054) (by decide) (by decide)

private theorem checked_prefix0_77 : prefixBox cfg cell0 77 = .ok prefix0_77 := by
  rw [prefixBox, checked_prefix0_76]
  decide +kernel

private def prefix0_78 : Box :=
  dataBox (270388187566) (3422174253114) (-335376549524) (3072787214750) (by decide) (by decide)

private theorem checked_prefix0_78 : prefixBox cfg cell0 78 = .ok prefix0_78 := by
  rw [prefixBox, checked_prefix0_77]
  decide +kernel

private def prefix0_79 : Box :=
  dataBox (153387738458) (3354412620771) (-312110854560) (3112958909114) (by decide) (by decide)

private theorem checked_prefix0_79 : prefixBox cfg cell0 79 = .ok prefix0_79 := by
  rw [prefixBox, checked_prefix0_78]
  decide +kernel

private def prefix0_80 : Box :=
  dataBox (88005414020) (3316605486050) (-251915532819) (3217058536538) (by decide) (by decide)

private theorem checked_prefix0_80 : prefixBox cfg cell0 80 = .ok prefix0_80 := by
  rw [prefixBox, checked_prefix0_79]
  decide +kernel

private theorem checked_0 : positiveCheck cfg 80
    (input cfg (1 / 2) (5 / 8) 54 (by norm_num)) false = true := by
  change positiveCheck cfg 80 cell0 false = true
  unfold positiveCheck evaluate
  rw [checked_prefix0_80]
  decide +kernel

/-- Actual zeta has positive real part throughout this closed contour cell. -/
theorem positive {x : ℝ} (hx : x ∈ Set.Icc (1 / 2 : ℝ) (5 / 8)) :
    0 < (riemannZeta ((x : ℂ) + 54 * Complex.I)).re := by
  simpa using positive_of_check checked_0
    (mem_input (by decide) (by norm_num : (1 / 2 : ℚ) ≤ 5 / 8)
      (x := x) (by simpa using hx.1) (by simpa using hx.2))

end RiemannGaussian.ZetaHeightFiftyFour.Cell0
