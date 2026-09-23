/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaBlockCacheCheck
import RiemannGaussian.ZetaBlockBatchHardy

/-!
# Checked shared data for the low-height Hardy lattice

Every one of the eighty original Dirichlet terms and its phase increment
is checked independently in the kernel. The cache starts at height 14,
with unit spacing and center 34. Sample checks still pay the full analytic
error and prove their own sign; these data alone assert no zero count.
-/

namespace RiemannGaussian.ZetaHardyBatchData
open LeanCert.Core LeanCert.Engine CertifiedComplexInterval

/-- Numerical precision and Taylor depth for this finite batch. -/
def cfg : DyadicConfig := {precision := -40, taylorDepth := 20}
/-- The exact center of the cached lattice. -/
def center : Box := rational cfg.precision (1 / 2) 34
private def initial : Box := rational cfg.precision 0 (-20)
private def step : Box := rational cfg.precision 0 1

private def dataInterval (a b : ℤ) (hab : a ≤ b) : IntervalDyadic :=
  ⟨⟨a, -40⟩, ⟨b, -40⟩, by
    change (a : ℚ) / 1099511627776 ≤ (b : ℚ) / 1099511627776
    exact div_le_div_of_nonneg_right (by exact_mod_cast hab) (by norm_num)⟩

private def dataBox (a b c d : ℤ) (hab : a ≤ b) (hcd : c ≤ d) : Box :=
  ⟨dataInterval a b hab, dataInterval c d hcd⟩

private def pair80 : Box × Box :=
  (dataBox (10720059282) (10720068210) (122460817940) (122460826504) (by decide) (by decide),
    dataBox (-356665964429) (-356665956968) (1040055385696) (1040055392213) (by decide) (by decide))

private theorem checked_pair80 :
    (ZetaBlockCacheCheck.powerCheck cfg 80
        (neg (add cfg.precision center initial)) pair80.1 &&
      ZetaBlockCacheCheck.powerCheck cfg 80 (neg step) pair80.2) = true := by
  decide +kernel

private def pair79 : Box × Box :=
  (dataBox (-10968928176) (-10968918051) (123217450286) (123217459603) (by decide) (by decide),
    dataBox (-369720033179) (-369720025662) (1035486799852) (1035486806412) (by decide) (by decide))

private theorem checked_pair79 :
    (ZetaBlockCacheCheck.powerCheck cfg 79
        (neg (add cfg.precision center initial)) pair79.1 &&
      ZetaBlockCacheCheck.powerCheck cfg 79 (neg step) pair79.2) = true := by
  decide +kernel

private def pair78 : Box × Box :=
  (dataBox (-32862671179) (-32862659741) (120079527662) (120079537869) (by decide) (by decide),
    dataBox (-382880770316) (-382880762742) (1030693034531) (1030693041135) (by decide) (by decide))

private theorem checked_pair78 :
    (ZetaBlockCacheCheck.powerCheck cfg 78
        (neg (add cfg.precision center initial)) pair78.1 &&
      ZetaBlockCacheCheck.powerCheck cfg 78 (neg step) pair78.2) = true := by
  decide +kernel

private def pair77 : Box × Box :=
  (dataBox (-54251098693) (-54251085842) (112947567644) (112947578904) (by decide) (by decide),
    dataBox (-396147976851) (-396147969218) (1025666903169) (1025666909818) (by decide) (by decide))

private theorem checked_pair77 :
    (ZetaBlockCacheCheck.powerCheck cfg 77
        (neg (add cfg.precision center initial)) pair77.1 &&
      ZetaBlockCacheCheck.powerCheck cfg 77 (neg step) pair77.2) = true := by
  decide +kernel

private def pair76 : Box × Box :=
  (dataBox (-74384979874) (-74384965482) (101851820043) (101851832549) (by decide) (by decide),
    dataBox (-409521350234) (-409521342541) (1020400940629) (1020400947324) (by decide) (by decide))

private theorem checked_pair76 :
    (ZetaBlockCacheCheck.powerCheck cfg 76
        (neg (add cfg.precision center initial)) pair76.1 &&
      ZetaBlockCacheCheck.powerCheck cfg 76 (neg step) pair76.2) = true := by
  decide +kernel

private def pair75 : Box × Box :=
  (dataBox (-92498976582) (-92498960483) (86965226000) (86965239986) (by decide) (by decide),
    dataBox (-423000475090) (-423000467335) (1014887389873) (1014887396617) (by decide) (by decide))

private theorem checked_pair75 :
    (ZetaBlockCacheCheck.powerCheck cfg 75
        (neg (add cfg.precision center initial)) pair75.1 &&
      ZetaBlockCacheCheck.powerCheck cfg 75 (neg step) pair75.2) = true := by
  decide +kernel

private def pair74 : Box × Box :=
  (dataBox (-107838508868) (-107838490860) (68612624700) (68612640440) (by decide) (by decide),
    dataBox (-436584813144) (-436584805329) (1009118187878) (1009118194668) (by decide) (by decide))

private theorem checked_pair74 :
    (ZetaBlockCacheCheck.powerCheck cfg 74
        (neg (add cfg.precision center initial)) pair74.1 &&
      ZetaBlockCacheCheck.powerCheck cfg 74 (neg step) pair74.2) = true := by
  decide +kernel

private def pair73 : Box × Box :=
  (dataBox (-119689957248) (-119689937056) (47275187718) (47275205557) (by decide) (by decide),
    dataBox (-450273692273) (-450273684396) (1003084950713) (1003084957553) (by decide) (by decide))

private theorem checked_pair73 :
    (ZetaBlockCacheCheck.powerCheck cfg 73
        (neg (add cfg.precision center initial)) pair73.1 &&
      ZetaBlockCacheCheck.powerCheck cfg 73 (neg step) pair73.2) = true := by
  decide +kernel

private def pair72 : Box × Box :=
  (dataBox (-127413478596) (-127413455863) (23589071010) (23589091378) (by decide) (by decide),
    dataBox (-464066294585) (-464066286644) (996778957774) (996778964665) (by decide) (by decide))

private theorem checked_pair72 :
    (ZetaBlockCacheCheck.powerCheck cfg 72
        (neg (add cfg.precision center initial)) pair72.1 &&
      ZetaBlockCacheCheck.powerCheck cfg 72 (neg step) pair72.2) = true := by
  decide +kernel

private def pair71 : Box × Box :=
  (dataBox (-130477442949) (-130477417575) (-1662663195) (-1662640141) (by decide) (by decide),
    dataBox (-477961643436) (-477961635430) (990191135069) (990191142012) (by decide) (by decide))

private theorem checked_pair71 :
    (ZetaBlockCacheCheck.powerCheck cfg 71
        (neg (add cfg.precision center initial)) pair71.1 &&
      ZetaBlockCacheCheck.powerCheck cfg 71 (neg step) pair71.2) = true := by
  decide +kernel

private def pair70 : Box × Box :=
  (dataBox (-128493213049) (-128493190374) (-27565676557) (-27565656285) (by decide) (by decide),
    dataBox (-491958589285) (-491958581213) (983312037521) (983312044518) (by decide) (by decide))

private theorem checked_pair70 :
    (ZetaBlockCacheCheck.powerCheck cfg 70
        (neg (add cfg.precision center initial)) pair70.1 &&
      ZetaBlockCacheCheck.powerCheck cfg 70 (neg step) pair70.2) = true := by
  decide +kernel

private def pair69 : Box × Box :=
  (dataBox (-121248717175) (-121248696835) (-53098173739) (-53098155811) (by decide) (by decide),
    dataBox (-506055794272) (-506055786132) (976131830202) (976131837254) (by decide) (by decide))

private theorem checked_pair69 :
    (ZetaBlockCacheCheck.powerCheck cfg 69
        (neg (add cfg.precision center initial)) pair69.1 &&
      ZetaBlockCacheCheck.powerCheck cfg 69 (neg step) pair69.2) = true := by
  decide +kernel

private def pair68 : Box × Box :=
  (dataBox (-108738953447) (-108738935187) (-77163230203) (-77163214277) (by decide) (by decide),
    dataBox (-520251715378) (-520251707169) (968640268441) (968640275550) (by decide) (by decide))

private theorem checked_pair68 :
    (ZetaBlockCacheCheck.powerCheck cfg 68
        (neg (add cfg.precision center initial)) pair68.1 &&
      ZetaBlockCacheCheck.powerCheck cfg 68 (neg step) pair68.2) = true := by
  decide +kernel

private def pair67 : Box × Box :=
  (dataBox (-91191378942) (-91191362573) (-98629631711) (-98629617502) (by decide) (by decide),
    dataBox (-534544586048) (-534544577768) (960826676712) (960826683879) (by decide) (by decide))

private theorem checked_pair67 :
    (ZetaBlockCacheCheck.powerCheck cfg 67
        (neg (add cfg.precision center initial)) pair67.1 &&
      ZetaBlockCacheCheck.powerCheck cfg 67 (neg step) pair67.2) = true := by
  decide +kernel

private def pair66 : Box × Box :=
  (dataBox (-69083912323) (-69083897705) (-116380726174) (-116380713433) (by decide) (by decide),
    dataBox (-548932396090) (-548932387738) (952679926228) (952679933454) (by decide) (by decide))

private theorem checked_pair66 :
    (ZetaBlockCacheCheck.powerCheck cfg 66
        (neg (add cfg.precision center initial)) pair66.1 &&
      ZetaBlockCacheCheck.powerCheck cfg 66 (neg step) pair66.2) = true := by
  decide +kernel

private def pair65 : Box × Box :=
  (dataBox (-43153198306) (-43153185343) (-129370252710) (-129370241220) (by decide) (by decide),
    dataBox (-563412869700) (-563412861274) (944188411143) (944188418431) (by decide) (by decide))

private theorem checked_pair65 :
    (ZetaBlockCacheCheck.powerCheck cfg 65
        (neg (add cfg.precision center initial)) pair65.1 &&
      ZetaBlockCacheCheck.powerCheck cfg 65 (neg step) pair65.2) = true := by
  decide +kernel

private def pair64 : Box × Box :=
  (dataBox (-14390798550) (-14390787176) (-136683475370) (-136683464938) (by decide) (by decide),
    dataBox (-577983441392) (-577983432890) (935340023268) (935340030621) (by decide) (by decide))

private theorem checked_pair64 :
    (ZetaBlockCacheCheck.powerCheck cfg 64
        (neg (add cfg.precision center initial)) pair64.1 &&
      ZetaBlockCacheCheck.powerCheck cfg 64 (neg step) pair64.2) = true := by
  decide +kernel

private def pair63 : Box × Box :=
  (dataBox (15974856913) (15974866178) (-137601249107) (-137601240153) (by decide) (by decide),
    dataBox (-592641229363) (-592641221309) (926122125423) (926122132386) (by decide) (by decide))

private theorem checked_pair63 :
    (ZetaBlockCacheCheck.powerCheck cfg 63
        (neg (add cfg.precision center initial)) pair63.1 &&
      ZetaBlockCacheCheck.powerCheck cfg 63 (neg step) pair63.2) = true := by
  decide +kernel

private def pair62 : Box × Box :=
  (dataBox (46512566502) (46512574072) (-131663910732) (-131663902828) (by decide) (by decide),
    dataBox (-607383007455) (-607382999674) (916521522077) (916521528803) (by decide) (by decide))

private theorem checked_pair62 :
    (ZetaBlockCacheCheck.powerCheck cfg 62
        (neg (add cfg.precision center initial)) pair62.1 &&
      ZetaBlockCacheCheck.powerCheck cfg 62 (neg step) pair62.2) = true := by
  decide +kernel

private def pair61 : Box × Box :=
  (dataBox (75639742764) (75639748842) (-118731149090) (-118731141939) (by decide) (by decide),
    dataBox (-622205172396) (-622205164767) (906524429801) (906524436396) (by decide) (by decide))

private theorem checked_pair61 :
    (ZetaBlockCacheCheck.powerCheck cfg 61
        (neg (add cfg.precision center initial)) pair61.1 &&
      ZetaBlockCacheCheck.powerCheck cfg 61 (neg step) pair61.2) = true := by
  decide +kernel

private def pair60 : Box × Box :=
  (dataBox (101691500404) (101691505089) (-99033340776) (-99033334163) (by decide) (by decide),
    dataBox (-637103709289) (-637103701730) (896116444545) (896116451080) (by decide) (by decide))

private theorem checked_pair60 :
    (ZetaBlockCacheCheck.powerCheck cfg 60
        (neg (add cfg.precision center initial)) pair60.1 &&
      ZetaBlockCacheCheck.powerCheck cfg 60 (neg step) pair60.2) = true := by
  decide +kernel

private def pair59 : Box × Box :=
  (dataBox (123006784225) (123006787544) (-73209283653) (-73209277416) (by decide) (by decide),
    dataBox (-652074153214) (-652074145672) (885282507152) (885282513672) (by decide) (by decide))

private theorem checked_pair59 :
    (ZetaBlockCacheCheck.powerCheck cfg 59
        (neg (add cfg.precision center initial)) pair59.1 &&
      ZetaBlockCacheCheck.powerCheck cfg 59 (neg step) pair59.2) = true := by
  decide +kernel

private def pair58 : Box × Box :=
  (dataBox (138029522490) (138029524433) (-42324927906) (-42324921904) (by decide) (by decide),
    dataBox (-667111546946) (-667111539385) (874006866607) (874006873144) (by decide) (by decide))

private theorem checked_pair58 :
    (ZetaBlockCacheCheck.powerCheck cfg 58
        (neg (add cfg.precision center initial)) pair58.1 &&
      ZetaBlockCacheCheck.powerCheck cfg 58 (neg step) pair58.2) = true := by
  decide +kernel

private def pair57 : Box × Box :=
  (dataBox (145421196861) (145421197391) (-7867679415) (-7867673519) (by decide) (by decide),
    dataBox (-682210394324) (-682210386717) (862273040868) (862273047446) (by decide) (by decide))

private theorem checked_pair57 :
    (ZetaBlockCacheCheck.powerCheck cfg 57
        (neg (add cfg.precision center initial)) pair57.1 &&
      ZetaBlockCacheCheck.powerCheck cfg 57 (neg step) pair57.2) = true := by
  decide +kernel

private def pair56 : Box × Box :=
  (dataBox (144179426585) (144179427941) (28288754835) (28288760833) (by decide) (by decide),
    dataBox (-697364608779) (-697364601115) (850063775105) (850063781734) (by decide) (by decide))

private theorem checked_pair56 :
    (ZetaBlockCacheCheck.powerCheck cfg 56
        (neg (add cfg.precision center initial)) pair56.1 &&
      ZetaBlockCacheCheck.powerCheck cfg 56 (neg step) pair56.2) = true := by
  decide +kernel

private def pair55 : Box × Box :=
  (dataBox (133755268156) (133755271010) (63953083640) (63953089896) (by decide) (by decide),
    dataBox (-712567456468) (-712567448738) (837360997124) (837361003812) (by decide) (by decide))

private theorem checked_pair55 :
    (ZetaBlockCacheCheck.powerCheck cfg 55
        (neg (add cfg.precision center initial)) pair55.1 &&
      ZetaBlockCacheCheck.powerCheck cfg 55 (neg step) pair55.2) = true := by
  decide +kernel

private def pair54 : Box × Box :=
  (dataBox (114160034827) (114160039224) (96721251444) (96721258109) (by decide) (by decide),
    dataBox (-727811493314) (-727811485506) (824145769828) (824145776587) (by decide) (by decide))

private theorem checked_pair54 :
    (ZetaBlockCacheCheck.powerCheck cfg 54
        (neg (add cfg.precision center initial)) pair54.1 &&
      ZetaBlockCacheCheck.powerCheck cfg 54 (neg step) pair54.2) = true := by
  decide +kernel

private def pair53 : Box × Box :=
  (dataBox (86050780207) (86050786202) (124117617354) (124117624591) (by decide) (by decide),
    dataBox (-743088495258) (-743088487369) (810398240469) (810398247300) (by decide) (by decide))

private theorem checked_pair53 :
    (ZetaBlockCacheCheck.powerCheck cfg 53
        (neg (add cfg.precision center initial)) pair53.1 &&
      ZetaBlockCacheCheck.powerCheck cfg 53 (neg step) pair53.2) = true := by
  decide +kernel

private def pair52 : Box × Box :=
  (dataBox (50782344157) (50782351823) (143769695824) (143769703828) (by decide) (by decide),
    dataBox (-758389380872) (-758389372901) (796097586443) (796097593349) (by decide) (by decide))

private theorem checked_pair52 :
    (ZetaBlockCacheCheck.powerCheck cfg 52
        (neg (add cfg.precision center initial)) pair52.1 &&
      ZetaBlockCacheCheck.powerCheck cfg 52 (neg step) pair52.2) = true := by
  decide +kernel

private def pair51 : Box × Box :=
  (dataBox (10413358564) (10413368010) (153609857486) (153609866502) (by decide) (by decide),
    dataBox (-773704125367) (-773704117309) (781221957435) (781221964421) (by decide) (by decide))

private theorem checked_pair51 :
    (ZetaBlockCacheCheck.powerCheck cfg 51
        (neg (add cfg.precision center initial)) pair51.1 &&
      ZetaBlockCacheCheck.powerCheck cfg 51 (neg step) pair51.2) = true := by
  decide +kernel

private def pair50 : Box × Box :=
  (dataBox (-32345822634) (-32345811155) (152092941822) (152092952151) (by decide) (by decide),
    dataBox (-789021664889) (-789021656743) (765748413621) (765748420689) (by decide) (by decide))

private theorem checked_pair50 :
    (ZetaBlockCacheCheck.powerCheck cfg 50
        (neg (add cfg.precision center initial)) pair50.1 &&
      ZetaBlockCacheCheck.powerCheck cfg 50 (neg step) pair50.2) = true := by
  decide +kernel

private def pair49 : Box × Box :=
  (dataBox (-74253311117) (-74253297330) (138413874479) (138413886523) (by decide) (by decide),
    dataBox (-804329789876) (-804329781634) (749652859659) (749652866815) (by decide) (by decide))

private theorem checked_pair49 :
    (ZetaBlockCacheCheck.powerCheck cfg 49
        (neg (add cfg.precision center initial)) pair49.1 &&
      ZetaBlockCacheCheck.powerCheck cfg 49 (neg step) pair49.2) = true := by
  decide +kernel

private def pair48 : Box × Box :=
  (dataBox (-111730261580) (-111730245143) (112704496147) (112704510420) (by decide) (by decide),
    dataBox (-819615025984) (-819615017648) (732909974223) (732909981466) (by decide) (by decide))

private theorem checked_pair48 :
    (ZetaBlockCacheCheck.powerCheck cfg 48
        (neg (add cfg.precision center initial)) pair48.1 &&
      ZetaBlockCacheCheck.powerCheck cfg 48 (neg step) pair48.2) = true := by
  decide +kernel

private def pair47 : Box × Box :=
  (dataBox (-141130277094) (-141130257482) (76184462292) (76184479495) (by decide) (by decide),
    dataBox (-834862500983) (-834862492545) (715493134738) (715493142077) (by decide) (by decide))

private theorem checked_pair47 :
    (ZetaBlockCacheCheck.powerCheck cfg 47
        (neg (add cfg.precision center initial)) pair47.1 &&
      ZetaBlockCacheCheck.powerCheck cfg 47 (neg step) pair47.2) = true := by
  decide +kernel

private def pair46 : Box × Box :=
  (dataBox (-159076034778) (-159076011214) (31238026929) (31238048025) (by decide) (by decide),
    dataBox (-850055795614) (-850055787073) (697374337086) (697374344523) (by decide) (by decide))

private theorem checked_pair46 :
    (ZetaBlockCacheCheck.powerCheck cfg 46
        (neg (add cfg.precision center initial)) pair46.1 &&
      ZetaBlockCacheCheck.powerCheck cfg 46 (neg step) pair46.2) = true := by
  decide +kernel

private def pair45 : Box × Box :=
  (dataBox (-162845344480) (-162845319489) (-18612266964) (-18612244448) (by decide) (by decide),
    dataBox (-865176776276) (-865176767628) (678524109939) (678524117477) (by decide) (by decide))

private theorem checked_pair45 :
    (ZetaBlockCacheCheck.powerCheck cfg 45
        (neg (add cfg.precision center initial)) pair45.1 &&
      ZetaBlockCacheCheck.powerCheck cfg 45 (neg step) pair45.2) = true := by
  decide +kernel

private def pair44 : Box × Box :=
  (dataBox (-150776977778) (-150776956739) (-68861413216) (-68861394690) (by decide) (by decide),
    dataBox (-880205406889) (-880205398133) (658911423458) (658911431099) (by decide) (by decide))

private theorem checked_pair44 :
    (ZetaBlockCacheCheck.powerCheck cfg 44
        (neg (add cfg.precision center initial)) pair44.1 &&
      ZetaBlockCacheCheck.powerCheck cfg 44 (neg step) pair44.2) = true := by
  decide +kernel

private def pair43 : Box × Box :=
  (dataBox (-122653909818) (-122653892061) (-114326621107) (-114326605680) (by decide) (by decide),
    dataBox (-895119536979) (-895119528108) (638503592093) (638503599845) (by decide) (by decide))

private theorem checked_pair43 :
    (ZetaBlockCacheCheck.powerCheck cfg 43
        (neg (add cfg.precision center initial)) pair43.1 &&
      ZetaBlockCacheCheck.powerCheck cfg 43 (neg step) pair43.2) = true := by
  decide +kernel

private def pair42 : Box × Box :=
  (dataBox (-80009607064) (-80009592188) (-149607533232) (-149607520235) (by decide) (by decide),
    dataBox (-909894662449) (-909894653458) (617266171255) (617266179123) (by decide) (by decide))

private theorem checked_pair42 :
    (ZetaBlockCacheCheck.powerCheck cfg 42
        (neg (add cfg.precision center initial)) pair42.1 &&
      ZetaBlockCacheCheck.powerCheck cfg 42 (neg step) pair42.2) = true := by
  decide +kernel

private def pair41 : Box × Box :=
  (dataBox (-26293904842) (-26293892616) (-169689800448) (-169689789341) (by decide) (by decide),
    dataBox (-924503654967) (-924503645851) (595162847655) (595162855644) (by decide) (by decide))

private theorem checked_pair41 :
    (ZetaBlockCacheCheck.powerCheck cfg 41
        (neg (add cfg.precision center initial)) pair41.1 &&
      ZetaBlockCacheCheck.powerCheck cfg 41 (neg step) pair41.2) = true := by
  decide +kernel

private def pair40 : Box × Box :=
  (dataBox (33168390119) (33168399896) (-170654635782) (-170654626117) (by decide) (by decide),
    dataBox (-938916455143) (-938916445893) (572155323231) (572155331351) (by decide) (by decide))

private theorem checked_pair40 :
    (ZetaBlockCacheCheck.powerCheck cfg 40
        (neg (add cfg.precision center initial)) pair40.1 &&
      ZetaBlockCacheCheck.powerCheck cfg 40 (neg step) pair40.2) = true := by
  decide +kernel

private def pair39 : Box × Box :=
  (dataBox (91487176389) (91487183788) (-150426710103) (-150426701511) (by decide) (by decide),
    dataBox (-953099723824) (-953099714440) (548203192680) (548203200931) (by decide) (by decide))

private theorem checked_pair39 :
    (ZetaBlockCacheCheck.powerCheck cfg 39
        (neg (add cfg.precision center initial)) pair39.1 &&
      ZetaBlockCacheCheck.powerCheck cfg 39 (neg step) pair39.2) = true := by
  decide +kernel

private def pair38 : Box × Box :=
  (dataBox (140827251618) (140827256560) (-109460142179) (-109460134321) (by decide) (by decide),
    dataBox (-967016444853) (-967016435323) (523263814725) (523263823121) (by decide) (by decide))

private theorem checked_pair38 :
    (ZetaBlockCacheCheck.powerCheck cfg 38
        (neg (add cfg.precision center initial)) pair38.1 &&
      ZetaBlockCacheCheck.powerCheck cfg 38 (neg step) pair38.2) = true := by
  decide +kernel

private def pair37 : Box × Box :=
  (dataBox (173346245668) (173346248006) (-51232312954) (-51232305518) (by decide) (by decide),
    dataBox (-980625471288) (-980625461610) (497292177591) (497292186135) (by decide) (by decide))

private theorem checked_pair37 :
    (ZetaBlockCacheCheck.powerCheck cfg 37
        (neg (add cfg.precision center initial)) pair37.1 &&
      ZetaBlockCacheCheck.powerCheck cfg 37 (neg step) pair37.2) = true := by
  decide +kernel

private def pair36 : Box × Box :=
  (dataBox (182404339302) (182404340275) (17604813680) (17604821079) (by decide) (by decide),
    dataBox (-993881005727) (-993880995889) (470240759320) (470240768023) (by decide) (by decide))

private theorem checked_pair36 :
    (ZetaBlockCacheCheck.powerCheck cfg 36
        (neg (add cfg.precision center initial)) pair36.1 &&
      ZetaBlockCacheCheck.powerCheck cfg 36 (neg step) pair36.2) = true := by
  decide +kernel

private def pair35 : Box × Box :=
  (dataBox (163929433009) (163929436909) (87566416894) (87566424790) (by decide) (by decide),
    dataBox (-1006732003373) (-1006731993366) (442059384152) (442059393024) (by decide) (by decide))

private theorem checked_pair35 :
    (ZetaBlockCacheCheck.powerCheck cfg 35
        (neg (add cfg.precision center initial)) pair35.1 &&
      ZetaBlockCacheCheck.powerCheck cfg 35 (neg step) pair35.2) = true := by
  decide +kernel

private def pair34 : Box × Box :=
  (dataBox (117739502164) (117739509137) (147288999120) (147289007963) (by decide) (by decide),
    dataBox (-1019121484380) (-1019121474194) (412695076653) (412695085706) (by decide) (by decide))

private theorem checked_pair34 :
    (ZetaBlockCacheCheck.powerCheck cfg 34
        (neg (add cfg.precision center initial)) pair34.1 &&
      ZetaBlockCacheCheck.powerCheck cfg 34 (neg step) pair34.2) = true := by
  decide +kernel

private def pair33 : Box × Box :=
  (dataBox (48542769637) (48542779900) (185142412335) (185142422707) (by decide) (by decide),
    dataBox (-1030985739150) (-1030985728768) (382091916173) (382091925424) (by decide) (by decide))

private theorem checked_pair33 :
    (ZetaBlockCacheCheck.powerCheck cfg 33
        (neg (add cfg.precision center initial)) pair33.1 &&
      ZetaBlockCacheCheck.powerCheck cfg 33 (neg step) pair33.2) = true := by
  decide +kernel

private def pair32 : Box × Box :=
  (dataBox (-33723057445) (-33723043414) (191420179979) (191420192680) (by decide) (by decide),
    dataBox (-1042253406880) (-1042253396291) (350190895266) (350190904727) (by decide) (by decide))

private theorem checked_pair32 :
    (ZetaBlockCacheCheck.powerCheck cfg 32
        (neg (add cfg.precision center initial)) pair32.1 &&
      ZetaBlockCacheCheck.powerCheck cfg 32 (neg step) pair32.2) = true := by
  decide +kernel

private def pair31 : Box × Box :=
  (dataBox (-114559286685) (-114559270300) (160853276332) (160853290573) (by decide) (by decide),
    dataBox (-1052844402779) (-1052844393262) (316929787809) (316929796337) (by decide) (by decide))

private theorem checked_pair31 :
    (ZetaBlockCacheCheck.powerCheck cfg 31
        (neg (add cfg.precision center initial)) pair31.1 &&
      ZetaBlockCacheCheck.powerCheck cfg 31 (neg step) pair31.2) = true := by
  decide +kernel

private def pair30 : Box × Box :=
  (dataBox (-176849454044) (-176849433689) (94983155504) (94983173361) (by decide) (by decide),
    dataBox (-1062668668282) (-1062668659090) (282243030777) (282243039041) (by decide) (by decide))

private theorem checked_pair30 :
    (ZetaBlockCacheCheck.powerCheck cfg 30
        (neg (add cfg.precision center initial)) pair30.1 &&
      ZetaBlockCacheCheck.powerCheck cfg 30 (neg step) pair30.2) = true := by
  decide +kernel

private def pair29 : Box × Box :=
  (dataBox (-204140189715) (-204140162961) (3726330358) (3726354660) (by decide) (by decide),
    dataBox (-1071624700222) (-1071624691009) (246061637036) (246061645348) (by decide) (by decide))

private theorem checked_pair29 :
    (ZetaBlockCacheCheck.powerCheck cfg 29
        (neg (add cfg.precision center initial)) pair29.1 &&
      ZetaBlockCacheCheck.powerCheck cfg 29 (neg step) pair29.2) = true := by
  decide +kernel

private def pair28 : Box × Box :=
  (dataBox (-184971679879) (-184971659224) (-94664699390) (-94664681249) (by decide) (by decide),
    dataBox (-1079597824042) (-1079597814646) (208313144568) (208313153076) (by decide) (by decide))

private theorem checked_pair28 :
    (ZetaBlockCacheCheck.powerCheck cfg 28
        (neg (add cfg.precision center initial)) pair28.1 &&
      ZetaBlockCacheCheck.powerCheck cfg 28 (neg step) pair28.2) = true := by
  decide +kernel

private def pair27 : Box × Box :=
  (dataBox (-117484329793) (-117484314065) (-175989962403) (-175989948722) (by decide) (by decide),
    dataBox (-1086458150432) (-1086458140773) (168921626376) (168921635156) (by decide) (by decide))

private theorem checked_pair27 :
    (ZetaBlockCacheCheck.powerCheck cfg 27
        (neg (add cfg.precision center initial)) pair27.1 &&
      ZetaBlockCacheCheck.powerCheck cfg 27 (neg step) pair27.2) = true := by
  decide +kernel

private def pair26 : Box × Box :=
  (dataBox (-12985706955) (-12985695411) (-215240611354) (-215240600664) (by decide) (by decide),
    dataBox (-1092058148147) (-1092058138165) (127807786424) (127807795537) (by decide) (by decide))

private theorem checked_pair26 :
    (ZetaBlockCacheCheck.powerCheck cfg 26
        (neg (add cfg.precision center initial)) pair26.1 &&
      ZetaBlockCacheCheck.powerCheck cfg 26 (neg step) pair26.2) = true := by
  decide +kernel

private def pair25 : Box × Box :=
  (dataBox (103265015552) (103265023349) (-194147805149) (-194147796394) (by decide) (by decide),
    dataBox (-1096229746616) (-1096229736246) (84889178612) (84889188121) (by decide) (by decide))

private theorem checked_pair25 :
    (ZetaBlockCacheCheck.powerCheck cfg 25
        (neg (add cfg.precision center initial)) pair25.1 &&
      ZetaBlockCacheCheck.powerCheck cfg 25 (neg step) pair25.2) = true := by
  decide +kernel

private def pair24 : Box × Box :=
  (dataBox (195826010722) (195826014633) (-109654378623) (-109654370963) (by decide) (by decide),
    dataBox (-1098780859143) (-1098780848311) (40080600296) (40080610279) (by decide) (by decide))

private theorem checked_pair24 :
    (ZetaBlockCacheCheck.powerCheck cfg 24
        (neg (add cfg.precision center initial)) pair24.1 &&
      ZetaBlockCacheCheck.powerCheck cfg 24 (neg step) pair24.2) = true := by
  decide +kernel

private def pair23 : Box × Box :=
  (dataBox (228428928420) (228428929314) (19550357314) (19550364716) (by decide) (by decide),
    dataBox (-1099491187432) (-1099491176213) (-6705266232) (-6705255853) (by decide) (by decide))

private theorem checked_pair23 :
    (ZetaBlockCacheCheck.powerCheck cfg 23
        (neg (add cfg.precision center initial)) pair23.1 &&
      ZetaBlockCacheCheck.powerCheck cfg 23 (neg step) pair23.2) = true := by
  decide +kernel

private def pair22 : Box × Box :=
  (dataBox (178123204155) (178123209698) (152391914161) (152391922518) (by decide) (by decide),
    dataBox (-1098107128630) (-1098107117969) (-55556869467) (-55556859658) (by decide) (by decide))

private theorem checked_pair22 :
    (ZetaBlockCacheCheck.powerCheck cfg 22
        (neg (add cfg.precision center initial)) pair22.1 &&
      ZetaBlockCacheCheck.powerCheck cfg 22 (neg step) pair22.2) = true := by
  decide +kernel

private def pair21 : Box × Box :=
  (dataBox (50441857380) (50441868020) (234570910768) (234570921354) (by decide) (by decide),
    dataBox (-1094335555212) (-1094335545047) (-106562301838) (-106562292538) (by decide) (by decide))

private theorem checked_pair21 :
    (ZetaBlockCacheCheck.powerCheck cfg 21
        (neg (add cfg.precision center initial)) pair21.1 &&
      ZetaBlockCacheCheck.powerCheck cfg 21 (neg step) pair21.2) = true := by
  decide +kernel

private def pair20 : Box × Box :=
  (dataBox (-111619540974) (-111619523924) (219060191937) (219060206852) (by decide) (by decide),
    dataBox (-1087836161883) (-1087836152165) (-159807122388) (-159807113546) (by decide) (by decide))

private theorem checked_pair20 :
    (ZetaBlockCacheCheck.powerCheck cfg 20
        (neg (add cfg.precision center initial)) pair20.1 &&
      ZetaBlockCacheCheck.powerCheck cfg 20 (neg step) pair20.2) = true := by
  decide +kernel

private def pair19 : Box × Box :=
  (dataBox (-234116184933) (-234116158614) (93900429436) (93900452680) (by decide) (by decide),
    dataBox (-1078211986212) (-1078211976900) (-215371177624) (-215371169198) (by decide) (by decide))

private theorem checked_pair19 :
    (ZetaBlockCacheCheck.powerCheck cfg 19
        (neg (add cfg.precision center initial)) pair19.1 &&
      ZetaBlockCacheCheck.powerCheck cfg 19 (neg step) pair19.2) = true := by
  decide +kernel

private def pair18 : Box × Box :=
  (dataBox (-241100446718) (-241100419598) (-95042774279) (-95042750317) (by decide) (by decide),
    dataBox (-1064997572152) (-1064997563219) (-273323988247) (-273323980208) (by decide) (by decide))

private theorem checked_pair18 :
    (ZetaBlockCacheCheck.powerCheck cfg 18
        (neg (add cfg.precision center initial)) pair18.1 &&
      ZetaBlockCacheCheck.powerCheck cfg 18 (neg step) pair18.2) = true := by
  decide +kernel

private def pair17 : Box × Box :=
  (dataBox (-102636450649) (-102636432984) (-246128113279) (-246128097737) (by decide) (by decide),
    dataBox (-1047644067195) (-1047644058614) (-333718054015) (-333718046335) (by decide) (by decide))

private theorem checked_pair17 :
    (ZetaBlockCacheCheck.powerCheck cfg 17
        (neg (add cfg.precision center initial)) pair17.1 &&
      ZetaBlockCacheCheck.powerCheck cfg 17 (neg step) pair17.2) = true := by
  decide +kernel

private def pair16 : Box × Box :=
  (dataBox (120469002430) (120469012483) (-247073035170) (-247073024093) (by decide) (by decide),
    dataBox (-1025500290160) (-1025500281913) (-396579104115) (-396579096774) (by decide) (by decide))

private theorem checked_pair16 :
    (ZetaBlockCacheCheck.powerCheck cfg 16
        (neg (add cfg.precision center initial)) pair16.1 &&
      ZetaBlockCacheCheck.powerCheck cfg 16 (neg step) pair16.2) = true := by
  decide +kernel

private def pair15 : Box × Box :=
  (dataBox (277441513821) (277441515604) (-60176914140) (-60176906863) (by decide) (by decide),
    dataBox (-997788448371) (-997788442140) (-461891806214) (-461891800696) (by decide) (by decide))

private theorem checked_pair15 :
    (ZetaBlockCacheCheck.powerCheck cfg 15
        (neg (add cfg.precision center initial)) pair15.1 &&
      ZetaBlockCacheCheck.powerCheck cfg 15 (neg step) pair15.2) = true := by
  decide +kernel

private def pair14 : Box × Box :=
  (dataBox (214548657248) (214548662796) (200800187102) (200800195087) (by decide) (by decide),
    dataBox (-963572678898) (-963572673164) (-529578625207) (-529578620156) (by decide) (by decide))

private theorem checked_pair14 :
    (ZetaBlockCacheCheck.powerCheck cfg 14
        (neg (add cfg.precision center initial)) pair14.1 &&
      ZetaBlockCacheCheck.powerCheck cfg 14 (neg step) pair14.2) = true := by
  decide +kernel

private def pair13 : Box × Box :=
  (dataBox (-66258719315) (-66258705715) (297664363331) (297664375552) (by decide) (by decide),
    dataBox (-921717838448) (-921717832983) (-599468142438) (-599468137649) (by decide) (by decide))

private theorem checked_pair13 :
    (ZetaBlockCacheCheck.powerCheck cfg 13
        (neg (add cfg.precision center initial)) pair13.1 &&
      ZetaBlockCacheCheck.powerCheck cfg 13 (neg step) pair13.2) = true := by
  decide +kernel

private def pair12 : Box × Box :=
  (dataBox (-308958193202) (-308958166091) (72723172137) (72723196341) (by decide) (by decide),
    dataBox (-870834934425) (-870834929210) (-671246857860) (-671246853312) (by decide) (by decide))

private theorem checked_pair12 :
    (ZetaBlockCacheCheck.powerCheck cfg 12
        (neg (add cfg.precision center initial)) pair12.1 &&
      ZetaBlockCacheCheck.powerCheck cfg 12 (neg step) pair12.2) = true := by
  decide +kernel

private def pair11 : Box × Box :=
  (dataBox (-182733746936) (-182733728521) (-276605735241) (-276605719220) (by decide) (by decide),
    dataBox (-809208034288) (-809208029324) (-744384432993) (-744384428681) (by decide) (by decide))

private theorem checked_pair11 :
    (ZetaBlockCacheCheck.powerCheck cfg 11
        (neg (add cfg.precision center initial)) pair11.1 &&
      ZetaBlockCacheCheck.powerCheck cfg 11 (neg step) pair11.2) = true := by
  decide +kernel

private def pair10 : Box × Box :=
  (dataBox (237138337388) (237138344479) (-254279357517) (-254279347942) (by decide) (by decide),
    dataBox (-734695332479) (-734695327775) (-818015033379) (-818015029307) (by decide) (by decide))

private theorem checked_pair10 :
    (ZetaBlockCacheCheck.powerCheck cfg 10
        (neg (add cfg.precision center initial)) pair10.1 &&
      ZetaBlockCacheCheck.powerCheck cfg 10 (neg step) pair10.2) = true := by
  decide +kernel

private def pair9 : Box × Box :=
  (dataBox (290703698785) (290703704825) (223195982647) (223195992322) (by decide) (by decide),
    dataBox (-644594119283) (-644594114851) (-890743648458) (-890743644628) (by decide) (by decide))

private theorem checked_pair9 :
    (ZetaBlockCacheCheck.powerCheck cfg 9
        (neg (add cfg.precision center initial)) pair9.1 &&
      ZetaBlockCacheCheck.powerCheck cfg 9 (neg step) pair9.2) = true := by
  decide +kernel

private def pair8 : Box × Box :=
  (dataBox (-260089307363) (-260089283835) (288910504951) (288910525374) (by decide) (by decide),
    dataBox (-535456027259) (-535456023114) (-960319044980) (-960319041393) (by decide) (by decide))

private theorem checked_pair8 :
    (ZetaBlockCacheCheck.powerCheck cfg 8
        (neg (add cfg.precision center initial)) pair8.1 &&
      ZetaBlockCacheCheck.powerCheck cfg 8 (neg step) pair8.2) = true := by
  decide +kernel

private def pair7 : Box × Box :=
  (dataBox (-213379150333) (-213379135229) (-356613284442) (-356613271278) (by decide) (by decide),
    dataBox (-402837355326) (-402837352753) (-1023058105924) (-1023058103684) (by decide) (by decide))

private theorem checked_pair7 :
    (ZetaBlockCacheCheck.powerCheck cfg 7
        (neg (add cfg.precision center initial)) pair7.1 &&
      ZetaBlockCacheCheck.powerCheck cfg 7 (neg step) pair7.2) = true := by
  decide +kernel

private def pair6 : Box × Box :=
  (dataBox (448354395885) (448354396492) (21586381560) (21586388792) (by decide) (by decide),
    dataBox (-240979359826) (-240979357499) (-1072778994257) (-1072778992201) (by decide) (by decide))

private theorem checked_pair6 :
    (ZetaBlockCacheCheck.powerCheck cfg 6
        (neg (add cfg.precision center initial)) pair6.1 &&
      ZetaBlockCacheCheck.powerCheck cfg 6 (neg step) pair6.2) = true := by
  decide +kernel

private def pair5 : Box × Box :=
  (dataBox (-421501051798) (-421501028337) (253223284767) (253223305299) (by decide) (by decide),
    dataBox (-42476301160) (-42476299088) (-1098690850791) (-1098690848907) (by decide) (by decide))

private theorem checked_pair5 :
    (ZetaBlockCacheCheck.powerCheck cfg 5
        (neg (add cfg.precision center initial)) pair5.1 &&
      ZetaBlockCacheCheck.powerCheck cfg 5 (neg step) pair5.2) = true := by
  decide +kernel

private def pair4 : Box × Box :=
  (dataBox (466201954380) (466201959591) (-291354068058) (-291354058579) (by decide) (by decide),
    dataBox (201713076064) (201713077834) (-1080850431859) (-1080850430150) (by decide) (by decide))

private theorem checked_pair4 :
    (ZetaBlockCacheCheck.powerCheck cfg 4
        (neg (add cfg.precision center initial)) pair4.1 &&
      ZetaBlockCacheCheck.powerCheck cfg 4 (neg step) pair4.2) = true := by
  decide +kernel

private def pair3 : Box × Box :=
  (dataBox (-601085432461) (-601085415302) (-204136203290) (-204136188074) (by decide) (by decide),
    dataBox (500093537248) (500093537946) (-979199813123) (-979199812355) (by decide) (by decide))

private theorem checked_pair3 :
    (ZetaBlockCacheCheck.powerCheck cfg 3
        (neg (add cfg.precision center initial)) pair3.1 &&
      ZetaBlockCacheCheck.powerCheck cfg 3 (neg step) pair3.2) = true := by
  decide +kernel

private def pair2 : Box × Box :=
  (dataBox (-747347782067) (-747347760434) (214322687687) (214322706939) (by decide) (by decide),
    dataBox (845787116375) (845787116814) (-702545353340) (-702545352655) (by decide) (by decide))

private theorem checked_pair2 :
    (ZetaBlockCacheCheck.powerCheck cfg 2
        (neg (add cfg.precision center initial)) pair2.1 &&
      ZetaBlockCacheCheck.powerCheck cfg 2 (neg step) pair2.2) = true := by
  decide +kernel

private def pair1 : Box × Box :=
  (dataBox (1099511627776) (1099511627776) (0) (0) (by decide) (by decide),
    dataBox (1099511627776) (1099511627776) (0) (0) (by decide) (by decide))

private theorem checked_pair1 :
    (ZetaBlockCacheCheck.powerCheck cfg 1
        (neg (add cfg.precision center initial)) pair1.1 &&
      ZetaBlockCacheCheck.powerCheck cfg 1 (neg step) pair1.2) = true := by
  decide +kernel

private def prefixData : List (Box × Box) :=
  [pair80, pair79, pair78, pair77, pair76, pair75, pair74, pair73, pair72, pair71, pair70, pair69, pair68, pair67, pair66, pair65, pair64, pair63, pair62, pair61, pair60, pair59, pair58, pair57, pair56, pair55, pair54, pair53, pair52, pair51, pair50, pair49, pair48, pair47, pair46, pair45, pair44, pair43, pair42, pair41, pair40, pair39, pair38, pair37, pair36, pair35, pair34, pair33, pair32, pair31, pair30, pair29, pair28, pair27, pair26, pair25, pair24, pair23, pair22, pair21, pair20, pair19, pair18, pair17, pair16, pair15, pair14, pair13, pair12, pair11, pair10, pair9, pair8, pair7, pair6, pair5, pair4, pair3, pair2, pair1]

/-- The complete checked eighty-term prefix, with no approximate blocks. -/
def batch : ZetaBlockBatchCertificate.Batch := ⟨prefixData, []⟩

private theorem checked_prefix :
    ZetaBlockCacheCheck.prefixCheck cfg (add cfg.precision center initial) step
      80 prefixData = true := by
  exact ZetaBlockCacheCheck.prefixCheck_cons checked_pair80 <|
    ZetaBlockCacheCheck.prefixCheck_cons checked_pair79 <|
    ZetaBlockCacheCheck.prefixCheck_cons checked_pair78 <|
    ZetaBlockCacheCheck.prefixCheck_cons checked_pair77 <|
    ZetaBlockCacheCheck.prefixCheck_cons checked_pair76 <|
    ZetaBlockCacheCheck.prefixCheck_cons checked_pair75 <|
    ZetaBlockCacheCheck.prefixCheck_cons checked_pair74 <|
    ZetaBlockCacheCheck.prefixCheck_cons checked_pair73 <|
    ZetaBlockCacheCheck.prefixCheck_cons checked_pair72 <|
    ZetaBlockCacheCheck.prefixCheck_cons checked_pair71 <|
    ZetaBlockCacheCheck.prefixCheck_cons checked_pair70 <|
    ZetaBlockCacheCheck.prefixCheck_cons checked_pair69 <|
    ZetaBlockCacheCheck.prefixCheck_cons checked_pair68 <|
    ZetaBlockCacheCheck.prefixCheck_cons checked_pair67 <|
    ZetaBlockCacheCheck.prefixCheck_cons checked_pair66 <|
    ZetaBlockCacheCheck.prefixCheck_cons checked_pair65 <|
    ZetaBlockCacheCheck.prefixCheck_cons checked_pair64 <|
    ZetaBlockCacheCheck.prefixCheck_cons checked_pair63 <|
    ZetaBlockCacheCheck.prefixCheck_cons checked_pair62 <|
    ZetaBlockCacheCheck.prefixCheck_cons checked_pair61 <|
    ZetaBlockCacheCheck.prefixCheck_cons checked_pair60 <|
    ZetaBlockCacheCheck.prefixCheck_cons checked_pair59 <|
    ZetaBlockCacheCheck.prefixCheck_cons checked_pair58 <|
    ZetaBlockCacheCheck.prefixCheck_cons checked_pair57 <|
    ZetaBlockCacheCheck.prefixCheck_cons checked_pair56 <|
    ZetaBlockCacheCheck.prefixCheck_cons checked_pair55 <|
    ZetaBlockCacheCheck.prefixCheck_cons checked_pair54 <|
    ZetaBlockCacheCheck.prefixCheck_cons checked_pair53 <|
    ZetaBlockCacheCheck.prefixCheck_cons checked_pair52 <|
    ZetaBlockCacheCheck.prefixCheck_cons checked_pair51 <|
    ZetaBlockCacheCheck.prefixCheck_cons checked_pair50 <|
    ZetaBlockCacheCheck.prefixCheck_cons checked_pair49 <|
    ZetaBlockCacheCheck.prefixCheck_cons checked_pair48 <|
    ZetaBlockCacheCheck.prefixCheck_cons checked_pair47 <|
    ZetaBlockCacheCheck.prefixCheck_cons checked_pair46 <|
    ZetaBlockCacheCheck.prefixCheck_cons checked_pair45 <|
    ZetaBlockCacheCheck.prefixCheck_cons checked_pair44 <|
    ZetaBlockCacheCheck.prefixCheck_cons checked_pair43 <|
    ZetaBlockCacheCheck.prefixCheck_cons checked_pair42 <|
    ZetaBlockCacheCheck.prefixCheck_cons checked_pair41 <|
    ZetaBlockCacheCheck.prefixCheck_cons checked_pair40 <|
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

/-- Every cache entry has its exact original mathematical meaning. -/
theorem sound : ZetaBlockBatchCertificate.Sound cfg.precision
    (1 / 2 + 34 * Complex.I) (-20 * Complex.I) Complex.I 80 [] batch := by
  have hp : cfg.precision ≤ 0 := by decide
  have hs : Mem (1 / 2 + 34 * Complex.I) center := by
    simpa [center] using mem_rational hp (1 / 2) 34
  have hd : Mem (-20 * Complex.I) initial := by
    simpa [initial] using mem_rational hp 0 (-20)
  have hq : Mem Complex.I step := by simpa [step] using mem_rational hp 0 1
  exact ⟨ZetaBlockCacheCheck.sound_prefix_of_check hp (mem_add hs hd cfg.precision)
    hq 80 checked_prefix, trivial⟩

/-- Literal shift from the retained center at an integer height. -/
def shift (T : ℕ) : Box := rational cfg.precision 0 ((T : ℚ) - 34)

/-- A proposed micro-radian bracket, checked again at every sample. -/
def angle (a : ℚ) : IntervalRat := ⟨a / 10^6, (a + 1) / 10^6, by linarith⟩

/-- A sign check using the shared data and all original error allowances. -/
def signCheck (T : ℕ) (a : ℚ) (positive : Bool) : Bool :=
  ZetaBlockBatchHardy.signCheck cfg 80 [] batch center (shift T) (T - 14) T (angle a) positive

/-- Checked numerical signs give signs of actual Hardy Z. -/
theorem hardy_sign_of_check {T : ℕ} (hT : 14 ≤ T) {a : ℚ} {positive : Bool}
    (hc : signCheck T a positive = true) :
    if positive then 0 < ZetaHardyPhase.hardy T else ZetaHardyPhase.hardy T < 0 := by
  have hp : cfg.precision ≤ 0 := by decide
  have hs : Mem (1 / 2 + 34 * Complex.I) center := by
    simpa [center] using mem_rational hp (1 / 2) 34
  have he : (-20 : ℂ) * Complex.I + (T - 14 : ℕ) * Complex.I =
      ((T : ℂ) - 34) * Complex.I := by
    rw [Nat.cast_sub hT]
    norm_num
    ring
  have hd : Mem ((-20 : ℂ) * Complex.I + (T - 14 : ℕ) * Complex.I) (shift T) := by
    rw [he]
    simpa only [shift, Rat.cast_zero, Rat.cast_sub, Rat.cast_natCast,
      Rat.cast_ofNat, zero_add] using mem_rational hp 0 ((T : ℚ) - 34)
  have hpoint : ZetaHardyPhase.point (T : ℚ) =
      (1 / 2 + 34 * Complex.I) + (-20 * Complex.I + (T - 14 : ℕ) * Complex.I) := by
    rw [he]
    simp only [ZetaHardyPhase.point, Rat.cast_natCast, Complex.ofReal_natCast]
    ring
  simpa only [Rat.cast_natCast] using
    ZetaBlockBatchHardy.hardy_sign_of_check sound (T - 14) hpoint hs hd hc

end RiemannGaussian.ZetaHardyBatchData
