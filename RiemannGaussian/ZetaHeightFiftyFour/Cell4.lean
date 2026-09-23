/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaHorizontalCertificate

/-!
# Checked height-fifty-four contour cell 4

Every literal prefix checkpoint is checked in the kernel. This independent
module bounds compiler memory while retaining the complete original
Euler--Maclaurin expression, rounding errors and analytic tail.
-/

namespace RiemannGaussian.ZetaHeightFiftyFour.Cell4
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


private def cell4 : Box := input cfg (1 / 2) (1 / 2) 54 (by norm_num)

private def prefix4_1 : Box :=
  dataBox (1099511627776) (1099511627776) (0) (0) (by decide) (by decide)

private theorem checked_prefix4_1 : prefixBox cfg cell4 1 = .ok prefix4_1 := by
  decide +kernel

private def prefix4_2 : Box :=
  dataBox (1848989719502) (1848989726216) (206749824040) (206749848530) (by decide) (by decide)

private theorem checked_prefix4_2 : prefixBox cfg cell4 2 = .ok prefix4_2 := by
  rw [prefixBox, checked_prefix4_1]
  decide +kernel

private def prefix4_3 : Box :=
  dataBox (1256049421112) (1256049491908) (-19959519915) (-19959438521) (by decide) (by decide)

private theorem checked_prefix4_3 : prefixBox cfg cell4 3 = .ok prefix4_3 := by
  rw [prefixBox, checked_prefix4_2]
  decide +kernel

private def prefix4_4 : Box :=
  dataBox (1728051623582) (1728051713016) (261901007377) (261901124713) (by decide) (by decide)

private theorem checked_prefix4_4 : prefixBox cfg cell4 4 = .ok prefix4_4 := by
  rw [prefixBox, checked_prefix4_3]
  decide +kernel

private def prefix4_5 : Box :=
  dataBox (1970602501620) (1970602623490) (689632479109) (689632633182) (by decide) (by decide)

private theorem checked_prefix4_5 : prefixBox cfg cell4 5 = .ok prefix4_5 := by
  rw [prefixBox, checked_prefix4_4]
  decide +kernel

private def prefix4_6 : Box :=
  dataBox (1609056829770) (1609057029342) (423601635215) (423601857092) (by decide) (by decide)

private theorem checked_prefix4_6 : prefixBox cfg cell4 6 = .ok prefix4_6 := by
  rw [prefixBox, checked_prefix4_5]
  decide +kernel

private def prefix4_7 : Box :=
  dataBox (1541122995446) (1541123241213) (833587816537) (833588079725) (by decide) (by decide)

private theorem checked_prefix4_7 : prefixBox cfg cell4 7 = .ok prefix4_7 := by
  rw [prefixBox, checked_prefix4_6]
  decide +kernel

private def prefix4_8 : Box :=
  dataBox (1809861109082) (1809861384321) (1114471305636) (1114471609295) (by decide) (by decide)

private theorem checked_prefix4_8 : prefixBox cfg cell4 8 = .ok prefix4_8 := by
  rw [prefixBox, checked_prefix4_7]
  decide +kernel

private def prefix4_9 : Box :=
  dataBox (2082874167021) (2082874467408) (1358989086698) (1358989427761) (by decide) (by decide)

private theorem checked_prefix4_9 : prefixBox cfg cell4 9 = .ok prefix4_9 := by
  rw [prefixBox, checked_prefix4_8]
  decide +kernel

private def prefix4_10 : Box :=
  dataBox (2167778355845) (2167778699483) (1696159433165) (1696159817164) (by decide) (by decide)

private theorem checked_prefix4_10 : prefixBox cfg cell4 10 = .ok prefix4_10 := by
  rw [prefixBox, checked_prefix4_9]
  decide +kernel

private def prefix4_11 : Box :=
  dataBox (1910219285996) (1910219713492) (1904883363604) (1904883820616) (by decide) (by decide)

private theorem checked_prefix4_11 : prefixBox cfg cell4 11 = .ok prefix4_11 := by
  rw [prefixBox, checked_prefix4_10]
  decide +kernel

private def prefix4_12 : Box :=
  dataBox (1713796856816) (1713797355167) (1655560125962) (1655560644307) (by decide) (by decide)

private theorem checked_prefix4_12 : prefixBox cfg cell4 12 = .ok prefix4_12 := by
  rw [prefixBox, checked_prefix4_11]
  decide +kernel

private def prefix4_13 : Box :=
  dataBox (2007106155534) (2007106662005) (1572109846589) (1572110393744) (by decide) (by decide)

private theorem checked_prefix4_13 : prefixBox cfg cell4 13 = .ok prefix4_13 := by
  rw [prefixBox, checked_prefix4_12]
  decide +kernel

private def prefix4_14 : Box :=
  dataBox (1883706355279) (1883706919359) (1838801292451) (1838801889741) (by decide) (by decide)

private theorem checked_prefix4_14 : prefixBox cfg cell4 14 = .ok prefix4_14 := by
  rw [prefixBox, checked_prefix4_13]
  decide +kernel

private def prefix4_15 : Box :=
  dataBox (1841098797426) (1841099410290) (1558124138043) (1558124779051) (by decide) (by decide)

private theorem checked_prefix4_15 : prefixBox cfg cell4 15 = .ok prefix4_15 := by
  rw [prefixBox, checked_prefix4_14]
  decide +kernel

private def prefix4_16 : Box :=
  dataBox (1971466405195) (1971467055040) (1800120286254) (1800120968599) (by decide) (by decide)

private theorem checked_prefix4_16 : prefixBox cfg cell4 16 = .ok prefix4_16 := by
  rw [prefixBox, checked_prefix4_15]
  decide +kernel

private def prefix4_17 : Box :=
  dataBox (1815162033277) (1815162760636) (1584059522946) (1584060272386) (by decide) (by decide)

private theorem checked_prefix4_17 : prefixBox cfg cell4 17 = .ok prefix4_17 := by
  rw [prefixBox, checked_prefix4_16]
  decide +kernel

private def prefix4_18 : Box :=
  dataBox (1955281773052) (1955282532766) (1802070970457) (1802071757889) (by decide) (by decide)

private theorem checked_prefix4_18 : prefixBox cfg cell4 18 = .ok prefix4_18 := by
  rw [prefixBox, checked_prefix4_17]
  decide +kernel

private def prefix4_19 : Box :=
  dataBox (1868959000620) (1868959822757) (1565056051060) (1565056893127) (by decide) (by decide)

private theorem checked_prefix4_19 : prefixBox cfg cell4 19 = .ok prefix4_19 := by
  rw [prefixBox, checked_prefix4_18]
  decide +kernel

private def prefix4_20 : Box :=
  dataBox (1863432820183) (1863433691765) (1810852189000) (1810853076470) (by decide) (by decide)

private theorem checked_prefix4_20 : prefixBox cfg cell4 20 = .ok prefix4_20 := by
  rw [prefixBox, checked_prefix4_19]
  decide +kernel

private def prefix4_21 : Box :=
  dataBox (1984603313472) (1984604216275) (1603763774710) (1603764697844) (by decide) (by decide)

private theorem checked_prefix4_21 : prefixBox cfg cell4 21 = .ok prefix4_21 := by
  rw [prefixBox, checked_prefix4_20]
  decide +kernel

private def prefix4_22 : Box :=
  dataBox (1769791082107) (1769792076879) (1697608811844) (1697609816357) (by decide) (by decide)

private theorem checked_prefix4_22 : prefixBox cfg cell4 22 = .ok prefix4_22 := by
  rw [prefixBox, checked_prefix4_21]
  decide +kernel

private def prefix4_23 : Box :=
  dataBox (1986735342315) (1986736346699) (1771751754086) (1771752787627) (by decide) (by decide)

private theorem checked_prefix4_23 : prefixBox cfg cell4 23 = .ok prefix4_23 := by
  rw [prefixBox, checked_prefix4_22]
  decide +kernel

private def prefix4_24 : Box :=
  dataBox (1899726912125) (1899727973693) (1564866622863) (1564867706274) (by decide) (by decide)

private theorem checked_prefix4_24 : prefixBox cfg cell4 24 = .ok prefix4_24 := by
  rw [prefixBox, checked_prefix4_23]
  decide +kernel

private def prefix4_25 : Box :=
  dataBox (1786837405886) (1786838528290) (1753580663374) (1753581799507) (by decide) (by decide)

private theorem checked_prefix4_25 : prefixBox cfg cell4 25 = .ok prefix4_25 := by
  rw [prefixBox, checked_prefix4_24]
  decide +kernel

private def prefix4_26 : Box :=
  dataBox (2002462434209) (2002463557078) (1751850340616) (1751851503488) (by decide) (by decide)

private theorem checked_prefix4_26 : prefixBox cfg cell4 26 = .ok prefix4_26 := by
  rw [prefixBox, checked_prefix4_25]
  decide +kernel

private def prefix4_27 : Box :=
  dataBox (1905650351387) (1905651530714) (1563694911066) (1563696122970) (by decide) (by decide)

private theorem checked_prefix4_27 : prefixBox cfg cell4 27 = .ok prefix4_27 := by
  rw [prefixBox, checked_prefix4_26]
  decide +kernel

private def prefix4_28 : Box :=
  dataBox (1771387216121) (1771388458765) (1722280321637) (1722281588366) (by decide) (by decide)

private theorem checked_prefix4_28 : prefixBox cfg cell4 28 = .ok prefix4_28 := by
  rw [prefixBox, checked_prefix4_27]
  decide +kernel

private def prefix4_29 : Box :=
  dataBox (1961117552544) (1961118805100) (1797709048297) (1797710341336) (by decide) (by decide)

private theorem checked_prefix4_29 : prefixBox cfg cell4 29 = .ok prefix4_29 := by
  rw [prefixBox, checked_prefix4_28]
  decide +kernel

private def prefix4_30 : Box :=
  dataBox (1984852196810) (1984853487279) (1598374655195) (1598375984302) (by decide) (by decide)

private theorem checked_prefix4_30 : prefixBox cfg cell4 30 = .ok prefix4_30 := by
  rw [prefixBox, checked_prefix4_29]
  decide +kernel

private def prefix4_31 : Box :=
  dataBox (1788026983896) (1788028377390) (1614420259512) (1614421682249) (by decide) (by decide)

private theorem checked_prefix4_31 : prefixBox cfg cell4 31 = .ok prefix4_31 := by
  rw [prefixBox, checked_prefix4_30]
  decide +kernel

private def prefix4_32 : Box :=
  dataBox (1831387134128) (1831388568595) (1803890098312) (1803891561399) (by decide) (by decide)

private theorem checked_prefix4_32 : prefixBox cfg cell4 32 = .ok prefix4_32 := by
  rw [prefixBox, checked_prefix4_31]
  decide +kernel

private def prefix4_33 : Box :=
  dataBox (2013319526641) (2013320970741) (1744436584137) (1744438077470) (by decide) (by decide)

private theorem checked_prefix4_33 : prefixBox cfg cell4 33 = .ok prefix4_33 := by
  rw [prefixBox, checked_prefix4_32]
  decide +kernel

private def prefix4_34 : Box :=
  dataBox (1947402819862) (1947404322548) (1567768413723) (1567769958300) (by decide) (by decide)

private theorem checked_prefix4_34 : prefixBox cfg cell4 34 = .ok prefix4_34 := by
  rw [prefixBox, checked_prefix4_33]
  decide +kernel

private def prefix4_35 : Box :=
  dataBox (1772924021475) (1772925618445) (1631783237811) (1631784866191) (by decide) (by decide)

private theorem checked_prefix4_35 : prefixBox cfg cell4 35 = .ok prefix4_35 := by
  rw [prefixBox, checked_prefix4_34]
  decide +kernel

private def prefix4_36 : Box :=
  dataBox (1827441710291) (1827443343621) (1806737763151) (1806739428429) (by decide) (by decide)

private theorem checked_prefix4_36 : prefixBox cfg cell4 36 = .ok prefix4_36 := by
  rw [prefixBox, checked_prefix4_35]
  decide +kernel

private def prefix4_37 : Box :=
  dataBox (2004198142205) (2004199781695) (1768911389289) (1768913082835) (by decide) (by decide)

private theorem checked_prefix4_37 : prefixBox cfg cell4 37 = .ok prefix4_37 := by
  rw [prefixBox, checked_prefix4_36]
  decide +kernel

private def prefix4_38 : Box :=
  dataBox (1989924314866) (1989926000957) (1591119085192) (1591120821022) (by decide) (by decide)

private theorem checked_prefix4_38 : prefixBox cfg cell4 38 = .ok prefix4_38 := by
  rw [prefixBox, checked_prefix4_37]
  decide +kernel

private def prefix4_39 : Box :=
  dataBox (1814542899231) (1814544689438) (1575644050149) (1575645880546) (by decide) (by decide)

private theorem checked_prefix4_39 : prefixBox cfg cell4 39 = .ok prefix4_39 := by
  rw [prefixBox, checked_prefix4_38]
  decide +kernel

private def prefix4_40 : Box :=
  dataBox (1764557000222) (1764558842362) (1742150958052) (1742152834144) (by decide) (by decide)

private theorem checked_prefix4_40 : prefixBox cfg cell4 40 = .ok prefix4_40 := by
  rw [prefixBox, checked_prefix4_39]
  decide +kernel

private def prefix4_41 : Box :=
  dataBox (1912797214931) (1912799071363) (1828816001758) (1828817905838) (by decide) (by decide)

private theorem checked_prefix4_41 : prefixBox cfg cell4 41 = .ok prefix4_41 := by
  rw [prefixBox, checked_prefix4_40]
  decide +kernel

private def prefix4_42 : Box :=
  dataBox (2034333103785) (2034334980712) (1710439581945) (1710441515174) (by decide) (by decide)

private theorem checked_prefix4_42 : prefixBox cfg cell4 42 = .ok prefix4_42 := by
  rw [prefixBox, checked_prefix4_41]
  decide +kernel

private def prefix4_43 : Box :=
  dataBox (1958085049291) (1958086981976) (1561105059427) (1561107041087) (by decide) (by decide)

private theorem checked_prefix4_43 : prefixBox cfg cell4 43 = .ok prefix4_43 := by
  rw [prefixBox, checked_prefix4_42]
  decide +kernel

private def prefix4_44 : Box :=
  dataBox (1794012628785) (1794014656369) (1584681343796) (1584683411250) (by decide) (by decide)

private theorem checked_prefix4_44 : prefixBox cfg cell4 44 = .ok prefix4_44 := by
  rw [prefixBox, checked_prefix4_43]
  decide +kernel

private def prefix4_45 : Box :=
  dataBox (1759116750338) (1759118824608) (1744829059588) (1744831168492) (by decide) (by decide)

private theorem checked_prefix4_45 : prefixBox cfg cell4 45 = .ok prefix4_45 := by
  rw [prefixBox, checked_prefix4_44]
  decide +kernel

private def prefix4_46 : Box :=
  dataBox (1893054326088) (1893056415593) (1836162062360) (1836164198048) (by decide) (by decide)

private theorem checked_prefix4_46 : prefixBox cfg cell4 46 = .ok prefix4_46 := by
  rw [prefixBox, checked_prefix4_45]
  decide +kernel

private def prefix4_47 : Box :=
  dataBox (2028693502936) (2028695606631) (1750582625684) (1750584787686) (by decide) (by decide)

private theorem checked_prefix4_47 : prefixBox cfg cell4 47 = .ok prefix4_47 := by
  rw [prefixBox, checked_prefix4_46]
  decide +kernel

private def prefix4_48 : Box :=
  dataBox (2008286758532) (2008288905021) (1593199252070) (1593201452560) (by decide) (by decide)

private theorem checked_prefix4_48 : prefixBox cfg cell4 48 = .ok prefix4_48 := by
  rw [prefixBox, checked_prefix4_47]
  decide +kernel

private def prefix4_49 : Box :=
  dataBox (1859608269510) (1859610496776) (1542536859132) (1542539131547) (by decide) (by decide)

private theorem checked_prefix4_49 : prefixBox cfg cell4 49 = .ok prefix4_49 := by
  rw [prefixBox, checked_prefix4_48]
  decide +kernel

private def prefix4_50 : Box :=
  dataBox (1747172145124) (1747174435001) (1649945590292) (1649947917050) (by decide) (by decide)

private theorem checked_prefix4_50 : prefixBox cfg cell4 50 = .ok prefix4_50 := by
  rw [prefixBox, checked_prefix4_49]
  decide +kernel

private def prefix4_51 : Box :=
  dataBox (1786913548782) (1786915870225) (1798690481737) (1798692840003) (by decide) (by decide)

private theorem checked_prefix4_51 : prefixBox cfg cell4 51 = .ok prefix4_51 := by
  rw [prefixBox, checked_prefix4_50]
  decide +kernel

private def prefix4_52 : Box :=
  dataBox (1934218924400) (1934221252228) (1838056684065) (1838059066289) (by decide) (by decide)

private theorem checked_prefix4_52 : prefixBox cfg cell4 52 = .ok prefix4_52 := by
  rw [prefixBox, checked_prefix4_51]
  decide +kernel

private def prefix4_53 : Box :=
  dataBox (2042911026923) (2042913372896) (1733195114735) (1733197522893) (by decide) (by decide)

private theorem checked_prefix4_53 : prefixBox cfg cell4 53 = .ok prefix4_53 := by
  rw [prefixBox, checked_prefix4_52]
  decide +kernel

private def prefix4_54 : Box :=
  dataBox (2012299765035) (2012302153427) (1586735316000) (1586737761862) (by decide) (by decide)

private theorem checked_prefix4_54 : prefixBox cfg cell4 54 = .ok prefix4_54 := by
  rw [prefixBox, checked_prefix4_53]
  decide +kernel

private def prefix4_55 : Box :=
  dataBox (1874284829136) (1874287291891) (1532584039442) (1532586551288) (by decide) (by decide)

private theorem checked_prefix4_55 : prefixBox cfg cell4 55 = .ok prefix4_55 := by
  rw [prefixBox, checked_prefix4_54]
  decide +kernel

private def prefix4_56 : Box :=
  dataBox (1752944771565) (1752947299334) (1615436647572) (1615439216255) (by decide) (by decide)

private theorem checked_prefix4_56 : prefixBox cfg cell4 56 = .ok prefix4_56 := by
  rw [prefixBox, checked_prefix4_55]
  decide +kernel

private def prefix4_57 : Box :=
  dataBox (1750626219527) (1750628783930) (1761052046491) (1761054648863) (by decide) (by decide)

private theorem checked_prefix4_57 : prefixBox cfg cell4 57 = .ok prefix4_57 := by
  rw [prefixBox, checked_prefix4_56]
  decide +kernel

private def prefix4_58 : Box :=
  dataBox (1865771747685) (1865774326881) (1848144251306) (1848146877991) (by decide) (by decide)

private theorem checked_prefix4_58 : prefixBox cfg cell4 58 = .ok prefix4_58 := by
  rw [prefixBox, checked_prefix4_57]
  decide +kernel

private def prefix4_59 : Box :=
  dataBox (2003516487327) (2003519072937) (1809199998342) (1809202647914) (by decide) (by decide)

private theorem checked_prefix4_59 : prefixBox cfg cell4 59 = .ok prefix4_59 := by
  rw [prefixBox, checked_prefix4_58]
  decide +kernel

private def prefix4_60 : Box :=
  dataBox (2057177533983) (2057180146582) (1677787449372) (1677790127419) (by decide) (by decide)

private theorem checked_prefix4_60 : prefixBox cfg cell4 60 = .ok prefix4_60 := by
  rw [prefixBox, checked_prefix4_59]
  decide +kernel

private def prefix4_61 : Box :=
  dataBox (1989079556231) (1989082218829) (1554575720079) (1554578441500) (by decide) (by decide)

private theorem checked_prefix4_61 : prefixBox cfg cell4 61 = .ok prefix4_61 := by
  rw [prefixBox, checked_prefix4_60]
  decide +kernel

private def prefix4_62 : Box :=
  dataBox (1851897169844) (1851899916420) (1528502555735) (1528505352789) (by decide) (by decide)

private theorem checked_prefix4_62 : prefixBox cfg cell4 62 = .ok prefix4_62 := by
  rw [prefixBox, checked_prefix4_61]
  decide +kernel

private def prefix4_63 : Box :=
  dataBox (1743853038494) (1743855851033) (1615196076558) (1615198931056) (by decide) (by decide)

private theorem checked_prefix4_63 : prefixBox cfg cell4 63 = .ok prefix4_63 := by
  rw [prefixBox, checked_prefix4_62]
  decide +kernel

private def prefix4_64 : Box :=
  dataBox (1737781809108) (1737784663719) (1752500850991) (1752503743941) (by decide) (by decide)

private theorem checked_prefix4_64 : prefixBox cfg cell4 64 = .ok prefix4_64 := by
  rw [prefixBox, checked_prefix4_63]
  decide +kernel

private def prefix4_65 : Box :=
  dataBox (1834949247965) (1834952122486) (1848194857916) (1848197779023) (by decide) (by decide)

private theorem checked_prefix4_65 : prefixBox cfg cell4 65 = .ok prefix4_65 := by
  rw [prefixBox, checked_prefix4_64]
  decide +kernel

private def prefix4_66 : Box :=
  dataBox (1970142313004) (1970145188935) (1841878766733) (1841881713024) (by decide) (by decide)

private theorem checked_prefix4_66 : prefixBox cfg cell4 66 = .ok prefix4_66 := by
  rw [prefixBox, checked_prefix4_65]
  decide +kernel

private def prefix4_67 : Box :=
  dataBox (2057911264523) (2057914162086) (1740191594078) (1740194568705) (by decide) (by decide)

private theorem checked_prefix4_67 : prefixBox cfg cell4 67 = .ok prefix4_67 := by
  rw [prefixBox, checked_prefix4_66]
  decide +kernel

private def prefix4_68 : Box :=
  dataBox (2046199684009) (2046202623580) (1607371545491) (1607374558178) (by decide) (by decide)

private theorem checked_prefix4_68 : prefixBox cfg cell4 68 = .ok prefix4_68 := by
  rw [prefixBox, checked_prefix4_67]
  decide +kernel

private def prefix4_69 : Box :=
  dataBox (1944494413275) (1944497419287) (1522656059224) (1522659129725) (by decide) (by decide)

private theorem checked_prefix4_69 : prefixBox cfg cell4 69 = .ok prefix4_69 := by
  rw [prefixBox, checked_prefix4_68]
  decide +kernel

private def prefix4_70 : Box :=
  dataBox (1813524341682) (1813527441248) (1533482902239) (1533486057751) (by decide) (by decide)

private theorem checked_prefix4_70 : prefixBox cfg cell4 70 = .ok prefix4_70 := by
  rw [prefixBox, checked_prefix4_69]
  decide +kernel

private def prefix4_71 : Box :=
  dataBox (1727252532981) (1727255692628) (1631382337034) (1631385544584) (by decide) (by decide)

private theorem checked_prefix4_71 : prefixBox cfg cell4 71 = .ok prefix4_71 := by
  rw [prefixBox, checked_prefix4_70]
  decide +kernel

private def prefix4_72 : Box :=
  dataBox (1731516228871) (1731519426153) (1760890840957) (1760894083509) (by decide) (by decide)

private theorem checked_prefix4_72 : prefixBox cfg cell4 72 = .ok prefix4_72 := by
  rw [prefixBox, checked_prefix4_71]
  decide +kernel

private def prefix4_73 : Box :=
  dataBox (1821813820268) (1821817036703) (1852580363148) (1852583632375) (by decide) (by decide)

private theorem checked_prefix4_73 : prefixBox cfg cell4 73 = .ok prefix4_73 := by
  rw [prefixBox, checked_prefix4_72]
  decide +kernel

private def prefix4_74 : Box :=
  dataBox (1949411987896) (1949415205939) (1860033056400) (1860036349418) (by decide) (by decide)

private theorem checked_prefix4_74 : prefixBox cfg cell4 74 = .ok prefix4_74 := by
  rw [prefixBox, checked_prefix4_73]
  decide +kernel

private def prefix4_75 : Box :=
  dataBox (2049201695723) (2049204929685) (1781540855789) (1781544174343) (by decide) (by decide)

private theorem checked_prefix4_75 : prefixBox cfg cell4 75 = .ok prefix4_75 := by
  rw [prefixBox, checked_prefix4_74]
  decide +kernel

private def prefix4_76 : Box :=
  dataBox (2072903676910) (2072906943644) (1657665362089) (1657668712516) (by decide) (by decide)

private theorem checked_prefix4_76 : prefixBox cfg cell4 76 = .ok prefix4_76 := by
  rw [prefixBox, checked_prefix4_75]
  decide +kernel

private def prefix4_77 : Box :=
  dataBox (2010987998609) (2010991316662) (1548730555316) (1548733950246) (by decide) (by decide)

private theorem checked_prefix4_77 : prefixBox cfg cell4 77 = .ok prefix4_77 := by
  rw [prefixBox, checked_prefix4_76]
  decide +kernel

private def prefix4_78 : Box :=
  dataBox (1894349777248) (1894353170854) (1505203712775) (1505207174830) (by decide) (by decide)

private theorem checked_prefix4_78 : prefixBox cfg cell4 78 = .ok prefix4_78 := by
  rw [prefixBox, checked_prefix4_77]
  decide +kernel

private def prefix4_79 : Box :=
  dataBox (1777349328140) (1777352797962) (1545375339287) (1545378869194) (by decide) (by decide)

private theorem checked_prefix4_79 : prefixBox cfg cell4 79 = .ok prefix4_79 := by
  rw [prefixBox, checked_prefix4_78]
  decide +kernel

private def prefix4_80 : Box :=
  dataBox (1711967003702) (1711970525163) (1649474921980) (1649478496618) (by decide) (by decide)

private theorem checked_prefix4_80 : prefixBox cfg cell4 80 = .ok prefix4_80 := by
  rw [prefixBox, checked_prefix4_79]
  decide +kernel

private theorem checked_imaginary : positiveCheck cfg 80
    (input cfg (1 / 2) (1 / 2) 54 (by norm_num)) true = true := by
  change positiveCheck cfg 80 cell4 true = true
  unfold positiveCheck evaluate
  rw [checked_prefix4_80]
  decide +kernel

/-- Actual zeta has strictly positive imaginary part at the counting endpoint. -/
theorem positive : 0 < (riemannZeta ((1 / 2 : ℂ) + 54 * Complex.I)).im := by
  simpa using positive_of_check checked_imaginary
    (mem_input (by decide) (by norm_num : (1 / 2 : ℚ) ≤ 1 / 2)
      (x := (1 / 2 : ℝ)) (by norm_num) (by norm_num))

end RiemannGaussian.ZetaHeightFiftyFour.Cell4
