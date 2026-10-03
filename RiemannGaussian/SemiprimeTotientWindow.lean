/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeLongPowerRouting

/-!
# Retained global collisions around a public totient centre

Both rough local periods are odd. Their actual global order therefore
divides the quarter totient. A short, labelled global collision recovers
that quarter totient when the factor-sum offset fits the public window.
The true order is never supplied. Wider offsets and the every-run bit
bound remain open.
-/

namespace RiemannGaussian.SemiprimeTotientWindow

open SemiprimeGroupSelection SemiprimeLocalOrderRouting SemiprimeCentreFreeCover
open SemiprimeLongPowerRouting SemiprimeProgressionPrefix

/-- Retain the actual totient as a proof-side arithmetic object. -/
def totientCore (p q : ℕ) : ℕ := (p-1)*(q-1)

/-- The useful annihilator need not be the exact global order. -/
def quarterTotient (p q : ℕ) : ℕ := totientCore p q/4

/-- This estimate is computed from N and its integer square root only. -/
def quarterCentre (N : ℕ) : ℕ := (N+1-2*N.sqrt)/4

/-- Retain the literal factor-sum offset for the coverage theorem. -/
def quarterOffset (p q : ℕ) : ℕ := (p+q-2*(p*q).sqrt)/4

/-- The literal factor sum is at least twice the public square root. -/
theorem factor_sum_ge_twice_sqrt (p q : ℕ) : 2*(p*q).sqrt≤p+q := by
  have hZ : 4*(p : ℤ)*q≤((p : ℤ)+q)^2 := by
    nlinarith [sq_nonneg ((p : ℤ)-q)]
  have hN : 4*p*q≤(p+q)^2 := by exact_mod_cast hZ
  nlinarith [Nat.sqrt_le' (p*q)]

/-- Preserve both the product and sum in the exact totient identity. -/
theorem totient_sum_identity {p q : ℕ} (hp : 1<p) (hq : 1<q) :
    p*q+1=totientCore p q+(p+q) := by
  unfold totientCore
  have hP := Nat.sub_add_cancel hp.le
  have hQ := Nat.sub_add_cancel hq.le
  nlinarith

/-- Both literal field cardinalities are even on the long complement. -/
theorem four_dvd_totient {p q B : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hB : 2≤B) (h : (ZMod (p*q))ˣ) (hc : CoreData p q B h) :
    4∣totientCore p q := by
  obtain ⟨hP,hQ⟩ := local_card_bounds hp hq h hc.1
  have hp2 : p≠2 := by
    intro he
    rw [he] at hP
    norm_num only [Nat.reduceSub] at hP
    nlinarith
  have hq2 : q≠2 := by
    intro he
    rw [he] at hQ
    norm_num only [Nat.reduceSub] at hQ
    nlinarith
  have hpD : 2∣p-1 := (even_iff_two_dvd).mp (hp.even_sub_one hp2)
  have hqD : 2∣q-1 := (even_iff_two_dvd).mp (hq.even_sub_one hq2)
  simpa only [totientCore] using Nat.mul_dvd_mul hpD hqD

/-- The original rough periods certify that the global period is odd. -/
theorem core_order_coprime_four {p q B : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p≠q) (hB : 2≤B) (h : (ZMod (p*q))ˣ) (hc : CoreData p q B h) :
    (orderOf h).Coprime 4 := by
  have hleft : (orderOf (leftUnit h)).Coprime 2 :=
    (Nat.prime_two.coprime_iff_not_dvd.mpr
      (fun hd => by have hh:=hc.2.2.1 2 Nat.prime_two hd; omega)).symm
  have hright : (orderOf (rightUnit h)).Coprime 2 :=
    (Nat.prime_two.coprime_iff_not_dvd.mpr
      (fun hd => by have hh:=hc.2.2.2 2 Nat.prime_two hd; omega)).symm
  have htwo : (orderOf h).Coprime 2 := by
    rw [global_order_eq_lcm hp hq hpq h,hc.2.1.lcm_eq_mul]
    exact hleft.mul_left hright
  simpa using htwo.pow_right 2

/-- No order acquisition is needed: the projected unit is annihilated
by the quarter totient, which is proved larger than the factor sum. -/
theorem quarter_totient_properties {p q B : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hB : 2≤B) (hbudget : p*q≤B^6) (h : (ZMod (p*q))ˣ)
    (hc : CoreData p q B h) :
    h^(quarterTotient p q)=1 ∧ quarterTotient p q∣totientCore p q ∧
      p+q<quarterTotient p q := by
  have hpq := core_distinct (by omega : 0<B) h hc
  have h4 := four_dvd_totient hp hq hB h hc
  obtain ⟨hM,hS⟩ := global_order_totient_and_sum hp hq hpq (by omega) hbudget h hc.1 hc.2.1
  change orderOf h∣totientCore p q at hM
  have he : 4*quarterTotient p q=totientCore p q := Nat.mul_div_cancel' h4
  rw [←he] at hM
  have hD : orderOf h∣quarterTotient p q :=
    (core_order_coprime_four hp hq hpq hB h hc).dvd_of_dvd_mul_left hM
  have hT : 0<quarterTotient p q := by
    have hP := hp.one_lt
    have hQ := hq.one_lt
    have hpositive : 0<totientCore p q := Nat.mul_pos (by omega) (by omega)
    nlinarith
  exact ⟨(orderOf_dvd_iff_pow_eq_one).mp hD,Nat.div_dvd_of_dvd h4,
    hS.trans_le (Nat.le_of_dvd hT hD)⟩

/-- The public centre is the actual quarter totient plus the retained
offset, including every floor and remainder exactly. -/
theorem quarter_centre_encoding {p q : ℕ} (hp : 1<p) (hq : 1<q)
    (h4 : 4∣totientCore p q) :
    quarterCentre (p*q)=quarterTotient p q+quarterOffset p q := by
  have hid := totient_sum_identity hp hq
  have hamgm := factor_sum_ge_twice_sqrt p q
  have hm := Nat.mod_eq_zero_of_dvd h4
  unfold quarterCentre quarterTotient quarterOffset
  omega

/-- Retain b shifted giant values with their original block labels. -/
noncomputable def shiftedRecords {N : ℕ} (h : (ZMod N)ˣ) (C b : ℕ) : List (ℕ×ℕ) :=
  (List.range b).map fun j => (((h^C*(h^(b*j))⁻¹ : (ZMod N)ˣ) : ZMod N).val,j)

/-- The actual ordered global lookup keeps equal residues and labels. -/
noncomputable def shiftedCollision {N : ℕ} (h : (ZMod N)ˣ) (C b : ℕ) : Option (ℕ×ℕ) :=
  matchSorted (sortedRecords (babyRecords N b h)) (sortedRecords (shiftedRecords h C b))

/-- Each input list has b entries, including before and after sorting. -/
theorem shifted_records_budget {N : ℕ} (h : (ZMod N)ˣ) (C b : ℕ) :
    (sortedRecords (babyRecords N b h)).length=b ∧
    (sortedRecords (shiftedRecords h C b)).length=b := by
  simp only [sortedRecords,List.length_mergeSort,babyRecords,shiftedRecords,
    List.length_map,List.length_range,and_self]

/-- The merge makes at most 2b comparisons; construction and both sorts
remain charged setup rather than a supplied table. -/
theorem shifted_merge_budget {N : ℕ} (h : (ZMod N)ˣ) (C b : ℕ) :
    matchComparisons (sortedRecords (babyRecords N b h))
      (sortedRecords (shiftedRecords h C b))≤2*b := by
  have he := matchComparisons_le (sortedRecords (babyRecords N b h))
    (sortedRecords (shiftedRecords h C b))
  obtain ⟨hb,hg⟩ := shifted_records_budget h C b
  simpa only [hb,hg,two_mul] using he

/-- A global equality retains its bounded offset instead of being
discarded as a full-modulus GCD. -/
theorem shiftedCollision_sound {N C b i j : ℕ} [NeZero N] (h : (ZMod N)ˣ)
    (hs : shiftedCollision h C b=some (i,j)) :
    i<b ∧ j<b ∧ b*j+i<b^2 ∧ h^(b*j+i)=h^C := by
  obtain ⟨x,hx,y,hy,hv,hxi,hyj⟩ := matchSorted_sound hs
  obtain ⟨u,hu,rfl⟩ := List.mem_map.mp (mem_sortedRecords.mp hx)
  obtain ⟨v,hvb,rfl⟩ := List.mem_map.mp (mem_sortedRecords.mp hy)
  dsimp only at hxi hyj hv
  rw [←hxi,←hyj]
  have hi := List.mem_range.mp hu
  have hj := List.mem_range.mp hvb
  have hbound : b*v+u<b^2 := by
    have hh := Nat.mul_le_mul_left b (show v+1≤b by omega)
    nlinarith
  have he : h^u=h^C*(h^(b*v))⁻¹ := Units.ext (ZMod.val_injective N hv)
  have hh := congrArg (fun z : (ZMod N)ˣ => z*h^(b*v)) he
  rw [mul_assoc,inv_mul_cancel,mul_one,←pow_add] at hh
  exact ⟨hi,hj,hbound,by simpa only [Nat.add_comm] using hh⟩

/-- Every offset below b² has an actual retained global collision in
the implemented two-list lookup, including the zero offset. -/
theorem shiftedCollision_succeeds {N C b d : ℕ} (h : (ZMod N)ˣ)
    (hd : d<b^2) (he : h^d=h^C) : ∃ pair, shiftedCollision h C b=some pair := by
  have hb : 0<b := by nlinarith
  let i := d%b
  let j := d/b
  have hi : i<b := Nat.mod_lt d hb
  have hj : j<b := (Nat.div_lt_iff_lt_mul hb).mpr (by nlinarith)
  have hde : b*j+i=d := by simpa only [i,j,Nat.add_comm] using Nat.mod_add_div d b
  have hunit : h^i=h^C*(h^(b*j))⁻¹ := by
    rw [←he,←hde,Nat.add_comm (b*j) i,pow_add,mul_assoc,mul_inv_cancel,mul_one]
  have hbm : (((h^i : (ZMod N)ˣ) : ZMod N).val,i)∈sortedRecords (babyRecords N b h) :=
    mem_sortedRecords.mpr (List.mem_map.mpr ⟨i,List.mem_range.mpr hi,rfl⟩)
  have hgm : (((h^C*(h^(b*j))⁻¹ : (ZMod N)ˣ) : ZMod N).val,j)∈
      sortedRecords (shiftedRecords h C b) :=
    mem_sortedRecords.mpr (List.mem_map.mpr ⟨j,List.mem_range.mpr hj,rfl⟩)
  cases hs : shiftedCollision h C b with
  | some pair => exact ⟨pair,rfl⟩
  | none =>
    have hn := matchSorted_none_no_common
      (sortedRecords_pairwise (babyRecords N b h))
      (sortedRecords_pairwise (shiftedRecords h C b)) hs _ hbm _ hgm
    exact False.elim (hn (congrArg (fun z : (ZMod N)ˣ => (z : ZMod N).val) hunit))

/-- A supplied large totient divisor gives a checked smaller-factor
candidate. This arithmetic helper does not acquire its modulus. -/
theorem known_totient_divisor_recovers {p q t : ℕ} (hp : 1<p) (hq : 1<q)
    (hpq : p≤q) (ht : t∣totientCore p q) (hs : p+q<t) :
    recoverKnownOrder (p*q) t=some p := by
  have hc := sumCandidate_of_sum hpq (sumSignal_eq_sum hp hq ht hs)
  have hg : (p*q).gcd p=p := Nat.gcd_eq_right (dvd_mul_right p q)
  unfold recoverKnownOrder
  rw [hc,checkedSignal,hg,if_pos]
  exact ⟨hp,by nlinarith⟩

/-- Search only the public quarter-centre window, preserving offset
labels even when the original GCD would be the full input. -/
noncomputable def recoverQuarter {N : ℕ} (h : (ZMod N)ˣ) (B : ℕ) : Option ℕ :=
  match shiftedCollision h (quarterCentre N) (2*B) with
  | none => none
  | some (i,j) => recoverKnownOrder N (quarterCentre N-((2*B)*j+i))

/-- Every returned quarter-window candidate is independently checked. -/
theorem recoverQuarter_sound {N B f : ℕ} (h : (ZMod N)ˣ)
    (hf : recoverQuarter h B=some f) : ProperDivisor N f := by
  unfold recoverQuarter at hf
  split at hf
  · contradiction
  · exact recoverKnownOrder_sound hf

/-- A short retained global offset is unique when the actual period
exceeds the whole window. Neither its value nor its factorization is input. -/
theorem shiftedCollision_unique_offset {N C b d i j : ℕ} [NeZero N]
    (h : (ZMod N)ˣ) (hd : d<b^2) (hm : b^2<orderOf h) (he : h^d=h^C)
    (hs : shiftedCollision h C b=some (i,j)) : b*j+i=d := by
  obtain ⟨_,_,hbound,hpow⟩ := shiftedCollision_sound h hs
  exact pow_injOn_Iio_orderOf (x:=h) (hbound.trans hm) (hd.trans hm)
    (hpow.trans he.symm)

/-- Every covered quarter-centre offset recovers a proper factor through
the actual sorted lookup and checked quadratic decoder. -/
theorem recoverQuarter_complete {p q B : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hB : 2≤B) (hbudget : p*q≤B^6) (h : (ZMod (p*q))ˣ)
    (hc : CoreData p q B h) (hoff : quarterOffset p q<(2*B)^2) :
    ∃ f, recoverQuarter h B=some f ∧ ProperDivisor (p*q) f := by
  let : NeZero (p*q) := ⟨Nat.mul_ne_zero hp.ne_zero hq.ne_zero⟩
  have hpq := core_distinct (by omega : 0<B) h hc
  obtain ⟨hpow,hdiv,hlarge⟩ := quarter_totient_properties hp hq hB hbudget h hc
  have henc := quarter_centre_encoding hp.one_lt hq.one_lt (four_dvd_totient hp hq hB h hc)
  have he : h^(quarterOffset p q)=h^(quarterCentre (p*q)) := by
    rw [henc,pow_add,hpow,one_mul]
  obtain ⟨⟨i,j⟩,hs⟩ := shiftedCollision_succeeds h hoff he
  have hlocal : orderOf (leftUnit h)∣orderOf h := by
    rw [global_order_eq_lcm hp hq hpq h]
    exact Nat.dvd_lcm_left _ _
  have hm : (2*B)^2<orderOf h :=
    hc.1.1.trans_le (Nat.le_of_dvd (orderOf_pos h) hlocal)
  have hlabel := shiftedCollision_unique_offset h hoff hm he hs
  have hsub : quarterCentre (p*q)-((2*B)*j+i)=quarterTotient p q := by
    rw [hlabel,henc]
    omega
  have hdecode : ∃ f, recoverKnownOrder (p*q) (quarterTotient p q)=some f ∧
      ProperDivisor (p*q) f := by
    by_cases horder : p≤q
    · have hf := known_totient_divisor_recovers hp.one_lt hq.one_lt horder hdiv hlarge
      exact ⟨p,hf,recoverKnownOrder_sound hf⟩
    · have horder' : q≤p := by omega
      have hdiv' : quarterTotient p q∣totientCore q p := by
        simpa only [totientCore,Nat.mul_comm] using hdiv
      have hlarge' : q+p<quarterTotient p q := by omega
      have hf := known_totient_divisor_recovers hq.one_lt hp.one_lt horder' hdiv' hlarge'
      rw [Nat.mul_comm q p] at hf
      exact ⟨q,hf,recoverKnownOrder_sound hf⟩
  obtain ⟨f,hf,hproper⟩ := hdecode
  exact ⟨f,by simpa only [recoverQuarter,hs,hsub] using hf,hproper⟩

/-- A failed actual quarter window certifies a large literal factor-sum
gap. It is a strengthened residual population, not universal recovery. -/
theorem recoverQuarter_none_gap {p q B : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hB : 2≤B) (hbudget : p*q≤B^6) (h : (ZMod (p*q))ˣ)
    (hc : CoreData p q B h) (hn : recoverQuarter h B=none) :
    4*(2*B)^2≤p+q-2*(p*q).sqrt := by
  have hbig : (2*B)^2≤quarterOffset p q := by
    by_contra he
    obtain ⟨f,hf,_⟩ := recoverQuarter_complete hp hq hB hbudget h hc (by omega)
    rw [hn] at hf
    contradiction
  unfold quarterOffset at hbig
  omega

/-- Retain the complete labelled window before decoding its summary. -/
structure Source (N : ℕ) where
  /-- The cached active unit from the preceding long-power route. -/
  active : (ZMod N)ˣ
  /-- Public quarter-totient centre used for this window. -/
  centre : ℕ
  /-- Public centre power, retained as a group element. -/
  target : (ZMod N)ˣ
  /-- Sorted baby residues with all original exponent labels. -/
  babies : List (ℕ×ℕ)
  /-- Sorted shifted residues with all original block labels. -/
  giants : List (ℕ×ℕ)
  /-- The actual global equality returned by the ordered merge. -/
  collision : Option (ℕ×ℕ)
  /-- The checked factor candidate decoded from that equality. -/
  factor : Option ℕ

/-- Build each window source once from the cached unit and public input;
retain the actual lists and match even when the decoder has no factor. -/
noncomputable def buildSource {N : ℕ} (h : (ZMod N)ˣ) (B : ℕ) : Source N :=
  let C := quarterCentre N
  let target := h^C
  let babies := sortedRecords (babyRecords N (2*B) h)
  let giants := sortedRecords (shiftedRecords h C (2*B))
  let collision := matchSorted babies giants
  let factor := match collision with
    | none => none
    | some (i,j) => recoverKnownOrder N (C-((2*B)*j+i))
  ⟨h,C,target,babies,giants,collision,factor⟩

/-- The factor option is a downstream view of the retained source. -/
theorem buildSource_factor {N : ℕ} (h : (ZMod N)ˣ) (B : ℕ) :
    (buildSource h B).factor=recoverQuarter h B := rfl

/-- Two actual 2B-entry sorted lists require at most 4B merge comparisons.
Power construction, both sorts and their bit costs remain separate charges. -/
theorem buildSource_budget {N : ℕ} (h : (ZMod N)ˣ) (B : ℕ) :
    (buildSource h B).babies.length=2*B ∧ (buildSource h B).giants.length=2*B ∧
    matchComparisons (buildSource h B).babies (buildSource h B).giants≤4*B := by
  obtain ⟨hb,hg⟩ := shifted_records_budget h (quarterCentre N) (2*B)
  refine ⟨hb,hg,?_⟩
  have hh := shifted_merge_budget h (quarterCentre N) (2*B)
  change matchComparisons (sortedRecords (babyRecords N (2*B) h))
    (sortedRecords (shiftedRecords h (quarterCentre N) (2*B)))≤4*B
  omega

/-- Every source decoder checks its candidate independently. -/
theorem buildSource_sound {N B d : ℕ} (h : (ZMod N)ˣ)
    (hd : (buildSource h B).factor=some d) : ProperDivisor N d :=
  recoverQuarter_sound h hd

/-- Every semiprime's public sixth-root width is at least two. -/
theorem sixthWidth_ge_two {N : ℕ} (hN : 4≤N) :
    2≤SemiprimeLehmanCoverage.sixthWidth N := by
  have hpos := SemiprimeKernelDescent.sixthWidth_pos (by omega : 0<N)
  have hbudget := SemiprimeLehmanCoverage.sixthWidth_upper N
  by_contra he
  have hw : SemiprimeLehmanCoverage.sixthWidth N=1 := by omega
  rw [hw] at hbudget
  norm_num at hbudget
  omega

/-- A retained window certificate comes from the actual preceding long
route. It does not supply the numerical order or quarter totient. -/
inductive WindowCertified : {N : ℕ} → Source N → Prop where
  | remaining {p q : ℕ} {g h z s : (ZMod (p*q))ˣ}
      (hp : p.Prime) (hq : q.Prime)
      (hd : GoodPower p q (SemiprimeLehmanCoverage.sixthWidth (p*q)) (.remaining g h z s)) :
      WindowCertified (buildSource h (SemiprimeLehmanCoverage.sixthWidth (p*q)))

/-- A certified source's successful factor is proper for its literal input. -/
theorem windowCertified_factor {N d : ℕ} {source : Source N}
    (hc : WindowCertified source) (hd : source.factor=some d) : ProperDivisor N d := by
  cases hc with
  | remaining hp hq hdata => exact buildSource_sound _ hd

/-- A failed certified source retains a true semiprime and the large
literal factor-sum gap, including the actual public leaf width. -/
theorem windowCertified_gap {N : ℕ} {source : Source N}
    (hc : WindowCertified source) (hn : source.factor=none) :
    ∃ p q, p.Prime ∧ q.Prime ∧ N=p*q ∧
      4*(2*SemiprimeLehmanCoverage.sixthWidth N)^2≤p+q-2*N.sqrt := by
  cases hc with
  | @remaining p q g h z s hp hq hdata =>
    have hN : 4≤p*q := by nlinarith [hp.two_le,hq.two_le]
    have hcore : CoreData p q (SemiprimeLehmanCoverage.sixthWidth (p*q)) h := by
      rw [hdata.2.1]
      exact projected_core g hdata.1
    exact ⟨p,q,hp,hq,rfl,recoverQuarter_none_gap hp hq (sixthWidth_ge_two hN)
      (SemiprimeLehmanCoverage.sixthWidth_upper _) h hcore hn⟩

/-- Refine only an actual remaining power leaf; factor leaves construct
no new source. The cached active unit is used without reprojecting. -/
noncomputable def sourceForLeaf {N : ℕ} : PowerRoute N → Option (Source N)
  | .remaining _ h _ _ => some (buildSource h (SemiprimeLehmanCoverage.sixthWidth N))
  | _ => none

/-- A certified preceding leaf gives a certified actual window source. -/
theorem sourceForLeaf_certified {N : ℕ} {leaf : PowerRoute N} {source : Source N}
    (hc : PowerCertified leaf) (hs : sourceForLeaf leaf=some source) : WindowCertified source := by
  cases hc with
  | factor hp hq hd => simp only [sourceForLeaf] at hs; contradiction
  | remaining hp hq hd =>
    have he := Option.some.inj hs
    rw [←he]
    exact .remaining hp hq hd

/-- Every certified nonfactor leaf supplies an actual retained window. -/
theorem sourceForLeaf_exists {N : ℕ} {leaf : PowerRoute N} (hc : PowerCertified leaf)
    (hn : ∀ d, leaf≠.factor d) : ∃ source, sourceForLeaf leaf=some source := by
  cases leaf with
  | factor d => exact False.elim (hn d rfl)
  | remaining g h z s => exact ⟨_,rfl⟩
  | unresolved => exact False.elim (powerCertified_not_unresolved hc)

/-- Reuse an already recovered original factor, or transport only a new
window factor through the preceding retained descent. -/
noncomputable def factorWithSource {N : ℕ} (parent : SemiprimeLongPowerRouting.Packet N)
    (source : Option (Source (SemiprimeKernelDescent.leafInput parent.source))) : Option ℕ :=
  match parent.factor with
  | some d => some d
  | none => match source with
    | none => none
    | some source => match source.factor with
      | none => none
      | some d => transportCandidate parent.source d

/-- The richer packet retains the preceding complete descent and its
power channels alongside the actual labelled window. -/
structure Packet (N : ℕ) where
  /-- Complete preceding public result and every original parent frame. -/
  parent : SemiprimeLongPowerRouting.Packet N
  /-- The actual new source, if the remaining leaf required a window. -/
  source : Option (Source (SemiprimeKernelDescent.leafInput parent.source))
  /-- Downstream checked original-input factor when available. -/
  factor : Option ℕ

/-- N-only public refinement uses the preceding result once and reuses
its projected unit. Every new source and successful transport is charged. -/
noncomputable def publicPacket (N : ℕ) : Packet N :=
  let parent := SemiprimeLongPowerRouting.publicPacket N
  let source := sourceForLeaf parent.leaf
  ⟨parent,source,factorWithSource parent source⟩

/-- Every original-input factor from the full quarter-window refinement
is proper, including an already successful preceding stage. -/
theorem publicPacket_sound {p q d : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hf : (publicPacket (p*q)).factor=some d) : ProperDivisor (p*q) d := by
  dsimp only [publicPacket] at hf
  unfold factorWithSource at hf
  cases hold : (SemiprimeLongPowerRouting.publicPacket (p*q)).factor with
  | some f =>
    simp only [hold] at hf
    obtain ⟨e,he,hproper⟩ | hn := SemiprimeLongPowerRouting.publicPacket_cases hp hq
    · rw [hold] at he
      have hed : e=d := (Option.some.inj he).symm.trans (Option.some.inj hf)
      rwa [hed] at hproper
    · have hfalse := hn.1
      rw [hold] at hfalse
      contradiction
  | none =>
    simp only [hold] at hf
    cases hs : sourceForLeaf (SemiprimeLongPowerRouting.publicPacket (p*q)).leaf with
    | none => simp only [hs] at hf; contradiction
    | some source =>
      simp only [hs] at hf
      cases hd : source.factor with
      | none => simp only [hd] at hf; contradiction
      | some f =>
        simp only [hd] at hf
        exact transportCandidate_sound (SemiprimeKernelDescent.publicTrace_certified hp hq) hf

/-- The full public result either recovers an original factor or keeps
an actual certified long window whose literal factor-sum gap is large. -/
theorem publicPacket_cases {p q : ℕ} (hp : p.Prime) (hq : q.Prime) :
    (∃ d,(publicPacket (p*q)).factor=some d ∧ ProperDivisor (p*q) d) ∨
    ((publicPacket (p*q)).factor=none ∧ ∃ source,
      (publicPacket (p*q)).source=some source ∧ WindowCertified source ∧ source.factor=none ∧
      ∃ u v, u.Prime ∧ v.Prime ∧
        SemiprimeKernelDescent.leafInput (publicPacket (p*q)).parent.source=u*v ∧
        4*(2*SemiprimeLehmanCoverage.sixthWidth
          (SemiprimeKernelDescent.leafInput (publicPacket (p*q)).parent.source))^2≤
            u+v-2*(SemiprimeKernelDescent.leafInput (publicPacket (p*q)).parent.source).sqrt) := by
  cases hf : (publicPacket (p*q)).factor with
  | some d => exact Or.inl ⟨d,rfl,publicPacket_sound hp hq hf⟩
  | none =>
    right
    refine ⟨rfl,?_⟩
    obtain ⟨d,hd,hproper⟩ | ⟨hn,hc,hnot⟩ := SemiprimeLongPowerRouting.publicPacket_cases hp hq
    · have he : (publicPacket (p*q)).factor=some d := by
        simp only [publicPacket,factorWithSource,hd]
      rw [hf] at he
      contradiction
    · obtain ⟨source,hs⟩ := sourceForLeaf_exists hc hnot
      have hsource := sourceForLeaf_certified hc hs
      have hnone : source.factor=none := by
        cases hd : source.factor with
        | none => rfl
        | some d =>
          have hproper := windowCertified_factor hsource hd
          obtain ⟨f,hf',_⟩ := transportCandidate_complete
            (SemiprimeKernelDescent.publicTrace_certified hp hq) hproper
          have he : (publicPacket (p*q)).factor=some f := by
            simp only [publicPacket,factorWithSource,hn,hs,hd]
            exact hf'
          rw [hf] at he
          contradiction
      exact ⟨source,hs,hsource,hnone,windowCertified_gap hsource hnone⟩

/-- An actual leaf source has exactly two linear-size lists and one
bounded merge, independently of which labelled equality was selected. -/
theorem sourceForLeaf_budget {N : ℕ} {leaf : PowerRoute N} {source : Source N}
    (hs : sourceForLeaf leaf=some source) :
    source.babies.length=2*SemiprimeLehmanCoverage.sixthWidth N ∧
      source.giants.length=2*SemiprimeLehmanCoverage.sixthWidth N ∧
      matchComparisons source.babies source.giants≤4*SemiprimeLehmanCoverage.sixthWidth N := by
  cases leaf with
  | factor d => simp only [sourceForLeaf] at hs; contradiction
  | unresolved => simp only [sourceForLeaf] at hs; contradiction
  | remaining g h z s =>
    have he := Option.some.inj hs
    rw [←he]
    exact buildSource_budget h _

/-- Every new source fits the ORIGINAL input's sixth-root width after
all retained descents. This does not assert a complete bit backend. -/
theorem publicPacket_source_budget {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    {source : Source (SemiprimeKernelDescent.leafInput (publicPacket (p*q)).parent.source)}
    (hs : (publicPacket (p*q)).source=some source) :
    source.babies.length≤2*SemiprimeLehmanCoverage.sixthWidth (p*q) ∧
      source.giants.length≤2*SemiprimeLehmanCoverage.sixthWidth (p*q) ∧
      matchComparisons source.babies source.giants≤4*SemiprimeLehmanCoverage.sixthWidth (p*q) := by
  have hb := sourceForLeaf_budget hs
  have hw := SemiprimeKernelDescent.sixthWidth_mono
    (certified_leaf_input_le (SemiprimeKernelDescent.publicTrace_certified hp hq))
  change source.babies.length=2*SemiprimeLehmanCoverage.sixthWidth
      (SemiprimeKernelDescent.leafInput (SemiprimeKernelDescent.publicTrace (p*q))) ∧
    source.giants.length=2*SemiprimeLehmanCoverage.sixthWidth
      (SemiprimeKernelDescent.leafInput (SemiprimeKernelDescent.publicTrace (p*q))) ∧
    matchComparisons source.babies source.giants≤4*SemiprimeLehmanCoverage.sixthWidth
      (SemiprimeKernelDescent.leafInput (SemiprimeKernelDescent.publicTrace (p*q))) at hb
  omega

set_option maxRecDepth 32768 in
/-- Exact quarter offsets and quadratic decoders for the three old long
leaves. Literal preceding route selection remains a separate replay. -/
theorem control_old_leaf_arithmetic :
    quarterOffset 44963 62347=354 ∧ (354 : ℕ)<(2*38)^2 ∧
    quarterCentre 2803308161=700800567 ∧
    recoverKnownOrder 2803308161 (700800567-354)=some 44963 ∧
    quarterOffset 714107 1013003=6515 ∧ (6515 : ℕ)<(2*95)^2 ∧
    quarterCentre 723392533321=180847708068 ∧
    recoverKnownOrder 723392533321 (180847708068-6515)=some 714107 ∧
    quarterOffset 74099 197599=7423 ∧ (7423 : ℕ)<(2*50)^2 ∧
    quarterCentre 14641888301=3660411574 ∧
    recoverKnownOrder 14641888301 (3660411574-7423)=some 74099 := by
  norm_num [quarterOffset,quarterCentre,recoverKnownOrder,sumCandidate,sumSignal,checkedSignal]

/-- The old first leaf's global equality carries a nonzero, bounded
offset. Both scalar powers are checked by fast modular arithmetic. -/
theorem control_first_leaf_powers :
    (183584004 : ZMod 2803308161)^700800567=1216857719 ∧
    (183584004 : ZMod 2803308161)^354=1216857719 := by
  constructor <;> reduce_mod_char

set_option maxRecDepth 32768 in
/-- A larger selected control lies beyond the covered window. These
exact arithmetic facts do not assert an unconditional failure theorem. -/
theorem control_large_gap_arithmetic :
    (1000000007 : ℕ)*1400000543=1400000552800003801 ∧
    quarterOffset 1000000007 1400000543=8392042 ∧
    (2*1058 : ℕ)^2=4477456 ∧ (4477456 : ℕ)<8392042 ∧
    1400000552800003801≤(1058 : ℕ)^6 := by
  norm_num [quarterOffset]

end RiemannGaussian.SemiprimeTotientWindow
