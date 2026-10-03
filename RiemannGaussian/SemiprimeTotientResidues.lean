/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeTotientWindow

/-!
# Proper field collisions in the retained quarter-totient window

Reuse the actual sorted quarter-window lists for one distinct-root
polynomial batch. A short offset modulo either hidden local period is
enough, even when the literal offset exceeds the global window. No period
is supplied to the public procedure. Universal coverage and the complete
every-run bit bound remain open.
-/

namespace RiemannGaussian.SemiprimeTotientResidues

open SemiprimeGroupSelection SemiprimeLocalOrderRouting SemiprimeCentreFreeCover
open SemiprimeLongPowerRouting SemiprimeTotientWindow SemiprimeProgressionPrefix
open SemiprimeCartesianCompletion

/-- Recover the residue represented by each retained labelled record. -/
def recordValues {N : ℕ} (records : List (ℕ×ℕ)) : List (ZMod N) :=
  records.map fun entry => (entry.1 : ZMod N)

/-- Reuse the preceding shifted values as polynomial roots. -/
def windowRoots {N : ℕ} (source : SemiprimeTotientWindow.Source N) : List (ZMod N) :=
  recordValues source.giants

/-- Reuse the preceding baby values as evaluation targets. -/
def windowTargets {N : ℕ} (source : SemiprimeTotientWindow.Source N) : List (ZMod N) :=
  recordValues source.babies

/-- Retain the actual residue batch and its evaluated columns. -/
structure ResidueSource (N : ℕ) where
  /-- Roots cast from the cached shifted records. -/
  roots : List (ZMod N)
  /-- Targets cast from the cached baby records. -/
  targets : List (ZMod N)
  /-- Distinct global roots of the detector polynomial. -/
  distinct : Finset (ZMod N)
  /-- Evaluated deflated columns, each with its actual target identifier. -/
  columns : List (ℕ×ℕ)
  /-- The checked proper factor supplied by these actual columns. -/
  factor : Option ℕ

/-- Construct one batch from the retained lists, without new powers or
another window. The existing lazy leaf scan is used only when needed. -/
noncomputable def buildResidueSource {N : ℕ}
    (window : SemiprimeTotientWindow.Source N) : ResidueSource N :=
  let roots := windowRoots window
  let targets := windowTargets window
  let distinct := roots.toFinset
  let columns := evaluatedColumns distinct targets
  let factor := recoverColumns N (fun i => residueLeaves distinct (i : ZMod N)) columns
  ⟨roots,targets,distinct,columns,factor⟩

/-- The retained factor comes from the proved complete polynomial batch. -/
theorem buildResidueSource_factor {N : ℕ} (window : SemiprimeTotientWindow.Source N) :
    (buildResidueSource window).factor=
      recoverResidueBatch (windowRoots window).toFinset (windowTargets window) := rfl

/-- Every successful new batch checks a proper factor of its literal input. -/
theorem buildResidueSource_sound {N d : ℕ} (window : SemiprimeTotientWindow.Source N)
    (hd : (buildResidueSource window).factor=some d) : ProperDivisor N d :=
  recoverResidueBatch_sound hd

/-- The quarter offset is below the actual global period even outside
the covered literal window. The period is proof-side information only. -/
theorem quarterOffset_lt_order {p q B : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hB : 2≤B) (hbudget : p*q≤B^6) (h : (ZMod (p*q))ˣ)
    (hc : CoreData p q B h) : quarterOffset p q<orderOf h := by
  have hpq := core_distinct (by omega : 0<B) h hc
  have hlarge := (global_order_totient_and_sum hp hq hpq (by omega) hbudget h hc.1 hc.2.1).2
  have hle : quarterOffset p q≤p+q := by
    unfold quarterOffset
    exact (Nat.div_le_self _ _).trans (Nat.sub_le _ _)
  exact hle.trans_lt hlarge

/-- The cancelled centre power agrees with the literal offset power. -/
theorem quarter_power_offset {p q B : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hB : 2≤B) (hbudget : p*q≤B^6) (h : (ZMod (p*q))ˣ)
    (hc : CoreData p q B h) : h^(quarterOffset p q)=h^(quarterCentre (p*q)) := by
  have hpow := (quarter_totient_properties hp hq hB hbudget h hc).1
  have henc := quarter_centre_encoding hp.one_lt hq.one_lt (four_dvd_totient hp hq hB h hc)
  rw [henc,pow_add,hpow,one_mul]

/-- Every actual global match is the literal offset, not a wrapped global
offset. A successful match is therefore within the proved decoder range. -/
theorem global_match_offset {p q B i j : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hB : 2≤B) (hbudget : p*q≤B^6) (h : (ZMod (p*q))ˣ)
    (hc : CoreData p q B h)
    (hs : shiftedCollision h (quarterCentre (p*q)) (2*B)=some (i,j)) :
    (2*B)*j+i=quarterOffset p q ∧ quarterOffset p q<(2*B)^2 := by
  let : NeZero (p*q) := ⟨Nat.mul_ne_zero hp.ne_zero hq.ne_zero⟩
  obtain ⟨_,_,hbound,hpow⟩ := shiftedCollision_sound h hs
  have hpq := core_distinct (by omega : 0<B) h hc
  have hdiv : orderOf (leftUnit h)∣orderOf h := by
    rw [global_order_eq_lcm hp hq hpq h]
    exact Nat.dvd_lcm_left _ _
  have hm := hc.1.1.trans_le (Nat.le_of_dvd (orderOf_pos h) hdiv)
  have he := quarter_power_offset hp hq hB hbudget h hc
  have hlabel := pow_injOn_Iio_orderOf (x:=h) (hbound.trans hm)
    (quarterOffset_lt_order hp hq hB hbudget h hc) (hpow.trans he.symm)
  exact ⟨hlabel,by rwa [hlabel] at hbound⟩

/-- A failed actual global decoder has no global match to deflate. -/
theorem failed_window_no_global {p q B : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hB : 2≤B) (hbudget : p*q≤B^6) (h : (ZMod (p*q))ˣ)
    (hc : CoreData p q B h) (hn : recoverQuarter h B=none) :
    shiftedCollision h (quarterCentre (p*q)) (2*B)=none := by
  cases hs : shiftedCollision h (quarterCentre (p*q)) (2*B) with
  | none => rfl
  | some pair =>
    obtain ⟨i,j⟩ := pair
    have hsmall := (global_match_offset hp hq hB hbudget h hc hs).2
    obtain ⟨f,hf,_⟩ := recoverQuarter_complete hp hq hB hbudget h hc hsmall
    rw [hn] at hf
    contradiction

/-- An actual baby residue belongs to the cached batch targets. -/
theorem baby_mem_windowTargets {N B i : ℕ} [NeZero N] (h : (ZMod N)ˣ)
    (hi : i<2*B) : (h^i : ZMod N)∈windowTargets (buildSource h B) := by
  apply List.mem_map.mpr
  refine ⟨(((h^i : (ZMod N)ˣ) : ZMod N).val,i),?_,?_⟩
  · exact mem_sortedRecords.mpr (List.mem_map.mpr ⟨i,List.mem_range.mpr hi,rfl⟩)
  · exact ZMod.natCast_zmod_val _

/-- An actual shifted residue belongs to the cached batch roots. -/
theorem shifted_mem_windowRoots {N B j : ℕ} [NeZero N] (h : (ZMod N)ˣ)
    (hj : j<2*B) :
    ((h^(quarterCentre N)*(h^((2*B)*j))⁻¹ : (ZMod N)ˣ) : ZMod N)∈
      windowRoots (buildSource h B) := by
  apply List.mem_map.mpr
  refine ⟨(((h^(quarterCentre N)*(h^((2*B)*j))⁻¹ : (ZMod N)ˣ) : ZMod N).val,j),?_,?_⟩
  · exact mem_sortedRecords.mpr (List.mem_map.mpr ⟨j,List.mem_range.mpr hj,rfl⟩)
  · exact ZMod.natCast_zmod_val _

/-- A failed ordered global lookup proves every original baby/shifted
pair globally unequal, without enumerating its Cartesian grid. -/
theorem shifted_pair_ne_of_no_global {N B i j : ℕ}
    (h : (ZMod N)ˣ) (hi : i<2*B) (hj : j<2*B)
    (hn : shiftedCollision h (quarterCentre N) (2*B)=none) :
    (h^i : ZMod N)≠((h^(quarterCentre N)*(h^((2*B)*j))⁻¹ : (ZMod N)ˣ) : ZMod N) := by
  have hb : (((h^i : (ZMod N)ˣ) : ZMod N).val,i)∈
      sortedRecords (babyRecords N (2*B) h) :=
    mem_sortedRecords.mpr (List.mem_map.mpr ⟨i,List.mem_range.mpr hi,rfl⟩)
  have hg : (((h^(quarterCentre N)*(h^((2*B)*j))⁻¹ : (ZMod N)ˣ) : ZMod N).val,j)∈
      sortedRecords (shiftedRecords h (quarterCentre N) (2*B)) :=
    mem_sortedRecords.mpr (List.mem_map.mpr ⟨j,List.mem_range.mpr hj,rfl⟩)
  have he := matchSorted_none_no_common (sortedRecords_pairwise _)
    (sortedRecords_pairwise _) hn _ hb _ hg
  intro heq
  exact he (congrArg ZMod.val heq)

/-- A nonzero original residual vanishing modulo any nontrivial divisor
gives a proper GCD of the original modulus. -/
theorem proper_gcd_of_reduction {N r : ℕ} [NeZero N] (hr : r∣N) (hr1 : 1<r)
    (z : ZMod N) (hz : z≠0) (he : ZMod.castHom hr (ZMod r) z=0) :
    ProperDivisor N (N.gcd z.val) := by
  have hd : r∣z.val := by
    apply (ZMod.natCast_eq_zero_iff _ r).mp
    rwa [castHom_val hr]
  have hD := Nat.dvd_gcd hr hd
  have hpos := Nat.gcd_pos_of_pos_left z.val (NeZero.pos N)
  have hlow := Nat.le_of_dvd hpos hD
  have hle := Nat.gcd_le_left z.val (NeZero.pos N)
  have hne : N.gcd z.val≠N := by
    intro hh
    exact hz (SemiprimeSourceHead.residual_zero_of_gcd_eq_modulus z hh)
  exact ⟨by omega,by omega,Nat.gcd_dvd_left _ _⟩

/-- A covered offset in any divisor ring supplies a proper original pair
when the preceding global lookup has no equality. Its local period is
used only to prove coverage, never as an input to the detector. -/
theorem residue_source_of_reduced_offset {N r B d : ℕ} [NeZero N]
    (hr : r∣N) (hr1 : 1<r) (h : (ZMod N)ˣ)
    (hn : shiftedCollision h (quarterCentre N) (2*B)=none)
    (he : h^d=h^(quarterCentre N))
    (hoff : d%orderOf (Units.map (ZMod.castHom hr (ZMod r)).toMonoidHom h)<(2*B)^2) :
    ∃ f,(buildResidueSource (buildSource h B)).factor=some f := by
  let u := Units.map (ZMod.castHom hr (ZMod r)).toMonoidHom h
  let b := 2*B
  let k := d%orderOf u
  have hk : k<b^2 := hoff
  have hb : 0<b := by nlinarith
  let i := k%b
  let j := k/b
  have hi : i<b := Nat.mod_lt k hb
  have hj : j<b := (Nat.div_lt_iff_lt_mul hb).mpr (by nlinarith)
  have hde : b*j+i=k := by simpa only [i,j,Nat.add_comm] using Nat.mod_add_div k b
  have hu : u^d=u^(quarterCentre N) := by
    simpa only [u,map_pow] using congrArg (Units.map (ZMod.castHom hr (ZMod r)).toMonoidHom) he
  have hpow : u^k=u^(quarterCentre N) := (pow_mod_orderOf u d).trans hu
  have hunit : u^i=u^(quarterCentre N)*(u^(b*j))⁻¹ := by
    rw [←hpow,←hde,Nat.add_comm (b*j) i,pow_add,mul_assoc,mul_inv_cancel,mul_one]
  let z : ZMod N := (h^i : ZMod N)-
    ((h^(quarterCentre N)*(h^(b*j))⁻¹ : (ZMod N)ˣ) : ZMod N)
  have hz : z≠0 := sub_ne_zero.mpr (shifted_pair_ne_of_no_global h hi hj hn)
  have hlocal : ZMod.castHom hr (ZMod r) z=0 := by
    change ZMod.castHom hr (ZMod r) (_-_)=0
    rw [map_sub]
    apply sub_eq_zero.mpr
    have hmap : Units.map (ZMod.castHom hr (ZMod r)).toMonoidHom (h^i)=
        Units.map (ZMod.castHom hr (ZMod r)).toMonoidHom
          (h^(quarterCentre N)*(h^(b*j))⁻¹) := by
      simpa only [map_pow,map_mul,map_inv] using hunit
    exact congrArg (fun v : (ZMod r)ˣ => (v : ZMod r)) hmap
  have hproper := proper_gcd_of_reduction hr hr1 z hz hlocal
  exact recoverResidueList_succeeds_of_proper_pair (shifted_mem_windowRoots h hj)
    (baby_mem_windowTargets h hi) hproper

/-- Failure of the global decoder still allows recovery when the literal
offset wraps to a short value in the first hidden field. -/
theorem residue_source_of_left_offset {p q B : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hB : 2≤B) (hbudget : p*q≤B^6) (h : (ZMod (p*q))ˣ)
    (hc : CoreData p q B h) (hn : recoverQuarter h B=none)
    (hoff : quarterOffset p q%orderOf (leftUnit h)<(2*B)^2) :
    ∃ f,(buildResidueSource (buildSource h B)).factor=some f := by
  let : NeZero (p*q) := ⟨Nat.mul_ne_zero hp.ne_zero hq.ne_zero⟩
  exact residue_source_of_reduced_offset (dvd_mul_right p q) hp.one_lt h
    (failed_window_no_global hp hq hB hbudget h hc hn)
    (quarter_power_offset hp hq hB hbudget h hc) hoff

/-- The same cached batch recovers the second-field orientation. -/
theorem residue_source_of_right_offset {p q B : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hB : 2≤B) (hbudget : p*q≤B^6) (h : (ZMod (p*q))ˣ)
    (hc : CoreData p q B h) (hn : recoverQuarter h B=none)
    (hoff : quarterOffset p q%orderOf (rightUnit h)<(2*B)^2) :
    ∃ f,(buildResidueSource (buildSource h B)).factor=some f := by
  let : NeZero (p*q) := ⟨Nat.mul_ne_zero hp.ne_zero hq.ne_zero⟩
  exact residue_source_of_reduced_offset (dvd_mul_left q p) hq.one_lt h
    (failed_window_no_global hp hq hB hbudget h hc hn)
    (quarter_power_offset hp hq hB hbudget h hc) hoff

/-- A failed actual residue batch excludes both short reduced offsets.
This is the remaining universal coverage question, not an assumed cover. -/
theorem residue_source_none_offsets {p q B : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hB : 2≤B) (hbudget : p*q≤B^6) (h : (ZMod (p*q))ˣ)
    (hc : CoreData p q B h) (hn : recoverQuarter h B=none)
    (hf : (buildResidueSource (buildSource h B)).factor=none) :
    (2*B)^2≤quarterOffset p q%orderOf (leftUnit h) ∧
      (2*B)^2≤quarterOffset p q%orderOf (rightUnit h) := by
  constructor
  · by_contra he
    obtain ⟨f,hs⟩ := residue_source_of_left_offset hp hq hB hbudget h hc hn (by omega)
    rw [hf] at hs
    contradiction
  · by_contra he
    obtain ⟨f,hs⟩ := residue_source_of_right_offset hp hq hB hbudget h hc hn (by omega)
    rw [hf] at hs
    contradiction

/-- The two cached lists also bound roots, targets and every actual column. -/
theorem buildResidueSource_budget {N : ℕ} (h : (ZMod N)ˣ) (B : ℕ) :
    (buildResidueSource (buildSource h B)).roots.length=2*B ∧
    (buildResidueSource (buildSource h B)).targets.length=2*B ∧
    (buildResidueSource (buildSource h B)).distinct.card≤2*B ∧
    (buildResidueSource (buildSource h B)).columns.length=2*B := by
  obtain ⟨hb,hg,_⟩ := buildSource_budget h B
  have hroots : (windowRoots (buildSource h B)).length=2*B := by
    simpa only [windowRoots,recordValues,List.length_map] using hg
  have htargets : (windowTargets (buildSource h B)).length=2*B := by
    simpa only [windowTargets,recordValues,List.length_map] using hb
  refine ⟨hroots,htargets,?_,?_⟩
  · exact ((windowRoots (buildSource h B)).toFinset_card_le).trans_eq hroots
  · simpa only [buildResidueSource,evaluatedColumns,List.length_map] using htargets

/-- At most 4B new GCD queries include the possible lazy root scan.
Polynomial construction and evaluation retain their separate bit charges. -/
theorem buildResidueSource_gcd_bound {N : ℕ} (h : (ZMod N)ˣ) (B : ℕ) :
    recoveryGcdCount N
      (fun i => residueLeaves (buildResidueSource (buildSource h B)).distinct (i : ZMod N))
      (buildResidueSource (buildSource h B)).columns≤4*B := by
  have hbound := recoverResidueList_gcd_bound (windowRoots (buildSource h B))
    (windowTargets (buildSource h B))
  obtain ⟨hroots,htargets,_,_⟩ := buildResidueSource_budget h B
  change (windowRoots (buildSource h B)).length=2*B at hroots
  change (windowTargets (buildSource h B)).length=2*B at htargets
  change recoveryGcdCount N
    (fun i => residueLeaves (windowRoots (buildSource h B)).toFinset (i : ZMod N))
    (evaluatedColumns (windowRoots (buildSource h B)).toFinset
      (windowTargets (buildSource h B)))≤4*B
  rw [hroots,htargets] at hbound
  omega

/-- The detector has degree at most 2B; the virtual pair count is absent
from its actual polynomial representation. -/
theorem buildResidueSource_degree {N : ℕ} [Nontrivial (ZMod N)]
    (h : (ZMod N)ˣ) (B : ℕ) :
    (rootPolynomial (buildResidueSource (buildSource h B)).distinct id).natDegree≤2*B := by
  have he : (rootPolynomial (buildResidueSource (buildSource h B)).distinct id).natDegree=
      (buildResidueSource (buildSource h B)).distinct.card :=
    Polynomial.natDegree_finsetProd_X_sub_C_eq_card _ _
  rw [he]
  exact (buildResidueSource_budget h B).2.2.1

/-- A residue certificate retains the actual preceding long-power route
and its failed global decoder, without supplying either local period. -/
inductive ResidueCertified : {N : ℕ} → ResidueSource N → Prop where
  | remaining {p q : ℕ} {g h z s : (ZMod (p*q))ˣ}
      (hp : p.Prime) (hq : q.Prime)
      (hd : GoodPower p q (SemiprimeLehmanCoverage.sixthWidth (p*q)) (.remaining g h z s))
      (hn : recoverQuarter h (SemiprimeLehmanCoverage.sixthWidth (p*q))=none) :
      ResidueCertified (buildResidueSource (buildSource h
        (SemiprimeLehmanCoverage.sixthWidth (p*q))))

/-- A certified successful residue batch gives a proper leaf factor. -/
theorem residueCertified_factor {N d : ℕ} {source : ResidueSource N}
    (hc : ResidueCertified source) (hd : source.factor=some d) : ProperDivisor N d := by
  cases hc with
  | remaining hp hq hdata hn => exact buildResidueSource_sound _ hd

/-- A failed certified batch keeps both actual reduced-offset exclusions
and the literal large factor-sum gap on its true semiprime leaf. -/
theorem residueCertified_none_offsets {N : ℕ} {source : ResidueSource N}
    (hc : ResidueCertified source) (hf : source.factor=none) :
    ∃ p q, ∃ h : (ZMod (p*q))ˣ, p.Prime ∧ q.Prime ∧ N=p*q ∧
      HEq source (buildResidueSource (buildSource h (SemiprimeLehmanCoverage.sixthWidth (p*q)))) ∧
      4*(2*SemiprimeLehmanCoverage.sixthWidth N)^2≤p+q-2*N.sqrt ∧
      (2*SemiprimeLehmanCoverage.sixthWidth N)^2≤quarterOffset p q%orderOf (leftUnit h) ∧
      (2*SemiprimeLehmanCoverage.sixthWidth N)^2≤quarterOffset p q%orderOf (rightUnit h) := by
  cases hc with
  | @remaining p q g h z s hp hq hdata hn =>
    have hN : 4≤p*q := by nlinarith [hp.two_le,hq.two_le]
    have hcore : CoreData p q (SemiprimeLehmanCoverage.sixthWidth (p*q)) h := by
      rw [hdata.2.1]
      exact projected_core g hdata.1
    have hwidth := sixthWidth_ge_two hN
    have hbudget := SemiprimeLehmanCoverage.sixthWidth_upper (p*q)
    have hoff := residue_source_none_offsets hp hq hwidth hbudget h hcore hn hf
    exact ⟨p,q,h,hp,hq,rfl,HEq.rfl,
      recoverQuarter_none_gap hp hq hwidth hbudget h hcore hn,hoff⟩

/-- Each certified actual batch has two short lists and at most 4B GCDs. -/
theorem residueCertified_budget {N : ℕ} {source : ResidueSource N}
    (hc : ResidueCertified source) :
    source.roots.length=2*SemiprimeLehmanCoverage.sixthWidth N ∧
    source.targets.length=2*SemiprimeLehmanCoverage.sixthWidth N ∧
    source.distinct.card≤2*SemiprimeLehmanCoverage.sixthWidth N ∧
    source.columns.length=2*SemiprimeLehmanCoverage.sixthWidth N ∧
    recoveryGcdCount N (fun i => residueLeaves source.distinct (i : ZMod N))
      source.columns≤4*SemiprimeLehmanCoverage.sixthWidth N := by
  cases hc with
  | remaining hp hq hdata hn =>
    obtain ⟨hr,ht,hd,hc⟩ := buildResidueSource_budget _ _
    exact ⟨hr,ht,hd,hc,buildResidueSource_gcd_bound _ _⟩

/-- Refine only an actual failed global window, reusing its cached lists. -/
noncomputable def sourceForWindow {N : ℕ} :
    Option (SemiprimeTotientWindow.Source N) → Option (ResidueSource N)
  | none => none
  | some window => match window.factor with
    | some _ => none
    | none => some (buildResidueSource window)

/-- The actual failed certified window produces a certified residue batch. -/
theorem sourceForWindow_certified {N : ℕ} {window : SemiprimeTotientWindow.Source N}
    {source : ResidueSource N} (hw : WindowCertified window)
    (hs : sourceForWindow (some window)=some source) : ResidueCertified source := by
  cases hw with
  | @remaining p q g h z s hp hq hdata =>
    cases hf : (buildSource h (SemiprimeLehmanCoverage.sixthWidth (p*q))).factor with
    | some d => simp only [sourceForWindow,hf] at hs; contradiction
    | none =>
      simp only [sourceForWindow,hf] at hs
      have he := Option.some.inj hs
      rw [←he]
      exact .remaining hp hq hdata hf

/-- An actual failed window constructs exactly one retained residue batch. -/
theorem sourceForWindow_exists {N : ℕ} (window : SemiprimeTotientWindow.Source N)
    (hn : window.factor=none) :
    sourceForWindow (some window)=some (buildResidueSource window) := by
  simp only [sourceForWindow,hn]

/-- A successful preceding packet needs no new polynomial source. -/
noncomputable def packetSource {N : ℕ} (parent : SemiprimeTotientWindow.Packet N) :
    Option (ResidueSource (SemiprimeKernelDescent.leafInput parent.parent.source)) :=
  match parent.factor with
  | some _ => none
  | none => sourceForWindow parent.source

/-- Reuse an existing original factor or transport only a new residue
factor through every retained original descent frame. -/
noncomputable def factorWithResidue {N : ℕ} (parent : SemiprimeTotientWindow.Packet N)
    (source : Option (ResidueSource (SemiprimeKernelDescent.leafInput parent.parent.source))) :
    Option ℕ :=
  match parent.factor with
  | some d => some d
  | none => match source with
    | none => none
    | some source => match source.factor with
      | none => none
      | some d => transportCandidate parent.parent.source d

/-- Keep the preceding complete packet and the actual polynomial batch. -/
structure Packet (N : ℕ) where
  /-- Every original parent frame, power channel and labelled window. -/
  parent : SemiprimeTotientWindow.Packet N
  /-- Actual new residue source when the preceding window failed. -/
  source : Option (ResidueSource (SemiprimeKernelDescent.leafInput parent.parent.source))
  /-- The downstream checked original-input factor option. -/
  factor : Option ℕ

/-- The public procedure receives N alone and computes each stage once. -/
noncomputable def publicPacket (N : ℕ) : Packet N :=
  let parent := SemiprimeTotientWindow.publicPacket N
  let source := packetSource parent
  ⟨parent,source,factorWithResidue parent source⟩

/-- Every full public residue-packet factor is proper for the original N. -/
theorem publicPacket_sound {p q d : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hf : (publicPacket (p*q)).factor=some d) : ProperDivisor (p*q) d := by
  dsimp only [publicPacket] at hf
  unfold factorWithResidue at hf
  cases hold : (SemiprimeTotientWindow.publicPacket (p*q)).factor with
  | some f =>
    simp only [hold] at hf
    have hproper := SemiprimeTotientWindow.publicPacket_sound hp hq hold
    rwa [Option.some.inj hf] at hproper
  | none =>
    simp only [hold] at hf
    cases hs : packetSource (SemiprimeTotientWindow.publicPacket (p*q)) with
    | none => simp only [hs] at hf; contradiction
    | some source =>
      simp only [hs] at hf
      cases hd : source.factor with
      | none => simp only [hd] at hf; contradiction
      | some f =>
        simp only [hd] at hf
        exact transportCandidate_sound (SemiprimeKernelDescent.publicTrace_certified hp hq) hf

/-- Every actual new source in the full public procedure is certified. -/
theorem publicPacket_source_certified {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    {source : ResidueSource (SemiprimeKernelDescent.leafInput (publicPacket (p*q)).parent.parent.source)}
    (hs : (publicPacket (p*q)).source=some source) : ResidueCertified source := by
  obtain ⟨d,hd,_⟩ | ⟨hn,window,hw,hc,hf,_⟩ := SemiprimeTotientWindow.publicPacket_cases hp hq
  · simp only [publicPacket,packetSource,hd] at hs
    contradiction
  · apply sourceForWindow_certified hc
    simpa only [publicPacket,packetSource,hn,hw] using hs

/-- The full N-only route recovers an original factor or retains the
actual certified batch excluding both short local offset residues. -/
theorem publicPacket_cases {p q : ℕ} (hp : p.Prime) (hq : q.Prime) :
    (∃ d,(publicPacket (p*q)).factor=some d ∧ ProperDivisor (p*q) d) ∨
    ((publicPacket (p*q)).factor=none ∧ ∃ source,
      (publicPacket (p*q)).source=some source ∧ ResidueCertified source ∧ source.factor=none ∧
      ∃ u v, ∃ h : (ZMod (u*v))ˣ, u.Prime ∧ v.Prime ∧
        SemiprimeKernelDescent.leafInput (publicPacket (p*q)).parent.parent.source=u*v ∧
        HEq source (buildResidueSource (buildSource h (SemiprimeLehmanCoverage.sixthWidth (u*v)))) ∧
        4*(2*SemiprimeLehmanCoverage.sixthWidth
          (SemiprimeKernelDescent.leafInput (publicPacket (p*q)).parent.parent.source))^2≤
            u+v-2*(SemiprimeKernelDescent.leafInput (publicPacket (p*q)).parent.parent.source).sqrt ∧
        (2*SemiprimeLehmanCoverage.sixthWidth
          (SemiprimeKernelDescent.leafInput (publicPacket (p*q)).parent.parent.source))^2≤
            quarterOffset u v%orderOf (leftUnit h) ∧
        (2*SemiprimeLehmanCoverage.sixthWidth
          (SemiprimeKernelDescent.leafInput (publicPacket (p*q)).parent.parent.source))^2≤
            quarterOffset u v%orderOf (rightUnit h)) := by
  cases hf : (publicPacket (p*q)).factor with
  | some d => exact Or.inl ⟨d,rfl,publicPacket_sound hp hq hf⟩
  | none =>
    right
    refine ⟨rfl,?_⟩
    obtain ⟨d,hd,_⟩ | ⟨hn,window,hw,hc,hnone,_⟩ := SemiprimeTotientWindow.publicPacket_cases hp hq
    · have he : (publicPacket (p*q)).factor=some d := by
        simp only [publicPacket,factorWithResidue,hd]
      rw [hf] at he
      contradiction
    · have hpacket : packetSource (SemiprimeTotientWindow.publicPacket (p*q))=
          some (buildResidueSource window) := by
        simp only [packetSource,hn,hw,sourceForWindow,hnone]
      have hs : (publicPacket (p*q)).source=some (buildResidueSource window) := hpacket
      have hcert := publicPacket_source_certified hp hq hs
      have hfailed : (buildResidueSource window).factor=none := by
        cases hd : (buildResidueSource window).factor with
        | none => rfl
        | some d =>
          have hproper := residueCertified_factor hcert hd
          obtain ⟨f,hf',_⟩ := transportCandidate_complete
            (SemiprimeKernelDescent.publicTrace_certified hp hq) hproper
          have he : (publicPacket (p*q)).factor=some f := by
            simp only [publicPacket,factorWithResidue,hn,hpacket,hd]
            exact hf'
          rw [hf] at he
          contradiction
      exact ⟨_,hs,hcert,hfailed,residueCertified_none_offsets hcert hfailed⟩

/-- Both actual source axes, all columns, and added GCD queries fit the
ORIGINAL input's sixth-root width after every retained descent. -/
theorem publicPacket_source_budget {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    {source : ResidueSource (SemiprimeKernelDescent.leafInput (publicPacket (p*q)).parent.parent.source)}
    (hs : (publicPacket (p*q)).source=some source) :
    source.roots.length≤2*SemiprimeLehmanCoverage.sixthWidth (p*q) ∧
    source.targets.length≤2*SemiprimeLehmanCoverage.sixthWidth (p*q) ∧
    source.distinct.card≤2*SemiprimeLehmanCoverage.sixthWidth (p*q) ∧
    source.columns.length≤2*SemiprimeLehmanCoverage.sixthWidth (p*q) ∧
    recoveryGcdCount (SemiprimeKernelDescent.leafInput (publicPacket (p*q)).parent.parent.source)
      (fun i => residueLeaves source.distinct
        (i : ZMod (SemiprimeKernelDescent.leafInput (publicPacket (p*q)).parent.parent.source)))
      source.columns≤4*SemiprimeLehmanCoverage.sixthWidth (p*q) := by
  have hb := residueCertified_budget (publicPacket_source_certified hp hq hs)
  have hw := SemiprimeKernelDescent.sixthWidth_mono
    (certified_leaf_input_le (SemiprimeKernelDescent.publicTrace_certified hp hq))
  change SemiprimeLehmanCoverage.sixthWidth
    (SemiprimeKernelDescent.leafInput (publicPacket (p*q)).parent.parent.source)≤
      SemiprimeLehmanCoverage.sixthWidth (p*q) at hw
  omega

set_option maxRecDepth 32768 in
/-- The selected wrapped offset is far beyond the literal window but
reduces to 205 in the first reference period. No routing claim is assumed. -/
theorem control_wrapped_arithmetic :
    (1000000007 : ℕ)*5828428559=5828428599798999913 ∧
    quarterOffset 1000000007 5828428559=500000208 ∧
    (500000208 : ℕ)%500000003=205 ∧ (2*1342 : ℕ)^2=7203856 ∧
    (205 : ℕ)<7203856 ∧ (7203856 : ℕ)<500000208 ∧
    quarterCentre 5828428599798999913=1457107148742643045 := by
  norm_num [quarterOffset,quarterCentre]

/-- Actual scalar powers and their proper original residual GCD are
checked without enumerating the virtual source grid. -/
theorem control_wrapped_pair :
    (3505347010863074752 : ZMod 5828428599798999913)^205=5616586799466348465 ∧
    (3505347010863074752 : ZMod 5828428599798999913)^1457107148742643045=904283392480224847 ∧
    (5828428599798999913 : ℕ).gcd
      ((5616586799466348465 : ZMod 5828428599798999913)-904283392480224847).val=1000000007 := by
  constructor
  · reduce_mod_char
  constructor
  · reduce_mod_char
  have he : (5616586799466348465 : ZMod 5828428599798999913)-904283392480224847=
      4712303406986123618 := by reduce_mod_char
  rw [he,ZMod.val_ofNat]
  norm_num

end RiemannGaussian.SemiprimeTotientResidues
