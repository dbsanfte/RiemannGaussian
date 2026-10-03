/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeFirstNorm
import RiemannGaussian.SemiprimeRHCancellation

/-!
# Phase-free bulk norm queries and saturated binary recovery

Unit phases can be omitted from the detector. A saturated aggregate
keeps the original hit union; a balanced left-first search restores
the needed row label and infers a zero right product after a unit left
product. Constructors are explicit, not free bulk oracles. The native
shared point layout and complete one-sixth bit theorem remain open.
-/

namespace RiemannGaussian.SemiprimeBulkNorm

open SemiprimeFirstNorm SemiprimeMultiplierNorm SemiprimeIntervalJet
open SemiprimeTotientWindow SemiprimeTotientMultipliers SemiprimeTotientResidues
open SemiprimeGroupSelection SemiprimeLocalOrderRouting SemiprimeLongPowerRouting

/-- A balanced interval product in any monoid; leaves retain their public indices. -/
def modelBlock {M : Type*} [Monoid M] (value : ℕ → M) (start : ℕ) : ℕ → M
  | 0 => value start
  | depth+1 => modelBlock value start depth*modelBlock value (start+2^depth) depth

/-- Exact doubled span of a balanced block. -/
theorem doubleSpan (depth : ℕ) : 2^(depth+1)=2^depth+2^depth := by
  rw [pow_succ]
  omega

/-- Normalized full-block products contain no unit phase construction. -/
def normalizedBlocks {R : Type*} [CommRing R] (alpha : Rˣ) (x : R) (m : ℕ) : ℕ → R
  | 0 => 1
  | J+1 => normalizedBlocks alpha x m J*
    intervalProduct (alpha : R) (x*(((alpha^(J*m))⁻¹ : Rˣ) : R)) m

/-- Proof-side unit phase of the full blocks. The detector does not compute it. -/
def blockPhase {R : Type*} [CommRing R] (alpha : Rˣ) (m : ℕ) : ℕ → Rˣ
  | 0 => 1
  | J+1 => blockPhase alpha m J*(alpha^(J*m))^m

/-- The omitted full-block phase is invertible and independent of the target. -/
theorem normalizedBlocks_rephase {R : Type*} [CommRing R] (alpha : Rˣ) (x : R) (m J : ℕ) :
    scalarBlocks alpha x m J=(blockPhase alpha m J : R)*normalizedBlocks alpha x m J := by
  induction J with
  | zero => simp [scalarBlocks,blockPhase,normalizedBlocks]
  | succ J ih =>
    simp only [scalarBlocks,blockPhase,normalizedBlocks,scalarBlock,Units.val_mul,
      Units.val_pow_eq_pow_val,ih]
    ring

/-- Phase-free full blocks and the original exact tail; no interval padding. -/
def normalizedInterval {R : Type*} [CommRing R] (alpha : Rˣ) (x : R) (L m : ℕ) : R :=
  normalizedBlocks alpha x m (L/m)*
    intervalProduct (alpha : R) (x*(((alpha^((L/m)*m))⁻¹ : Rˣ) : R)) (L%m)

/-- Proof-side phase of one complete exact interval. -/
def intervalPhase {R : Type*} [CommRing R] (alpha : Rˣ) (L m : ℕ) : Rˣ :=
  blockPhase alpha m (L/m)*(alpha^((L/m)*m))^(L%m)

/-- Unit normalization preserves every original interval factor. -/
theorem normalizedInterval_rephase {R : Type*} [CommRing R] (alpha : Rˣ) (x : R) (L m : ℕ) :
    intervalProduct (alpha : R) x L=(intervalPhase alpha L m : R)*normalizedInterval alpha x L m := by
  rw [←scalarSharedProduct_exact alpha x L m]
  simp only [scalarSharedProduct,normalizedInterval,intervalPhase,normalizedBlocks_rephase,
    scalarBlock,Units.val_mul,Units.val_pow_eq_pow_val]
  ring

/-- Rephasing each leaf rephases a complete block by one unit. -/
theorem modelBlock_rephase {R : Type*} [CommRing R] (r v : ℕ → R) (u : ℕ → Rˣ)
    (h : ∀ i,r i=(u i : R)*v i) (start depth : ℕ) :
    modelBlock r start depth=((modelBlock u start depth : Rˣ) : R)*modelBlock v start depth := by
  induction depth generalizing start with
  | zero => exact h start
  | succ depth ih =>
    simp only [modelBlock,Units.val_mul,ih]
    ring

/-- Canonical source norms, with invertible dummy leaves after the public cache. -/
noncomputable def rowValue {N : ℕ} (window : SemiprimeTotientWindow.Source N) (B i : ℕ) : ZMod N :=
  if i<2*B then normProduct window B i else 1

/-- Normalized real rows and unit dummy leaves. Dummy padding never changes H. -/
def normalizedRow {N : ℕ} (window : SemiprimeTotientWindow.Source N) (B m i : ℕ) : ZMod N :=
  if i<2*B then normalizedInterval window.active
    ((indexedPoint window.target i : (ZMod N)ˣ) : ZMod N) (normLength B) m else 1

/-- Proof-side unit for each real row, or one on an unused leaf. -/
def rowPhase {N : ℕ} (window : SemiprimeTotientWindow.Source N) (B m i : ℕ) : (ZMod N)ˣ :=
  if i<2*B then intervalPhase window.active (normLength B) m else 1

/-- Every normalized row keeps the literal original norm up to a unit. -/
theorem row_rephase {N : ℕ} (window : SemiprimeTotientWindow.Source N) (B m i : ℕ) :
    rowValue window B i=(rowPhase window B m i : ZMod N)*normalizedRow window B m i := by
  by_cases hi : i<2*B
  · simp only [rowValue,rowPhase,normalizedRow,hi,if_true,normProduct_exact]
    exact normalizedInterval_rephase _ _ _ _
  · simp [rowValue,rowPhase,normalizedRow,hi]

/-- Number of real rows in this public block; unused leaves are excluded from native inputs. -/
def groupLength (B start depth : ℕ) : ℕ := min (2^depth) (2*B-start)

/-- Each concrete bulk query uses a public width and returns only its
phase-free product. Neither derivatives nor original row norm outputs are retained. -/
def bulkDetector {N : ℕ} (window : SemiprimeTotientWindow.Source N) (B start depth : ℕ) : ZMod N :=
  modelBlock (normalizedRow window B (normWidth B (groupLength B start depth))) start depth

/-- Removing all phases preserves the exact GCD of the original row product,
even if every prime divides that product. Widths may differ between queries. -/
theorem bulkDetector_gcd {N : ℕ} (window : SemiprimeTotientWindow.Source N) (B start depth : ℕ) :
    N.gcd (bulkDetector window B start depth).val=
      N.gcd (modelBlock (rowValue window B) start depth).val := by
  have hp := modelBlock_rephase (rowValue window B)
    (normalizedRow window B (normWidth B (groupLength B start depth)))
    (rowPhase window B (normWidth B (groupLength B start depth)))
    (row_rephase window B _) start depth
  rw [hp]
  exact (SemiprimeRHCancellation.unit_mul_gcd_eq _ _).symm

/-- A public GCD-one test is exactly a unit test over a nonzero modulus. -/
theorem gcd_one_iff_unit {N : ℕ} [NeZero N] (x : ZMod N) : N.gcd x.val=1 ↔ IsUnit x := by
  have h := ZMod.isUnit_iff_coprime x.val N
  simpa only [ZMod.natCast_zmod_val,Nat.coprime_iff_gcd_eq_one,Nat.gcd_comm] using h.symm

/-- A unit block has only unit leaves, retaining the complete original hit union. -/
theorem modelBlock_unit_leaf {R : Type*} [CommRing R] (value : ℕ → R) {start depth w : ℕ}
    (hwlo : start≤w) (hwhi : w<start+2^depth) (hu : IsUnit (modelBlock value start depth)) :
    IsUnit (value w) := by
  induction depth generalizing start with
  | zero =>
    have he : w=start := by simp only [pow_zero] at hwhi; omega
    subst w
    exact hu
  | succ depth ih =>
    have hc : Commute (modelBlock value start depth) (modelBlock value (start+2^depth) depth) := mul_comm _ _
    have hp := hc.isUnit_mul_iff.mp hu
    rw [doubleSpan] at hwhi
    by_cases hw : w<start+2^depth
    · exact ih hwlo hw hp.1
    · exact ih (by omega) (by omega) hp.2

/-- The saturated search returns a proper factor or a labelled saturated leaf. -/
def splitZero {N : ℕ} (bulk : ℕ → ℕ → ZMod N) (start : ℕ) : ℕ → (ℕ⊕ℕ)×ℕ
  | 0 => (.inr start,0)
  | depth+1 =>
    let d := N.gcd (bulk start depth).val
    if 1<d ∧ d<N then (.inl d,1)
    else if d=1 then
      let next := splitZero bulk (start+2^depth) depth
      (next.1,next.2+1)
    else
      let next := splitZero bulk start depth
      (next.1,next.2+1)

/-- Each saturated-search level pays only its left product GCD; the
right product is inferred zero when the left product is a unit. -/
theorem splitZero_gcd_bound {N : ℕ} (bulk : ℕ → ℕ → ZMod N) (start depth : ℕ) :
    (splitZero bulk start depth).2≤depth := by
  induction depth generalizing start with
  | zero => simp only [splitZero]; omega
  | succ depth ih =>
    dsimp only [splitZero]
    split_ifs
    · omega
    · have h := ih (start+2^depth); omega
    · have h := ih start; omega

/-- The labelled alternative retains its range, exact zero norm, and
position no later than any original nonunit leaf in that range. -/
def AnswerValid {N : ℕ} (value : ℕ → ZMod N) (start depth : ℕ) : ℕ⊕ℕ → Prop
  | .inl d => ProperDivisor N d
  | .inr i => start ≤ i ∧ i<start+2^depth ∧ value i=0 ∧
    ∀ w,start≤w → w<start+2^depth → N.gcd (value w).val≠1 → i ≤ w

/-- Saturated binary recovery is correct for any concrete producer
whose GCD is the original block GCD. The public producer discharges this identity. -/
theorem splitZero_correct {N : ℕ} (hN : 1<N) (value : ℕ → ZMod N)
    (bulk : ℕ → ℕ → ZMod N)
    (hbulk : ∀ start depth,N.gcd (bulk start depth).val=N.gcd (modelBlock value start depth).val)
    {start depth : ℕ} (hz : modelBlock value start depth=0) :
    AnswerValid value start depth (splitZero bulk start depth).1 := by
  let : NeZero N := ⟨by omega⟩
  induction depth generalizing start with
  | zero =>
    change start≤start ∧ start<start+1 ∧ value start=0 ∧ _
    exact ⟨le_rfl,by omega,hz,by intros; omega⟩
  | succ depth ih =>
    have hspan := doubleSpan depth
    have hprod : modelBlock value start depth*modelBlock value (start+2^depth) depth=0 := hz
    dsimp only [splitZero]
    split_ifs with hp hu
    · exact ⟨hp.1,hp.2,Nat.gcd_dvd_left _ _⟩
    · have hleft : IsUnit (modelBlock value start depth) :=
        (gcd_one_iff_unit _).mp ((hbulk start depth).symm.trans hu)
      have hright := hleft.mul_right_eq_zero.mp hprod
      have hv := ih hright
      cases hs : (splitZero bulk (start+2^depth) depth).1 with
      | inl d => simpa only [hs,AnswerValid] using hv
      | inr i =>
        simp only [hs,AnswerValid] at hv ⊢
        obtain ⟨hlo,hhi,hzi,hfirst⟩ := hv
        refine ⟨by omega,by omega,hzi,?_⟩
        intro w hwlo hwhi hwn
        have hwr : start+2^depth≤w := by
          by_contra hbad
          have hwu := modelBlock_unit_leaf value hwlo (by omega) hleft
          exact hwn ((gcd_one_iff_unit _).mpr hwu)
        exact hfirst w hwr (by omega) hwn
    · have hpos := Nat.gcd_pos_of_pos_left (bulk start depth).val (by omega : 0<N)
      have hle := Nat.gcd_le_left (bulk start depth).val (by omega : 0<N)
      have hg : N.gcd (bulk start depth).val=N := by omega
      have hzero : modelBlock value start depth=0 :=
        SemiprimeSourceHead.residual_zero_of_gcd_eq_modulus _ ((hbulk start depth).symm.trans hg)
      have hv := ih hzero
      cases hs : (splitZero bulk start depth).1 with
      | inl d => simpa only [hs,AnswerValid] using hv
      | inr i =>
        simp only [hs,AnswerValid] at hv ⊢
        obtain ⟨hlo,hhi,hzi,hfirst⟩ := hv
        refine ⟨hlo,by omega,hzi,?_⟩
        intro w hwlo hwhi hwn
        by_cases hw : w<start+2^depth
        · exact hfirst w hwlo hw hwn
        · omega

/-- One paid aggregate test; only saturation invokes the balanced search. -/
def inspectBlock {N : ℕ} (bulk : ℕ → ℕ → ZMod N) (start depth : ℕ) : Option (ℕ⊕ℕ)×ℕ :=
  let d := N.gcd (bulk start depth).val
  if d=1 then (none,1)
  else if 1<d ∧ d<N then (some (.inl d),1)
  else
    let next := splitZero bulk start depth
    (some next.1,next.2+1)

/-- A successful aggregate query returns a proper factor or the first
saturated leaf of its original block. -/
theorem inspectBlock_sound {N : ℕ} (hN : 1<N) (value : ℕ → ZMod N)
    (bulk : ℕ → ℕ → ZMod N)
    (hbulk : ∀ start depth,N.gcd (bulk start depth).val=N.gcd (modelBlock value start depth).val)
    {start depth : ℕ} {answer : ℕ⊕ℕ} (hs : (inspectBlock bulk start depth).1=some answer) :
    AnswerValid value start depth answer := by
  let : NeZero N := ⟨by omega⟩
  dsimp only [inspectBlock] at hs
  split_ifs at hs with hu hp
  · obtain rfl := Option.some.inj hs
    exact ⟨hp.1,hp.2,Nat.gcd_dvd_left _ _⟩
  · have hpos := Nat.gcd_pos_of_pos_left (bulk start depth).val (by omega : 0<N)
    have hle := Nat.gcd_le_left (bulk start depth).val (by omega : 0<N)
    have hg : N.gcd (bulk start depth).val=N := by omega
    have hz := SemiprimeSourceHead.residual_zero_of_gcd_eq_modulus _
      ((hbulk start depth).symm.trans hg)
    rw [←Option.some.inj hs]
    exact splitZero_correct hN value bulk hbulk hz

/-- A skipped aggregate block has no nonunit leaf. -/
theorem inspectBlock_miss_unit {N : ℕ} [NeZero N] (value : ℕ → ZMod N)
    (bulk : ℕ → ℕ → ZMod N)
    (hbulk : ∀ start depth,N.gcd (bulk start depth).val=N.gcd (modelBlock value start depth).val)
    {start depth : ℕ} (hs : (inspectBlock bulk start depth).1=none) :
    IsUnit (modelBlock value start depth) := by
  dsimp only [inspectBlock] at hs
  split_ifs at hs with hu
  · exact (gcd_one_iff_unit _).mp ((hbulk start depth).symm.trans hu)

/-- One root GCD and at most one left GCD per search level. -/
theorem inspectBlock_gcd_bound {N : ℕ} (bulk : ℕ → ℕ → ZMod N) (start depth : ℕ) :
    (inspectBlock bulk start depth).2≤depth+1 := by
  dsimp only [inspectBlock]
  have h := splitZero_gcd_bound bulk start depth
  split_ifs <;> omega

/-- Exact span of successive doubling groups. -/
def forestSpan (depth : ℕ) : ℕ → ℕ
  | 0 => 0
  | fuel+1 => 2^depth+forestSpan (depth+1) fuel

/-- Successive doubling groups cover the full prefix without gaps. -/
theorem forestSpan_power (depth fuel : ℕ) : forestSpan depth fuel+2^depth=2^(depth+fuel) := by
  induction fuel generalizing depth with
  | zero => simp only [forestSpan,Nat.add_zero,Nat.zero_add]
  | succ fuel ih =>
    have h := ih (depth+1)
    rw [doubleSpan] at h
    have he : depth+1+fuel=depth+(fuel+1) := by omega
    rw [he] at h
    dsimp only [forestSpan]
    omega

/-- Adaptive groups have sizes 1,2,4,...; a successful group stops the
forest. Cleared groups do not construct individual row outputs. -/
def forest {N : ℕ} (bulk : ℕ → ℕ → ZMod N) (start depth : ℕ) : ℕ → Option (ℕ⊕ℕ)×ℕ
  | 0 => (none,0)
  | fuel+1 =>
    let query := inspectBlock bulk start depth
    match query.1 with
    | some answer => (some answer,query.2)
    | none =>
      let next := forest bulk (start+2^depth) (depth+1) fuel
      (next.1,query.2+next.2)

/-- Exact query-clock bound of the doubling forest, including saturation. -/
theorem forest_gcd_bound {N : ℕ} (bulk : ℕ → ℕ → ZMod N) (start depth fuel : ℕ) :
    (forest bulk start depth fuel).2≤depth+2*fuel := by
  induction fuel generalizing start depth with
  | zero => simp only [forest]; omega
  | succ fuel ih =>
    dsimp only [forest]
    cases hs : (inspectBlock bulk start depth).1 with
    | some answer =>
      simp only
      have h := inspectBlock_gcd_bound bulk start depth
      omega
    | none =>
      simp only
      have hq : (inspectBlock bulk start depth).2=1 := by
        dsimp only [inspectBlock] at hs ⊢
        split_ifs at hs ⊢; simp_all
      have h := ih (start+2^depth) (depth+1)
      omega

/-- A forest answer keeps the original range and the earliest nonunit
position. It has not discarded a row label by bulk multiplication. -/
def ForestValid {N : ℕ} (value : ℕ → ZMod N) (start depth fuel : ℕ) : ℕ⊕ℕ → Prop
  | .inl d => ProperDivisor N d
  | .inr i => start ≤ i ∧ i<start+forestSpan depth fuel ∧ value i=0 ∧
    ∀ w,start≤w → w<start+forestSpan depth fuel → N.gcd (value w).val≠1 → i ≤ w

/-- Every returned forest answer is valid for its whole original prefix. -/
theorem forest_sound {N : ℕ} (hN : 1<N) (value : ℕ → ZMod N)
    (bulk : ℕ → ℕ → ZMod N)
    (hbulk : ∀ start depth,N.gcd (bulk start depth).val=N.gcd (modelBlock value start depth).val)
    {start depth fuel : ℕ} {answer : ℕ⊕ℕ} (hs : (forest bulk start depth fuel).1=some answer) :
    ForestValid value start depth fuel answer := by
  let : NeZero N := ⟨by omega⟩
  induction fuel generalizing start depth with
  | zero => simp only [forest] at hs; contradiction
  | succ fuel ih =>
    dsimp only [forest] at hs
    cases hq : (inspectBlock bulk start depth).1 with
    | some hit =>
      simp only [hq] at hs
      obtain rfl := Option.some.inj hs
      have hv := inspectBlock_sound hN value bulk hbulk hq
      cases hit with
      | inl d => exact hv
      | inr i =>
        obtain ⟨hlo,hhi,hzi,hfirst⟩ := hv
        dsimp only [ForestValid,forestSpan]
        refine ⟨hlo,by omega,hzi,?_⟩
        intro w hwlo hwhi hwn
        by_cases hw : w<start+2^depth
        · exact hfirst w hwlo hw hwn
        · omega
    | none =>
      simp only [hq] at hs
      have hv := ih (start:=start+2^depth) (depth:=depth+1) hs
      have hu := inspectBlock_miss_unit value bulk hbulk hq
      cases answer with
      | inl d => exact hv
      | inr i =>
        dsimp only [ForestValid] at hv
        obtain ⟨hlo,hhi,hzi,hfirst⟩ := hv
        dsimp only [ForestValid,forestSpan]
        refine ⟨(Nat.le_add_right start (2^depth)).trans hlo,?_,hzi,?_⟩
        · simpa only [Nat.add_assoc] using hhi
        intro w hwlo hwhi hwn
        have hwr : start+2^depth≤w := by
          by_contra hbad
          have hwu := modelBlock_unit_leaf value hwlo (by omega) hu
          exact hwn ((gcd_one_iff_unit _).mpr hwu)
        exact hfirst w hwr (by omega) hwn

/-- Any original nonunit leaf forces the actual forest to return an answer. -/
theorem forest_exists {N : ℕ} [NeZero N] (value : ℕ → ZMod N)
    (bulk : ℕ → ℕ → ZMod N)
    (hbulk : ∀ start depth,N.gcd (bulk start depth).val=N.gcd (modelBlock value start depth).val)
    {start depth fuel w : ℕ} (hwlo : start≤w) (hwhi : w<start+forestSpan depth fuel)
    (hwn : N.gcd (value w).val≠1) : ∃ answer,(forest bulk start depth fuel).1=some answer := by
  induction fuel generalizing start depth with
  | zero => simp only [forestSpan,Nat.add_zero] at hwhi; omega
  | succ fuel ih =>
    dsimp only [forest]
    cases hq : (inspectBlock bulk start depth).1 with
    | some hit => exact ⟨hit,rfl⟩
    | none =>
      have hu := inspectBlock_miss_unit value bulk hbulk hq
      have hwr : start+2^depth≤w := by
        by_contra hbad
        have hwu := modelBlock_unit_leaf value hwlo (by omega) hu
        exact hwn ((gcd_one_iff_unit _).mpr hwu)
      exact ih hwr (by dsimp only [forestSpan] at hwhi; omega)

/-- Public group count; virtual unused leaves are units, not added interval targets. -/
def publicDepth (B : ℕ) : ℕ := (2*B).log2+1

/-- The public group budget covers all 2B signed rows. -/
theorem publicDepth_covers {B : ℕ} (hB : 0<B) : 2*B≤forestSpan 0 (publicDepth B) := by
  have hp : 2*B<2^(publicDepth B) := (Nat.log2_lt (by omega : 2*B≠0)).mp (by
    unfold publicDepth
    omega)
  have h := forestSpan_power 0 (publicDepth B)
  simp only [pow_zero,Nat.zero_add] at h
  omega

/-- Public doubling forest with the concrete normalized producer. -/
def scanForest {N : ℕ} (window : SemiprimeTotientWindow.Source N) (B : ℕ) : Option (ℕ⊕ℕ)×ℕ :=
  forest (bulkDetector window B) 0 0 (publicDepth B)

/-- The actual public forest inherits the original canonical hit union. -/
theorem scanForest_sound {N B : ℕ} (hN : 1<N) (window : SemiprimeTotientWindow.Source N)
    {answer : ℕ⊕ℕ} (hs : (scanForest window B).1=some answer) :
    ForestValid (rowValue window B) 0 0 (publicDepth B) answer :=
  forest_sound hN _ _ (bulkDetector_gcd window B) hs

/-- The source computes no derivatives for an aggregate proper factor,
and at most one exact original jet for a selected saturated row. -/
noncomputable def treeLateJet {N : ℕ} (window : SemiprimeTotientWindow.Source N) (B : ℕ)
    (choice : Option (ℕ⊕ℕ)) : Option ((ZMod N)ˣ×(ZMod N×ZMod N×ZMod N)) :=
  match choice with
  | some (.inr i) => if i<2*B then
      some (indexedPoint window.target i,
        exactSharedJet window.active ((indexedPoint window.target i : (ZMod N)ˣ) : ZMod N)
          (normLength B) (normWidth B 1))
    else none
  | _ => none

/-- Consume a checked aggregate candidate or the one retained late jet. -/
noncomputable def factorFromAnswer (N b : ℕ) (choice : Option (ℕ⊕ℕ))
    (jet : Option ((ZMod N)ˣ×(ZMod N×ZMod N×ZMod N))) : Option ℕ :=
  match choice with
  | none => none
  | some (.inl d) => if 1<d ∧ d<N then some d else none
  | some (.inr _) => jet.bind (fun row => recoverNormJet row.1 b row.2)

/-- A valid leaf uses the same exact interval recovery as the frozen
single-row specification. No norm reconstruction precedes its jet. -/
theorem factorFromAnswer_inr_exact {N B i : ℕ} (window : SemiprimeTotientWindow.Source N)
    (hi : i<2*B) :
    factorFromAnswer N (2*B) (some (.inr i)) (treeLateJet window B (some (.inr i)))=
      recoverInterval window.active (indexedPoint window.target i) (normLength B) (2*B) := by
  simp only [factorFromAnswer,treeLateJet,hi,if_true,Option.bind_some]
  rw [exactSharedJet_exact _ _ _ (normWidth_pos B 1),recoverNormJet_exact]

/-- On the remaining core, the concrete forest either already factors
or selects the same first recoverable nonunit row as the proved scalar scan.
The old scan is used in this proof only; it is not called by the source. -/
theorem bulk_norm_complete {p q B : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hB : 2≤B) (hbudget : p*q≤B^6) (h : (ZMod (p*q))ˣ)
    (hc : CoreData p q B h) (hn : recoverQuarter h B=none) :
    ∃ answer f,(scanForest (buildSource h B) B).1=some answer ∧
      factorFromAnswer (p*q) (2*B) (some answer)
        (treeLateJet (buildSource h B) B (some answer))=some f := by
  let : NeZero (p*q) := ⟨Nat.mul_ne_zero hp.ne_zero hq.ne_zero⟩
  have hN : 1<p*q := by nlinarith [hp.two_le,hq.two_le]
  obtain ⟨i,d,f,hs,hf⟩ := first_norm_complete hp hq hB hbudget h hc hn
  obtain ⟨hi,hd,hne⟩ := scanCache_sound _ hs
  have hni : (p*q).gcd (normProduct (buildSource h B) B i).val≠1 := by omega
  have hir : rowValue (buildSource h B) B i=normProduct (buildSource h B) B i := by
    simp only [rowValue,hi,if_true]
  have hispan : i<0+forestSpan 0 (publicDepth B) := by
    have hcover := publicDepth_covers (by omega : 0<B)
    omega
  obtain ⟨answer,hanswer⟩ := forest_exists (rowValue (buildSource h B) B)
    (bulkDetector (buildSource h B) B) (bulkDetector_gcd _ _)
    (by omega : 0 ≤ i) hispan (by rwa [hir])
  have hans : (scanForest (buildSource h B) B).1=some answer := hanswer
  have hv := scanForest_sound hN _ hans
  cases answer with
  | inl e =>
    have he : 1<e ∧ e<p*q := ⟨hv.1,hv.2.1⟩
    exact ⟨.inl e,e,hans,by dsimp only [factorFromAnswer]; rw [if_pos he]⟩
  | inr j =>
    obtain ⟨_,_,hz,hfirst⟩ := hv
    have hji : j ≤ i := hfirst i (by omega) hispan (by rwa [hir])
    have hj : j<2*B := by omega
    have hjz : normProduct (buildSource h B) B j=0 := by
      simpa only [rowValue,hj,if_true] using hz
    have hnj : (p*q).gcd (normProduct (buildSource h B) B j).val≠1 := by
      simp only [hjz,ZMod.val_zero,Nat.gcd_zero_right]
      omega
    obtain ⟨i',d',hs',hle⟩ := scanFrom_exists_le
      (fun index => (productCache (buildSource h B) B)[index]?.getD 0)
      (by omega : 0≤j) (by omega : j<0+2*B)
      (by simpa only [productCache_getD _ hj] using hnj)
    have hs'' : (scanCache (buildSource h B) B).1=some (i',d') := hs'
    have he : (i',d')=(i,d) := Option.some.inj (hs''.symm.trans hs)
    have heq : j=i := by have hh := (Prod.mk.inj he).1; omega
    subst j
    refine ⟨.inr i,f,hans,?_⟩
    rw [factorFromAnswer_inr_exact _ hi]
    rw [recoverSelected_exact _ hd] at hf
    exact hf

/-- The actual retained query, at most one jet, and original leaf candidate.
No list of per-row scalar norms is a source field. -/
structure Source (N : ℕ) where
  /-- Actual aggregate/split answer and recursive GCD-query clock. -/
  search : Option (ℕ⊕ℕ)×ℕ
  /-- At most one original labelled row receives derivative channels. -/
  jet : Option ((ZMod N)ˣ×(ZMod N×ZMod N×ZMod N))
  /-- Proper candidate of this descent leaf. -/
  factor : Option ℕ
  /-- Aggregate/search queries and the optional consumer query trace. -/
  gcdQueries : ℕ

/-- Construct the concrete bulk forest and its single optional late consumer. -/
noncomputable def buildBulkSource {N : ℕ} (window : SemiprimeTotientWindow.Source N)
    (B : ℕ) : Source N :=
  let search := scanForest window B
  let jet := treeLateJet window B search.1
  let factor := factorFromAnswer N (2*B) search.1 jet
  let extra := jet.map (fun row => jetGcdCount row.1 (2*B) row.2)
  ⟨search,jet,factor,search.2+extra.getD 0⟩

/-- Actual aggregate/split GCDs have a logarithmic query bound. Their
polynomial and point construction is not priced by this theorem. -/
theorem scanForest_gcd_bound {N : ℕ} (window : SemiprimeTotientWindow.Source N) (B : ℕ) :
    (scanForest window B).2≤2*publicDepth B := by
  simpa only [scanForest,Nat.zero_add] using forest_gcd_bound (bulkDetector window B) 0 0 (publicDepth B)

/-- The complete source has at most logarithmically many bulk GCDs
and one existing linear-width integer-index consumer. -/
theorem buildBulkSource_gcd_bound {N : ℕ} (window : SemiprimeTotientWindow.Source N) (B : ℕ) :
    (buildBulkSource window B).gcdQueries≤2*publicDepth B+4*B+2 := by
  dsimp only [buildBulkSource]
  have hs := scanForest_gcd_bound window B
  cases hj : treeLateJet window B (scanForest window B).1 with
  | none => simp only [Option.map_none,Option.getD_none]; omega
  | some row =>
    simp only [Option.map_some,Option.getD_some]
    have h := jetGcdCount_bound row.1 (2*B) row.2
    omega

/-- Every actual bulk-source factor is proper, including arbitrary
moduli for soundness. The concrete producer justifies aggregate candidates. -/
theorem buildBulkSource_sound {N B f : ℕ} (window : SemiprimeTotientWindow.Source N)
    (hf : (buildBulkSource window B).factor=some f) : ProperDivisor N f := by
  dsimp only [buildBulkSource] at hf
  cases hs : (scanForest window B).1 with
  | none => simp only [hs,factorFromAnswer] at hf; contradiction
  | some answer =>
    simp only [hs] at hf
    cases answer with
    | inl d =>
      dsimp only [factorFromAnswer] at hf
      split_ifs at hf with hp
      have he := Option.some.inj hf
      subst f
      exact scanForest_sound (by omega : 1<N) window hs
    | inr i =>
      dsimp only [factorFromAnswer] at hf
      cases hj : treeLateJet window B (some (.inr i)) with
      | none => simp only [hj,Option.bind_none] at hf; contradiction
      | some row =>
        simp only [hj,Option.bind_some] at hf
        exact recoverNormJet_sound row.1 row.2 hf

/-- The actual concrete bulk forest factors every remaining certified core. -/
theorem buildBulkSource_complete {p q B : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hB : 2≤B) (hbudget : p*q≤B^6) (h : (ZMod (p*q))ˣ)
    (hc : CoreData p q B h) (hn : recoverQuarter h B=none) :
    ∃ f,(buildBulkSource (buildSource h B) B).factor=some f := by
  obtain ⟨answer,f,hs,hf⟩ := bulk_norm_complete hp hq hB hbudget h hc hn
  exact ⟨f,by dsimp only [buildBulkSource]; rw [hs]; exact hf⟩

/-- Certified public windows supply every premise for the concrete bulk route. -/
theorem windowCertified_bulk_complete {N : ℕ} {window : SemiprimeTotientWindow.Source N}
    (hc : WindowCertified window) (hn : window.factor=none) :
    ∃ f,(buildBulkSource window (SemiprimeLehmanCoverage.sixthWidth N)).factor=some f := by
  cases hc with
  | @remaining p q g h z s hp hq hdata =>
    have hN : 4≤p*q := by nlinarith [hp.two_le,hq.two_le]
    have hcore : CoreData p q (SemiprimeLehmanCoverage.sixthWidth (p*q)) h := by
      rw [hdata.2.1]
      exact projected_core g hdata.1
    exact buildBulkSource_complete hp hq (sixthWidth_ge_two hN)
      (SemiprimeLehmanCoverage.sixthWidth_upper _) h hcore hn

/-- The new source begins at the public residue packet; no full scalar
norm cache is executed before its bulk queries. -/
noncomputable def packetSource {N : ℕ} (parent : SemiprimeTotientResidues.Packet N) :
    Option (Source (SemiprimeKernelDescent.leafInput parent.parent.parent.source)) :=
  match parent.factor with
  | some _ => none
  | none => parent.parent.source.map fun window => buildBulkSource window
    (SemiprimeLehmanCoverage.sixthWidth (SemiprimeKernelDescent.leafInput parent.parent.parent.source))

/-- The actually retained public source uses its own descent leaf's
public width in the bulk/search and late-consumer query bound. -/
theorem packetSource_gcd_bound {N : ℕ} (parent : SemiprimeTotientResidues.Packet N)
    {source : Source (SemiprimeKernelDescent.leafInput parent.parent.parent.source)}
    (hs : packetSource parent=some source) :
    source.gcdQueries≤2*publicDepth (SemiprimeLehmanCoverage.sixthWidth
      (SemiprimeKernelDescent.leafInput parent.parent.parent.source))+
      4*SemiprimeLehmanCoverage.sixthWidth
        (SemiprimeKernelDescent.leafInput parent.parent.parent.source)+2 := by
  unfold packetSource at hs
  cases hp : parent.factor with
  | some d => simp only [hp] at hs; contradiction
  | none =>
    simp only [hp] at hs
    cases hw : parent.parent.source with
    | none => simp only [hw,Option.map_none] at hs; contradiction
    | some window =>
      simp only [hw,Option.map_some] at hs
      obtain rfl := Option.some.inj hs
      exact buildBulkSource_gcd_bound window _

/-- Preserve existing public successes or transport the concrete bulk
candidate through every original descent frame. -/
noncomputable def factorWithBulkNorm {N : ℕ} (parent : SemiprimeTotientResidues.Packet N)
    (source : Option (Source (SemiprimeKernelDescent.leafInput parent.parent.parent.source))) : Option ℕ :=
  match parent.factor with
  | some d => some d
  | none => match source with
    | none => none
    | some source => source.factor.bind (transportCandidate parent.parent.parent.source)

/-- Original-input public packet, concrete aggregate search and optional late jet. -/
structure Packet (N : ℕ) where
  /-- Preceding public packet before scalar norm or derivative sources. -/
  parent : SemiprimeTotientResidues.Packet N
  /-- The concrete retained source at the actual remaining leaf. -/
  source : Option (Source (SemiprimeKernelDescent.leafInput parent.parent.parent.source))
  /-- Proper candidate of the original input. -/
  factor : Option ℕ

/-- N alone constructs the complete phase-free bulk public specification. -/
noncomputable def publicPacket (N : ℕ) : Packet N :=
  let parent := SemiprimeTotientResidues.publicPacket N
  let source := packetSource parent
  ⟨parent,source,factorWithBulkNorm parent source⟩

/-- Every public bulk norm output is proper for the original input. -/
theorem publicPacket_sound {p q d : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hf : (publicPacket (p*q)).factor=some d) : ProperDivisor (p*q) d := by
  dsimp only [publicPacket] at hf
  unfold factorWithBulkNorm at hf
  cases hold : (SemiprimeTotientResidues.publicPacket (p*q)).factor with
  | some f =>
    simp only [hold] at hf
    have hproper := SemiprimeTotientResidues.publicPacket_sound hp hq hold
    rwa [Option.some.inj hf] at hproper
  | none =>
    simp only [hold] at hf
    cases hs : packetSource (SemiprimeTotientResidues.publicPacket (p*q)) with
    | none => simp only [hs] at hf; contradiction
    | some source =>
      simp only [hs] at hf
      cases hd : source.factor with
      | none => simp only [hd,Option.bind_none] at hf; contradiction
      | some f =>
        simp only [hd,Option.bind_some] at hf
        exact transportCandidate_sound (SemiprimeKernelDescent.publicTrace_certified hp hq) hf

/-- The concrete phase-free aggregate forest factors every semiprime,
including squares and arbitrary ratios. This is a universal correctness
theorem; the every-run one-sixth bit-cost theorem remains open. -/
theorem publicPacket_complete {p q : ℕ} (hp : p.Prime) (hq : q.Prime) :
    ∃ d,(publicPacket (p*q)).factor=some d ∧ ProperDivisor (p*q) d := by
  cases hold : (SemiprimeTotientResidues.publicPacket (p*q)).factor with
  | some d =>
    have he : (publicPacket (p*q)).factor=some d := by
      simp only [publicPacket,factorWithBulkNorm,hold]
    exact ⟨d,he,publicPacket_sound hp hq he⟩
  | none =>
    obtain ⟨d,hd,_⟩ | ⟨_,window,hw,hc,hfailed,_⟩ := SemiprimeTotientWindow.publicPacket_cases hp hq
    · have he : (SemiprimeTotientResidues.publicPacket (p*q)).factor=some d := by
        simp only [SemiprimeTotientResidues.publicPacket,factorWithResidue,hd]
      rw [hold] at he
      contradiction
    · obtain ⟨d,hd⟩ := windowCertified_bulk_complete hc hfailed
      have hs : packetSource (SemiprimeTotientResidues.publicPacket (p*q))=
          some (buildBulkSource window
            (SemiprimeLehmanCoverage.sixthWidth
              (SemiprimeKernelDescent.leafInput
                (SemiprimeTotientWindow.publicPacket (p*q)).parent.source))) := by
        rw [packetSource,hold]
        change (SemiprimeTotientWindow.publicPacket (p*q)).source.map _=_
        rw [hw]
        rfl
      obtain ⟨f,hf,_⟩ := transportCandidate_complete
        (SemiprimeKernelDescent.publicTrace_certified hp hq) (buildBulkSource_sound _ hd)
      have he : (publicPacket (p*q)).factor=some f := by
        simp only [publicPacket,factorWithBulkNorm,hold,hs]
        dsimp only [SemiprimeTotientResidues.publicPacket]
        rw [hd]
        exact hf
      exact ⟨f,he,publicPacket_sound hp hq he⟩

end RiemannGaussian.SemiprimeBulkNorm
