/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeTotientResidues

/-!
# Charged construction of the retained quarter-window lists

Explicit binary modular powers and geometric recurrences construct the
same public residue lists used by the checked recovery procedure. Their
actual multiplication and halving counters are retained. Sorting,
inverse acquisition, polynomial evaluation, transport and full bit costs
remain separate charges; universal one-sixth factoring is still open.
-/

namespace RiemannGaussian.SemiprimeWindowConstruction

open SemiprimeTotientWindow SemiprimeTotientResidues SemiprimeProgressionPrefix

/-- Actual result and arithmetic counters from one binary modular power. -/
structure PowerReport where
  /-- The computed canonical modular residue. -/
  value : ℕ
  /-- Every explicit multiplication, including repeated squaring. -/
  multiplications : ℕ
  /-- Recursive halvings of the natural exponent. -/
  halvings : ℕ
  /-- Every explicit residue reduction, including base normalization. -/
  reductions : ℕ

/-- Binary modular powering retains its actual operation counters. At
positive N its reduced residues remain bounded by N. -/
def countedPower (N a e : ℕ) : PowerReport :=
  if he : e=0 then ⟨1%N,0,0,1⟩
  else
    let child := countedPower N a (e/2)
    let square := child.value*child.value%N
    if e%2=0 then
      ⟨square,child.multiplications+1,child.halvings+1,child.reductions+1⟩
    else
      ⟨square*(a%N)%N,child.multiplications+2,child.halvings+1,child.reductions+3⟩
termination_by e
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero he) (by decide)

/-- The binary exponent length decreases exactly once on each halving. -/
theorem clog_halving {e : ℕ} (he : 0<e) :
    Nat.clog 2 (e+1)=Nat.clog 2 (e/2+1)+1 := by
  have h := Nat.clog_of_two_le (by decide : 1<(2 : ℕ)) (by omega : 2≤e+1)
  have hd : (e+1+2-1)/2=e/2+1 := by omega
  rwa [hd] at h

/-- The actual binary residue equals the mathematical public power. -/
theorem countedPower_correct (N a e : ℕ) :
    ((countedPower N a e).value : ZMod N)=(a : ZMod N)^e := by
  induction e using Nat.strong_induction_on with
  | h e ih =>
    by_cases he : e=0
    · subst e
      rw [countedPower,dif_pos rfl]
      simp only [ZMod.natCast_mod,Nat.cast_one,pow_zero]
    · have hsmall := Nat.div_lt_self (Nat.pos_of_ne_zero he) (by decide : 1<(2 : ℕ))
      have hc := ih (e/2) hsmall
      rw [countedPower,dif_neg he]
      by_cases hp : e%2=0
      · rw [if_pos hp]
        simp only [ZMod.natCast_mod,Nat.cast_mul,hc]
        have hd : e/2+e/2=e := by omega
        rw [←pow_add,hd]
      · rw [if_neg hp]
        simp only [ZMod.natCast_mod,Nat.cast_mul,hc]
        have hd : e/2+e/2+1=e := by omega
        rw [←pow_add,←pow_succ,hd]

/-- Every computed power residue is below the actual public modulus. -/
theorem countedPower_value_lt {N : ℕ} (hN : 0<N) (a e : ℕ) :
    (countedPower N a e).value<N := by
  rw [countedPower]
  split
  · exact Nat.mod_lt _ hN
  · split <;> exact Nat.mod_lt _ hN

/-- The halving counter is the literal binary exponent length. -/
theorem countedPower_halvings (N a e : ℕ) :
    (countedPower N a e).halvings=Nat.clog 2 (e+1) := by
  induction e using Nat.strong_induction_on with
  | h e ih =>
    by_cases he : e=0
    · subst e
      rw [countedPower,dif_pos rfl]
      simp
    · have hsmall := Nat.div_lt_self (Nat.pos_of_ne_zero he) (by decide : 1<(2 : ℕ))
      have hc := ih (e/2) hsmall
      have hlog := clog_halving (Nat.pos_of_ne_zero he)
      rw [countedPower,dif_neg he]
      split <;> simpa only [hc] using hlog.symm

/-- At most two explicit modular multiplications per actual halving. -/
theorem countedPower_multiplications (N a e : ℕ) :
    (countedPower N a e).multiplications≤2*Nat.clog 2 (e+1) := by
  induction e using Nat.strong_induction_on with
  | h e ih =>
    by_cases he : e=0
    · subst e
      rw [countedPower,dif_pos rfl]
      simp
    · have hsmall := Nat.div_lt_self (Nat.pos_of_ne_zero he) (by decide : 1<(2 : ℕ))
      have hc := ih (e/2) hsmall
      have hlog := clog_halving (Nat.pos_of_ne_zero he)
      rw [countedPower,dif_neg he]
      split <;> dsimp only <;> omega

/-- Residue reductions are charged separately from exponent halvings:
an odd step pays both its input normalization and product reduction. -/
theorem countedPower_reductions (N a e : ℕ) :
    (countedPower N a e).reductions≤3*Nat.clog 2 (e+1)+1 := by
  induction e using Nat.strong_induction_on with
  | h e ih =>
    by_cases he : e=0
    · subst e
      rw [countedPower,dif_pos rfl]
      simp
    · have hsmall := Nat.div_lt_self (Nat.pos_of_ne_zero he) (by decide : 1<(2 : ℕ))
      have hc := ih (e/2) hsmall
      have hlog := clog_halving (Nat.pos_of_ne_zero he)
      rw [countedPower,dif_neg he]
      split <;> dsimp only <;> omega

/-- Actual labelled geometric records and their multiplication counter. -/
structure WalkReport where
  /-- Every constructed residue retains its original exponent label. -/
  records : List (ℕ×ℕ)
  /-- Multiplications performed while advancing to the next record. -/
  multiplications : ℕ
  /-- All current-residue and next-product reductions. -/
  reductions : ℕ

/-- Generate only successive modular residues, stopping before the
unused multiplication after the final record. -/
def countedWalk (N start step : ℕ) : ℕ → ℕ → WalkReport
  | 0,_ => ⟨[],0,0⟩
  | 1,index => ⟨[(start%N,index)],0,1⟩
  | k+2,index =>
    let current := start%N
    let tail := countedWalk N (current*step%N) step (k+1) (index+1)
    ⟨(current,index)::tail.records,tail.multiplications+1,tail.reductions+2⟩

/-- The recurrence constructs precisely the original geometric powers
and every original label, rather than an assumed supplied table. -/
theorem countedWalk_records (N start step len index : ℕ) :
    (countedWalk N start step len index).records=
      (List.range len).map fun i =>
        (((start : ZMod N)*(step : ZMod N)^i).val,index+i) := by
  induction len generalizing start index with
  | zero => simp only [countedWalk,List.range_zero,List.map_nil]
  | succ len ih =>
    cases len with
    | zero => simp [countedWalk,List.range_succ_eq_map,ZMod.val_natCast]
    | succ k =>
      rw [countedWalk]
      rw [ih]
      conv_rhs => rw [List.range_succ_eq_map,List.map_cons,List.map_map]
      simp only [pow_zero,mul_one,ZMod.val_natCast,Nat.add_zero]
      congr 1
      apply List.map_congr_left
      intro i hi
      simp only [Function.comp_apply,ZMod.natCast_mod,Nat.cast_mul,pow_succ',mul_assoc]
      congr 1
      omega

/-- The actual recurrence performs exactly len-1 multiplications. -/
theorem countedWalk_multiplications (N start step len index : ℕ) :
    (countedWalk N start step len index).multiplications=len-1 := by
  induction len generalizing start index with
  | zero => simp only [countedWalk,Nat.zero_sub]
  | succ len ih =>
    cases len with
    | zero => simp only [countedWalk,Nat.sub_self]
    | succ k =>
      rw [countedWalk]
      dsimp only
      rw [ih]
      omega

/-- Each constructed record pays its normalization and each advance its
product reduction; the omitted final advance is not charged. -/
theorem countedWalk_reductions (N start step len index : ℕ) :
    (countedWalk N start step len index).reductions=len+(len-1) := by
  induction len generalizing start index with
  | zero => simp only [countedWalk,Nat.zero_sub,Nat.zero_add]
  | succ len ih =>
    cases len with
    | zero => simp only [countedWalk,Nat.sub_self,Nat.add_zero]
    | succ k =>
      rw [countedWalk]
      dsimp only
      rw [ih]
      omega

/-- Every actual generated list has exactly its requested length. -/
theorem countedWalk_length (N start step len index : ℕ) :
    (countedWalk N start step len index).records.length=len := by
  rw [countedWalk_records,List.length_map,List.length_range]

/-- Every integer residue in the actual list is below the public modulus. -/
theorem countedWalk_values_lt {N : ℕ} (hN : 0<N) (start step len index : ℕ) :
    ∀ record∈(countedWalk N start step len index).records,record.1<N := by
  let : NeZero N := ⟨hN.ne'⟩
  rw [countedWalk_records]
  intro record hr
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hr
  exact ZMod.val_lt _

/-- Bounded modular multiplication operands cannot hide huge intermediate
integers: their literal product is strictly below N squared. -/
theorem residue_product_lt_square {N a b : ℕ} (ha : a<N) (hb : b<N) : a*b<N^2 := by
  have hN : 0<N := by omega
  have hA : a≤N-1 := by omega
  have hB : b≤N-1 := by omega
  have hm := Nat.mul_le_mul hA hB
  have he := Nat.sub_add_cancel (by omega : 1≤N)
  nlinarith

/-- The integer product width is at most twice the public modulus width.
This operand-size theorem is not a claim about an implemented bit backend. -/
theorem residue_product_bit_width {N a b : ℕ} (ha : a<N) (hb : b<N) :
    Nat.clog 2 (a*b+1)≤2*Nat.clog 2 (N+1) := by
  have hm : a*b+1≤N^2 := by have h:=residue_product_lt_square ha hb; omega
  have hn := Nat.le_pow_clog (by decide : 1<(2 : ℕ)) (N+1)
  apply Nat.clog_le_of_le_pow
  have hs := Nat.pow_le_pow_left (by omega : N≤2^Nat.clog 2 (N+1)) 2
  calc
    _≤N^2 := hm
    _≤(2^Nat.clog 2 (N+1))^2 := hs
    _=2^(2*Nat.clog 2 (N+1)) := by rw [←pow_mul]; congr 1; omega

/-- All actual raw construction data, before sorting and decoding. -/
structure RawSource (N : ℕ) where
  /-- Cached public active scalar; no hidden period is retained. -/
  active : ℕ
  /-- Inverse scalar read or acquired from the actual public unit. -/
  inverse : ℕ
  /-- The public quarter centre, with its square root charged separately. -/
  centre : ℕ
  /-- The actual public block width 2B. -/
  block : ℕ
  /-- Actual binary centre power and all its arithmetic counters. -/
  target : PowerReport
  /-- Actual inverse block-step power and all its counters. -/
  step : PowerReport
  /-- Actual labelled baby list and its arithmetic counters. -/
  babies : WalkReport
  /-- Actual labelled shifted list and its arithmetic counters. -/
  giants : WalkReport

/-- This raw builder is executable natural-number code. Inverse acquisition,
the public square root and downstream sorting are separate operations. -/
def buildRawSource (N a inverse B : ℕ) : RawSource N :=
  let centre := quarterCentre N
  let block := 2*B
  let target := countedPower N a centre
  let step := countedPower N inverse block
  let babies := countedWalk N 1 a block 0
  let giants := countedWalk N target.value step.value block 0
  ⟨a,inverse,centre,block,target,step,babies,giants⟩

/-- All residue multiplications performed by the two actual powers and walks. -/
def rawMultiplications {N : ℕ} (source : RawSource N) : ℕ :=
  source.target.multiplications+source.step.multiplications+
    source.babies.multiplications+source.giants.multiplications

/-- All modulus-N reductions performed by the actual construction. -/
def rawReductions {N : ℕ} (source : RawSource N) : ℕ :=
  source.target.reductions+source.step.reductions+
    source.babies.reductions+source.giants.reductions

/-- Exponent halvings, and hence parity tests, of the two actual setup powers. -/
def rawHalvings {N : ℕ} (source : RawSource N) : ℕ :=
  source.target.halvings+source.step.halvings

/-- Construction pays both setup powers and exactly two linear walks.
These are actual arithmetic counts, not a complete bit-cost certificate. -/
theorem buildRawSource_counts (N a inverse B : ℕ) :
    rawMultiplications (buildRawSource N a inverse B)≤
      2*Nat.clog 2 (quarterCentre N+1)+2*Nat.clog 2 (2*B+1)+2*(2*B-1) ∧
    rawReductions (buildRawSource N a inverse B)≤
      3*Nat.clog 2 (quarterCentre N+1)+3*Nat.clog 2 (2*B+1)+2+
        2*(2*B+(2*B-1)) ∧
    rawHalvings (buildRawSource N a inverse B)=
      Nat.clog 2 (quarterCentre N+1)+Nat.clog 2 (2*B+1) := by
  have hp := countedPower_multiplications N a (quarterCentre N)
  have hs := countedPower_multiplications N inverse (2*B)
  have hrp := countedPower_reductions N a (quarterCentre N)
  have hrs := countedPower_reductions N inverse (2*B)
  have hb := countedWalk_multiplications N 1 a (2*B) 0
  have hg := countedWalk_multiplications N
    (countedPower N a (quarterCentre N)).value (countedPower N inverse (2*B)).value (2*B) 0
  have hbr := countedWalk_reductions N 1 a (2*B) 0
  have hgr := countedWalk_reductions N
    (countedPower N a (quarterCentre N)).value (countedPower N inverse (2*B)).value (2*B) 0
  constructor
  · dsimp only [rawMultiplications,buildRawSource]
    omega
  constructor
  · dsimp only [rawReductions,buildRawSource]
    omega
  · simp only [rawHalvings,buildRawSource,countedPower_halvings]

/-- The actual raw baby array is exactly the existing recovery source. -/
theorem buildRawSource_babies {N : ℕ} [NeZero N] (h : (ZMod N)ˣ) (B : ℕ) :
    (buildRawSource N (h : ZMod N).val (h⁻¹ : ZMod N).val B).babies.records=
      babyRecords N (2*B) h := by
  change (countedWalk N 1 (h : ZMod N).val (2*B) 0).records=_
  rw [countedWalk_records]
  simp only [Nat.cast_one,one_mul,ZMod.natCast_zmod_val,Nat.zero_add,
    Units.val_pow_eq_pow_val,babyRecords]

/-- The actual inverse-step walk is exactly the shifted giant array,
including all original labels and zero block. -/
theorem buildRawSource_giants {N : ℕ} [NeZero N] (h : (ZMod N)ˣ) (B : ℕ) :
    (buildRawSource N (h : ZMod N).val (h⁻¹ : ZMod N).val B).giants.records=
      shiftedRecords h (quarterCentre N) (2*B) := by
  change (countedWalk N (countedPower N (h : ZMod N).val (quarterCentre N)).value
    (countedPower N (h⁻¹ : ZMod N).val (2*B)).value (2*B) 0).records=_
  rw [countedWalk_records]
  simp only [countedPower_correct,ZMod.natCast_zmod_val,ZMod.inv_coe_unit,
    Nat.zero_add,shiftedRecords]
  apply List.map_congr_left
  intro j hj
  have he : h^(quarterCentre N)*(((h⁻¹)^(2*B))^j)=
      h^(quarterCentre N)*(h^((2*B)*j))⁻¹ := by rw [←pow_mul,inv_pow]
  have hv := congrArg (fun u : (ZMod N)ˣ => (u : ZMod N)) he
  simpa only [Units.val_mul,Units.val_pow_eq_pow_val] using
    congrArg (fun z : ZMod N => (z.val,j)) hv

/-- Two actual raw lists have the expected length before any sorting. -/
theorem buildRawSource_lengths (N a inverse B : ℕ) :
    (buildRawSource N a inverse B).babies.records.length=2*B ∧
      (buildRawSource N a inverse B).giants.records.length=2*B := by
  simp only [buildRawSource,countedWalk_length,and_self]

/-- Both lists retain bounded public-ring residues, and both binary
setup results are below N. No large hidden full powers are constructed. -/
theorem buildRawSource_values_lt {N : ℕ} (hN : 0<N) (a inverse B : ℕ) :
    (buildRawSource N a inverse B).target.value<N ∧
    (buildRawSource N a inverse B).step.value<N ∧
    (∀ record∈(buildRawSource N a inverse B).babies.records,record.1<N) ∧
    (∀ record∈(buildRawSource N a inverse B).giants.records,record.1<N) := by
  exact ⟨countedPower_value_lt hN _ _,countedPower_value_lt hN _ _,
    countedWalk_values_lt hN _ _ _ _,countedWalk_values_lt hN _ _ _ _⟩

/-- Ready source keeps the actual sorted arrays, match and checked candidate.
Sorting, lookup and decoding are separate from the raw arithmetic counters. -/
structure ReadySource (N : ℕ) where
  /-- Every binary-power and recurrence construction record. -/
  raw : RawSource N
  /-- Actual sorted labelled baby array. -/
  babies : List (ℕ×ℕ)
  /-- Actual sorted labelled shifted array. -/
  giants : List (ℕ×ℕ)
  /-- Actual ordered global equality, if present. -/
  collision : Option (ℕ×ℕ)
  /-- Checked proper-factor candidate decoded from that equality. -/
  factor : Option ℕ

/-- Sort each constructed list once, keep its actual match, and decode once.
The raw source remains available for the proper-residue continuation. -/
def prepareSource {N : ℕ} (raw : RawSource N) : ReadySource N :=
  let babies := sortedRecords raw.babies.records
  let giants := sortedRecords raw.giants.records
  let collision := matchSorted babies giants
  let factor := match collision with
    | none => none
    | some (i,j) => SemiprimeLongPowerRouting.recoverKnownOrder N (raw.centre-(raw.block*j+i))
  ⟨raw,babies,giants,collision,factor⟩

/-- The executable raw construction has exactly the old global collision. -/
theorem prepareSource_collision {N : ℕ} [NeZero N] (h : (ZMod N)ˣ) (B : ℕ) :
    (prepareSource (buildRawSource N (h : ZMod N).val (h⁻¹ : ZMod N).val B)).collision=
      shiftedCollision h (quarterCentre N) (2*B) := by
  change matchSorted (sortedRecords _) (sortedRecords _)=_
  rw [buildRawSource_babies,buildRawSource_giants]
  rfl

/-- The executable construction produces exactly the proved global decoder
factor, with no hidden order or factor input. -/
theorem prepareSource_factor {N : ℕ} [NeZero N] (h : (ZMod N)ˣ) (B : ℕ) :
    (prepareSource (buildRawSource N (h : ZMod N).val (h⁻¹ : ZMod N).val B)).factor=
      (buildSource h B).factor := by
  unfold prepareSource
  rw [buildRawSource_babies,buildRawSource_giants]
  rfl

/-- The actual sorted arrays agree with the retained semantic source,
and their ordered lookup keeps its existing linear comparison bound. -/
theorem prepareSource_arrays {N : ℕ} [NeZero N] (h : (ZMod N)ˣ) (B : ℕ) :
    (prepareSource (buildRawSource N (h : ZMod N).val (h⁻¹ : ZMod N).val B)).babies=
      (buildSource h B).babies ∧
    (prepareSource (buildRawSource N (h : ZMod N).val (h⁻¹ : ZMod N).val B)).giants=
      (buildSource h B).giants ∧
    matchComparisons
      (prepareSource (buildRawSource N (h : ZMod N).val (h⁻¹ : ZMod N).val B)).babies
      (prepareSource (buildRawSource N (h : ZMod N).val (h⁻¹ : ZMod N).val B)).giants≤4*B := by
  have hb : (prepareSource (buildRawSource N (h : ZMod N).val (h⁻¹ : ZMod N).val B)).babies=
      (buildSource h B).babies := congrArg sortedRecords (buildRawSource_babies h B)
  have hg : (prepareSource (buildRawSource N (h : ZMod N).val (h⁻¹ : ZMod N).val B)).giants=
      (buildSource h B).giants := congrArg sortedRecords (buildRawSource_giants h B)
  exact ⟨hb,hg,by rw [hb,hg]; exact (buildSource_budget h B).2.2⟩

/-- The public centre is no larger than the positive input N. -/
theorem quarterCentre_le_input {N : ℕ} (hN : 0<N) : quarterCentre N≤N := by
  unfold quarterCentre
  omega

/-- The actual least sixth-root width is bounded by the positive input. -/
theorem sixthWidth_le_input {N : ℕ} (hN : 0<N) :
    SemiprimeLehmanCoverage.sixthWidth N≤N := by
  exact Nat.find_min' _ (le_self_pow (by omega : 1≤N) (by decide : (6 : ℕ)≠0))

/-- The block exponent needs at most one bit beyond the public input width. -/
theorem block_exponent_bits {N B : ℕ} (hB : B≤N) :
    Nat.clog 2 (2*B+1)≤Nat.clog 2 (N+1)+1 := by
  have hN := Nat.le_pow_clog (by decide : 1<(2 : ℕ)) (N+1)
  apply Nat.clog_le_of_le_pow
  rw [pow_succ]
  omega

/-- At the actual public width, the full raw arithmetic construction is
linear in B plus the bit length of N. All modular reductions are included. -/
theorem buildRawSource_public_counts {N : ℕ} (hN : 0<N) (a inverse : ℕ) :
    rawMultiplications (buildRawSource N a inverse (SemiprimeLehmanCoverage.sixthWidth N))≤
      4*SemiprimeLehmanCoverage.sixthWidth N+4*Nat.clog 2 (N+1)+2 ∧
    rawReductions (buildRawSource N a inverse (SemiprimeLehmanCoverage.sixthWidth N))≤
      8*SemiprimeLehmanCoverage.sixthWidth N+6*Nat.clog 2 (N+1)+5 ∧
    rawHalvings (buildRawSource N a inverse (SemiprimeLehmanCoverage.sixthWidth N))≤
      2*Nat.clog 2 (N+1)+1 := by
  obtain ⟨hm,hr,hh⟩ := buildRawSource_counts N a inverse (SemiprimeLehmanCoverage.sixthWidth N)
  have hc := Nat.clog_mono_right 2 (Nat.add_le_add_right (quarterCentre_le_input hN) 1)
  have hb := block_exponent_bits (sixthWidth_le_input hN)
  omega

/-- Every actual certified window has the same constructed sorted arrays,
global match and factor option. This links executable construction to the
full preceding proof without a supplied factor or numerical order. -/
theorem windowCertified_reconstruction {N : ℕ} {window : SemiprimeTotientWindow.Source N}
    (hw : WindowCertified window) :
    let source := prepareSource (buildRawSource N window.active.val.val
      ((window.active⁻¹ : (ZMod N)ˣ) : ZMod N).val (SemiprimeLehmanCoverage.sixthWidth N))
    source.babies=window.babies ∧ source.giants=window.giants ∧
      source.collision=window.collision ∧ source.factor=window.factor := by
  cases hw with
  | @remaining p q g h z s hp hq hdata =>
    let : NeZero (p*q) := ⟨Nat.mul_ne_zero hp.ne_zero hq.ne_zero⟩
    have hi : ((h⁻¹ : (ZMod (p*q))ˣ) : ZMod (p*q))=(h : ZMod (p*q))⁻¹ :=
      (ZMod.inv_coe_unit h).symm
    dsimp only
    rw [show (buildSource h (SemiprimeLehmanCoverage.sixthWidth (p*q))).active=h from rfl]
    rw [hi]
    obtain ⟨hb,hg,_⟩ := prepareSource_arrays h (SemiprimeLehmanCoverage.sixthWidth (p*q))
    exact ⟨hb,hg,prepareSource_collision h _,prepareSource_factor h _⟩

/-- Every binary multiplication temporary has at most twice the public
modulus bit width, including the odd-step product after squaring. -/
theorem countedPower_temporary_widths {N : ℕ} (hN : 0<N) (a e : ℕ) :
    Nat.clog 2 ((countedPower N a (e/2)).value^2+1)≤2*Nat.clog 2 (N+1) ∧
    Nat.clog 2 (((countedPower N a (e/2)).value^2%N)*(a%N)+1)≤
      2*Nat.clog 2 (N+1) := by
  have hc := countedPower_value_lt hN a (e/2)
  exact ⟨by simpa only [pow_two] using residue_product_bit_width hc hc,
    residue_product_bit_width (Nat.mod_lt _ hN) (Nat.mod_lt _ hN)⟩

/-- Any recurrence advance with its actual bounded step has a bounded
integer product, uniformly across all preceding recurrence states. -/
theorem countedWalk_temporary_width {N step : ℕ} (hN : 0<N) (hstep : step<N)
    (start : ℕ) : Nat.clog 2 ((start%N)*step+1)≤2*Nat.clog 2 (N+1) :=
  residue_product_bit_width (Nat.mod_lt _ hN) hstep

/-- A certified actual source supplies bounded active and inverse inputs.
Their acquisition remains part of the preceding/public inverse charges. -/
theorem windowCertified_input_bounds {N : ℕ} {window : SemiprimeTotientWindow.Source N}
    (hw : WindowCertified window) :
    window.active.val.val<N ∧ ((window.active⁻¹ : (ZMod N)ˣ) : ZMod N).val<N := by
  cases hw with
  | remaining hp hq hdata =>
    let : NeZero _ := ⟨Nat.mul_ne_zero hp.ne_zero hq.ne_zero⟩
    exact ⟨ZMod.val_lt _,ZMod.val_lt _⟩

/-- The exact reconstruction of every certified actual leaf pays linear
raw arithmetic plus logarithmic setup work, without free inverse acquisition. -/
theorem windowCertified_construction_budget {N : ℕ} {window : SemiprimeTotientWindow.Source N}
    (hw : WindowCertified window) :
    let source := buildRawSource N window.active.val.val
      ((window.active⁻¹ : (ZMod N)ˣ) : ZMod N).val (SemiprimeLehmanCoverage.sixthWidth N)
    rawMultiplications source≤4*SemiprimeLehmanCoverage.sixthWidth N+4*Nat.clog 2 (N+1)+2 ∧
    rawReductions source≤8*SemiprimeLehmanCoverage.sixthWidth N+6*Nat.clog 2 (N+1)+5 ∧
    rawHalvings source≤2*Nat.clog 2 (N+1)+1 := by
  have hN : 0<N := by
    cases hw with
    | remaining hp hq hdata => exact Nat.mul_pos hp.pos hq.pos
  exact buildRawSource_public_counts hN _ _

/-- Every window retained by the actual N-only public procedure is
certified, including an already successful window. -/
theorem publicWindow_source_certified {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    {window : SemiprimeTotientWindow.Source
      (SemiprimeKernelDescent.leafInput (SemiprimeTotientWindow.publicPacket (p*q)).parent.source)}
    (hs : (SemiprimeTotientWindow.publicPacket (p*q)).source=some window) :
    WindowCertified window := by
  have hc := SemiprimeLongPowerRouting.leafRefinement_certified
    (SemiprimeKernelDescent.publicTrace_certified hp hq)
  exact SemiprimeTotientWindow.sourceForLeaf_certified hc hs

/-- The actual public leaf construction fits the ORIGINAL input's width
and bit length, paying every raw residue multiplication and reduction. -/
theorem publicWindow_construction_budget {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    {window : SemiprimeTotientWindow.Source
      (SemiprimeKernelDescent.leafInput (SemiprimeTotientWindow.publicPacket (p*q)).parent.source)}
    (hs : (SemiprimeTotientWindow.publicPacket (p*q)).source=some window) :
    let N := SemiprimeKernelDescent.leafInput (SemiprimeTotientWindow.publicPacket (p*q)).parent.source
    let source := buildRawSource N window.active.val.val
      ((window.active⁻¹ : (ZMod N)ˣ) : ZMod N).val (SemiprimeLehmanCoverage.sixthWidth N)
    rawMultiplications source≤4*SemiprimeLehmanCoverage.sixthWidth (p*q)+4*Nat.clog 2 (p*q+1)+2 ∧
    rawReductions source≤8*SemiprimeLehmanCoverage.sixthWidth (p*q)+6*Nat.clog 2 (p*q+1)+5 ∧
    rawHalvings source≤2*Nat.clog 2 (p*q+1)+1 := by
  have hb := windowCertified_construction_budget (publicWindow_source_certified hp hq hs)
  have hn := SemiprimeLongPowerRouting.certified_leaf_input_le
    (SemiprimeKernelDescent.publicTrace_certified hp hq)
  have hw := SemiprimeKernelDescent.sixthWidth_mono hn
  have hl := Nat.clog_mono_right 2 (Nat.add_le_add_right hn 1)
  dsimp only
  dsimp only at hb
  change SemiprimeKernelDescent.leafInput
    (SemiprimeTotientWindow.publicPacket (p*q)).parent.source≤p*q at hn
  change SemiprimeLehmanCoverage.sixthWidth
    (SemiprimeKernelDescent.leafInput (SemiprimeTotientWindow.publicPacket (p*q)).parent.source)≤
      SemiprimeLehmanCoverage.sixthWidth (p*q) at hw
  change Nat.clog 2
    (SemiprimeKernelDescent.leafInput (SemiprimeTotientWindow.publicPacket (p*q)).parent.source+1)≤
      Nat.clog 2 (p*q+1) at hl
  omega

end RiemannGaussian.SemiprimeWindowConstruction
