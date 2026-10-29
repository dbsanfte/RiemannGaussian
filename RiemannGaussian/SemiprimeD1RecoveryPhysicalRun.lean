/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1RecoveryChildBits
import RiemannGaussian.SemiprimeD1RecoveryStripBits
import RiemannGaussian.SemiprimeD1RecoveryFinishBits

/-! # Original physical scalar recovery from literal child coefficient caches
The physical source rows are acquired internally. Child data are literal nested
Boolean lists. Only proof-side projections interpret their scalar values.
-/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace RiemannGaussian.SemiprimeD1RecoveryPhysicalRun
open SemiprimeBitArithmetic SemiprimeRationalBits
open SemiprimeD1RecoveryIntegerBits

/-- Actual cached physical row/child operands and retained reports. -/
structure EntriesReport where
  /-- Canonical physical source words beside physically copied child digits. -/
  entries : List Entry
  /-- Actual payload/address scans and copies. -/
  clock : ℕ
  /-- Typed original index digit acquisition/control stages. -/
  metadataWork : ℕ

/-- Every original nonnegative index has a derived, non-advised digit width. -/
theorem index_fits (n : ℕ) : n < 2^(n+1) := by
  have h:=SemiprimeD1HermiteDenominatorBits.self_le_two_power n
  exact lt_of_le_of_lt h (Nat.pow_lt_pow_right (by omega) (by omega))

/-- Literal physical child selection beside each actual acquired source row. -/
def entries (children : List (List (List Bool))) :
    List SemiprimeD1RecoveryRowsBits.Row → EntriesReport
  | [] => ⟨[],1,1⟩
  | r::rs =>
    let node:=SemiprimeEncodedRowSelection.digits (r.node+1) r.node
    let index:=SemiprimeEncodedRowSelection.digits (r.index+1) r.index
    let child:=SemiprimeD1RecoveryChildBits.read children node.bits index.bits
    let tail:=entries children rs
    ⟨⟨r.word.numerator,r.word.denominator,child.bits⟩::tail.entries,
      child.clock+tail.clock+4,node.work+index.work+tail.metadataWork+4⟩

/-- Proof-only literal child cache view, never evaluated by the runtime. -/
def childView (children : List (List (List Bool))) (node : ℕ) : Array (List Bool) :=
  ((children[node]?).getD []).toArray

/-- Proof-only canonical row projection, never used to produce a coefficient. -/
def rowView (rs : List SemiprimeD1RecoveryRowsBits.Row) :
    List SemiprimeD1RecoveryRowsRun.Row :=
  rs.map fun r => ⟨r.node,r.index,r.word.numerator.value,bitValue r.word.denominator⟩

/-- Physical child-cache selection agrees exactly with the original native
canonical row traversal on the actual literal child data. -/
theorem entries_native (children : List (List (List Bool)))
    (rs : List SemiprimeD1RecoveryRowsBits.Row) :
    native (entries children rs).entries=
      (SemiprimeD1RecoveryCanonicalRun.entries (childView children) (rowView rs)).value := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    simp only [native,rowView] at ih
    have hn:=SemiprimeEncodedRowSelection.digits_value (r.node+1) r.node (index_fits r.node)
    have hj:=SemiprimeEncodedRowSelection.digits_value (r.index+1) r.index (index_fits r.index)
    have hc:=SemiprimeD1RecoveryChildBits.read_bits children
      (SemiprimeEncodedRowSelection.digits (r.node+1) r.node).bits
      (SemiprimeEncodedRowSelection.digits (r.index+1) r.index).bits
    rw [hn,hj] at hc
    simp only [entries,native,List.map_cons,rowView,SemiprimeD1RecoveryCanonicalRun.entries,
      childView,List.getElem?_toArray,List.map_id]
    change _::_ = _::_
    rw [←ih]
    congr 1
    rw [hc]

/-- The actual physical canonical row list is exactly the original row list,
without executing native numerator or denominator extraction. -/
theorem rowView_original (a M u : ℕ) (hM : u ≤ M) :
    rowView (SemiprimeD1RecoveryRowsBits.acquire a M u).rows=
      (SemiprimeD1RecoveryRowsRun.acquire a M u).rows := by
  let decode : (ℕ×ℕ×ℤ×ℕ) → SemiprimeD1RecoveryRowsRun.Row :=
    fun q => ⟨q.1,q.2.1,q.2.2.1,q.2.2.2⟩
  have hv:=congrArg (List.map decode) (SemiprimeD1RecoveryRowsBits.acquire_view a M u hM)
  simpa [rowView,SemiprimeD1RecoveryRowsBits.view,List.map_map,decode,Function.comp_def] using hv

/-- Actual original row/child operands equal the original rational-weight term
projection; all scalar canonical values in this theorem are proof-only. -/
theorem entries_original (a M u : ℕ) (hM : u ≤ M)
    (children : List (List (List Bool))) :
    native (entries children (SemiprimeD1RecoveryRowsBits.acquire a M u).rows).entries=
      SemiprimeD1RecoveryCanonicalRun.canonical
        (SemiprimeD1IntegerRecovery.terms a M u (childView children)) := by
  rw [entries_native,rowView_original a M u hM]
  exact SemiprimeD1RecoveryCanonicalRun.acquired_entries a M u (childView children)

/-- Actual canonical source caps follow from original acquired weights, with
no requested coefficient/height/Fits answer at the physical entrypoint. -/
theorem original_entry_bounds (a M u : ℕ) (hM : u ≤ M)
    (children : List (List (List Bool))) :
    let es:=(entries children (SemiprimeD1RecoveryRowsBits.acquire a M u).rows).entries
    (∀ e ∈ es, 0 < bitValue e.denominator ∧
      bitValue e.denominator ≤ 2^SemiprimeD1HermiteWeightBits.weightEnvelope a M ∧
      e.numerator.value.natAbs ≤ 2^SemiprimeD1HermiteWeightBits.weightEnvelope a M) ∧
    es.length ≤ SemiprimeD1WireKernelOriginal.size a*(4*M) := by
  dsimp only
  have hv:=entries_original a M u hM children
  constructor
  · intro e he
    have hm : SemiprimeD1RecoveryCanonicalRun.Entry.mk e.numerator.value
        (bitValue e.denominator) e.child ∈ SemiprimeD1RecoveryCanonicalRun.canonical
          (SemiprimeD1IntegerRecovery.terms a M u (childView children)) := by
      rw [←hv]
      exact List.mem_map.mpr ⟨e,he,rfl⟩
    obtain ⟨v,hv,hve⟩:=List.mem_map.mp hm
    have hb:=SemiprimeD1IntegerRecoveryHeight.term_bounds a M u hM (childView children) v hv
    have hn:=congrArg SemiprimeD1RecoveryCanonicalRun.Entry.numerator hve
    have hd:=congrArg SemiprimeD1RecoveryCanonicalRun.Entry.denominator hve
    change v.weight.num=e.numerator.value at hn
    change v.weight.den=bitValue e.denominator at hd
    rw [←hd,←hn]
    exact ⟨Rat.den_pos _,hb⟩
  · have hl:=congrArg List.length hv
    simp only [native,SemiprimeD1RecoveryCanonicalRun.canonical,List.length_map] at hl
    rw [hl]
    exact SemiprimeD1IntegerRecoveryHeight.terms_length a M u hM (childView children)

/-- Literal child words, including missing-cache zero defaults, preserve their
actual input precision bound through both physical address scans. -/
theorem child_read_length (children : List (List (List Bool))) (node coordinate : List Bool)
    (P : ℕ) (hc : ∀ row ∈ children, ∀ x ∈ row, x.length ≤ P) :
    (SemiprimeD1RecoveryChildBits.read children node coordinate).bits.length ≤ P := by
  rw [SemiprimeD1RecoveryChildBits.read_bits]
  cases hn:children[bitValue node]? with
  | none => simp
  | some row =>
    simp only [Option.getD_some]
    cases hj:row[bitValue coordinate]? with
    | none => simp
    | some x => exact hc row (List.mem_of_getElem? hn) x (List.mem_of_getElem? hj)

/-- Every actual retained physical child operand derives its precision from the
literal input cache, not an advised decoded child coefficient. -/
theorem entries_child_length (children : List (List (List Bool)))
    (rs : List SemiprimeD1RecoveryRowsBits.Row) (P : ℕ)
    (hc : ∀ row ∈ children, ∀ x ∈ row, x.length ≤ P) :
    ∀ e ∈ (entries children rs).entries, e.child.length ≤ P := by
  induction rs with
  | nil => simp [entries]
  | cons r rs ih =>
    intro e he
    simp only [entries,List.mem_cons] at he
    rcases he with he|he
    · subst e
      exact child_read_length children _ _ P hc
    · exact ih e he

/-- Public store width is derived from original producer widths and the exact
original signed suffix exponent; no intermediate/output fit is supplied. -/
def width (a M P : ℕ) : ℕ :=
  SemiprimeD1RecoveryNodeBits.width a M+
  SemiprimeD1IntegerRecoveryHeight.recoveryExponent a M P+P+
  SemiprimeD1HermiteWeightBits.weightEnvelope a M+20

/-- Acquire original grid sizes for each width supplier and evaluate only fixed
scalar resource polynomials. These native metadata stages are retained explicitly. -/
def widthRun (a M P : ℕ) : SemiprimeD1RecoveryScalarRun.Run ℕ :=
  let node:=SemiprimeD1RecoveryNodeBits.widthRun a M
  let recovery:=SemiprimeD1RecoveryFinishBits.widthRun a M P
  let grid:=SemiprimeD1RecoveryWeightRun.geometry a 0
  ⟨node.value+recovery.value+P+
    SemiprimeD1HermiteWeightBits.weightPolynomial a M grid.size+20,
    node.work+recovery.work+grid.work+300⟩

/-- Actual width acquisition returns exactly the original-derived bound. -/
theorem widthRun_value (a M P : ℕ) : (widthRun a M P).value=width a M P := by
  simp only [widthRun,width,SemiprimeD1RecoveryNodeBits.widthRun_value,
    SemiprimeD1RecoveryFinishBits.widthRun_value,SemiprimeD1RecoveryWeightRun.geometry_size,
    SemiprimeD1HermiteWeightBits.weightEnvelope_eq]

/-- Actual original-source physical recovery data and separately scoped control. -/
structure Report where
  /-- Actual final compact residue bits. -/
  bits : List Bool
  /-- All source, cache-address, integer, strip and odd-inverse bit reports. -/
  clock : ℕ
  /-- Retained original typed/index/digit-generation/control stages. -/
  metadataWork : ℕ

/-- Complete physical coefficient-data path. Original source rows are acquired
internally, every literal child is physically read, and all reports are retained.
The native width expression is an explicitly scoped original-parameter stage. -/
def runAt (a M u p W : ℕ) (children : List (List (List Bool))) : Report :=
  let rows:=SemiprimeD1RecoveryRowsBits.acquire a M u
  let cached:=entries children rows.rows
  let template:=List.replicate W false
  let D:=denominator template cached.entries
  let N:=accumulate template D.bits cached.entries
  let out:=SemiprimeD1RecoveryStripBits.finish p N.word D.bits
  ⟨out.bits,rows.clock+cached.clock+D.clock+N.clock+out.clock+3*W+10,
    rows.metadataWork+cached.metadataWork+10⟩

/-- Acquire the original numeric template before executing the complete data path.
Native width arithmetic is retained separately from physical bit operations. -/
def run (a M u p P : ℕ) (children : List (List (List Bool))) : Report :=
  let acquiredWidth:=widthRun a M P
  let out:=runAt a M u p acquiredWidth.value children
  ⟨out.bits,out.clock,out.metadataWork+acquiredWidth.work+10⟩

/-- The actual original width supplier specializes the fixed-width data path. -/
theorem run_bits (a M u p P : ℕ) (children : List (List (List Bool))) :
    (run a M u p P children).bits=(runAt a M u p (width a M P) children).bits := by
  change (runAt a M u p (widthRun a M P).value children).bits=_
  rw [widthRun_value]

/-- The actual complete physical source/cache/integer/finalizer run refines the
original recovery result. Only original u<=M and literal child precisions enter. -/
theorem run_value (a M u p P : ℕ) (children : List (List (List Bool)))
    (hM : u ≤ M) (hc : ∀ row ∈ children, ∀ x ∈ row, x.length ≤ P) :
    (bitValue (run a M u p P children).bits:ZMod (2^p))=
      SemiprimeD1IntegerRecoveryResidue.finish p
        (SemiprimeD1IntegerRecovery.run a M u (childView children)) := by
  let es:=(entries children (SemiprimeD1RecoveryRowsBits.acquire a M u).rows).entries
  let A:=SemiprimeD1HermiteWeightBits.weightEnvelope a M
  let K:=SemiprimeD1WireKernelOriginal.size a*(4*M)
  let template:=List.replicate (width a M P) false
  let D:=(SemiprimeD1RecoveryCanonicalRun.denominator (native es)).value
  have hb:=original_entry_bounds a M u hM children
  change (∀ e ∈ es, 0 < bitValue e.denominator ∧ bitValue e.denominator ≤ 2^A ∧
    e.numerator.value.natAbs ≤ 2^A) ∧ es.length ≤ K at hb
  have hW : K+A+A*K+P+1 ≤ template.length := by
    dsimp only [template,width,A,K,SemiprimeD1IntegerRecoveryHeight.recoveryExponent]
    rw [List.length_replicate]
    nlinarith only
  have hwd : A*es.length+1 ≤ template.length := by
    have hm:=Nat.mul_le_mul_left A hb.2
    omega
  have hdval:=denominator_correct template es A (fun e he => (hb.1 e he).2.1) hwd
  have hdb : D ≤ 2^(A*K) :=
    (native_denominator_bound es A (fun e he => (hb.1 e he).2.1)).trans
      (Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_left A hb.2))
  have hnval:=accumulate_dyadic template (denominator template es).bits es D A K P hdval
    (fun e he => (hb.1 e he).2.2)
    (entries_child_length children _ P hc) hb.2 hdb hW
  have he:=entries_original a M u hM children
  change native es=SemiprimeD1RecoveryCanonicalRun.canonical
    (SemiprimeD1IntegerRecovery.terms a M u (childView children)) at he
  have hdOriginal : D=(SemiprimeD1IntegerRecovery.run a M u (childView children)).denominator := by
    dsimp only [D]
    rw [he,SemiprimeD1RecoveryCanonicalRun.denominator_value]
    simp only [SemiprimeD1IntegerRecovery.run,SemiprimeD1IntegerRecovery.denominatorRun_value]
  have hnOriginal : (SemiprimeD1RecoveryCanonicalRun.accumulate D (native es)).value=
      (SemiprimeD1IntegerRecovery.run a M u (childView children)).numerator := by
    rw [he,SemiprimeD1RecoveryCanonicalRun.accumulate_value,hdOriginal]
    simp only [SemiprimeD1IntegerRecovery.run,SemiprimeD1IntegerRecovery.accumulateRun_value]
  have hpos : 0 < bitValue (denominator template es).bits := by
    rw [hdval]
    change 0 < D
    rw [hdOriginal]
    simpa only [SemiprimeD1IntegerRecovery.run,
      SemiprimeD1IntegerRecovery.denominatorRun_value] using
      SemiprimeD1IntegerRecovery.denominator_pos
        (SemiprimeD1IntegerRecovery.terms a M u (childView children))
  have hf:=SemiprimeD1RecoveryStripBits.finish_value p
    (accumulate template (denominator template es).bits es).word
    (denominator template es).bits hpos
  have hrun : (run a M u p P children).bits=
      (SemiprimeD1RecoveryStripBits.finish p
        (accumulate template (denominator template es).bits es).word
        (denominator template es).bits).bits := by
    rw [run_bits]
    rfl
  rw [hrun,hf]
  have hnFinal:=hnval.trans hnOriginal
  have hdFinal : bitValue (denominator template es).bits=
      (SemiprimeD1IntegerRecovery.run a M u (childView children)).denominator :=
    hdval.trans hdOriginal
  simp only [SemiprimeD1IntegerRecoveryResidue.finish,SemiprimeD1IntegerRecoveryResidue.stripped,
    SemiprimeD1CrossingResidue.residue,hnFinal,hdFinal]

end RiemannGaussian.SemiprimeD1RecoveryPhysicalRun
