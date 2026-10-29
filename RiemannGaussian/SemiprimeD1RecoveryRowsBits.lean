/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1RecoveryNodeBitsBounds
import RiemannGaussian.SemiprimeD1RecoveryRowsRun

/-! # Actual original-grid physical canonical-row cache
Every node is acquired by the physical constructor, including inactive nodes
before filtering. Only native node/index labels are metadata; canonical signed
numerator and positive-denominator payloads are actual copied Boolean words.
-/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace RiemannGaussian.SemiprimeD1RecoveryRowsBits
open SemiprimeRationalBits SemiprimeBitArithmetic SemiprimeSourceMemoryBits
open SemiprimeD1RecoveryScalarRun SemiprimeD1RecoveryWeightRun
open SemiprimeD1WireKernelOriginal SemiprimeD1TaperedLoss SemiprimeD1JetRecoveryGrid

/-- One physical canonical row with typed original indexing metadata. -/
structure Row where
  /-- Original grid node label, native metadata. -/
  node : ℕ
  /-- Original retained coefficient index, native metadata. -/
  index : ℕ
  /-- Actual physical canonical weight payload. -/
  word : RationalWord

/-- Actual physical canonical rows and distinctly retained reports. -/
structure Report where
  /-- Original node-major/index-major physical rows. -/
  rows : List Row
  /-- Actual rational arithmetic and physical payload copies. -/
  clock : ℕ
  /-- Typed indexing/valuation/width/control stages. -/
  metadataWork : ℕ

/-- Copy every actual canonical payload once while assigning original local indices. -/
def pack (node : ℕ) : ℕ → List RationalWord → Report
  | _,[] => ⟨[],1,1⟩
  | index,x::xs =>
    let current:=copyWord x
    let tail:=pack node (index+1) xs
    ⟨⟨node,index,current.word⟩::tail.rows,current.clock+tail.clock+3,tail.metadataWork+3⟩

/-- Acquire every original physical node before the original active-row filter. -/
def gather (a M u : ℕ) : List (Fin (size a)) → Report
  | [] => ⟨[],1,1⟩
  | t::ts =>
    let current:=SemiprimeD1RecoveryNodeBits.acquire a M u t
    let tail:=gather a M u ts
    if t.val=center a ∨ current.retained=0 then
      ⟨tail.rows,current.clock+tail.clock+3,current.metadataWork+tail.metadataWork+4⟩
    else
      let rows:=pack t.val 0 current.words
      ⟨rows.rows++tail.rows,current.clock+tail.clock+rows.clock+3,
        current.metadataWork+tail.metadataWork+rows.metadataWork+2*rows.rows.length+6⟩

/-- ORIGINAL-input full physical canonical row acquisition; no row/word/count supplier. -/
def acquire (a M u : ℕ) : Report :=
  let nodes:=SemiprimeD1RecoveryRowsRun.nodeIndices a
  let rows:=gather a M u nodes.value
  ⟨rows.rows,rows.clock+3,nodes.work+rows.metadataWork+3⟩

/-- Proof-only scalar view; the runtime constructor never calls this decoder. -/
def view (rows : List Row) : List (ℕ×ℕ×ℤ×ℕ) :=
  rows.map fun r => (r.node,r.index,r.word.numerator.value,bitValue r.word.denominator)

/-- Original labels applied to canonical component pairs, for proof comparison. -/
def tag (node : ℕ) : ℕ → List (ℤ×ℕ) → List (ℕ×ℕ×ℤ×ℕ)
  | _,[] => []
  | index,(n,d)::xs => (node,index,n,d)::tag node (index+1) xs

/-- Canonical views preserve actual concatenation order. -/
theorem view_append (xs ys : List Row) : view (xs++ys)=view xs++view ys := by
  simp only [view,List.map_append]

/-- Actual deep payload copying preserves exact canonical components and order. -/
theorem pack_view (node index : ℕ) (words : List RationalWord) :
    view (pack node index words).rows=
      tag node index (words.map (fun x => (x.numerator.value,bitValue x.denominator))) := by
  induction words generalizing index with
  | nil => rfl
  | cons x xs ih =>
    simp only [view] at ih
    simp only [pack,view,List.map_cons,copyWord_word,tag,ih]

/-- Native original canonical records have the same precise index traversal. -/
theorem tag_native (node index : ℕ) (rows : List CanonicalRow) :
    tag node index (rows.map (fun r => (r.numerator,r.denominator)))=
      (List.range rows.length).map fun j =>
        let r:=(rows[j]?).getD ⟨0,1⟩
        (node,index+j,r.numerator,r.denominator) := by
  induction rows generalizing index with
  | nil => rfl
  | cons r rows ih =>
    simp only [List.map_cons,tag,List.length_cons,List.range_succ_eq_map,List.map_cons,
      List.getElem?_cons_zero,Option.getD_some,Nat.add_zero,List.map_map,Function.comp_def,
      List.getElem?_cons_succ,ih,Nat.add_left_comm,Nat.add_comm]

/-- The original acquired retained count is computed, not supplied as row advice. -/
theorem native_retained (a M u : ℕ) (t : Fin (size a)) :
    (SemiprimeD1RecoveryWeightRun.acquire a M u t).data.retained=nodeMultiplicity a (height M u) u t.val := by
  rw [SemiprimeD1RecoveryWeightRun.acquire_data]
  rfl

/-- Full actual physical row-cache traversal refines the EXACT frozen native
row constructor, including original active-node and local-index order. -/
theorem gather_view (a M u : ℕ) (ts : List (Fin (size a))) (hM : u ≤ M) :
    view (gather a M u ts).rows=
      (SemiprimeD1RecoveryRowsRun.gather a M u ts).rows.map
        (fun r => (r.node,r.index,r.numerator,r.denominator)) := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    have he:=SemiprimeD1RecoveryNodeBitsCorrectness.acquire_canonical a M u t hM
    have hr:=SemiprimeD1RecoveryNodeBits.acquire_retained a M u t
    have hn:=native_retained a M u t
    simp only [gather,SemiprimeD1RecoveryRowsRun.gather,hr,hn]
    split_ifs
    · exact ih
    · rw [view_append,pack_view,he,tag_native,ih]
      simp only [indices_value,List.map_append,List.map_map,Function.comp_def,Nat.zero_add]


/-- ORIGINAL-input actual physical rows equal the original acquired canonical
integer records. No native canonical-field extraction executes in this path. -/
theorem acquire_view (a M u : ℕ) (hM : u ≤ M) :
    view (acquire a M u).rows=(SemiprimeD1RecoveryRowsRun.acquire a M u).rows.map
      (fun r => (r.node,r.index,r.numerator,r.denominator)) := by
  exact gather_view a M u (SemiprimeD1RecoveryRowsRun.nodeIndices a).value hM

/-- Actual copied payload widths and denominator legality are inherited physically. -/
theorem pack_good (node index : ℕ) (words : List RationalWord) (W : ℕ)
    (hv : ∀x∈words,x.Valid) (hw : ∀x∈words,Width x W) :
    (∀r∈(pack node index words).rows,r.word.Valid) ∧
      (∀r∈(pack node index words).rows,Width r.word W) := by
  induction words generalizing index with
  | nil => exact ⟨by simp [pack],by simp [pack]⟩
  | cons x xs ih =>
    have old:=ih (index+1) (fun y hy => hv y (List.mem_cons_of_mem _ hy))
      (fun y hy => hw y (List.mem_cons_of_mem _ hy))
    constructor <;> intro r hr <;> simp only [pack,List.mem_cons,copyWord_word] at hr
    · rcases hr with rfl|hr
      · exact hv x List.mem_cons_self
      · exact old.1 r hr
    · rcases hr with rfl|hr
      · exact hw x List.mem_cons_self
      · exact old.2 r hr

/-- Every actual full-grid physical row has the original internally derived width. -/
theorem gather_good (a M u : ℕ) (ts : List (Fin (size a))) (hM : u ≤ M) :
    (∀r∈(gather a M u ts).rows,r.word.Valid) ∧
      (∀r∈(gather a M u ts).rows,Width r.word (SemiprimeD1RecoveryNodeBits.width a M)) := by
  induction ts with
  | nil => exact ⟨by simp [gather],by simp [gather]⟩
  | cons t ts ih =>
    have cur:=SemiprimeD1RecoveryNodeBitsCorrectness.acquire_correct a M u t hM
    have current:=pack_good t.val 0 (SemiprimeD1RecoveryNodeBits.acquire a M u t).words
      (SemiprimeD1RecoveryNodeBits.width a M) cur.2.1 cur.2.2.1
    simp only [gather]
    split_ifs
    · exact ih
    · constructor <;> intro r hr <;> rcases List.mem_append.mp hr with hh|hh
      · exact current.1 r hh
      · exact ih.1 r hh
      · exact current.2 r hh
      · exact ih.2 r hh

/-- ORIGINAL full physical canonical cache legality/width, with no Fits advice. -/
theorem acquire_good (a M u : ℕ) (hM : u ≤ M) :
    (∀r∈(acquire a M u).rows,r.word.Valid) ∧
      (∀r∈(acquire a M u).rows,Width r.word (SemiprimeD1RecoveryNodeBits.width a M)) :=
  gather_good a M u (SemiprimeD1RecoveryRowsRun.nodeIndices a).value hM

/-- Actual canonical payload packing stores one row per computed weight. -/
theorem pack_length (node index : ℕ) (words : List RationalWord) :
    (pack node index words).rows.length=words.length := by
  induction words generalizing index with
  | nil => rfl
  | cons x xs ih => simp only [pack,List.length_cons,ih]

/-- Every actual repeated payload bit copy is charged from the source width. -/
theorem pack_clock (node index : ℕ) (words : List RationalWord) (W : ℕ)
    (hw : ∀x∈words,Width x W) : (pack node index words).clock ≤ words.length*(8*W+9)+1 := by
  induction words generalizing index with
  | nil => simp [pack]
  | cons x xs ih =>
    have hc:=copyWord_clock x W (hw x List.mem_cons_self)
    have ht:=ih (index+1) (fun y hy => hw y (List.mem_cons_of_mem _ hy))
    simp only [pack,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

/-- Exact native row-label counter stages are retained distinctly. -/
theorem pack_metadataWork (node index : ℕ) (words : List RationalWord) :
    (pack node index words).metadataWork=3*words.length+1 := by
  induction words generalizing index with
  | nil => rfl
  | cons x xs ih => simp only [pack,List.length_cons,ih]; omega

/-- The original physical node stores exactly its original retained multiplicity. -/
theorem node_length (a M u : ℕ) (t : Fin (size a)) (hM : u ≤ M) :
    (SemiprimeD1RecoveryNodeBits.acquire a M u t).words.length=nodeMultiplicity a (height M u) u t.val := by
  have h:=congrArg List.length (SemiprimeD1RecoveryNodeBitsCorrectness.acquire_correct a M u t hM).1
  simpa only [List.length_map,Array.length_toList,SemiprimeD1JetRecoveryWeights.acquire_weights_size] using h

/-- Literal actual physical per-node row-cache report envelope. -/
def nodeBudget (a M : ℕ) : ℕ :=
  SemiprimeD1RecoveryNodeBitsBounds.budget a M (SemiprimeD1RecoveryNodeBits.width a M)+
    SemiprimeD1RecoveryNodeBits.m M*(8*SemiprimeD1RecoveryNodeBits.width a M+9)+4

/-- Every actual original node producer and copied canonical payload is retained. -/
theorem gather_clock (a M u : ℕ) (ts : List (Fin (size a))) (hM : u ≤ M) :
    (gather a M u ts).clock ≤ ts.length*nodeBudget a M+1 := by
  induction ts with
  | nil => simp [gather]
  | cons t ts ih =>
    have cc:=SemiprimeD1RecoveryNodeBitsBounds.acquire_clock a M u t hM
    have cur:=SemiprimeD1RecoveryNodeBitsCorrectness.acquire_correct a M u t hM
    have cp:=pack_clock t.val 0 (SemiprimeD1RecoveryNodeBits.acquire a M u t).words
      (SemiprimeD1RecoveryNodeBits.width a M) cur.2.2.1
    have hl : (SemiprimeD1RecoveryNodeBits.acquire a M u t).words.length ≤ SemiprimeD1RecoveryNodeBits.m M :=
      (node_length a M u t hM).le.trans (SemiprimeD1WeightPrecision.nodeMultiplicity_le a M u t.val hM)
    have hp:=Nat.mul_le_mul_right (8*SemiprimeD1RecoveryNodeBits.width a M+9) hl
    simp only [gather]
    split_ifs <;> dsimp only
    · simp only [List.length_cons,Nat.add_mul,Nat.one_mul,nodeBudget]
      simp only [nodeBudget] at ih
      omega
    · simp only [List.length_cons,Nat.add_mul,Nat.one_mul,nodeBudget]
      simp only [nodeBudget] at ih
      omega

/-- Complete physical original canonical-row cache arithmetic budget. -/
def budget (a M : ℕ) : ℕ := size a*nodeBudget a M+4

/-- The ORIGINAL full physical row acquisition has a closed arithmetic/copy
report with no source coefficient, height, Fits or callback-cost advice. -/
theorem acquire_clock (a M u : ℕ) (hM : u ≤ M) : (acquire a M u).clock ≤ budget a M := by
  have h:=gather_clock a M u (SemiprimeD1RecoveryRowsRun.nodeIndices a).value hM
  have hn : (SemiprimeD1RecoveryRowsRun.nodeIndices a).value.length=size a := by
    have hh:=congrArg List.length (SemiprimeD1RecoveryRowsRun.nodeIndices_values a)
    simpa only [List.length_map,List.length_range] using hh
  simp only [acquire,budget]
  rw [hn] at h
  omega

/-- Actual full physical cache length is bounded from original multiplicities. -/
theorem acquire_length (a M u : ℕ) (hM : u ≤ M) :
    (acquire a M u).rows.length ≤ size a*(4*M) := by
  have he:=congrArg List.length (acquire_view a M u hM)
  simp only [view,List.length_map] at he
  have hl:=SemiprimeD1RecoveryRowsRun.acquire_length a M u
  have hm:=Nat.mul_le_mul_left (size a) (SemiprimeD1WeightPrecision.height_mul_le M u hM)
  omega

end RiemannGaussian.SemiprimeD1RecoveryRowsBits
