/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackBooleanFactorCatalogueSource
import RiemannGaussian.SemiprimeD1StackPhysicalLoops
/-! # Actual descriptor, full cache erasure and retained-source filter calls -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
set_option maxRecDepth 32000
set_option synthInstance.maxSize 131072
namespace RiemannGaussian.SemiprimeD1StackBooleanFactorCataloguePrimitives
open SemiprimeD1StackBooleanFactorCatalogue SemiprimeD1StackBooleanFactorCatalogueView
open SemiprimeD1StackBooleanFactorCatalogueSource
open SemiprimeD1StackProcedureFragments (Runs one_base)
namespace DA
export SemiprimeD1StackBooleanDescriptorRecordAll (done afterHistory rowBound)
end DA
namespace E
export SemiprimeD1EdgeCatalogueEncoding (vertex)
end E
/-- A real included descriptor call parses all five fields and executes its
actual finite branch. Both shared operands are already acquired source bytes. -/
theorem descriptor_call (N : Nat) (hN:0<N) (v : SemiprimePublicAcquiredExecution.PublicVertex N)
    (fibre : F.Stack→List Bool) (catalogue : V.Stack→List Bool) (tail hist out : List Bool)
    (scopeWords : List (List Bool)) (M : Nat)
    (hbank:fibre F.output=SemiprimeD1TensorTapeCodec.vectorBits scopeWords)
    (hreader:catalogue catalogueOutput=SemiprimeD1VertexCatalogueEncoding.vertex v tail)
    (hl:∀s∈scopeWords,s.length ≤ M) (hv:∀s∈scopeWords,SemiprimeBitArithmetic.bitValue s ≤ M) :
    ∃t ≤ DA.rowBound (E.vertex v) scopeWords M,
      Runs program (t+1) (.local .row) (data fibre catalogue (fun _=>[]) hist out)
        (.local (.clearField 0))
        (data fibre (Function.update catalogue catalogueOutput tail) (E.vertex v) (DA.afterHistory v scopeWords hist) out) := by
  obtain ⟨t,ht,hr⟩:=SemiprimeD1StackBooleanDescriptorRecordAll.source_run N hN v tail scopeWords hist out M hl hv
  refine ⟨t,ht,?_⟩
  apply SemiprimeD1StackProcedureCallsTrace.included_call program descriptorStack Label.descriptor descriptor_injective
    D.program (.local (.field 0)) (fun _=>rfl) (.local .row) (.local (.clearField 0)) rfl t
    (SemiprimeD1StackBooleanDescriptorRecord.initial (SemiprimeD1VertexCatalogueEncoding.vertex v tail)
      (SemiprimeD1TensorTapeCodec.vectorBits scopeWords) hist out) (DA.done v tail scopeWords hist out)
    _ _ rfl rfl rfl rfl hr
  · constructor
    · intro k
      have h:=data_descriptor fibre catalogue (fun _=>[]) hist out k
      rw [hbank,hreader] at h
      exact h
    · intro k _;rfl
  · constructor
    · intro k
      have h:=data_descriptor fibre (Function.update catalogue catalogueOutput tail) (E.vertex v)
        (DA.afterHistory v scopeWords hist) out k
      rw [hbank,Function.update_self] at h
      change _=DD.clean (SemiprimeD1StackBooleanDescriptorRecordAll.recordResult v scopeWords hist out) (E.vertex v) tail k
      rw [SemiprimeD1StackBooleanDescriptorRecordAll.recordResult_initial]
      exact h
    · intro k hk
      rcases k with k|k|k|k
      · rfl
      · by_cases he:k=catalogueOutput
        · subst k;exact (hk (D.aux .reader) rfl).elim
        · change (Function.update catalogue catalogueOutput tail) k=catalogue k
          exact Function.update_of_ne he _ _
      · by_cases hr:k=D.aux .reader
        · subst k;rfl
        · by_cases hb:k=.inl SemiprimeD1StackBooleanRecord.original
          · subst k;rfl
          · have he:descriptorStack k=.inr (.inr (.inl k)):=by simp [descriptorStack,hr,hb]
            exact (hk k he).elim
      · rfl
/-- Every byte in one cached field is physically popped, including its actual EOF. -/
theorem clear_field (part : Fin 5) (fibre : F.Stack→List Bool) (catalogue : V.Stack→List Bool)
    (words : Fin 5→List Bool) (hist out : List Bool) :
    Runs program ((words part).length+1) (.local (.clearField part)) (data fibre catalogue words hist out)
      (nextClear part) (data fibre catalogue (Function.update words part []) hist out) := by
  have h:=SemiprimeD1StackPhysicalLoops.drain program (.local (.clearField part)) (nextClear part)
    (descriptorStack (D.cache part)) rfl (data fibre catalogue words hist out) (words part)
  have hi:Function.update (data fibre catalogue words hist out) (descriptorStack (D.cache part)) (words part)=
      data fibre catalogue words hist out:=Function.update_eq_self _ _
  rw [hi,update_cache] at h
  exact h
/-- Proof-side cached prefix already physically erased by the fixed five-field loop. -/
def cleared (n : Nat) (words : Fin 5→List Bool) : Fin 5→List Bool :=
  fun k=>if k.val<n then [] else words k
/-- One actual field erasure advances its finite physical cleanup invariant. -/
theorem cleared_step (part : Fin 5) (words : Fin 5→List Bool) :
    Function.update (cleared part.val words) part []=cleared (part.val+1) words := by
  funext k;fin_cases part <;> fin_cases k <;> rfl
/-- The fixed five-field loop starts with every actual parsed coordinate. -/
theorem cleared_zero (words : Fin 5→List Bool) : cleared 0 words=words := by
  funext k;simp [cleared]
/-- All five fields have really been erased. -/
theorem cleared_end (words : Fin 5→List Bool) : cleared 5 words=fun _=>[] := by
  funext k;fin_cases k <;> rfl
/-- One concrete bounded-control cleanup site on the actual partially cleared data. -/
theorem clear_one (part : Fin 5) (fibre : F.Stack→List Bool) (catalogue : V.Stack→List Bool)
    (words : Fin 5→List Bool) (hist out : List Bool) :
    Runs program ((words part).length+1) (.local (.clearField part))
      (data fibre catalogue (cleared part.val words) hist out) (nextClear part)
      (data fibre catalogue (cleared (part.val+1) words) hist out) := by
  have h:=clear_field part fibre catalogue (cleared part.val words) hist out
  have he:cleared part.val words part=words part:=by simp [cleared]
  rw [he,cleared_step] at h
  exact h
/-- All actual tag/coordinate payloads and all five EOF reads are charged. -/
theorem clear_fields (fibre : F.Stack→List Bool) (catalogue : V.Stack→List Bool)
    (words : Fin 5→List Bool) (hist out : List Bool) :
    Runs program (SemiprimeD1StackBooleanDescriptorRecordEncoding.mass words+5) (.local (.clearField 0))
      (data fibre catalogue words hist out) (.local .clearScope) (data fibre catalogue (fun _=>[]) hist out) := by
  have h0:=clear_one 0 fibre catalogue words hist out
  have h1:=clear_one 1 fibre catalogue words hist out
  have h2:=clear_one 2 fibre catalogue words hist out
  have h3:=clear_one 3 fibre catalogue words hist out
  have h4:=clear_one 4 fibre catalogue words hist out
  have h:=h0.trans (h1.trans (h2.trans (h3.trans h4)))
  have ht:((words 0).length+1)+(((words 1).length+1)+(((words 2).length+1)+
      (((words 3).length+1)+((words 4).length+1))))=
      SemiprimeD1StackBooleanDescriptorRecordEncoding.mass words+5 := by
    change _=(words 0).length+((words 1).length+((words 2).length+((words 3).length+((words 4).length+0))))+5
    omega
  rw [ht] at h
  change Runs program (SemiprimeD1StackBooleanDescriptorRecordEncoding.mass words+5) (.local (.clearField 0))
    (data fibre catalogue (cleared 0 words) hist out) (.local .clearScope)
    (data fibre catalogue (cleared 5 words) hist out) at h
  rw [cleared_zero,cleared_end] at h
  exact h
/-- The preserved binary scope bank is actually drained before the next filter call. -/
theorem clear_scope (fibre : F.Stack→List Bool) (catalogue : V.Stack→List Bool) (hist out : List Bool) :
    Runs program ((fibre F.output).length+1) (.local .clearScope)
      (data fibre catalogue (fun _=>[]) hist out) (.local .advance)
      (data (Function.update fibre F.output []) catalogue (fun _=>[]) hist out) := by
  have h:=SemiprimeD1StackPhysicalLoops.drain program (.local .clearScope) (.local .advance) scope rfl
    (data fibre catalogue (fun _=>[]) hist out) (fibre F.output)
  have hi:Function.update (data fibre catalogue (fun _=>[]) hist out) scope (fibre F.output)=
      data fibre catalogue (fun _=>[]) hist out:=Function.update_eq_self _ _
  rw [hi] at h
  change Runs program _ _ _ _ (Function.update (data fibre catalogue (fun _=>[]) hist out) (sourceStack F.output) []) at h
  rw [update_source] at h
  exact h
/-- Exactly one physical unary marker advances the factor counter per descriptor. -/
theorem advance_run (fibre : F.Stack→List Bool) (catalogue : V.Stack→List Bool) (hist out : List Bool) :
    Runs program 1 (.local .advance) (data fibre catalogue (fun _=>[]) hist out) (.local .next)
      (data (Function.update fibre F.query (true::fibre F.query)) catalogue (fun _=>[]) hist out) := by
  apply one_base program (.local .advance) (.local .next) (.push counter true (.local .next)) _ _ rfl
  · rfl
  · exact update_source _ _ _ _ _ _ _
/-- Real filtering clears every private filter role except its physically retained output. -/
theorem result_clear (bits key : List Bool) :
    Function.update (FS.result bits key) F.output []=SemiprimeD1StackFactorScopeFibre.afterSource bits key := by
  funext k
  rcases k with k|k|k
  · rfl
  · cases k with
    | inl k=>cases k <;> rfl
    | inr k=>cases k <;> rfl
  · cases k;rfl
/-- A physical query-key update changes no already acquired source byte. -/
theorem afterSource_key (bits key next : List Bool) :
    Function.update (SemiprimeD1StackFactorScopeFibre.afterSource bits key) F.query next=
      SemiprimeD1StackFactorScopeFibre.afterSource bits next := by
  funext k
  rcases k with k|k|k
  · rfl
  · cases k with
    | inl k=>cases k <;> rfl
    | inr k=>cases k <;> rfl
  · cases k;rfl
/-- The repeated query calls the real retained-source copy/filter program;
the122-role N-only pair acquisition is not executed again. -/
theorem query_call (bits key : List Bool) (catalogue : V.Stack→List Bool) (hist out : List Bool) :
    Runs program (SemiprimeD1StackFactorScopeFibreExecution.preparedTime bits key+2) (.local .query)
      (data (SemiprimeD1StackFactorScopeFibre.afterSource bits key) catalogue (fun _=>[]) hist out)
      (.local .loop) (data (FS.result bits key) catalogue (fun _=>[]) hist out) := by
  apply SemiprimeD1StackProcedureCallsTrace.included_call program sourceStack Label.source Sum.inl_injective F.program .copy
    (fun _=>rfl) (.local .query) (.local .loop) rfl
    (SemiprimeD1StackFactorScopeFibreExecution.preparedTime bits key+1)
    (⟨some .copy,none,none,SemiprimeD1StackFactorScopeFibre.afterSource bits key,[]⟩:C.State F.Stack F.Label)
    (SemiprimeD1StackFactorScopeFibre.done bits key) _ _ rfl rfl rfl rfl
    (SemiprimeD1StackFactorScopeFibreExecution.prepared_run bits key)
  · constructor
    · intro k;rfl
    · intro k _;rfl
  · constructor
    · intro k;rfl
    · intro k hk
      cases k with
      | inl k=>exact (hk k rfl).elim
      | inr k=>rfl
end RiemannGaussian.SemiprimeD1StackBooleanFactorCataloguePrimitives
