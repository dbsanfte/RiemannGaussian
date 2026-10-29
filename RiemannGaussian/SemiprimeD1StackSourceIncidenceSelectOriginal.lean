/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourceIncidenceSelectStorage
import RiemannGaussian.SemiprimeD1StackSourceIncidenceSelectOccurrences
import RiemannGaussian.SemiprimeD1StackSourceAlphabet64Original
/-! # Exact original incidence-only choice on actual acquired physical inputs
The whole literal selector returns the exact original D1IncidenceSearch.run ID
list, including every first-on-tie choice. Source occurrence and alphabet words
come from their frozen actual acquisition ABIs; no selected prefix, dictionary,
query value, score callback or evaluator is an input of this source.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceIncidenceSelectOriginal
open SemiprimeD1StackSourceIncidenceSelect SemiprimeD1StackSourceIncidenceSelectExecution
open SemiprimeD1StackSourceIncidenceSelectClock SemiprimeD1StackSourceIncidenceSelectCalls
open SemiprimeD1StackSourceIncidenceSelectMeaning
open SemiprimeBitArithmetic (bitValue)
open SemiprimeD1TensorTapeCodec (vectorBits)
namespace Alpha
export SemiprimeD1StackSourceAlphabet64 (aux)
export SemiprimeD1StackSourceAlphabet64Encoding (result)
end Alpha
/-- Generic final25-role projection is proved before any original graph/source instantiation. -/
theorem result_environment (i:Inputs) (k:SemiprimeD1StackSourceEnvironment.Stack) :
    result i (environmentStack k)=SemiprimeD1StackSourceEnvironmentExecution.result (selectedIDs i) k :=rfl
/-- All other38 words retain exactly the input bank, with every helper/output word empty. -/
theorem result_eq_withEnvironment (i:Inputs) :
    result i=withEnvironment (source i).data (SemiprimeD1StackSourceEnvironmentExecution.result (selectedIDs i)) :=by
  funext k
  rcases k with k|k
  · rcases k with k|k
    · rfl
    · cases k <;> rfl
  · cases k <;> rfl
/-- Exact selected vector is newest first and contains one actual framed ID per variable. -/
theorem output_vector (i:Inputs) :result i selected=vectorBits (selectedIDs i) :=rfl
/-- The actual closed-score controller has exactly the original literal ID result, including every tie. -/
theorem selectedIDs_original (n F a:Nat) (arity:Fin F→Nat)
    (owner:((e:Fin F)×Fin (arity e))→Fin n) (i:Inputs)
    (hn:i.n=n) (hF:i.F=F) (hrows:i.rows=originalKeys n F a arity owner)
    (hmenu:i.first.1::i.entries.map Prod.fst=[]::(SemiprimeSourceCompactWordBank.acquire 64 a).ids.tail)
    (hs:bitValue i.square=(64^a)^2) (hc:bitValue i.cube=(64^a)^3) (hf:bitValue i.fourth=(64^a)^4) :
    selectedIDs i=(SemiprimeD1IncidenceSearch.run n F 64 a arity owner).value :=by
  have hhead: i.first.1=[]:=(List.cons.inj hmenu).1
  have htail: i.entries.map Prod.fst=(SemiprimeSourceCompactWordBank.acquire 64 a).ids.tail:=(List.cons.inj hmenu).2
  unfold selectedIDs
  rw [hn,hF,hrows,hhead,htail]
  rw [SemiprimeD1StackSourceIncidenceSelectScore.selected_original n F 64 a arity owner
    (List.replicate (n+F) true) [] i.square i.cube i.fourth hs hc hf [] _ (by simp)]
  exact select_run_original n F 64 a arity owner
/-- Actual acquired original alphabet entries, before physical record encoding. -/
def originalCatalogue (a:Nat) :List (List Bool×List Bool) :=
  (SemiprimeSourceCompactWordBank.acquire 64 a).ids.zip
    ((SemiprimeSourceWordBankRows.rows 64 a).value.map SemiprimeSourceHistogramRows.layout)
/-- Physically paired colour rows preserve the exact ascending compact original candidate-ID order. -/
theorem originalCatalogue_ids (a:Nat) :
    (originalCatalogue a).map Prod.fst=(SemiprimeSourceCompactWordBank.acquire 64 a).ids :=by
  apply List.map_fst_zip
  simp only [List.length_map,SemiprimeSourceCompactWordBank.ids_length]
  exact Nat.le_refl _
/-- The actual alphabet has a physical first record even at dimension zero. -/
theorem originalCatalogue_nonempty (a:Nat) :originalCatalogue a≠[] :=by
  intro h
  have hi:=originalCatalogue_ids a
  rw [h,List.map_nil,SemiprimeSourceCompactWordBank.default_head 64 a] at hi
  cases hi
/-- Actual byte source, supplied only the acquired occurrence/catalogue/power and unary-count words. -/
def acquiredSource (n F a:Nat) (arity:Fin F→Nat)
    (owner:((e:Fin F)×Fin (arity e))→Fin n) :C.State Stack Label :=
  initial (SemiprimeD1StackOwnerLookup.records (originalKeys n F a arity owner) [])
    (Alpha.result a (Alpha.aux .output)) (Alpha.result a (Alpha.aux .square))
    (Alpha.result a (Alpha.aux .cube)) (Alpha.result a (Alpha.aux .fourth))
    (List.replicate n true) (List.replicate F true)
/-- Physical input mass on this exact original acquired-source ABI, including all unused colour bytes. -/
def acquiredSize (n F a:Nat) (arity:Fin F→Nat)
    (owner:((e:Fin F)×Fin (arity e))→Fin n) :Nat :=
  (SemiprimeD1StackOwnerLookup.records (originalKeys n F a arity owner) []).length+
    (Alpha.result a (Alpha.aux .output)).length+(Alpha.result a (Alpha.aux .square)).length+
    (Alpha.result a (Alpha.aux .cube)).length+(Alpha.result a (Alpha.aux .fourth)).length+n+F+1
/-- Complete63-word original stopped bank; the native run occurs only in this mathematical specification. -/
def acquiredData (n F a:Nat) (arity:Fin F→Nat)
    (owner:((e:Fin F)×Fin (arity e))→Fin n) :Stack→List Bool :=
  withEnvironment (acquiredSource n F a arity owner).data
    (SemiprimeD1StackSourceEnvironmentExecution.result (SemiprimeD1IncidenceSearch.run n F 64 a arity owner).value)
/-- Exact true halt and complete original output/cache bank. -/
def acquiredDone (n F a:Nat) (arity:Fin F→Nat)
    (owner:((e:Fin F)×Fin (arity e))→Fin n) :C.State Stack Label :=
  ⟨none,none,none,acquiredData n F a arity owner,[]⟩
/-- Whole actual original family: original catalogue order/powers, repeated occurrences and every first-on-tie ID agree literally. -/
theorem acquired_source_run (n F a:Nat) (arity:Fin F→Nat)
    (owner:((e:Fin F)×Fin (arity e))→Fin n) :
    ∃t ≤ 1000000000000000000000000000000*(acquiredSize n F a arity owner+1)^16,
      SemiprimeD1StackCalls.run program t (acquiredSource n F a arity owner)=some (acquiredDone n F a arity owner) :=by
  cases hcat:originalCatalogue a with
  | nil=>exact (originalCatalogue_nonempty a hcat).elim
  | cons first entries=>
    let i:Inputs:=⟨originalKeys n F a arity owner,first,entries,
      Alpha.result a (Alpha.aux .square),Alpha.result a (Alpha.aux .cube),Alpha.result a (Alpha.aux .fourth),n,F⟩
    have hmenu:first.1::entries.map Prod.fst=[]::(SemiprimeSourceCompactWordBank.acquire 64 a).ids.tail:=by
      have h:=originalCatalogue_ids a
      rw [hcat,List.map_cons,SemiprimeSourceCompactWordBank.default_head 64 a] at h
      exact h
    have hs:bitValue i.square=(64^a)^2:=by
      have h:=SemiprimeD1StackSourceAlphabet64Original.square_value a
      simpa only [pow_mul,Nat.mul_comm] using h
    have hc:bitValue i.cube=(64^a)^3:=by
      have h:=SemiprimeD1StackSourceAlphabet64Original.cube_value a
      simpa only [pow_mul,Nat.mul_comm] using h
    have hf:bitValue i.fourth=(64^a)^4:=by
      have h:=SemiprimeD1StackSourceAlphabet64Original.fourth_value a
      simpa only [pow_mul,Nat.mul_comm] using h
    have hsel:=selectedIDs_original n F a arity owner i rfl rfl rfl hmenu hs hc hf
    have hsource:source i=acquiredSource n F a arity owner:=by
      have he:catalogue i=Alpha.result a (Alpha.aux .output):=by
        rw [SemiprimeD1StackSourceAlphabet64Original.output_original]
        change SemiprimeD1StackOwnerLookup.records (first::entries) []=
          SemiprimeD1StackOwnerLookup.records (originalCatalogue a) []
        rw [hcat]
      change initial _ (catalogue i) _ _ _ _ _=_
      rw [he]
      rfl
    have hsize:inputSize i=acquiredSize n F a arity owner:=by
      have he:catalogue i=Alpha.result a (Alpha.aux .output):=by
        rw [SemiprimeD1StackSourceAlphabet64Original.output_original]
        change SemiprimeD1StackOwnerLookup.records (first::entries) []=
          SemiprimeD1StackOwnerLookup.records (originalCatalogue a) []
        rw [hcat]
      change (SemiprimeD1StackOwnerLookup.records (originalKeys n F a arity owner) []).length+
        (catalogue i).length+_+_+_+n+F+1=_
      rw [he]
      rfl
    have hdata:result i=acquiredData n F a arity owner:=by
      rw [result_eq_withEnvironment,hsource,hsel]
      rfl
    have hdone:done i=acquiredDone n F a arity owner:=by
      unfold done acquiredDone
      rw [hdata]
    obtain ⟨t,ht,hr⟩:=source_run_bounded i
    rw [hsource,hdone] at hr
    exact ⟨t,by simpa only [polynomial,hsize] using ht,hr⟩
/-- Every actual original environment field is ready for a preserving lookup or subsequent selected-key source without replay. -/
theorem acquired_environment (n F a:Nat) (arity:Fin F→Nat)
    (owner:((e:Fin F)×Fin (arity e))→Fin n) (k:SemiprimeD1StackSourceEnvironment.Stack) :
    (acquiredDone n F a arity owner).data (environmentStack k)=
      SemiprimeD1StackSourceEnvironmentExecution.result (SemiprimeD1IncidenceSearch.run n F 64 a arity owner).value k :=rfl
/-- The output bytes themselves equal the exact original newest-first selected-ID vector. -/
theorem acquired_output (n F a:Nat) (arity:Fin F→Nat)
    (owner:((e:Fin F)×Fin (arity e))→Fin n) :
    (acquiredDone n F a arity owner).data selected=
      vectorBits (SemiprimeD1IncidenceSearch.run n F 64 a arity owner).value :=rfl
end RiemannGaussian.SemiprimeD1StackSourceIncidenceSelectOriginal
