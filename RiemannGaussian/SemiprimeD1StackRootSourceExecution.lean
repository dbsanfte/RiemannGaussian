/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootSourceStages
/-! # CLOSED original-input acquisition of four actual expression streams -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option synthInstance.maxSize 4096
namespace RiemannGaussian.SemiprimeD1StackRootSourceExecution
open SemiprimeD1StackRootSources SemiprimeD1StackRootSourceStages SemiprimeD1StackProcedureTrace
/-- Actual inverse-root marker bytes after TWO literal modulus-word pops. -/
def rootMarkers (cache : P.Stack→List Bool) : List Bool := (cache modulusKey).tail.tail
/-- Actual normalization markers after one modulus pop and physical paired cancellation. -/
def normalMarkers (cache : P.Stack→List Bool) : List Bool := (cache modulusKey).tail.drop (cache exponentKey).length
/-- Byte specification of the ACTUAL root power constructor, not an input. -/
def rootCode (cache : P.Stack→List Bool) : List Bool :=
  SemiprimeD1StackExprPowerSpec.result (rootMarkers cache).length (literalCode 0) []
/-- Byte specification before the ACTUAL five normalization-prefix pushes. -/
def normalPowerCode (cache : P.Stack→List Bool) : List Bool :=
  SemiprimeD1StackExprPowerSpec.result (normalMarkers cache).length (literalCode 1) []
/-- Final whole physical data, with only original public cache and four source codes. -/
def result (cache : P.Stack→List Bool) : Stack→List Bool :=
  store cache [] [] [] [] (rootCode cache) (literalCode 4++normalPowerCode cache) (literalCode 2) (literalCode 3)
/-- Full exact body transition count; this is proof data, not executing control. -/
def bodyTime (cache : P.Stack→List Bool) : ℕ :=
  (5*(cache modulusKey).length+4)+1+1+((literalCode 0).length+1)+
  (SemiprimeD1StackExprPowerExecution.totalTime (literalCode 0) (rootMarkers cache)+1)+
  ((rootMarkers cache).length+1)+((literalCode 0).length+1)+
  (5*(cache modulusKey).length+4)+1+(5*(cache exponentKey).length+4)+(2*(cache exponentKey).length+1)+
  ((literalCode 1).length+1)+(SemiprimeD1StackExprPowerExecution.totalTime (literalCode 1) (normalMarkers cache)+1)+
  ((normalMarkers cache).length+1)+((literalCode 1).length+1)+
  ((literalCode 4).length+1)+((literalCode 2).length+1)+((literalCode 3).length+1)
/-- Actual fixed body on the acquired cache, with no exponent/source/result advice. -/
theorem body_run (cache : P.Stack→List Bool) :
    Runs program (bodyTime cache) .copyRoot (store cache [] [] [] [] [] [] [] []) .done (result cache) := by
  let d0:=store cache [] [] [] [] [] [] [] []
  let d1:=store cache [] (cache modulusKey) [] [] [] [] [] []
  let d2:=store cache [] ((cache modulusKey).tail) [] [] [] [] [] []
  let d3:=store cache [] (rootMarkers cache) [] [] [] [] [] []
  let d4:=store cache (literalCode 0) (rootMarkers cache) [] [] [] [] [] []
  let d5:=store cache (literalCode 0) (rootMarkers cache) [] [] (rootCode cache) [] [] []
  let d6:=store cache (literalCode 0) [] [] [] (rootCode cache) [] [] []
  let d7:=store cache [] [] [] [] (rootCode cache) [] [] []
  let d8:=store cache [] (cache modulusKey) [] [] (rootCode cache) [] [] []
  let d9:=store cache [] ((cache modulusKey).tail) [] [] (rootCode cache) [] [] []
  let d10:=store cache [] ((cache modulusKey).tail) (cache exponentKey) [] (rootCode cache) [] [] []
  let d11:=store cache [] (normalMarkers cache) [] [] (rootCode cache) [] [] []
  let d12:=store cache (literalCode 1) (normalMarkers cache) [] [] (rootCode cache) [] [] []
  let d13:=store cache (literalCode 1) (normalMarkers cache) [] [] (rootCode cache) (normalPowerCode cache) [] []
  let d14:=store cache (literalCode 1) [] [] [] (rootCode cache) (normalPowerCode cache) [] []
  let d15:=store cache [] [] [] [] (rootCode cache) (normalPowerCode cache) [] []
  let d16:=store cache [] [] [] [] (rootCode cache) (literalCode 4++normalPowerCode cache) [] []
  let d17:=store cache [] [] [] [] (rootCode cache) (literalCode 4++normalPowerCode cache) (literalCode 2) []
  let d18:=store cache [] [] [] [] (rootCode cache) (literalCode 4++normalPowerCode cache) (literalCode 2) (literalCode 3)
  have h0 : Runs program (5*(cache modulusKey).length+4) .copyRoot d0 .dropRoot1 d1 := by
    exact copy_call 0 .copyRoot .dropRoot1 rfl cache [] [] [] [] []
  have h1 : Runs program (1) .dropRoot1 d1 .dropRoot2 d2 := by
    exact drop_marker .dropRoot1 .dropRoot2 rfl cache (cache modulusKey) [] []
  have h2 : Runs program (1) .dropRoot2 d2 (.seed 0 0) d3 := by
    exact drop_marker .dropRoot2 (.seed 0 0) rfl cache ((cache modulusKey).tail) [] []
  have h3 : Runs program ((literalCode 0).length+1) (.seed 0 0) d3 .powerRoot d4 := by
    have h:=seed_run 0 d3 ([])
    have hi : Function.update d3 (literalStack 0) ([])=d3 := by
      funext k;rcases k with k|k
      · rfl
      · cases k <;> rfl
    have ho : Function.update d3 (literalStack 0) (literalCode 0++([]))=d4 := by
      funext k;rcases k with k|k
      · rfl
      · cases k <;> rfl
    rw [hi,ho] at h
    exact h
  have h4 : Runs program (SemiprimeD1StackExprPowerExecution.totalTime (literalCode 0) (rootMarkers cache)+1) .powerRoot d4 .clearRootMarkers d5 := by
    exact power_call false (literalCode 0) (rootMarkers cache) [] [] cache
  have h5 : Runs program ((rootMarkers cache).length+1) .clearRootMarkers d5 .clearRootBase d6 := by
    have h:=SemiprimeD1StackPhysicalLoops.drain program .clearRootMarkers .clearRootBase (.inr .markers) rfl d6 (rootMarkers cache)
    have hi : Function.update d6 (.inr .markers) (rootMarkers cache)=d5 := by
      funext k;rcases k with k|k
      · rfl
      · cases k <;> rfl
    have ho : Function.update d6 (.inr .markers) []=d6 := Function.update_eq_self _ _
    rw [hi,ho] at h
    exact h
  have h6 : Runs program ((literalCode 0).length+1) .clearRootBase d6 .copyNormal d7 := by
    have h:=SemiprimeD1StackPhysicalLoops.drain program .clearRootBase .copyNormal (.inr .base) rfl d7 (literalCode 0)
    have hi : Function.update d7 (.inr .base) (literalCode 0)=d6 := by
      funext k;rcases k with k|k
      · rfl
      · cases k <;> rfl
    have ho : Function.update d7 (.inr .base) []=d7 := Function.update_eq_self _ _
    rw [hi,ho] at h
    exact h
  have h7 : Runs program (5*(cache modulusKey).length+4) .copyNormal d7 .dropNormal d8 := by
    exact copy_call 1 .copyNormal .dropNormal rfl cache [] (rootCode cache) [] [] []
  have h8 : Runs program (1) .dropNormal d8 .copyExponent d9 := by
    exact drop_marker .dropNormal .copyExponent rfl cache (cache modulusKey) (rootCode cache) []
  have h9 : Runs program (5*(cache exponentKey).length+4) .copyExponent d9 .cancel d10 := by
    exact copy_exponent cache (cache modulusKey).tail (rootCode cache)
  have h10 : Runs program (2*(cache exponentKey).length+1) .cancel d10 (.seed 1 0) d11 := by
    exact cancel_run (cache exponentKey) (cache modulusKey).tail cache (rootCode cache)
  have h11 : Runs program ((literalCode 1).length+1) (.seed 1 0) d11 .powerNormal d12 := by
    have h:=seed_run 1 d11 ([])
    have hi : Function.update d11 (literalStack 1) ([])=d11 := by
      funext k;rcases k with k|k
      · rfl
      · cases k <;> rfl
    have ho : Function.update d11 (literalStack 1) (literalCode 1++([]))=d12 := by
      funext k;rcases k with k|k
      · rfl
      · cases k <;> rfl
    rw [hi,ho] at h
    exact h
  have h12 : Runs program (SemiprimeD1StackExprPowerExecution.totalTime (literalCode 1) (normalMarkers cache)+1) .powerNormal d12 .clearNormalMarkers d13 := by
    exact power_call true (literalCode 1) (normalMarkers cache) (rootCode cache) [] cache
  have h13 : Runs program ((normalMarkers cache).length+1) .clearNormalMarkers d13 .clearNormalBase d14 := by
    have h:=SemiprimeD1StackPhysicalLoops.drain program .clearNormalMarkers .clearNormalBase (.inr .markers) rfl d14 (normalMarkers cache)
    have hi : Function.update d14 (.inr .markers) (normalMarkers cache)=d13 := by
      funext k;rcases k with k|k
      · rfl
      · cases k <;> rfl
    have ho : Function.update d14 (.inr .markers) []=d14 := Function.update_eq_self _ _
    rw [hi,ho] at h
    exact h
  have h14 : Runs program ((literalCode 1).length+1) .clearNormalBase d14 (.seed 4 0) d15 := by
    have h:=SemiprimeD1StackPhysicalLoops.drain program .clearNormalBase (.seed 4 0) (.inr .base) rfl d15 (literalCode 1)
    have hi : Function.update d15 (.inr .base) (literalCode 1)=d14 := by
      funext k;rcases k with k|k
      · rfl
      · cases k <;> rfl
    have ho : Function.update d15 (.inr .base) []=d15 := Function.update_eq_self _ _
    rw [hi,ho] at h
    exact h
  have h15 : Runs program ((literalCode 4).length+1) (.seed 4 0) d15 (.seed 2 0) d16 := by
    have h:=seed_run 4 d15 (normalPowerCode cache)
    have hi : Function.update d15 (literalStack 4) (normalPowerCode cache)=d15 := by
      funext k;rcases k with k|k
      · rfl
      · cases k <;> rfl
    have ho : Function.update d15 (literalStack 4) (literalCode 4++(normalPowerCode cache))=d16 := by
      funext k;rcases k with k|k
      · rfl
      · cases k <;> rfl
    rw [hi,ho] at h
    exact h
  have h16 : Runs program ((literalCode 2).length+1) (.seed 2 0) d16 (.seed 3 0) d17 := by
    have h:=seed_run 2 d16 ([])
    have hi : Function.update d16 (literalStack 2) ([])=d16 := by
      funext k;rcases k with k|k
      · rfl
      · cases k <;> rfl
    have ho : Function.update d16 (literalStack 2) (literalCode 2++([]))=d17 := by
      funext k;rcases k with k|k
      · rfl
      · cases k <;> rfl
    rw [hi,ho] at h
    exact h
  have h17 : Runs program ((literalCode 3).length+1) (.seed 3 0) d17 .done d18 := by
    have h:=seed_run 3 d17 ([])
    have hi : Function.update d17 (literalStack 3) ([])=d17 := by
      funext k;rcases k with k|k
      · rfl
      · cases k <;> rfl
    have ho : Function.update d17 (literalStack 3) (literalCode 3++([]))=d18 := by
      funext k;rcases k with k|k
      · rfl
      · cases k <;> rfl
    rw [hi,ho] at h
    exact h
  have h:=h0
  have h:=runs_trans program _ _ _ _ _ _ _ _ h h1
  have h:=runs_trans program _ _ _ _ _ _ _ _ h h2
  have h:=runs_trans program _ _ _ _ _ _ _ _ h h3
  have h:=runs_trans program _ _ _ _ _ _ _ _ h h4
  have h:=runs_trans program _ _ _ _ _ _ _ _ h h5
  have h:=runs_trans program _ _ _ _ _ _ _ _ h h6
  have h:=runs_trans program _ _ _ _ _ _ _ _ h h7
  have h:=runs_trans program _ _ _ _ _ _ _ _ h h8
  have h:=runs_trans program _ _ _ _ _ _ _ _ h h9
  have h:=runs_trans program _ _ _ _ _ _ _ _ h h10
  have h:=runs_trans program _ _ _ _ _ _ _ _ h h11
  have h:=runs_trans program _ _ _ _ _ _ _ _ h h12
  have h:=runs_trans program _ _ _ _ _ _ _ _ h h13
  have h:=runs_trans program _ _ _ _ _ _ _ _ h h14
  have h:=runs_trans program _ _ _ _ _ _ _ _ h h15
  have h:=runs_trans program _ _ _ _ _ _ _ _ h h16
  have h:=runs_trans program _ _ _ _ _ _ _ _ h h17
  exact h

/-- Actual public-acquisition call; the following source constructor receives
only the metadata bytes that this SAME original-input program really acquired. -/
theorem acquire_call (bits : List Bool) (hb : bits≠[]) :
    ∃t ≤ SemiprimeD1BinaryPublicAcquisitionExecution.timeBound bits+1,
      Runs program t .start (input bits) .copyRoot
        (store (SemiprimeD1BinaryPublicAcquisitionComponents.result bits) [] [] [] [] [] [] [] []) := by
  obtain ⟨t,ht,hr⟩:=SemiprimeD1BinaryPublicAcquisitionExecution.source_run bits hb
  refine ⟨t+1,Nat.add_le_add_right ht 1,?_⟩
  apply SemiprimeD1StackProcedureCallsTrace.included_call program Sum.inl Label.preprocess Sum.inl_injective
    P.program (SemiprimeD1BinaryPublicAcquisition.mainLabel .start) (fun _=>rfl) .start .copyRoot rfl t
    (P.initial bits) (⟨none,none,none,SemiprimeD1BinaryPublicAcquisitionComponents.result bits,[]⟩:C.State P.Stack P.Label)
    _ _ rfl rfl rfl rfl hr
  · constructor
    · intro k;rfl
    · intro k _;rfl
  · constructor
    · intro k;rfl
    · intro k hk;rcases k with k|k
      · exact (hk k rfl).elim
      · rfl
/-- Actual original-only clean halt; all four code streams and original caches remain. -/
def done (bits : List Bool) : C.State Stack Label :=
  ⟨none,none,none,result (SemiprimeD1BinaryPublicAcquisitionComponents.result bits),[]⟩
/-- CLOSED original BINARY N-only whole execution. No count/exponent/base/source
cache is initially supplied; original public acquisition is executed exactly once. -/
theorem source_run (bits : List Bool) (hb : bits≠[]) :
    ∃t ≤ SemiprimeD1BinaryPublicAcquisitionExecution.timeBound bits+
      bodyTime (SemiprimeD1BinaryPublicAcquisitionComponents.result bits)+2,
      C.run program t (initial bits)=some (done bits) := by
  obtain ⟨t,ht,h0⟩:=acquire_call bits hb
  have h1:=body_run (SemiprimeD1BinaryPublicAcquisitionComponents.result bits)
  obtain ⟨finish,hfinish,hout⟩:=(runs_trans program _ _ _ _ _ _ _ _ h0 h1) [] (initial bits) ⟨rfl,rfl,rfl⟩
  have hh:=halt_run program .done rfl (result (SemiprimeD1BinaryPublicAcquisitionComponents.result bits)) [] finish hout
  refine ⟨t+bodyTime (SemiprimeD1BinaryPublicAcquisitionComponents.result bits)+1,by omega,?_⟩
  rw [SemiprimeD1StackReturnLink.run_add,hfinish,Option.bind_some,hh]
  rfl
end RiemannGaussian.SemiprimeD1StackRootSourceExecution
