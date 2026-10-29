/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPublicProduct

/-! # Complete original-input public product trace
Both whole literal calls and the enclosing halt are charged. The SAME acquired
modulus feeds physical grouping, computed guards, multiplication and division.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 1600000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackPublicProductExecution
open SemiprimeD1StackPublicProduct SemiprimeD1StackProcedureTrace
/-- Actual completed public cache, specified only after its paid source trace. -/
def context (bits : List Bool) : P.Stack→List Bool := SemiprimeD1BinaryPublicAcquisitionComponents.result bits
/-- Physical modulus word actually constructed by public acquisition. -/
def cached (bits : List Bool) : List Bool := context bits modulusKey
/-- Reached physical state after the complete public acquisition ONCE. -/
def ready (bits raw : List Bool) : Stack→List Bool := Sum.elim (context bits) (V.input raw [])
/-- Final actual cells, preserving every acquired public field and shadow. -/
def result (bits raw : List Bool) : Stack→List Bool :=
  Sum.elim (context bits) (fun k=>if k=V.modulus then [] else
    (SemiprimeD1StackProductCheckExecution.done raw (cached bits)).data k)
/-- Exact completed original-input product checker. -/
def done (bits raw : List Bool) : C.State Stack Label := ⟨none,none,none,result bits raw,[]⟩
/-- Actual original acquisition plus actual product checker and caller returns. -/
def timeBound (bits raw : List Bool) : ℕ :=
  SemiprimeD1BinaryPublicAcquisitionExecution.timeBound bits+
    SemiprimeD1StackProductCheckBounds.runBound raw (cached bits)+3

/-- Public preprocessing is actually executed INSIDE this whole program. -/
theorem acquire_call (bits raw : List Bool) (hb : bits≠[]) :
    ∃t≤SemiprimeD1BinaryPublicAcquisitionExecution.timeBound bits,
      Runs program (t+1) .start (input bits raw) .check (ready bits raw) := by
  obtain ⟨t,ht,hr⟩:=SemiprimeD1BinaryPublicAcquisitionExecution.source_run bits hb
  refine ⟨t,ht,?_⟩
  apply SemiprimeD1StackProcedureCallsTrace.included_call program Sum.inl Label.acquire Sum.inl_injective
    P.program (SemiprimeD1BinaryPublicAcquisition.mainLabel .start) (fun _=>rfl) .start .check rfl t
    (P.initial bits) (⟨none,none,none,context bits,[]⟩:C.State P.Stack P.Label)
    (input bits raw) (ready bits raw)
  · rfl
  · rfl
  · rfl
  · rfl
  · exact hr
  · constructor
    · intro k;rfl
    · intro k _;rfl
  · constructor
    · intro k;rfl
    · intro k hk
      rcases k with k|k
      · exact False.elim (hk k rfl)
      · rfl

/-- The whole raw checker runs using the actual acquired modulus DIRECTLY,
without a modulus copy, supplied width, vector, operand, guard or elapsed count. -/
theorem check_call (bits raw : List Bool) :
    ∃t≤SemiprimeD1StackProductCheckBounds.runBound raw (cached bits),
      Runs program (t+1) .check (ready bits raw) .done (result bits raw) := by
  obtain ⟨t,ht,hr⟩:=SemiprimeD1StackProductCheckBounds.source_run_bounded raw (cached bits)
  refine ⟨t,ht,?_⟩
  apply SemiprimeD1StackProcedureCallsTrace.included_call program checkStack Label.product checkStack_injective
    V.program .start (fun _=>rfl) .check .done rfl t
    (V.initial raw (cached bits)) (SemiprimeD1StackProductCheckExecution.done raw (cached bits))
    (ready bits raw) (result bits raw)
  · rfl
  · rfl
  · rfl
  · rfl
  · exact hr
  · constructor
    · intro k
      by_cases hk:k=V.modulus
      · subst k;rfl
      · simp only [checkStack,hk,ite_false,ready,Sum.elim_inr,SemiprimeD1StackProductCheck.initial,
          SemiprimeD1StackProductCheck.input]
    · intro k _;rfl
  · constructor
    · intro k
      by_cases hk:k=V.modulus
      · subst k;rfl
      · simp only [checkStack,hk,ite_false,result,Sum.elim_inr]
    · intro k hk
      rcases k with k|k
      · rfl
      · have he:k=V.modulus := by
          by_contra hn
          exact hk k (by simp only [checkStack,hn,ite_false])
        subst k;rfl

/-- COMPLETE actual original-input source trace. The only nonempty-source
premise is needed by the public metadata parser; no arithmetic verdict is input. -/
theorem source_run (bits raw : List Bool) (hb : bits≠[]) :
    ∃t≤timeBound bits raw,C.run program t (initial bits raw)=some (done bits raw) := by
  obtain ⟨a,ha,h0⟩:=acquire_call bits raw hb
  obtain ⟨b,hbTime,h1⟩:=check_call bits raw
  have h:=runs_trans program _ _ _ _ _ _ _ _ h0 h1
  obtain ⟨finish,hr,ho⟩:=h [] (initial bits raw) ⟨rfl,rfl,rfl⟩
  have he:=halt_run program .done rfl (result bits raw) [] finish ho
  refine ⟨(a+1)+(b+1)+1,by unfold timeBound;omega,?_⟩
  rw [SemiprimeD1StackReturnLink.run_add,hr,Option.bind_some,he]
  rfl

/-- Exact singleton verdict produced by the actual complete public checker. -/
theorem output_answer (bits raw : List Bool) :
    (done bits raw).data output=[SemiprimeD1StackProductCheckExecution.answer raw (cached bits)] := rfl
/-- Every public binary-input cache survives this actual computation. -/
theorem retained_public (bits raw : List Bool) (k : P.Stack) : (done bits raw).data (.inl k)=context bits k := rfl
/-- Actual raw assignment is preserved for the enclosing tensor-table caller. -/
theorem retained_raw (bits raw : List Bool) : (done bits raw).data assignment=raw := rfl
end RiemannGaussian.SemiprimeD1StackPublicProductExecution
