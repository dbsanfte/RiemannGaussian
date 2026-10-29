/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryNodeInputs
/-! # SAME immutable affine program reuses an actually acquired Grid cache
Only actual q acquisition/slope-copy/convolution/cleanup/halt work is charged.
The real Grid104 source is NOT replayed at this optional prepared entry.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryNodeInputsAffineReady
open SemiprimeD1StackProcedureTrace
namespace A
export SemiprimeD1StackRecoveryAffine (Stack Label program)
end A
namespace E
export SemiprimeD1StackRecoveryAffineEncoding (original retained result done)
end E
namespace Source
export SemiprimeD1StackRecoveryAffineSource (counted ready_counted)
end Source
namespace Original
export SemiprimeD1StackRecoveryAffineOriginalInput (slopes slopes_run loop_run)
end Original
/-- Actual five-word Grid cache is already present, with all8 affine words EMPTY. -/
def initial (a M u : ℕ) (selected : Fin (2^(a+1))) (t width : List Bool) : SemiprimeD1StackCalls.State A.Stack A.Label :=
  ⟨some (.local .ready),none,none,SemiprimeD1StackRecoveryAffineView.bank (E.original a M u selected t width),[]⟩
/-- This actual same-program ready budget omits the entire Grid call, counting only the real remaining work. -/
def timeBound (a M u : ℕ) (selected : Fin (2^(a+1))) (t width : List Bool) : ℕ :=
  SemiprimeD1StackRecoveryAffineRetained.runBound (E.original a M u selected t width) a (SemiprimeD1TaperedLoss.height M u) u t+
    SemiprimeD1StackRecoveryAffineSlopes.runBound (Original.slopes a M u selected width)+
    SemiprimeD1StackRecoveryAffineLoop.runBound (Source.counted a M u selected t width) width (E.retained a M u selected)
      (Original.slopes a M u selected width).reverse [SemiprimeJetBits.oneWord]+1
/-- No q or coefficient is supplied: the actual ready program acquires every remaining value from the real Grid bank. -/
theorem source_trace (a M u : ℕ) (selected : Fin (2^(a+1))) (t width : List Bool)
    (ht : SemiprimeBitArithmetic.bitValue t=selected.val) :
    ∃s≤timeBound a M u selected t width-1,Runs A.program s (.local .ready)
      (SemiprimeD1StackRecoveryAffineView.bank (E.original a M u selected t width))
      (.local .done) (E.result a M u selected t width) := by
  obtain ⟨s0,hs0,h0⟩:=Source.ready_counted a M u selected t width ht
  have h1:=Original.slopes_run a M u selected t width
  obtain ⟨s2,hs2,h2⟩:=Original.loop_run a M u selected t width
  have h:=SemiprimeD1StackRecoveryAffinePrimitives.join (SemiprimeD1StackRecoveryAffinePrimitives.join h0 h1) h2
  refine ⟨s0+SemiprimeD1StackRecoveryAffineSlopes.runBound (Original.slopes a M u selected width)+s2,?_,h⟩
  simp only [timeBound,Nat.add_sub_cancel]
  omega
/-- Whole actual ready subcall halts on the SAME immutable program, retaining all104 Grid fields and actual q/array. -/
theorem source_run (a M u : ℕ) (selected : Fin (2^(a+1))) (t width : List Bool)
    (ht : SemiprimeBitArithmetic.bitValue t=selected.val) :
    ∃s≤timeBound a M u selected t width,
      SemiprimeD1StackCalls.run A.program s (initial a M u selected t width)=some (E.done a M u selected t width) := by
  obtain ⟨s,hs,h⟩:=source_trace a M u selected t width ht
  obtain ⟨finish,hfinish,hAt⟩:=h [] (initial a M u selected t width) ⟨rfl,rfl,rfl⟩
  refine ⟨s+1,?_,?_⟩
  · simp only [timeBound,Nat.add_sub_cancel] at hs ⊢
    omega
  · rw [SemiprimeD1StackReturnLink.run_add,hfinish,Option.bind_some]
    exact halt_run A.program (.local .done) rfl _ [] finish hAt
/-- Omitting the real Grid call only reduces the SAME source's proved original whole budget. -/
theorem timeBound_le (a M u : ℕ) (selected : Fin (2^(a+1))) (t width : List Bool) :
    timeBound a M u selected t width≤SemiprimeD1StackRecoveryAffineExecution.timeBound a M u selected t width := by
  unfold timeBound SemiprimeD1StackRecoveryAffineExecution.timeBound SemiprimeD1StackRecoveryAffineSource.entryBound
  omega
end RiemannGaussian.SemiprimeD1StackRecoveryNodeInputsAffineReady
