/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPublicScaleTail
/-! # Closed original-input public scale execution
The only inputs are binary N, raw assignment, physical descriptor markers and
selector. Source, modulus, vector, guards and numerical result are all executed.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 4096
namespace RiemannGaussian.SemiprimeD1StackPublicScaleExecution
open SemiprimeD1StackPublicScale SemiprimeD1StackPublicScaleState SemiprimeD1StackPublicScaleAcquire
open SemiprimeD1StackPublicScaleDot SemiprimeD1StackPublicScaleTail SemiprimeD1StackProcedureTrace SemiprimeBitArithmetic
/-- Complete clean halt, retaining the ACTUAL branch-specific source/cache data. -/
def done (bits raw stride frequency : List Bool) (inverse : Bool) (j k : ℕ) : C.State Stack Label :=
  ⟨none,none,none,finalData bits raw stride frequency inverse j k,[]⟩
/-- Sum of own actually executed producer/copy/padding/dot/read/equality allowances.
No old/new clock equality or supplied component cost is used. -/
def timeBound (bits raw stride frequency : List Bool) (inverse : Bool) (j k : ℕ) : ℕ :=
  SemiprimeD1StackRootSourceBounds.timeBound bits+1+prepBudget (roots bits) raw inverse+
    (SemiprimeD1StackInputDotExecution.timeBound (paddedRaw bits raw) (args bits stride frequency inverse)
      (cached bits) (SemiprimeD1StackPublicScaleInputs.expression bits inverse) j k 2+1)+
    tailBudget bits raw stride frequency inverse j k+1
/-- ENTIRE fixed program: original root acquisition ONCE, physical zero padding,
actual guarded dot and actual comparison. No modulus, word/vector, source AST,
canonicality, guard, output truth, evaluator or component clock is a premise.
Descriptor markers are physical formats and remain an explicit caller boundary. -/
theorem source_run (bits raw stride frequency : List Bool) (inverse : Bool) (j k : ℕ)
    (hj : stride=SemiprimeD1StackUnaryDivmod.unary j)
    (hk : frequency=SemiprimeD1StackUnaryDivmod.unary k)
    (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits) :
    ∃t≤timeBound bits raw stride frequency inverse j k,
      C.run program t (initial bits raw stride frequency inverse)=some (done bits raw stride frequency inverse j k) := by
  have hb : bits≠[] := by intro he;rw [he] at hN;exact Nat.lt_irrefl 0 hN
  obtain ⟨t,ht,h0⟩:=acquire_run bits raw stride frequency inverse hb
  obtain ⟨u,hu,h1⟩:=dot_call bits raw stride frequency inverse j k hj hk hc hN
  obtain ⟨v,hv,h2⟩:=tail_run bits raw stride frequency inverse j k
  have hr:=runs_trans program _ _ _ _ _ _ _ _ (runs_trans program _ _ _ _ _ _ _ _ h0 h1) h2
  obtain ⟨finish,hfinish,hout⟩:=hr [] (initial bits raw stride frequency inverse) ⟨rfl,rfl,rfl⟩
  have hh:=halt_run program .done rfl (finalData bits raw stride frequency inverse j k) [] finish hout
  refine ⟨t+u+v+1,?_,?_⟩
  · unfold timeBound;omega
  · rw [SemiprimeD1StackReturnLink.run_add,hfinish,Option.bind_some,hh]
    rfl
end RiemannGaussian.SemiprimeD1StackPublicScaleExecution
