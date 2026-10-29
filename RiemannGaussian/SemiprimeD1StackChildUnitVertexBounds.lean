/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildUnitVertexOriginal
/-! # Fixed quadratic whole inactive-record acquisition and actual bit-machine clock
Both original control VALUES are charged. Table framing uses native Good byte
caps, independently of the preceding context/unit producer elapsed runtimes.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildUnitVertexBounds
open SemiprimeD1StackChildUnitVertex SemiprimeD1StackChildUnitVertexCalls
open SemiprimeD1StackChildUnitVertexFrames SemiprimeD1StackChildUnitVertexOriginal
/-- Actual header bytes, positive unary axis VALUES, axis product and binary precision VALUE. -/
def resource (axes : List ℕ) (precision : List Bool) : ℕ:=SemiprimeD1StackJetContextBounds.resource axes precision
/-- The actual acquired rank VALUE is fully paid. -/
theorem rank_le (axes : List ℕ) (precision : List Bool) : (ctx axes precision).rank≤resource axes precision := by
  unfold resource SemiprimeD1StackJetContextBounds.resource
  change axes.prod≤_
  omega
/-- The actual acquired precision VALUE is fully paid. -/
theorem precision_le (axes : List ℕ) (precision : List Bool) : (ctx axes precision).precision≤resource axes precision := by
  unfold resource SemiprimeD1StackJetContextBounds.resource
  change SemiprimeBitArithmetic.bitValue precision≤_
  omega
/-- Semantic table bytes, rather than elapsed producer runtime, bound the real frame input. -/
theorem table_bytes (axes : List ℕ) (precision : List Bool) (hp : ∀q∈axes,0<q) :
    (tableWord axes precision).length≤10*(resource axes precision+1)^2 := by
  rw [table_original axes precision hp]
  have ht:=SemiprimeD1TensorTables.storage_bound (ctx axes precision)
    (SemiprimeD1ChildTensorTables.unit (ctx axes precision)).table (SemiprimeD1ChildTensorTables.unit_good _)
  have hb:=SemiprimeD1TensorTapeCodec.tape_le_storage (SemiprimeD1StackChildUnitVertexSpec.vertex (ctx axes precision)).table
  change SemiprimeD1TensorTables.storage (SemiprimeD1StackChildUnitVertexSpec.vertex (ctx axes precision)).table+1≤
    ((ctx axes precision).rank*(3*(ctx axes precision).precision+4)+3)*2^0 at ht
  rw [pow_zero,Nat.mul_one] at ht
  have hr:=rank_le axes precision
  have hp':=precision_le axes precision
  have hm:=Nat.mul_le_mul hr (show 3*(ctx axes precision).precision+4≤3*resource axes precision+4 by omega)
  nlinarith only [ht,hb,hm]
/-- Both real unit-cache operands have independently acquired bounded VALUE lengths. -/
theorem unit_clock (axes : List ℕ) (precision : List Bool) :
    SemiprimeD1StackJetUnitExecution.totalTime (width axes precision) (rank axes precision)≤
      2000*(resource axes precision+1)^2 := by
  have ht:=SemiprimeD1StackJetUnitExecution.totalTime_le (width axes precision) (rank axes precision)
  rw [SemiprimeD1StackJetUnitExecution.timeBound,width_length,rank_length] at ht
  have hr:=rank_le axes precision
  have hp:=precision_le axes precision
  have hm:=Nat.mul_le_mul (show (ctx axes precision).rank+1≤resource axes precision+1 by omega)
    (show (ctx axes precision).precision+8≤resource axes precision+8 by omega)
  nlinarith only [ht,hm]
/-- Coefficient and degree precede every actual header/context. -/
def polynomial (axes : List ℕ) (precision : List Bool) : ℕ:=10^8*(resource axes precision+1)^2
/-- Whole literal32-source clock pays BOTH producers, actual table frame and every literal record bit. -/
theorem timeBound_le (axes : List ℕ) (precision : List Bool) (hp : ∀q∈axes,0<q) :
    timeBound axes precision≤polynomial axes precision := by
  have ht:=table_bytes axes precision hp
  have hu:=unit_clock axes precision
  have h1 : 1≤(resource axes precision+1)^2:=Nat.one_le_pow _ _ (by omega)
  unfold timeBound polynomial
  change 1000*(resource axes precision+1)^2+
    SemiprimeD1StackJetUnitExecution.totalTime (width axes precision) (rank axes precision)+
    6*(tableWord axes precision).length+14≤10^8*(resource axes precision+1)^2
  omega
/-- SAME actual two-header physical source, exact native unit record and closed own polynomial. -/
theorem source_run_bounded (axes : List ℕ) (hp : ∀q∈axes,0<q) (precision : List Bool) :
    ∃t≤polynomial axes precision,
      SemiprimeD1StackCalls.run program t (originalInitial axes precision)=some (done axes precision) := by
  obtain ⟨t,ht,hr⟩:=source_run axes hp precision
  exact ⟨t,ht.trans (timeBound_le axes precision hp),hr⟩
/-- Actual compiled finite machine starts before cache/unit/table/record acquisition. -/
noncomputable def machineSource (axes : List ℕ) (hp : ∀q∈axes,0<q) (precision : List Bool) :
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration (originalInitial axes precision))
      (some (SemiprimeD1StackCalls.configuration (done axes precision))) (polynomial axes precision) := by
  apply SemiprimeD1StackCalls.evalsCorrect (context J.axesCache) (aux .record) (.local .start) program
  let h:=source_run_bounded axes hp precision
  exact ⟨⟨Classical.choose h,(Classical.choose_spec h).2⟩,(Classical.choose_spec h).1⟩
end RiemannGaussian.SemiprimeD1StackChildUnitVertexBounds
