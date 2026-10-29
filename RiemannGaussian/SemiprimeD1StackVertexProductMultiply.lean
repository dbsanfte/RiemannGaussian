/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackVertexProductRead
/-! # The actual dense multiplication call inside the parsed vertex product -/
set_option autoImplicit false
set_option synthInstance.maxSize 65536
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
namespace RiemannGaussian.SemiprimeD1StackVertexProductMultiply
open SemiprimeD1StackVertexProduct SemiprimeD1StackVertexProductState
open SemiprimeD1StackVertexProductProjection
open SemiprimeD1StackProcedureTrace (Runs)
open SemiprimeD1TensorTapeCodec (vectorBits)
open SemiprimeD1StackUnaryDivmod (unary)

/-- The literal multiplier is invoked on the two physically present vectors;
all routing, coefficient reads, scalar arithmetic and framing execute inside it. -/
theorem multiply_call (ctx : SemiprimeD1JetAxes.Context) (hp : ctx.Positive)
    (v : Values) (a b : List (List Bool))
    (ha : v .left=vectorBits a) (hb : v .product=vectorBits b)
    (haxes : v .axes=vectorBits (ctx.axes.map unary))
    (hw : (v .width).length=ctx.precision) (hr : v .rank=unary ctx.rank)
    (hout : v .result=[]) :
    ∃ m ≤ 2000000*(SemiprimeD1StackJetMulBounds.inputSize ctx (multiplierCache v)+1)^6+1,
      Runs program m .callMul (data v) .clearA
        (data (Function.update v .result (vectorBits (SemiprimeD1JetRingBits.mul ctx a b).words))) := by
  obtain ⟨m,hm,hs⟩:=SemiprimeD1StackJetMulBounds.source_run_polynomial ctx hp
    (multiplierCache v) a b ha hb haxes hw hr
  refine ⟨m+1,by omega,?_⟩
  apply SemiprimeD1StackProcedureInclusion.included_call program main Label.multiply
    (by intro a b h; exact Sum.inl.inj h) M.program .start (fun _=>rfl)
    .callMul .clearA rfl m
    (SemiprimeD1StackJetMul.initial (v .left) (v .product) (v .axes) (v .width) (v .rank))
    (⟨none,none,none,SemiprimeD1StackJetMulExecution.data (multiplierCache v) [] []
      (vectorBits (SemiprimeD1JetRingBits.mul ctx a b).words),[]⟩:
      SemiprimeD1StackCalls.State M.Stack M.Label)
  · rfl
  · rfl
  · rfl
  · rfl
  · exact hs
  · constructor
    · intro k
      rw [main_project]
      have hi:=congrFun (SemiprimeD1StackJetMulExecution.initial_data (multiplierCache v)) k
      simpa only [multiplierCache,hout] using hi.symm
    · intro k hk
      rfl
  · constructor
    · intro k
      rw [main_project]
      fin_cases k <;> simp [multiplierCache]
    · intro k hk
      have hn : k ≠ address .result := fun he=>hk M.output he.symm
      rw [data_update]
      exact Function.update_of_ne hn _ _

end RiemannGaussian.SemiprimeD1StackVertexProductMultiply
