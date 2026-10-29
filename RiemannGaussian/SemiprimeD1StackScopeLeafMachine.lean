/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackScopeLeafBounds
/-! # Actual finite scope-counted leaf execution and every-prefix cells
The scope bank itself, not a supplied M word or maximum used port, determines
all assignments. Scope-bank production remains the caller's explicit operation.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 131072
set_option maxRecDepth 32768
set_option maxHeartbeats 2500000
namespace RiemannGaussian.SemiprimeD1StackScopeLeafMachine
open scoped BigOperators
open SemiprimeD1StackScopeLeaf SemiprimeD1StackScopeLeafBounds
open SemiprimeD1TensorTapeCodec (vectorBits)
open SemiprimeD1StackUnaryDivmod (unary)

/-- Genuine compiled fixed-machine scope-counted leaf; no binary M/cardinality
header or subroutine-cost promise is accepted. Noncomputability is proof-only
finite trace-certificate selection, never program or physical input construction. -/
noncomputable def machineLeaf (ctx : SemiprimeD1JetAxes.Context) (hp : ctx.Positive) (pBits : List Bool)
    (hprecision : SemiprimeBitArithmetic.bitValue pBits=ctx.precision)
    (vertices : List SemiprimeD1LeafCounter.Vertex) (hg : SemiprimeD1LeafCounter.Good ctx vertices)
    (scopeWords : List (List Bool)) :
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration
        (initial (vectorBits (ctx.axes.map unary)) pBits (SemiprimeD1StackVertexProduct.records vertices) (vectorBits scopeWords)))
      (some (SemiprimeD1StackCalls.configuration
        (⟨none,none,none,SemiprimeD1StackScopeLeafExecution.finalData ctx pBits vertices scopeWords,[]⟩:
          SemiprimeD1StackCalls.State Stack Label)))
      (polynomial (resource ctx pBits vertices scopeWords)*2^scopeWords.length) := by
  let h:=source_run_polynomial ctx hp pBits hprecision vertices hg scopeWords
  let m:=Classical.choose h
  have hm:=Classical.choose_spec h
  apply SemiprimeD1StackCalls.evalsCorrect scopes (leafStack (L.aux .sum)) Label.start program
  exact ⟨⟨m,hm.2⟩,hm.1⟩

/-- Every actual original input stack is covered by literal physical inventory. -/
theorem initial_length (ctx : SemiprimeD1JetAxes.Context) (pBits : List Bool)
    (vertices : List SemiprimeD1LeafCounter.Vertex) (scopeWords : List (List Bool)) (k : Stack) :
    ((initial (vectorBits (ctx.axes.map unary)) pBits (SemiprimeD1StackVertexProduct.records vertices)
      (vectorBits scopeWords)).data k).length≤resource ctx pBits vertices scopeWords := by
  cases k with
  | inl k =>
    exact (SemiprimeD1StackLeafMachine.initial_length scopeWords.length ctx pBits [] vertices k).trans
      (leaf_resource_le ctx pBits vertices scopeWords)
  | inr k =>
    cases k <;> first
      | exact Nat.zero_le _
      | dsimp only [initial,data]
        unfold resource
        omega

/-- No successful actual prefix can run past the proved real halt. -/
theorem prefix_fuel_le (ctx : SemiprimeD1JetAxes.Context) (hp : ctx.Positive) (pBits : List Bool)
    (hprecision : SemiprimeBitArithmetic.bitValue pBits=ctx.precision)
    (vertices : List SemiprimeD1LeafCounter.Vertex) (hg : SemiprimeD1LeafCounter.Good ctx vertices)
    (scopeWords : List (List Bool)) (fuel : ℕ) (out : SemiprimeD1StackCalls.State Stack Label)
    (hr : SemiprimeD1StackCalls.run program fuel
      (initial (vectorBits (ctx.axes.map unary)) pBits (SemiprimeD1StackVertexProduct.records vertices)
        (vectorBits scopeWords))=some out) :
    fuel≤polynomial (resource ctx pBits vertices scopeWords)*2^scopeWords.length := by
  obtain ⟨m,hm,hstop⟩:=source_run_polynomial ctx hp pBits hprecision vertices hg scopeWords
  by_contra hn
  have he : fuel=m+(1+(fuel-(m+1))) := by omega
  rw [he,SemiprimeD1StackReturnLink.run_add,hstop,Option.bind_some,SemiprimeD1StackReturnLink.run_add] at hr
  have hh : SemiprimeD1StackCalls.run program 1
      (⟨none,none,none,SemiprimeD1StackScopeLeafExecution.finalData ctx pBits vertices scopeWords,[]⟩:
        SemiprimeD1StackCalls.State Stack Label)=none := rfl
  rw [hh,Option.bind_none] at hr
  cases hr

/-- All 145 physical Boolean data stacks and actual finite return symbols at
EVERY source prefix, including the complete preserved scope bank and scanner. -/
theorem prefix_cells (ctx : SemiprimeD1JetAxes.Context) (hp : ctx.Positive) (pBits : List Bool)
    (hprecision : SemiprimeBitArithmetic.bitValue pBits=ctx.precision)
    (vertices : List SemiprimeD1LeafCounter.Vertex) (hg : SemiprimeD1LeafCounter.Good ctx vertices)
    (scopeWords : List (List Bool)) (fuel : ℕ) (out : SemiprimeD1StackCalls.State Stack Label)
    (hr : SemiprimeD1StackCalls.run program fuel
      (initial (vectorBits (ctx.axes.map unary)) pBits (SemiprimeD1StackVertexProduct.records vertices)
        (vectorBits scopeWords))=some out) :
    (∑s:Stack,(out.data s).length)+out.frames.length≤
      146*(resource ctx pBits vertices scopeWords+
        polynomial (resource ctx pBits vertices scopeWords)*2^scopeWords.length+1) := by
  have hf:=prefix_fuel_le ctx hp pBits hprecision vertices hg scopeWords fuel out hr
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel (resource ctx pBits vertices scopeWords) _ out
    (initial_length ctx pBits vertices scopeWords) hr
  have hframes:=SemiprimeD1StackCalls.run_frame_bound program fuel _ out hr
  change out.frames.length≤0+fuel at hframes
  have hs : (∑s:Stack,(out.data s).length)≤145*(resource ctx pBits vertices scopeWords+fuel) := by
    calc
      _≤∑_s:Stack,(resource ctx pBits vertices scopeWords+fuel) := Finset.sum_le_sum (fun s _=>hd s)
      _=145*(resource ctx pBits vertices scopeWords+fuel) := by
        have hc : Fintype.card Stack=145 := by decide
        simp [hc]
  omega

/-- The same actual storage bound holds at EVERY compiled FinTM2 prefix. -/
theorem machine_prefix_cells (ctx : SemiprimeD1JetAxes.Context) (hp : ctx.Positive) (pBits : List Bool)
    (hprecision : SemiprimeBitArithmetic.bitValue pBits=ctx.precision)
    (vertices : List SemiprimeD1LeafCounter.Vertex) (hg : SemiprimeD1LeafCounter.Good ctx vertices)
    (scopeWords : List (List Bool)) (fuel : ℕ) (cfg : machine.Cfg)
    (hr : (fun q=>q.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration
        (initial (vectorBits (ctx.axes.map unary)) pBits (SemiprimeD1StackVertexProduct.records vertices)
          (vectorBits scopeWords))))=some cfg) :
    (∑s:Stack,(cfg.stk (some s)).length)+(cfg.stk none).length≤
      146*(resource ctx pBits vertices scopeWords+
        polynomial (resource ctx pBits vertices scopeWords)*2^scopeWords.length+1) := by
  let start:=initial (vectorBits (ctx.axes.map unary)) pBits (SemiprimeD1StackVertexProduct.records vertices) (vectorBits scopeWords)
  have he:=SemiprimeD1StackCalls.run_correct scopes (leafStack (L.aux .sum)) Label.start program fuel start
  change (SemiprimeD1StackCalls.run program fuel start).map SemiprimeD1StackCalls.configuration=
    (fun q=>q.bind machine.step)^[fuel] (some (SemiprimeD1StackCalls.configuration start)) at he
  cases hc:SemiprimeD1StackCalls.run program fuel start with
  | none => rw [hc,hr] at he; cases he
  | some out =>
    rw [hc,hr] at he
    have hcfg : SemiprimeD1StackCalls.configuration out=cfg := Option.some.inj he
    rw [←hcfg]
    exact prefix_cells ctx hp pBits hprecision vertices hg scopeWords fuel out hc

end RiemannGaussian.SemiprimeD1StackScopeLeafMachine
