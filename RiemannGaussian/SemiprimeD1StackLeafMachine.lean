/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackLeafUniform
import RiemannGaussian.SemiprimeReportPolynomialGrowth
/-! # Actual finite-machine eager-leaf time and all-prefix storage
The source budget is refined to the literal compiled FinTM2, not transferred
from a native report. Original network/header serialization remains a caller
operation; the entire leaf arithmetic/enumeration executes here.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 131072
set_option maxRecDepth 32768
set_option maxHeartbeats 2500000
namespace RiemannGaussian.SemiprimeD1StackLeafMachine
open scoped BigOperators
open SemiprimeD1StackLeaf SemiprimeD1StackLeafUniform
open SemiprimeD1TensorTapeCodec (vectorBits)
open SemiprimeD1StackUnaryDivmod (unary)

/-- The multiplier of the actual 2^M enumeration is a fixed monomial, with
constants chosen before every original input and literal network. -/
theorem polynomial_monomial : ∃ C k : ℕ, ∀S, polynomial S≤C*(S+1)^k := by
  change SemiprimeReportPolynomialGrowth.Bound polynomial
  unfold polynomial overhead SemiprimeD1StackLeafPolynomial.roundPolynomial
    SemiprimeD1StackVertexProductPolynomial.preparedPolynomial
    SemiprimeD1StackVertexProductPolynomial.roundPolynomial
    SemiprimeD1StackVertexProductPolynomial.vectorBound
  boundArithmetic

/-- Complete original-input execution with a uniform fixed-polynomial overhead
and the literal exhaustive assignment factor, no subroutine-time premise. -/
theorem source_run_polynomial (M : ℕ) (ctx : SemiprimeD1JetAxes.Context) (hp : ctx.Positive)
    (pBits mBits : List Bool) (hprecision : SemiprimeBitArithmetic.bitValue pBits=ctx.precision)
    (hM : SemiprimeBitArithmetic.bitValue mBits=M) (vertices : List SemiprimeD1LeafCounter.Vertex)
    (hg : SemiprimeD1LeafCounter.Good ctx vertices) :
    ∃ m ≤ polynomial (resource M ctx pBits mBits vertices)*2^M,
      SemiprimeD1StackCalls.run program m
        (initial (vectorBits (ctx.axes.map unary)) pBits mBits (SemiprimeD1StackVertexProduct.records vertices))=
      some (⟨none,none,none,SemiprimeD1StackLeafExecution.finalData M ctx pBits mBits vertices,[]⟩:
        SemiprimeD1StackCalls.State Stack Label) := by
  obtain ⟨m,hm,hs⟩:=SemiprimeD1StackLeafExecution.source_run M ctx hp pBits mBits hprecision hM vertices
  exact ⟨m,hm.trans (budget_le M ctx pBits mBits hprecision vertices hg),hs⟩

/-- Genuine actual compiled finite-machine execution. Noncomputability chooses
only an already proved finite trace certificate, never program or tensor data. -/
noncomputable def machineLeaf (M : ℕ) (ctx : SemiprimeD1JetAxes.Context) (hp : ctx.Positive)
    (pBits mBits : List Bool) (hprecision : SemiprimeBitArithmetic.bitValue pBits=ctx.precision)
    (hM : SemiprimeBitArithmetic.bitValue mBits=M) (vertices : List SemiprimeD1LeafCounter.Vertex)
    (hg : SemiprimeD1LeafCounter.Good ctx vertices) :
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration
        (initial (vectorBits (ctx.axes.map unary)) pBits mBits (SemiprimeD1StackVertexProduct.records vertices)))
      (some (SemiprimeD1StackCalls.configuration
        (⟨none,none,none,SemiprimeD1StackLeafExecution.finalData M ctx pBits mBits vertices,[]⟩:
          SemiprimeD1StackCalls.State Stack Label)))
      (polynomial (resource M ctx pBits mBits vertices)*2^M) := by
  let h:=source_run_polynomial M ctx hp pBits mBits hprecision hM vertices hg
  let m:=Classical.choose h
  have hm:=Classical.choose_spec h
  apply SemiprimeD1StackCalls.evalsCorrect SemiprimeD1StackLeaf.vertices (aux .sum) Label.start program
  exact ⟨⟨m,hm.2⟩,hm.1⟩

/-- Every initial physical stack length is bounded by original inventory. -/
theorem initial_length (M : ℕ) (ctx : SemiprimeD1JetAxes.Context) (pBits mBits : List Bool)
    (vs : List SemiprimeD1LeafCounter.Vertex) (k : Stack) :
    ((initial (vectorBits (ctx.axes.map unary)) pBits mBits (SemiprimeD1StackVertexProduct.records vs)).data k).length≤
      resource M ctx pBits mBits vs := by
  have ha : (vectorBits (ctx.axes.map unary)).length≤resource M ctx pBits mBits vs := by unfold resource;omega
  have hp : pBits.length≤resource M ctx pBits mBits vs := by unfold resource;omega
  have hm : mBits.length≤resource M ctx pBits mBits vs := by unfold resource;omega
  have hv : (SemiprimeD1StackVertexProduct.records vs).length≤resource M ctx pBits mBits vs := by unfold resource;omega
  simp only [initial,inputData,Function.update_apply]
  split_ifs <;> first | exact ha | exact hp | exact hm | exact hv | exact Nat.zero_le _

/-- Actual successful prefixes stop no later than the proved physical halt. -/
theorem prefix_fuel_le (M : ℕ) (ctx : SemiprimeD1JetAxes.Context) (hp : ctx.Positive)
    (pBits mBits : List Bool) (hprecision : SemiprimeBitArithmetic.bitValue pBits=ctx.precision)
    (hM : SemiprimeBitArithmetic.bitValue mBits=M) (vs : List SemiprimeD1LeafCounter.Vertex)
    (hg : SemiprimeD1LeafCounter.Good ctx vs) (fuel : ℕ) (out : SemiprimeD1StackCalls.State Stack Label)
    (hr : SemiprimeD1StackCalls.run program fuel
      (initial (vectorBits (ctx.axes.map unary)) pBits mBits (SemiprimeD1StackVertexProduct.records vs))=some out) :
    fuel≤polynomial (resource M ctx pBits mBits vs)*2^M := by
  obtain ⟨m,hm,hstop⟩:=source_run_polynomial M ctx hp pBits mBits hprecision hM vs hg
  by_contra hn
  have he : fuel=m+(1+(fuel-(m+1))) := by omega
  rw [he,SemiprimeD1StackReturnLink.run_add,hstop,Option.bind_some,
    SemiprimeD1StackReturnLink.run_add] at hr
  have hh : SemiprimeD1StackCalls.run program 1
      (⟨none,none,none,SemiprimeD1StackLeafExecution.finalData M ctx pBits mBits vs,[]⟩:
        SemiprimeD1StackCalls.State Stack Label)=none := rfl
  rw [hh,Option.bind_none] at hr
  cases hr

/-- ALL actual source prefixes count every Boolean data cell plus real finite
return symbols; 138 fixed data stacks give the fixed factor 139. -/
theorem prefix_cells (M : ℕ) (ctx : SemiprimeD1JetAxes.Context) (hp : ctx.Positive)
    (pBits mBits : List Bool) (hprecision : SemiprimeBitArithmetic.bitValue pBits=ctx.precision)
    (hM : SemiprimeBitArithmetic.bitValue mBits=M) (vs : List SemiprimeD1LeafCounter.Vertex)
    (hg : SemiprimeD1LeafCounter.Good ctx vs) (fuel : ℕ) (out : SemiprimeD1StackCalls.State Stack Label)
    (hr : SemiprimeD1StackCalls.run program fuel
      (initial (vectorBits (ctx.axes.map unary)) pBits mBits (SemiprimeD1StackVertexProduct.records vs))=some out) :
    (∑s:Stack,(out.data s).length)+out.frames.length≤
      139*(resource M ctx pBits mBits vs+polynomial (resource M ctx pBits mBits vs)*2^M+1) := by
  have hf:=prefix_fuel_le M ctx hp pBits mBits hprecision hM vs hg fuel out hr
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel (resource M ctx pBits mBits vs) _ out
    (initial_length M ctx pBits mBits vs) hr
  have hframes:=SemiprimeD1StackCalls.run_frame_bound program fuel _ out hr
  change out.frames.length≤0+fuel at hframes
  have hs : (∑s:Stack,(out.data s).length)≤138*(resource M ctx pBits mBits vs+fuel) := by
    calc
      _≤∑_s:Stack,(resource M ctx pBits mBits vs+fuel) := Finset.sum_le_sum (fun s _=>hd s)
      _=138*(resource M ctx pBits mBits vs+fuel) := by
        have hc : Fintype.card Stack=138 := by decide
        simp [hc]
  omega

/-- The exact same bound holds at EVERY actual compiled-machine prefix. -/
theorem machine_prefix_cells (M : ℕ) (ctx : SemiprimeD1JetAxes.Context) (hp : ctx.Positive)
    (pBits mBits : List Bool) (hprecision : SemiprimeBitArithmetic.bitValue pBits=ctx.precision)
    (hM : SemiprimeBitArithmetic.bitValue mBits=M) (vs : List SemiprimeD1LeafCounter.Vertex)
    (hg : SemiprimeD1LeafCounter.Good ctx vs) (fuel : ℕ) (cfg : machine.Cfg)
    (hr : (fun q=>q.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration
        (initial (vectorBits (ctx.axes.map unary)) pBits mBits (SemiprimeD1StackVertexProduct.records vs))))=some cfg) :
    (∑s:Stack,(cfg.stk (some s)).length)+(cfg.stk none).length≤
      139*(resource M ctx pBits mBits vs+polynomial (resource M ctx pBits mBits vs)*2^M+1) := by
  let start:=initial (vectorBits (ctx.axes.map unary)) pBits mBits (SemiprimeD1StackVertexProduct.records vs)
  have he:=SemiprimeD1StackCalls.run_correct vertices (aux .sum) Label.start program fuel start
  change (SemiprimeD1StackCalls.run program fuel start).map SemiprimeD1StackCalls.configuration=
    (fun q=>q.bind machine.step)^[fuel] (some (SemiprimeD1StackCalls.configuration start)) at he
  cases hc:SemiprimeD1StackCalls.run program fuel start with
  | none => rw [hc,hr] at he; cases he
  | some out =>
    rw [hc,hr] at he
    have hcfg : SemiprimeD1StackCalls.configuration out=cfg := Option.some.inj he
    rw [←hcfg]
    exact prefix_cells M ctx hp pBits mBits hprecision hM vs hg fuel out hc

end RiemannGaussian.SemiprimeD1StackLeafMachine
