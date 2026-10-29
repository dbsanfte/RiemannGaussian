/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackLeafMachine
/-! # Actual frozen leaf entry after physically acquiring the scope count
This corollary executes the literal makeZero entry, not binary width conversion.
The count is physically present in the counter register; the final scope caller
acquires it by parsing every actual scope-bank record.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 131072
set_option maxRecDepth 131072
set_option maxHeartbeats 3000000
namespace RiemannGaussian.SemiprimeD1StackScopeLeafReady
open SemiprimeD1StackLeaf SemiprimeD1StackLeafState
open SemiprimeD1StackLeafEnumeration
open SemiprimeD1StackProcedureTrace (Runs runs_trans)
open SemiprimeD1TensorTapeCodec (vectorBits)

/-- All remaining actual leaf stages after acquiring a unary scope count. -/
def budget (M : ℕ) (ctx : SemiprimeD1JetAxes.Context)
    (vertices : List SemiprimeD1LeafCounter.Vertex) (p : PS.Values) : ℕ :=
  (2*M+1)+1+(100*(M+1)*2^M+11)+SemiprimeD1StackLeafLoop.loopBudget ctx vertices p
    (SemiprimeD1StackAssignmentOrder.assignments (2^M) (List.replicate M false)) []+1

/-- The actual acquired markers drive zero construction, complete enumeration,
literal tensor products and sums. No binary M word is read or supplied. -/
theorem ready_run (M : ℕ) (ctx : SemiprimeD1JetAxes.Context) (hp : ctx.Positive)
    (vertices : List SemiprimeD1LeafCounter.Vertex) (p : PS.Values) (v : Values)
    (hvertices : p .vertices=SemiprimeD1StackVertexProduct.records vertices)
    (hreader : p .reader=[]) (hleft : p .left=[]) (hprod : p .product=[])
    (hports : p .ports=[]) (htable : p .table=[]) (hvalid : p .valid=[]) (hout : p .result=[])
    (hassignment : p .assignment=[]) (hc : v .counter=[]) (hz : v .zero=[])
    (hcat : v .catalogue=[]) (hsum : v .sum=[]) (hsout : v .sumResult=[]) (hflag : v .valid=[])
    (haxes : p .axes=vectorBits (ctx.axes.map SemiprimeD1StackUnaryDivmod.unary))
    (hw : (p .width).length=ctx.precision) (hr : p .rank=SemiprimeD1StackUnaryDivmod.unary ctx.rank) :
    ∃ m ≤ budget M ctx vertices p,
      SemiprimeD1StackCalls.run program m
        (⟨some .makeZero,none,none,data p (Function.update v .counter (List.replicate M true)),[]⟩:
          SemiprimeD1StackCalls.State Stack Label)=
      some (⟨none,none,none,data p (Function.update v .sum
        (vectorBits (SemiprimeD1TensorTapeLeaf.run M ctx vertices).words)),[]⟩:
          SemiprimeD1StackCalls.State Stack Label) := by
  let v1:=Function.update v .zero (List.replicate M false)
  let v2:=Function.update v1 .sum [false]
  let catalogue:=SemiprimeD1StackAssignmentOrder.assignments (2^M) (List.replicate M false)
  let v3:=Function.update (Function.update v2 .zero []) .catalogue (vectorBits catalogue)
  have h1 : Runs program (2*M+1) .makeZero
      (data p (Function.update v .counter (List.replicate M true))) .initializeSum (data p v1) := by
    simpa [v1,hz] using zero_run p v M hc
  have h2 : Runs program 1 .initializeSum (data p v1) .enumerate (data p v2) := by
    simpa [v2,v1,hsum] using initialize_sum p v1
  obtain ⟨m3,hm3,h3⟩:=enumeration_call p v2 M (by simp [v2,v1]) (by simpa [v2,v1] using hcat)
  obtain ⟨m4,hm4,h4⟩:=SemiprimeD1StackLeafLoop.loop_run ctx hp vertices catalogue p v3 []
    (by simp [v3]) hvertices hreader hleft hprod hports htable hvalid hout hassignment
    (by simpa [v3,v2,v1] using hflag) (by simp [v3,v2,vectorBits])
    (by simpa [v3,v2,v1] using hsout) haxes hw hr
  have hh:=runs_trans program _ _ _ _ _ _ _ _ h1 h2
  have hh:=runs_trans program _ _ _ _ _ _ _ _ hh h3
  have hh:=runs_trans program _ _ _ _ _ _ _ _ hh h4
  obtain ⟨finish,hfinish,hfinishAt⟩:=hh []
    (⟨some .makeZero,none,none,data p (Function.update v .counter (List.replicate M true)),[]⟩:
      SemiprimeD1StackCalls.State Stack Label) ⟨rfl,rfl,rfl⟩
  have hd : data p (Function.update (Function.update v3 .catalogue []) .sum
      (vectorBits (SemiprimeD1StackLeafLoop.summed ctx vertices catalogue [])))=
      data p (Function.update v .sum (vectorBits (SemiprimeD1TensorTapeLeaf.run M ctx vertices).words)) := by
    apply congrArg (data p)
    funext s
    cases s <;> simp_all [v3,v2,v1,catalogue,SemiprimeD1StackLeafValue.summed_original M ctx hp]
  rw [hd] at hfinishAt
  have hhalt:=SemiprimeD1StackProcedureTrace.halt_run program .done rfl _ [] finish hfinishAt
  refine ⟨(2*M+1)+1+m3+m4+1,?_,?_⟩
  · unfold budget
    change _≤(2*M+1)+1+(100*(M+1)*2^M+11)+SemiprimeD1StackLeafLoop.loopBudget ctx vertices p catalogue []+1
    omega
  · rw [SemiprimeD1StackReturnLink.run_add,hfinish,Option.bind_some,hhalt]

/-- A numerical majorant only: skipped binary-width acquisition has nonnegative
cost. No equality or transfer of actual old/new execution clocks is asserted. -/
theorem budget_le_enumerated (M : ℕ) (ctx : SemiprimeD1JetAxes.Context)
    (vertices : List SemiprimeD1LeafCounter.Vertex) (p : PS.Values) (v : Values) :
    budget M ctx vertices p≤SemiprimeD1StackLeafSetup.enumeratedBudget M ctx vertices p v+1 := by
  unfold budget SemiprimeD1StackLeafSetup.enumeratedBudget
  omega

end RiemannGaussian.SemiprimeD1StackScopeLeafReady
