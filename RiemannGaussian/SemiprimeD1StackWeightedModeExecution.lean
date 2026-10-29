/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackWeightedModeLoop
/-! # Actual prepared positive-weight source, including initialization and output
Only the physical catalogue and unary precision WIDTH are supplied. The source
copies them, pops the budget predecessor, enumerates feasible branches, reverses
its actual chronological log, and halts with the exact ordered tuple vector.
-/
set_option autoImplicit false
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackWeightedModeExecution
open SemiprimeD1StackWeightedMode SemiprimeD1StackWeightedModePrimitives SemiprimeD1StackWeightedModeView
open SemiprimeD1StackWeightedModeActivation (join)
open SemiprimeD1StackWeightedModeSpec SemiprimeD1StackWeightedModeLoop
open SemiprimeD1StackProcedureTrace
open SemiprimeD1TensorTapeCodec (vectorBits)
local notation "ctl" => (Sum.inl : Control→Label)
/-- Literal output payloads, not a runtime feasible-tuple generator. -/
def payloads (ws:List Nat) (width:Nat) :List (List Bool):=values ws (width-1) []
/-- Exact initialized two-input store: no result, traversal or count is an input. -/
theorem input_store (cat width:List Bool) :input cat width=store (base cat width [] [] []):=by
  funext k;cases k <;> rfl
/-- A physical unary predecessor is one real pop, including WIDTH zero. -/
theorem unary_tail (n:Nat) :(unary n).tail=unary (n-1):=by
  cases n with
  | zero=>rfl
  | succ n=>simp only [unary_succ,List.tail_cons,Nat.add_sub_cancel]
/-- Exact paid initial copies, predecessor pop and path terminator push. -/
theorem setup_run (ws:List Nat) (width:Nat) :
    Runs program (5*(vector ws).length+5*width+10) (ctl .start)
      (input (vector ws) (unary width)) (ctl .root)
      (store (node (vector ws) (unary width) ws (width-1) (path []) [] [] [])):=by
  let a:=base (vector ws) (unary width) [] [] []
  let b:Words:={a with weights:=vector ws}
  let c:Words:={b with budget:=unary width}
  let d:Words:={c with budget:=unary (width-1)}
  have h0:=copy_call .catalogue .start .widthCopy rfl (store a) (vector ws) [] rfl rfl rfl
  rw [List.append_nil,store_write] at h0
  change Runs program (5*(vector ws).length+4) _ _ _ (store b) at h0
  have h1:=copy_call .width .widthCopy .budgetPred rfl (store b) (unary width) [] rfl rfl rfl
  rw [List.append_nil,store_write,unary_length] at h1
  change Runs program (5*width+4) _ _ _ (store c) at h1
  have h2:=pop_run .budgetPred (ctl .pathSeed) (ctl .pathSeed) (ctl .pathSeed) .budget
    (store c) (unary width) rfl rfl
  have hchoose:SemiprimeD1StackBytecode.choose (ctl .pathSeed) (ctl .pathSeed) (ctl .pathSeed)
      (unary width).head?=ctl .pathSeed:=by cases (unary width).head? with
    | none=>rfl
    | some b=>cases b <;> rfl
  rw [hchoose,unary_tail,store_write] at h2
  change Runs program 1 _ _ _ (store d) at h2
  have h3:=push_run .pathSeed (ctl .root) .path false (store d) rfl
  rw [store_write] at h3
  change Runs program 1 _ _ _ (store (node (vector ws) (unary width) ws (width-1) (path []) [] [] [])) at h3
  have h:=join h0 (join h1 (join h2 h3))
  rw [input_store]
  convert h using 1;omega
/-- Literal reverse log followed by its one physical false marker is the codec vector. -/
theorem history_vector (xs:List (List Bool)) :(history xs []).reverse++[false]=vectorBits xs:=by
  have hfold:xs.foldr (fun x tail=>row x++tail) []++[false]=vectorBits xs:=by
    induction xs with
    | nil=>rfl
    | cons x xs ih=>
      rw [List.foldr_cons,List.append_assoc]
      change (true::SemiprimeSourceHistogramKeyBits.frame x [])++_=_
      rw [List.cons_append,SemiprimeD1TensorTapeCodec.frame_append,List.nil_append,ih]
      rfl
  simpa only [history,List.append_nil,List.reverse_reverse] using hfold
/-- Exact stopped data retains both actual inputs and contains only their computed tuple vector. -/
def result (ws:List Nat) (width:Nat) :Stack→List Bool:=
  store (base (vector ws) (unary width) [] [] (vectorBits (payloads ws width)))
/-- Actual stopped source state; all work words and real return frames are empty. -/
def done (ws:List Nat) (width:Nat) :C.State Stack Label:=⟨none,none,none,result ws width,[]⟩
/-- Own complete primitive allowance includes the physical output reversal. -/
def timeBound (ws:List Nat) (width:Nat) :Nat:=
  nodeBudget ws (width-1) 1+5*(vector ws).length+5*width+
    2*(history (payloads ws width) []).length+17
attribute [local irreducible] nodeBudget
/-- The whole actual source executes from its two physical inputs to the literal ordered vector. -/
theorem source_trace (ws:List Nat) (hw:∀w∈ws,0 < w) (width:Nat) :
    ∃t,t+1 ≤ timeBound ws width ∧ Runs program t (ctl .start)
      (input (vector ws) (unary width)) (ctl .done) (result ws width):=by
  obtain ⟨t,ht,hr⟩:=visit_run (vector ws) (unary width) ws hw (width-1) [] [] [] []
  change t ≤ nodeBudget ws (width-1) 1 at ht
  change Runs program t (ctl .visit)
    (store (node (vector ws) (unary width) ws (width-1) (path []) [] [] []))
    (ctl .returning) (store (base (vector ws) (unary width) [] (history (payloads ws width) []) [])) at hr
  have h0:=setup_run ws width
  have h1:=recursive_call .root .finishSeed _ _ t rfl hr
  let v:=base (vector ws) (unary width) [] (history (payloads ws width) []) []
  let s:Words:={v with output:=[false]}
  have h2:=push_run .finishSeed (ctl .reverse) .output false (store v) rfl
  rw [store_write] at h2
  change Runs program 1 _ _ _ (store s) at h2
  have h3:=reverse_call (store s) (history (payloads ws width) []) [false] rfl rfl
  rw [store_write,store_write,history_vector] at h3
  change Runs program (2*(history (payloads ws width) []).length+3) _ _ _ (result ws width) at h3
  have h:=join h0 (join h1 (join h2 h3))
  refine ⟨(5*(vector ws).length+5*width+10)+((t+2)+(1+(2*(history (payloads ws width) []).length+3))),?_,h⟩
  unfold timeBound
  omega
/-- Exact source execution includes its final real halt, with no advised tuple or visit count. -/
theorem source_run (ws:List Nat) (hw:∀w∈ws,0 < w) (width:Nat) :
    ∃t ≤ timeBound ws width,C.run program t (initial (vector ws) (unary width))=some (done ws width):=by
  obtain ⟨t,ht,hr⟩:=source_trace ws hw width
  obtain ⟨finish,hf,ha⟩:=hr [] (initial (vector ws) (unary width)) ⟨rfl,rfl,rfl⟩
  have hh:=halt_run program (ctl .done) rfl (result ws width) [] finish ha
  refine ⟨t+1,ht,?_⟩
  rw [SemiprimeD1StackReturnLink.run_add,hf,Option.bind_some]
  exact hh
/-- Original native feasible tuple order, encoded by the actual physical output. -/
theorem output_exact (ws:List Nat) (width:Nat) :
    (done ws width).data .output=
      vectorBits ((SemiprimeD1WeightedTuples.tuples ws (width-1)).map vector):=by
  simp only [done,result,store,base,payloads,values,List.nil_append]
end RiemannGaussian.SemiprimeD1StackWeightedModeExecution
