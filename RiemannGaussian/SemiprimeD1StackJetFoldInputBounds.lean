/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackJetFoldSpec
/-! # Actual input-field maxima and linear physical fold-node inventories
Maxima and node counts are proof estimates derived from the actual input words.
They are never runtime control operands or externally supplied fit answers.
-/
set_option autoImplicit false
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackJetFoldInputBounds
open SemiprimeD1StackJetFoldWords SemiprimeD1StackJetFoldSpec
open SemiprimeD1JetAxes (Context)
/-- Largest actual child-vector byte length in one physical mode record. -/
def groupMax:Group→Nat | []=>0 | x::xs=>max (jetTape x).length (groupMax xs)
/-- Largest actual child-vector byte length in the physically supplied mode vector. -/
def childMax:Modes→Nat | []=>0 | x::xs=>max (groupMax x) (childMax xs)
/-- Actual product-entry and sum-entry recursion nodes, including every empty-vector base case. -/
def workNodes:Modes→Nat | []=>1 | x::xs=>x.length+2+workNodes xs
/-- The actual metadata/value inventory includes binary precision length and both physically acquired counters. -/
def metaSize (ctx:Context) (h:Header):Nat:=ctx.rank+ctx.precision+ctx.axes.length+h.width.length+
  h.axes.length+2*h.rank.length+h.precision.length+1
/-- One derived field/value capacity, independent of the number of actual modes. -/
def capacity (ctx:Context) (h:Header) (modes:Modes):Nat:=metaSize ctx h+denseBytes ctx+childMax modes+1
/-- Every supplied binary child-vector word pays its exact untrimmed encoded byte length. -/
theorem child_le_groupMax (g:Group) (x:Jet) (hx:x∈g):(jetTape x).length ≤groupMax g:=by
  induction g with
  | nil=>simp at hx
  | cons y ys ih=>
    rcases List.mem_cons.mp hx with rfl|ht
    · exact le_max_left _ _
    · exact (ih ht).trans (le_max_right _ _)
/-- Each physical group field is included in the actual original-input maximum. -/
theorem group_le_childMax (modes:Modes) (g:Group) (hg:g∈modes):groupMax g ≤childMax modes:=by
  induction modes with
  | nil=>simp at hg
  | cons x xs ih=>
    rcases List.mem_cons.mp hg with rfl|ht
    · exact le_max_left _ _
    · exact (ih ht).trans (le_max_right _ _)
/-- Actual dense child outputs internally satisfy the common field bound. -/
theorem groupMax_dense (ctx:Context) (g:Group) (hd:∀x∈g,Dense ctx x):groupMax g ≤denseBytes ctx:=by
  induction g with
  | nil=>exact Nat.zero_le _
  | cons x xs ih=>
    exact max_le (dense_tape_length ctx x (hd x (by simp))) (ih (fun y hy=>hd y (by simp [hy])))
/-- When actual child sources produced dense outputs, the original-input maximum is bounded independently of mode count. -/
theorem childMax_dense (ctx:Context) (modes:Modes) (hd:∀g∈modes,∀x∈g,Dense ctx x):childMax modes ≤denseBytes ctx:=by
  induction modes with
  | nil=>exact Nat.zero_le _
  | cons x xs ih=>
    exact max_le (groupMax_dense ctx x (hd x (by simp))) (ih (fun y hy=>hd y (by simp [hy])))
/-- Literal group framing pays every supplied child-result byte and each real tag/terminator. -/
theorem groupTape_length (g:Group) (S:Nat) (hm:groupMax g ≤S):
    (groupTape g).length ≤2*g.length*(S+1)+1:=by
  induction g with
  | nil=>simp [groupTape,SemiprimeD1TensorTapeCodec.vectorBits]
  | cons x xs ih=>
    have hx:(jetTape x).length ≤S:=(le_max_left _ _).trans hm
    have ht:=ih ((le_max_right _ _).trans hm)
    change (true::SemiprimeSourceHistogramKeyBits.frame (jetTape x) (groupTape xs)).length ≤_
    simp only [List.length_cons,SemiprimeSourceHistogramKeyBits.frame_length]
    nlinarith only [hx,ht]
/-- Every full input vector still has an actual terminating bit and a real sum base node. -/
theorem nodes_positive (modes:Modes):1 ≤workNodes modes:=by
  induction modes with
  | nil=>rfl
  | cons x xs ih=>change 1 ≤x.length+2+workNodes xs;omega
/-- The complete original input copy is linear in actual fold nodes and actual largest field bytes. -/
theorem modeTape_length (modes:Modes) (S:Nat) (hm:childMax modes ≤S):
    (modeTape modes).length ≤4*(S+1)*workNodes modes:=by
  induction modes with
  | nil=>simp only [modeTape,List.map_nil,SemiprimeD1TensorTapeCodec.vectorBits,List.length_cons,List.length_nil,workNodes,Nat.mul_one];omega
  | cons x xs ih=>
    have hx:=groupTape_length x S ((le_max_left _ _).trans hm)
    have ht:=ih ((le_max_right _ _).trans hm)
    change (true::SemiprimeSourceHistogramKeyBits.frame (groupTape x) (modeTape xs)).length ≤4*(S+1)*(x.length+2+workNodes xs)
    simp only [List.length_cons,SemiprimeSourceHistogramKeyBits.frame_length]
    nlinarith only [hx,ht]
/-- Literal64-group rows have exactly66 actual fold-recursion nodes per mode, plus the final sum base. -/
theorem nodes_sixtyfour (modes:Modes) (h64:∀g∈modes,g.length=64):workNodes modes=66*modes.length+1:=by
  induction modes with
  | nil=>rfl
  | cons x xs ih=>
    have hx:=h64 x (by simp)
    have ht:=ih (fun g hg=>h64 g (by simp [hg]))
    simp only [workNodes,List.length_cons,hx,ht]
    omega
/-- The actual metadata inventory fits the internally derived capacity. -/
theorem meta_le (ctx:Context) (h:Header) (modes:Modes):metaSize ctx h ≤capacity ctx h modes:=by unfold capacity;omega
/-- Every actual intermediate dense output fits the internally derived capacity. -/
theorem dense_le (ctx:Context) (h:Header) (modes:Modes):denseBytes ctx ≤capacity ctx h modes:=by unfold capacity;omega
/-- Every supplied child-vector field fits the internally derived capacity. -/
theorem max_le_capacity (ctx:Context) (h:Header) (modes:Modes):childMax modes ≤capacity ctx h modes:=by unfold capacity;omega
/-- Actual dense child sources remove any dependence of the polynomial factor on the number of modes. -/
theorem dense_capacity (ctx:Context) (h:Header) (modes:Modes) (hd:∀g∈modes,∀x∈g,Dense ctx x):
    capacity ctx h modes ≤ metaSize ctx h+2*denseBytes ctx+1:=by
  have hm:=childMax_dense ctx modes hd
  unfold capacity
  omega
end RiemannGaussian.SemiprimeD1StackJetFoldInputBounds
