/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackJetFoldOperatorBounds
import RiemannGaussian.SemiprimeD1StackJetFoldExecution
/-! # Same-program linear-per-actual-term physical fold clock
The polynomial factor uses actual original field maxima and actual acquired
rank/precision VALUES. Mode count occurs only in the linear physical recursion
inventory, never inside a power of the whole menu tape length.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 65536
namespace RiemannGaussian.SemiprimeD1StackJetFoldBudgetBounds
open SemiprimeD1StackJetFoldWords SemiprimeD1StackJetFoldSpec SemiprimeD1StackJetFoldContext
open SemiprimeD1StackJetFoldExecution SemiprimeD1StackJetFoldInputBounds SemiprimeD1StackJetFoldOperatorBounds
open SemiprimeD1JetAxes (Context)
attribute [local irreducible] roundCap productBudget productEdge sumBudget sumEdge
/-- Actual complete product cost is bounded per actual child and its real empty-product base. -/
theorem productBudget_le (ctx:Context) (h:Header) (g:Group) (S:Nat)
    (hm:metaSize ctx h ≤S) (hd:denseBytes ctx ≤S) (hg:groupMax g ≤S):
    productBudget ctx h g ≤roundCap S*(g.length+1):=by
  induction g with
  | nil=>simpa only [productBudget,List.length_nil,Nat.zero_add,Nat.mul_one] using unitBudget_le ctx h S hm
  | cons x xs ih=>
    have ht:=ih ((le_max_right _ _).trans hg)
    have he:=productEdge_le ctx h x xs S hm hd hg
    rw [productBudget,List.length_cons]
    calc
      _ ≤roundCap S*(xs.length+1)+roundCap S:=Nat.add_le_add ht he
      _= _:=by ring
/-- Actual complete sum cost is linear in the combined actual sum/product recursion inventory. -/
theorem sumBudget_le (ctx:Context) (h:Header) (modes:Modes) (S:Nat)
    (hm:metaSize ctx h ≤S) (hd:denseBytes ctx ≤S) (hg:childMax modes ≤S):
    sumBudget ctx h modes ≤2*roundCap S*workNodes modes:=by
  induction modes with
  | nil=>
    have h:=emptyBudget_le ctx h S hm
    rw [sumBudget,workNodes]
    omega
  | cons x xs ih=>
    have hx:groupMax x ≤S:=(le_max_left _ _).trans hg
    have ht:=ih ((le_max_right _ _).trans hg)
    have hp:=productBudget_le ctx h x S hm hd hx
    have he:=sumEdge_le ctx h x xs S hm hd hx
    rw [sumBudget,workNodes]
    calc
      _ ≤2*roundCap S*workNodes xs+roundCap S*(x.length+1)+roundCap S*(x.length+1):=
        Nat.add_le_add (Nat.add_le_add ht hp) he
      _ ≤2*roundCap S*(x.length+2+workNodes xs):=by nlinarith
/-- The actual original context resource is part of the actual metadata/value inventory. -/
theorem context_resource_le (axes:List Nat) (precision children:List Bool):
    SemiprimeD1StackJetContextBounds.resource axes precision ≤
      metaSize (context axes precision) (acquiredHeader axes precision children):=by
  unfold SemiprimeD1StackJetContextBounds.resource metaSize context acquiredHeader
  simp only [SemiprimeD1JetAxes.Context.rank,SemiprimeD1StackUnaryDivmod.unary,
    SemiprimeD1StackUnaryCounterExecution.markers,List.length_replicate]
  omega
/-- The full source pays the actual context acquisition once, including its actual caller return. -/
theorem contextBudget_le (axes:List Nat) (hp:∀q∈axes,0 < q) (precision children:List Bool) (S:Nat)
    (hm:metaSize (context axes precision) (acquiredHeader axes precision children) ≤S):
    SemiprimeD1StackJetContextCorrectness.budget axes precision+1 ≤roundCap S:=by
  have hs:SemiprimeD1StackJetContextBounds.resource axes precision ≤S:=(context_resource_le axes precision children).trans hm
  have ht:=SemiprimeD1StackJetContextBounds.budget_polynomial axes hp precision
  have hpow:=Nat.pow_le_pow_left (Nat.add_le_add_right hs 1) 2
  have hcap:SemiprimeD1StackJetContextCorrectness.budget axes precision+1 ≤1001*(S+1)^2:=by
    have h:=ht.trans (Nat.mul_le_mul_left 1000 hpow)
    have hpos:1 ≤(S+1)^2:=Nat.one_le_pow _ _ (by omega)
    omega
  calc
    _ ≤1001*(S+1)^2:=hcap
    _ ≤1001*(S+1)^6:=Nat.mul_le_mul_left 1001 (square_le_sixth S)
    _ ≤roundCap S:=by unfold roundCap;exact Nat.mul_le_mul_right _ (by decide:1001 ≤1000000000000)
/-- The physical original-input copy and actual outer return/halt are linear in actual nodes and actual field bytes. -/
theorem input_copy_le (modes:Modes) (S:Nat) (hm:childMax modes ≤S):
    5*(modeTape modes).length+7 ≤roundCap S*workNodes modes:=by
  have ht:=modeTape_length modes S hm
  have hn:=nodes_positive modes
  have hpos:1 ≤(S+1)*workNodes modes:=by
    simpa only [Nat.one_mul] using Nat.mul_le_mul (by omega:1 ≤S+1) hn
  have hcopy:5*(modeTape modes).length+7 ≤27*(S+1)*workNodes modes:=by
    nlinarith only [ht,hpos]
  have hfactor:27*(S+1) ≤roundCap S:=by
    calc
      _ ≤27*(S+1)^6:=Nat.mul_le_mul_left 27 (linear_le_sixth S)
      _ ≤roundCap S:=by unfold roundCap;exact Nat.mul_le_mul_right _ (by decide:27 ≤1000000000000)
  exact hcopy.trans (Nat.mul_le_mul_right _ hfactor)
/-- The full actually executed source clock is fixed-polynomial per actual recursion node. -/
theorem timeBound_le (axes:List Nat) (hp:∀q∈axes,0 < q) (precision:List Bool) (modes:Modes):
    timeBound axes precision modes ≤10*roundCap
      (capacity (context axes precision) (acquiredHeader axes precision (modeTape modes)) modes)*workNodes modes:=by
  let ctx:=context axes precision
  let h:=acquiredHeader axes precision (modeTape modes)
  let S:=capacity ctx h modes
  have hm:metaSize ctx h ≤S:=meta_le ctx h modes
  have hd:denseBytes ctx ≤S:=dense_le ctx h modes
  have hx:childMax modes ≤S:=max_le_capacity ctx h modes
  have hc:=contextBudget_le axes hp precision (modeTape modes) S hm
  have hsum:=sumBudget_le ctx h modes S hm hd hx
  have hcopy:=input_copy_le modes S hx
  have hn:=nodes_positive modes
  have hcontext:SemiprimeD1StackJetContextCorrectness.budget axes precision+1 ≤roundCap S*workNodes modes:=
    hc.trans (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left (roundCap S) hn)
  change _ ≤10*roundCap S*workNodes modes
  unfold timeBound readyTimeBound
  change SemiprimeD1StackJetContextCorrectness.budget axes precision+1+
    (5*(modeTape modes).length+sumBudget ctx h modes+7) ≤_
  nlinarith only [hcontext,hsum,hcopy,Nat.zero_le (roundCap S*workNodes modes)]
end RiemannGaussian.SemiprimeD1StackJetFoldBudgetBounds
