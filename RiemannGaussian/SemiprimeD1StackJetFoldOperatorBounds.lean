/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackJetFoldInputBounds
/-! # Uniform actual arithmetic and framing allowances per physical fold node
All operand/output bounds are derived from actual original fields and actual
modular output widths. No native report clock or intermediate-fit answer is used.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 65536
namespace RiemannGaussian.SemiprimeD1StackJetFoldOperatorBounds
open SemiprimeD1StackJetFoldWords SemiprimeD1StackJetFoldSpec SemiprimeD1StackJetFoldInputBounds
open SemiprimeD1StackJetFoldOperators SemiprimeD1StackJetFoldProjection
open SemiprimeD1JetAxes (Context)
/-- Fixed per-node degree-six physical source allowance, before all original inputs. -/
def roundCap (S:Nat):Nat:=1000000000000*(S+1)^6
/-- Acquired rank-counter bytes fit the actual metadata inventory. -/
theorem rank_length_le (ctx:Context) (h:Header) (S:Nat) (hm:metaSize ctx h ≤S):h.rank.length ≤S:=by
  unfold metaSize at hm
  omega
/-- Acquired precision-counter bytes fit the actual metadata inventory. -/
theorem width_length_le (ctx:Context) (h:Header) (S:Nat) (hm:metaSize ctx h ≤S):h.width.length ≤S:=by
  unfold metaSize at hm
  omega
/-- Actual operator powers compare at a positive physical inventory argument. -/
theorem square_le_sixth (S:Nat):(S+1)^2 ≤(S+1)^6:=Nat.pow_le_pow_right (by omega) (by decide)
/-- Actual linear byte work also fits the same fixed power. -/
theorem linear_le_sixth (S:Nat):S+1 ≤(S+1)^6:=by
  simpa only [pow_one] using Nat.pow_le_pow_right (by omega:1 ≤S+1) (by decide:1 ≤6)
/-- One complete real multiplication is bounded directly from its actual two operand fields and cached metadata. -/
theorem multiplyCost_le (ctx:Context) (h:Header) (a b:Jet) (S:Nat)
    (hm:metaSize ctx h ≤S) (ha:(jetTape a).length ≤S) (hb:(jetTape b).length ≤S):
    multiplyCost ctx h a b ≤10000000000*(S+1)^6:=by
  let v:=bank h [] [] [] (jetTape a) (jetTape b) [] [] [] []
  have hs:SemiprimeD1StackJetMulBounds.inputSize ctx (cache v)+1 ≤4*(S+1):=by
    unfold SemiprimeD1StackJetMulBounds.inputSize SemiprimeD1StackJetPointBounds.inputSize
      SemiprimeD1StackJetMulExecution.indexed cache
    dsimp only [v,bank,SemiprimeD1StackJetFoldState.values]
    unfold metaSize at hm
    omega
  have hp:=Nat.mul_le_mul_left 2000000 (Nat.pow_le_pow_left hs 6)
  have hpos:1 ≤(S+1)^6:=Nat.one_le_pow _ _ (by omega)
  unfold multiplyCost mulBound
  calc
    _ ≤2000000*(4*(S+1))^6+1:=Nat.add_le_add_right hp 1
    _=8192000000*(S+1)^6+1:=by ring
    _ ≤10000000000*(S+1)^6:=by omega
/-- Exact frozen dense-addition time is polynomial in its two actual binary tapes and acquired counters. -/
theorem addCost_le (ctx:Context) (h:Header) (a b:Jet) (S:Nat)
    (hm:metaSize ctx h ≤S) (ha:(jetTape a).length ≤S) (hb:(jetTape b).length ≤S):
    addCost h a b ≤1000*(S+1)^2:=by
  have hr:=rank_length_le ctx h S hm
  have hw:=width_length_le ctx h S hm
  have ht:=SemiprimeD1StackJetAddExecution.totalTime_le h.width h.rank a b
  change SemiprimeD1StackJetAddExecution.totalTime h.width h.rank a b ≤
    200*(h.rank.length+1)*((jetTape a).length+(jetTape b).length+h.width.length+2) at ht
  have hp:=Nat.mul_le_mul (Nat.add_le_add_right hr 1)
    (show (jetTape a).length+(jetTape b).length+h.width.length+2 ≤3*S+2 by omega)
  have hcap:addCost h a b ≤200*(S+1)*(3*S+2)+1:=by
    unfold addCost
    nlinarith only [ht,hp]
  exact hcap.trans (by nlinarith)
/-- The actual empty-product unit call and actual EOF fit the same per-node allowance. -/
theorem unitBudget_le (ctx:Context) (h:Header) (S:Nat) (hm:metaSize ctx h ≤S):
    SemiprimeD1StackJetUnitExecution.totalTime h.width h.rank+2 ≤roundCap S:=by
  have hr:=rank_length_le ctx h S hm
  have hw:=width_length_le ctx h S hm
  have ht:=SemiprimeD1StackJetUnitExecution.totalTime_le h.width h.rank
  unfold SemiprimeD1StackJetUnitExecution.timeBound at ht
  have hp:=Nat.mul_le_mul (Nat.add_le_add_right hr 1) (Nat.add_le_add_right hw 8)
  have hcap:SemiprimeD1StackJetUnitExecution.totalTime h.width h.rank+2 ≤200*(S+1)*(S+8)+10:=by
    nlinarith only [ht,hp]
  calc
    _ ≤2000*(S+1)^2:=hcap.trans (by nlinarith)
    _ ≤2000*(S+1)^6:=Nat.mul_le_mul_left 2000 (square_le_sixth S)
    _ ≤roundCap S:=by unfold roundCap;exact Nat.mul_le_mul_right _ (by decide:2000 ≤1000000000000)
/-- The two actual false-marker pushes, complete dense-zero addition and EOF are all charged. -/
theorem emptyBudget_le (ctx:Context) (h:Header) (S:Nat) (hm:metaSize ctx h ≤S):
    SemiprimeD1StackJetAddExecution.totalTime h.width h.rank [] []+4 ≤roundCap S:=by
  have hr:=rank_length_le ctx h S hm
  have hw:=width_length_le ctx h S hm
  have ht:=SemiprimeD1StackJetAddExecution.totalTime_le h.width h.rank [] []
  change SemiprimeD1StackJetAddExecution.totalTime h.width h.rank [] [] ≤
    200*(h.rank.length+1)*(1+1+h.width.length+2) at ht
  have hp:=Nat.mul_le_mul (Nat.add_le_add_right hr 1)
    (show 1+1+h.width.length+2 ≤S+4 by omega)
  have hcap:SemiprimeD1StackJetAddExecution.totalTime h.width h.rank [] []+4 ≤200*(S+1)*(S+4)+4:=by
    nlinarith only [ht,hp]
  calc
    _ ≤2000*(S+1)^2:=hcap.trans (by nlinarith)
    _ ≤2000*(S+1)^6:=Nat.mul_le_mul_left 2000 (square_le_sixth S)
    _ ≤roundCap S:=by unfold roundCap;exact Nat.mul_le_mul_right _ (by decide:2000 ≤1000000000000)
/-- Each actual product edge derives both its intermediate dense-output caps internally. -/
theorem productEdge_le (ctx:Context) (h:Header) (x:Jet) (xs:Group) (S:Nat)
    (hm:metaSize ctx h ≤S) (hd:denseBytes ctx ≤S) (hx:groupMax (x::xs) ≤S):
    productEdge ctx h x xs ≤roundCap S:=by
  have ha:(jetTape x).length ≤S:=(le_max_left _ _).trans hx
  have hb:(jetTape (productWords ctx xs)).length ≤S:=
    (dense_tape_length ctx _ (product_dense ctx xs)).trans hd
  have ho:(jetTape (productWords ctx (x::xs))).length ≤S:=
    (dense_tape_length ctx _ (product_dense ctx (x::xs))).trans hd
  have ht:=multiplyCost_le ctx h x (productWords ctx xs) S hm ha hb
  have hf:100*((jetTape x).length+(jetTape (productWords ctx xs)).length+
      (jetTape (productWords ctx (x::xs))).length+1) ≤400*(S+1):=by omega
  have hp:=hf.trans (Nat.mul_le_mul_left 400 (linear_le_sixth S))
  unfold productEdge roundCap
  omega
/-- Each actual sum edge pays the complete current group bytes and actual dense tail sum. -/
theorem sumEdge_le (ctx:Context) (h:Header) (x:Group) (xs:Modes) (S:Nat)
    (hm:metaSize ctx h ≤S) (hd:denseBytes ctx ≤S) (hx:groupMax x ≤S):
    sumEdge ctx h x xs ≤roundCap S*(x.length+1):=by
  have ha:(jetTape (productWords ctx x)).length ≤S:=
    (dense_tape_length ctx _ (product_dense ctx x)).trans hd
  have hb:(jetTape (sumWords ctx xs)).length ≤S:=
    (dense_tape_length ctx _ (sum_dense ctx xs)).trans hd
  have hAdd: addCost h (productWords ctx x) (sumWords ctx xs) ≤1000*(S+1)^6:=
    (addCost_le ctx h _ _ S hm ha hb).trans (Nat.mul_le_mul_left 1000 (square_le_sixth S))
  have hg:=groupTape_length x S hx
  have hf:100*((groupTape x).length+(jetTape (sumWords ctx xs)).length+1) ≤400*(x.length+1)*(S+1):=by
    nlinarith only [hg,hb]
  have hframe:=hf.trans (Nat.mul_le_mul_left (400*(x.length+1)) (linear_le_sixth S))
  have hAddLift:addCost h (productWords ctx x) (sumWords ctx xs) ≤1000*(x.length+1)*(S+1)^6:=by
    apply hAdd.trans
    exact Nat.mul_le_mul_right _ (by omega:1000 ≤1000*(x.length+1))
  unfold sumEdge
  calc
    _ ≤1000*(x.length+1)*(S+1)^6+400*(x.length+1)*(S+1)^6:=Nat.add_le_add hAddLift hframe
    _=1400*(x.length+1)*(S+1)^6:=by ring
    _ ≤1000000000000*(x.length+1)*(S+1)^6:=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by decide:1400 ≤1000000000000))
    _=roundCap S*(x.length+1):=by unfold roundCap;ring
end RiemannGaussian.SemiprimeD1StackJetFoldOperatorBounds
