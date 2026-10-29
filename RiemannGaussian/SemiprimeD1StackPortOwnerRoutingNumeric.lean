/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPortOwnerRoutingExecution
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32000
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPortOwnerRoutingNumeric
open SemiprimeD1StackPortOwnerRouting SemiprimeD1StackPortOwnerRoutingRow
open SemiprimeD1FactorScopePairEncoding (Record mass)
/-- Honest uniform complete-row bound in acquired nine-field payload mass and actual acquired E-map bytes. -/
def rowCap (payload mapBytes:Nat) : Nat :=100000*(payload+mapBytes+100*(2*payload+8)*(mapBytes+1)+1)
/-- Exact finite nine-field payload inventory, including scope/global/factor words. -/
theorem mass_expand (w:Record) : mass w=(w 0).length+(w 1).length+(w 2).length+(w 3).length+
    (w 4).length+(w 5).length+(w 6).length+(w 7).length+(w 8).length := by
  have he:mass w=(w 0).length+((w 1).length+((w 2).length+((w 3).length+((w 4).length+
      ((w 5).length+((w 6).length+((w 7).length+((w 8).length+0)))))))):=rfl
  omega
/-- Every actually parsed original field is included in its actual payload inventory. -/
theorem field_mass (w:Record) (i:Fin 9) : (w i).length≤ mass w := by
  have h:=mass_expand w
  fin_cases i
  · change (w (0:Fin 9)).length≤_;omega
  · change (w (1:Fin 9)).length≤_;omega
  · change (w (2:Fin 9)).length≤_;omega
  · change (w (3:Fin 9)).length≤_;omega
  · change (w (4:Fin 9)).length≤_;omega
  · change (w (5:Fin 9)).length≤_;omega
  · change (w (6:Fin 9)).length≤_;omega
  · change (w (7:Fin 9)).length≤_;omega
  · change (w (8:Fin 9)).length≤_;omega
/-- All six actual endpoint-key fields are part of the parsed original payload. -/
theorem key_mass (w:Record) : SemiprimeD1StackPortOwnerRoutingKey.mass w≤ mass w := by
  have h:=mass_expand w
  unfold SemiprimeD1StackPortOwnerRoutingKey.mass
  omega
/-- Actual compact key length follows from its six actual field frames and physical sentinel. -/
theorem query_length (w:Record) : (SemiprimeD1PortOwnerRoutingSpec.query w).length≤2*mass w+7 := by
  have h:=key_mass w
  simp only [SemiprimeD1PortOwnerRoutingSpec.query,SemiprimeSourceHistogramKeyBits.frame_length,
    List.length_cons,List.length_nil]
  unfold SemiprimeD1StackPortOwnerRoutingKey.mass at h
  omega
/-- All actual parser calls and validity pops are bounded by real parsed payload bytes. -/
theorem parse_time (w:Record) (n:Nat) :
    SemiprimeD1StackPortOwnerRoutingParse.time w n≤n*(8*mass w+8) := by
  induction n with
  | zero=>simp only [SemiprimeD1StackPortOwnerRoutingParse.time,Nat.zero_mul,Nat.le_refl]
  | succ n ih=>
    have h:=field_mass w ⟨n%9,Nat.mod_lt _ (by omega)⟩
    simp only [SemiprimeD1StackPortOwnerRoutingParse.time]
    nlinarith
/-- Every actual halted lookup word is bounded by its SAME physical source trace and counted clock. -/
theorem lookup_word (map:List (List Bool×List Bool)) (w:Record) (k:Lookup.Stack) :
    (lookupDone map w k).length≤(SemiprimeD1PortOwnerRoutingSpec.query w).length+
      (SemiprimeD1StackOwnerLookup.records map []).length+
      SemiprimeD1StackOwnerLookupBounds.runBound (SemiprimeD1PortOwnerRoutingSpec.query w) map := by
  let q:=SemiprimeD1PortOwnerRoutingSpec.query w
  let b:=SemiprimeD1StackOwnerLookup.records map []
  have hr:=SemiprimeD1StackOwnerLookupExecution.source_run q map []
  have hd:=SemiprimeD1StackReturnLink.run_data_bound SemiprimeD1StackOwnerLookup.program
    (SemiprimeD1StackOwnerLookupExecution.loopTime q map+1) (q.length+b.length) _ _ (by
      intro i;rcases i with i|i <;> cases i <;>
        simp [SemiprimeD1StackOwnerLookup.initial,SemiprimeD1StackOwnerLookup.data,
          SemiprimeD1StackAdder.store,b]) hr k
  have ht:=SemiprimeD1StackOwnerLookupBounds.time_le q map
  change (lookupDone map w k).length≤q.length+b.length+_ at hd
  exact hd.trans (Nat.add_le_add_left ht _)
/-- Complete physical twenty-role cleanup pays every reached payload and every EOF pop. -/
theorem clear_time (b:SemiprimeD1StackPortOwnerRoutingClear.Bank) (cap n:Nat) (hb:∀i,(b i).length≤cap) :
    SemiprimeD1StackPortOwnerRoutingClear.time b n≤n*(cap+1) := by
  induction n with
  | zero=>simp only [SemiprimeD1StackPortOwnerRoutingClear.time,Nat.zero_mul,Nat.le_refl]
  | succ n ih=>
    have h:=hb ⟨n%20,Nat.mod_lt _ (by omega)⟩
    simp only [SemiprimeD1StackPortOwnerRoutingClear.time]
    nlinarith
/-- COMPLETE actual routing-row clock is polynomial in ACTUALLY acquired bytes. -/
theorem row_budget (map:List (List Bool×List Bool)) (w:Record) :
    SemiprimeD1StackPortOwnerRoutingRow.budget map w≤rowCap (mass w) (SemiprimeD1StackOwnerLookup.records map []).length := by
  let Q:=(SemiprimeD1PortOwnerRoutingSpec.query w).length
  let B:=(SemiprimeD1StackOwnerLookup.records map []).length
  let R:=SemiprimeD1StackOwnerLookupBounds.runBound (SemiprimeD1PortOwnerRoutingSpec.query w) map
  have hparse:=parse_time w 9
  have hk:=key_mass w
  have hq:=query_length w
  have hw:=lookup_word map w
  have hscope:=field_mass w 0
  have hbank:∀i,(SemiprimeD1StackPortOwnerRoutingClear.bank (lookupDone map w) w i).length≤Q+B+R+mass w:=by
    intro i
    unfold SemiprimeD1StackPortOwnerRoutingClear.bank
    split
    · exact (hw _).trans (Nat.le_add_right _ _)
    · exact (field_mass w _).trans (Nat.le_add_left _ _)
  have hc:=clear_time (SemiprimeD1StackPortOwnerRoutingClear.bank (lookupDone map w) w) (Q+B+R+mass w) 20 hbank
  have ho:=hw (.inr .output)
  have hR:R≤100*(2*mass w+8)*(B+1):=by
    change 100*(Q+1)*(B+1)≤_
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by dsimp [Q] at *;omega))
  unfold SemiprimeD1StackPortOwnerRoutingRow.budget rowCap
  change Q≤2*mass w+7 at hq
  change (lookupDone map w (.inr .output)).length≤Q+B+R at ho
  change _≤100000*(mass w+B+100*(2*mass w+8)*(B+1)+1)
  dsimp only [Q,B,R] at hc ho hR ⊢
  omega
end RiemannGaussian.SemiprimeD1StackPortOwnerRoutingNumeric
