/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackCachePhaseBankState
/-! # Exact partial physical cleanup views and whole236-role cost
Only heap/counter persist. Every other actual component/shadow role belongs to
the finite sweep; mathematical prefixes/costs are not runtime operands.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackCachePhaseBankClearEncoding
open SemiprimeD1StackCachePhaseBank SemiprimeD1StackCachePhaseBankState
private instance:BEq P.Stack:=⟨fun a b=>decide (a=b)⟩
private instance:LawfulBEq P.Stack where
  eq_of_beq:=by intro a b h;exact of_decide_eq_true h
  rfl:=by intro a;exact decide_eq_true rfl
/-- Mathematical view after exactly n fixed physical ports have been visited. -/
def through (bank:P.Stack→List Bool) (n:Nat):P.Stack→List Bool:=fun k=>
  if persistent k then bank k else if k∈I.roles.take n then [] else bank k
/-- Exact fully swept bank; only the two actual immutable input roles remain. -/
def cleared (bank:P.Stack→List Bool):P.Stack→List Bool:=fun k=>if persistent k then bank k else []
/-- No word changes before the first real sweep instruction. -/
theorem through_zero (bank:P.Stack→List Bool):through bank 0=bank:=by funext k;simp [through]
/-- Complete sweep covers every real role, including every unused shadow allocation. -/
theorem through_all (bank:P.Stack→List Bool):through bank 238=cleared bank:=by
  have ht:I.roles.take 238=I.roles:=by rw [←I.roles_length,List.take_length]
  funext k
  simp only [through,cleared,ht,I.roles_complete,ite_true]
/-- The finite next port is really appended to the processed-prefix inventory. -/
theorem take_step (i:Fin 238):I.roles.take (i.val+1)=I.roles.take i.val++[I.role i]:=
  List.take_succ_eq_append_getElem (by rw [I.roles_length];exact i.isLt)
/-- Distinct cleanup labels have not previously modified the current real word. -/
theorem current_not_seen (i:Fin 238):I.role i∉I.roles.take i.val:=by
  intro h
  obtain ⟨j,hj,he⟩:=List.mem_take_iff_getElem.mp h
  have hi:j < i.val:=lt_of_lt_of_le hj (Nat.min_le_left _ _)
  have heq:j=i.val:=I.roles_nodup.getElem_inj.mp he
  omega
/-- The next actual word length is its ORIGINAL stopped-callee payload length. -/
theorem through_current (bank:P.Stack→List Bool) (i:Fin 238):through bank i.val (I.role i)=bank (I.role i):=by
  simp only [through,current_not_seen,ite_false,ite_self]
/-- A retained heap/counter port is skipped by an actual jump and has no mathematical change. -/
theorem through_skip (bank:P.Stack→List Bool) (i:Fin 238) (hp:persistent (I.role i)=true):
    through bank (i.val+1)=through bank i.val:=by
  funext k
  by_cases hk:k=I.role i
  · subst k;simp only [through,hp,ite_true]
  · simp only [through,take_step,List.mem_append,List.mem_singleton,hk,or_false]
/-- Every other real port advances ONLY by its actual physical drain. -/
theorem through_clear (bank:P.Stack→List Bool) (i:Fin 238) (hp:persistent (I.role i)=false):
    through bank (i.val+1)=Function.update (through bank i.val) (I.role i) []:=by
  funext k
  by_cases hk:k=I.role i
  · subst k;simp only [through,hp,Bool.false_eq_true,ite_false,Function.update_self,take_step,List.mem_append,List.mem_singleton,or_true,ite_true]
  · simp only [Function.update_of_ne hk,through,take_step,List.mem_append,List.mem_singleton,hk,or_false]
/-- Each physical sweep port costs one EOF pop/jump, plus precisely its nonpersistent payload bits. -/
def portTime (bank:P.Stack→List Bool) (k:P.Stack):Nat:=if persistent k then 1 else (bank k).length+1
/-- Sum of the SAME actual future physical drain/jump costs. -/
def sweepTime (bank:P.Stack→List Bool) (n:Nat):Nat:=((I.roles.drop n).map (portTime bank)).sum
/-- Exact remaining-time recurrence for the next finite source port. -/
theorem sweepTime_step (bank:P.Stack→List Bool) (i:Fin 238):
    sweepTime bank i.val=portTime bank (I.role i)+sweepTime bank (i.val+1):=by
  have hd:I.roles.drop i.val=I.role i::I.roles.drop (i.val+1):=
    List.drop_eq_getElem_cons (by rw [I.roles_length];exact i.isLt)
  simp only [sweepTime,hd,List.map_cons,List.sum_cons]
/-- No hidden cleanup occurs after the last actual physical port. -/
theorem sweepTime_all (bank:P.Stack→List Bool):sweepTime bank 238=0:=by
  unfold sweepTime
  rw [←I.roles_length,List.drop_length]
  rfl
/-- Exactly236 actual callee allocations are drained; exactly heap/counter are skipped. -/
theorem clear_count:(I.roles.filter (fun k=>!persistent k)).length=236:=by decide
/-- All actual sweep work has a linear cap in the actual full stopped-bank word bound. -/
theorem sweepTime_le (bank:P.Stack→List Bool) (L:Nat) (h:∀k,(bank k).length ≤L):
    sweepTime bank 0 ≤238*(L+1):=by
  have hbound:∀ks:List P.Stack,(ks.map (portTime bank)).sum ≤ks.length*(L+1):=by
    intro ks
    induction ks with
    | nil=>simp only [List.map_nil,List.sum_nil,List.length_nil,Nat.zero_mul,Nat.le_refl]
    | cons k ks ih=>
      have hk:portTime bank k ≤L+1:=by
        unfold portTime
        split_ifs <;> have h0:=h k <;> omega
      simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.add_mul,Nat.one_mul]
      omega
  simpa only [sweepTime,List.drop_zero,I.roles_length] using hbound I.roles
/-- The actually cleared copy scratch is safe to borrow before the next real parser/copy/callee call. -/
theorem cleared_scratch (bank:P.Stack→List Bool):cleared bank P.copyScratch=[]:=by
  simp only [cleared,scratch_not_persistent,Bool.false_eq_true,ite_false]
/-- Every skipped physical heap/counter word remains literally unchanged through the full sweep. -/
theorem cleared_retained (bank:P.Stack→List Bool) (k:P.Stack) (hp:persistent k=true):cleared bank k=bank k:=by
  simp only [cleared,hp,ite_true]
end RiemannGaussian.SemiprimeD1StackCachePhaseBankClearEncoding
