/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryCalls
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryActivationMap
/-! # Literal endpoint activation lookup and both real cleanup branches
The flag in the theorem describes the actual dictionary result. The source
obtains it through its real lookup and physical output pop, not as an input.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryEndpointFlag
open SemiprimeD1StackChildGroupFactoryRoles SemiprimeD1StackChildGroupFactoryWiring
open SemiprimeD1StackChildGroupFactory SemiprimeD1StackChildGroupFactoryPrimitives
open SemiprimeD1StackChildGroupFactoryCalls SemiprimeD1StackProcedureTrace
/-- Owner and factor keys are the actual pair fields, not supplied vertex addresses. -/
def vertex (owner:Bool):Stack:=aux (if owner then .ownerKey else .factorKey)
/-- The four literal actual query/table/call/result positions for each endpoint. -/
def pc (owner:Bool) (slot:Fin 4):Label:=if owner then match slot.val with
  | 0=>(.local 3 22)
  | 1=>(.local 3 23)
  | 2=>(.local 3 24)
  | 3=>(.local 3 25)
  | _=>(.local 3 25)
else match slot.val with
  | 0=>(.local 5 2)
  | 1=>(.local 5 3)
  | 2=>(.local 5 4)
  | 3=>(.local 5 5)
  | _=>(.local 5 5)
/-- Only the physically read flag selects actual emit or clear continuation. -/
def next (owner flag:Bool):Label:=if owner then (if flag then (.local 4 16) else (.local 4 25))
  else (if flag then (.local 5 28) else (.local 6 5))
/-- Actual eleven-word physical cleanup sites for all four finite branches. -/
def clearPC (owner flag:Bool) (slot:Fin 12):Label:=if owner then
  if flag then match slot.val with
    | 0=>(.local 4 5)
    | 1=>(.local 4 6)
    | 2=>(.local 4 7)
    | 3=>(.local 4 8)
    | 4=>(.local 4 9)
    | 5=>(.local 4 10)
    | 6=>(.local 4 11)
    | 7=>(.local 4 12)
    | 8=>(.local 4 13)
    | 9=>(.local 4 14)
    | 10=>(.local 4 15)
    | _=>next true true
  else match slot.val with
    | 0=>(.local 3 26)
    | 1=>(.local 3 27)
    | 2=>(.local 3 28)
    | 3=>(.local 3 29)
    | 4=>(.local 3 30)
    | 5=>(.local 3 31)
    | 6=>(.local 4 0)
    | 7=>(.local 4 1)
    | 8=>(.local 4 2)
    | 9=>(.local 4 3)
    | 10=>(.local 4 4)
    | _=>next true false
else
  if flag then match slot.val with
    | 0=>(.local 5 17)
    | 1=>(.local 5 18)
    | 2=>(.local 5 19)
    | 3=>(.local 5 20)
    | 4=>(.local 5 21)
    | 5=>(.local 5 22)
    | 6=>(.local 5 23)
    | 7=>(.local 5 24)
    | 8=>(.local 5 25)
    | 9=>(.local 5 26)
    | 10=>(.local 5 27)
    | _=>next false true
  else match slot.val with
    | 0=>(.local 5 6)
    | 1=>(.local 5 7)
    | 2=>(.local 5 8)
    | 3=>(.local 5 9)
    | 4=>(.local 5 10)
    | 5=>(.local 5 11)
    | 6=>(.local 5 12)
    | 7=>(.local 5 13)
    | 8=>(.local 5 14)
    | 9=>(.local 5 15)
    | 10=>(.local 5 16)
    | _=>next false false
/-- Same actual copies, complete first-match source, result pop, and every cleanup EOF. -/
def timeBound (query table:List Bool) (entries:List (List Bool×List Bool)) (unread:List Bool):Nat:=
  (5*query.length+4)+(5*table.length+4)+(SemiprimeD1StackOwnerLookupExecution.loopTime query entries+2)+1+
    (query.length+unread.length+11)
/-- Full physical activation lookup, restoring all eleven callee words before endpoint emit/clear. -/
theorem source_trace (owner flag:Bool) (before:Stack→List Bool) (query unread:List Bool)
    (entries:List (List Bool×List Bool))
    (hq:before (vertex owner)=query)
    (hm:before (aux .activationMap)=SemiprimeD1StackOwnerLookup.records entries [])
    (hc:before (aux .copyScratch)=[]) (hl:∀k,before (lookup k)=[])
    (hget:SemiprimeD1StackOwnerLookup.result query entries []=([flag],unread)):
    Runs program (timeBound query (SemiprimeD1StackOwnerLookup.records entries []) entries unread)
      (pc owner 0) before (next owner flag) before:=by
  simp only [vertex,aux,lookup] at hq hm hc hl
  have hsrc:copyStack (if owner then 16 else 18) 0=vertex owner:=by cases owner <;> rfl
  have hdst:copyStack (if owner then 16 else 18) 1=lookup (.inr .query):=by cases owner <;> rfl
  let b0:=before
  let b1:=Function.update b0 (lookup (.inr .query)) (query++[])
  have h0a:=copy_call (if owner then 16 else 18) (pc owner 0) (pc owner 1)
    (by cases owner <;> rfl) b0 query []
    (by cases owner <;> simp at hq <;> simp [b0,aux,lookup,copyStack,copyPorts,hq]) (by cases owner <;> simp at hq <;> simp [b0,aux,lookup,copyStack,copyPorts,hl]) (by cases owner <;> simp at hq <;> simp [b0,aux,copyStack,hc])
  have h0:Runs program (5*query.length+4) (pc owner 0) b0 (pc owner 1) b1:=by
    simpa only [hdst] using h0a
  let b2:=Function.update b1 (lookup (.inr .reader)) (SemiprimeD1StackOwnerLookup.records entries []++[])
  have h1:Runs program (5*(SemiprimeD1StackOwnerLookup.records entries []).length+4) (pc owner 1) b1 (pc owner 2) b2:=
    copy_call 17 (pc owner 1) (pc owner 2) (by cases owner <;> rfl) b1 (SemiprimeD1StackOwnerLookup.records entries []) [] (by cases owner <;> simp at hq <;> simp [b0,b1,aux,lookup,copyStack,copyPorts,hm]) (by cases owner <;> simp at hq <;> simp [b0,b1,aux,lookup,copyStack,copyPorts,hl]) (by cases owner <;> simp at hq <;> simp [b0,b1,aux,lookup,copyStack,hc])
  let b3:=withLookup b2 (SemiprimeD1StackOwnerLookup.done query entries []).data
  have h2:Runs program (SemiprimeD1StackOwnerLookupExecution.loopTime query entries+2)
      (pc owner 2) b2 (pc owner 3) b3:=
    lookup_call (pc owner 2) (pc owner 3) (by cases owner <;> rfl) b2 query entries [] (by
      intro k;rcases k with k|k <;> cases k <;> simp [b0,b1,b2,lookup,SemiprimeD1StackOwnerLookup.initial,SemiprimeD1StackOwnerLookup.data,SemiprimeD1StackAdder.store,hl])
  let b4:=Function.update b3 (lookup (.inr .output)) []
  have h3a:=pop_run (pc owner 3) abort (clearPC owner false 0) (clearPC owner true 0) (lookup (.inr .output)) b3 [flag] (by cases owner <;> rfl) (by cases owner <;> simp at hq <;> simp [b0,b1,b2,b3,lookup,withLookup,SemiprimeD1StackOwnerLookup.done,SemiprimeD1StackOwnerLookup.data,hget])
  have h3:Runs program 1 (pc owner 3) b3 (clearPC owner flag 0) b4:=by
    cases flag <;> simpa only [List.head?_cons,List.tail_cons,SemiprimeD1StackBytecode.choose] using h3a
  let b5:Stack→List Bool:=Function.update b4 (lookup (.inl .left)) []
  have h4:Runs program (([]:List Bool).length+1) (clearPC owner flag 0) b4 (clearPC owner flag 1) b5:=
    drain_loop (clearPC owner flag 0) (clearPC owner flag 1) (lookup (.inl .left))
      (by cases owner <;> cases flag <;> rfl) b4 ([]:List Bool) (by cases owner <;> simp at hq <;> simp [b0,b1,b2,b3,b4,lookup,withLookup,SemiprimeD1StackOwnerLookup.done,SemiprimeD1StackOwnerLookup.data,SemiprimeD1StackAdder.store,hget])
  let b6:Stack→List Bool:=Function.update b5 (lookup (.inl .right)) []
  have h5:Runs program (([]:List Bool).length+1) (clearPC owner flag 1) b5 (clearPC owner flag 2) b6:=
    drain_loop (clearPC owner flag 1) (clearPC owner flag 2) (lookup (.inl .right))
      (by cases owner <;> cases flag <;> rfl) b5 ([]:List Bool) (by cases owner <;> simp at hq <;> simp [b0,b1,b2,b3,b4,b5,lookup,withLookup,SemiprimeD1StackOwnerLookup.done,SemiprimeD1StackOwnerLookup.data,SemiprimeD1StackAdder.store,hget])
  let b7:Stack→List Bool:=Function.update b6 (lookup (.inl .scratch)) []
  have h6:Runs program (([]:List Bool).length+1) (clearPC owner flag 2) b6 (clearPC owner flag 3) b7:=
    drain_loop (clearPC owner flag 2) (clearPC owner flag 3) (lookup (.inl .scratch))
      (by cases owner <;> cases flag <;> rfl) b6 ([]:List Bool) (by cases owner <;> simp at hq <;> simp [b0,b1,b2,b3,b4,b5,b6,lookup,withLookup,SemiprimeD1StackOwnerLookup.done,SemiprimeD1StackOwnerLookup.data,SemiprimeD1StackAdder.store,hget])
  let b8:Stack→List Bool:=Function.update b7 (lookup (.inl .output)) []
  have h7:Runs program (([]:List Bool).length+1) (clearPC owner flag 3) b7 (clearPC owner flag 4) b8:=
    drain_loop (clearPC owner flag 3) (clearPC owner flag 4) (lookup (.inl .output))
      (by cases owner <;> cases flag <;> rfl) b7 ([]:List Bool) (by cases owner <;> simp at hq <;> simp [b0,b1,b2,b3,b4,b5,b6,b7,lookup,withLookup,SemiprimeD1StackOwnerLookup.done,SemiprimeD1StackOwnerLookup.data,SemiprimeD1StackAdder.store,hget])
  let b9:Stack→List Bool:=Function.update b8 (lookup (.inr .query)) []
  have h8:Runs program (query.length+1) (clearPC owner flag 4) b8 (clearPC owner flag 5) b9:=
    drain_loop (clearPC owner flag 4) (clearPC owner flag 5) (lookup (.inr .query))
      (by cases owner <;> cases flag <;> rfl) b8 query (by cases owner <;> simp at hq <;> simp [b0,b1,b2,b3,b4,b5,b6,b7,b8,lookup,withLookup,SemiprimeD1StackOwnerLookup.done,SemiprimeD1StackOwnerLookup.data,hget])
  let b10:Stack→List Bool:=Function.update b9 (lookup (.inr .reader)) []
  have h9:Runs program (unread.length+1) (clearPC owner flag 5) b9 (clearPC owner flag 6) b10:=
    drain_loop (clearPC owner flag 5) (clearPC owner flag 6) (lookup (.inr .reader))
      (by cases owner <;> cases flag <;> rfl) b9 unread (by cases owner <;> simp at hq <;> simp [b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,lookup,withLookup,SemiprimeD1StackOwnerLookup.done,SemiprimeD1StackOwnerLookup.data,hget])
  let b11:Stack→List Bool:=Function.update b10 (lookup (.inr .fieldScratch)) []
  have h10:Runs program (([]:List Bool).length+1) (clearPC owner flag 6) b10 (clearPC owner flag 7) b11:=
    drain_loop (clearPC owner flag 6) (clearPC owner flag 7) (lookup (.inr .fieldScratch))
      (by cases owner <;> cases flag <;> rfl) b10 ([]:List Bool) (by cases owner <;> simp at hq <;> simp [b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,lookup,withLookup,SemiprimeD1StackOwnerLookup.done,SemiprimeD1StackOwnerLookup.data,hget])
  let b12:Stack→List Bool:=Function.update b11 (lookup (.inr .valid)) []
  have h11:Runs program (([]:List Bool).length+1) (clearPC owner flag 7) b11 (clearPC owner flag 8) b12:=
    drain_loop (clearPC owner flag 7) (clearPC owner flag 8) (lookup (.inr .valid))
      (by cases owner <;> cases flag <;> rfl) b11 ([]:List Bool) (by cases owner <;> simp at hq <;> simp [b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,lookup,withLookup,SemiprimeD1StackOwnerLookup.done,SemiprimeD1StackOwnerLookup.data,hget])
  let b13:Stack→List Bool:=Function.update b12 (lookup (.inr .copyScratch)) []
  have h12:Runs program (([]:List Bool).length+1) (clearPC owner flag 8) b12 (clearPC owner flag 9) b13:=
    drain_loop (clearPC owner flag 8) (clearPC owner flag 9) (lookup (.inr .copyScratch))
      (by cases owner <;> cases flag <;> rfl) b12 ([]:List Bool) (by cases owner <;> simp at hq <;> simp [b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,lookup,withLookup,SemiprimeD1StackOwnerLookup.done,SemiprimeD1StackOwnerLookup.data,hget])
  let b14:Stack→List Bool:=Function.update b13 (lookup (.inr .discard)) []
  have h13:Runs program (([]:List Bool).length+1) (clearPC owner flag 9) b13 (clearPC owner flag 10) b14:=
    drain_loop (clearPC owner flag 9) (clearPC owner flag 10) (lookup (.inr .discard))
      (by cases owner <;> cases flag <;> rfl) b13 ([]:List Bool) (by cases owner <;> simp at hq <;> simp [b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,lookup,withLookup,SemiprimeD1StackOwnerLookup.done,SemiprimeD1StackOwnerLookup.data,hget])
  let b15:Stack→List Bool:=Function.update b14 (lookup (.inr .output)) []
  have h14:Runs program (([]:List Bool).length+1) (clearPC owner flag 10) b14 (clearPC owner flag 11) b15:=
    drain_loop (clearPC owner flag 10) (clearPC owner flag 11) (lookup (.inr .output))
      (by cases owner <;> cases flag <;> rfl) b14 ([]:List Bool) (by cases owner <;> simp at hq <;> simp [b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,lookup,SemiprimeD1StackOwnerLookup.done,hget])
  have hout:b15=before:=by
    funext k
    rcases k with k|k
    · rcases k with k|k <;> cases k <;> simp [b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15,lookup,SemiprimeD1StackOwnerLookup.done,hl,hget]
    · cases owner <;> simp [b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15,lookup,withLookup,SemiprimeD1StackOwnerLookup.done,hget]
  have hwhole:=join h0 (join h1 (join h2 (join h3 (join h4 (join h5 (join h6 (join h7 (join h8 (join h9 (join h10 (join h11 (join h12 (join h13 (h14))))))))))))))
  rw [hout] at hwhole
  have ht:((5*query.length+4))+((5*(SemiprimeD1StackOwnerLookup.records entries []).length+4))+((SemiprimeD1StackOwnerLookupExecution.loopTime query entries+2))+(1)+((([]:List Bool).length+1))+((([]:List Bool).length+1))+((([]:List Bool).length+1))+((([]:List Bool).length+1))+((query.length+1))+((unread.length+1))+((([]:List Bool).length+1))+((([]:List Bool).length+1))+((([]:List Bool).length+1))+((([]:List Bool).length+1))+((([]:List Bool).length+1))=timeBound query (SemiprimeD1StackOwnerLookup.records entries []) entries unread:=by
    simp only [timeBound,List.length_nil]
    omega
  have hlast:clearPC owner flag 11=next owner flag:=by cases owner <;> cases flag <;> rfl
  rw [hlast] at hwhole
  simpa only [←ht,Nat.add_assoc] using hwhole
/-- The actual prior activation source, rather than an input mask, determines the endpoint branch. -/
theorem source_from_activation (owner:Bool) (before:Stack→List Bool) (i:Inputs) (coordinate:Nat)
    (rows:List SemiprimeD1StackChildGroupFactoryActivationLoop.Row) (query:List Bool) (j:Nat)
    (hj:j<rows.length) (hvalue:SemiprimeBitArithmetic.bitValue query=j)
    (hq:before (vertex owner)=query)
    (hm:before (aux .activationMap)=
      SemiprimeD1StackChildGroupFactoryActivationSource.result i coordinate rows (aux .activationMap))
    (hc:before (aux .copyScratch)=[]) (hl:∀k,before (lookup k)=[]):
    let records:=SemiprimeD1StackChildGroupFactoryActivationMap.entries i coordinate [] rows
    let flag:=(SemiprimeD1StackChildGroupFactoryActivationMap.flags i coordinate rows).getD j false
    let unread:=(SemiprimeD1StackOwnerLookup.result query records []).2
    Runs program (timeBound query (SemiprimeD1StackOwnerLookup.records records []) records unread)
      (pc owner 0) before (next owner flag) before:=by
  dsimp only
  let records:=SemiprimeD1StackChildGroupFactoryActivationMap.entries i coordinate [] rows
  let flag:=(SemiprimeD1StackChildGroupFactoryActivationMap.flags i coordinate rows).getD j false
  let unread:=(SemiprimeD1StackOwnerLookup.result query records []).2
  have hmap:before (aux .activationMap)=SemiprimeD1StackOwnerLookup.records records []:=
    hm.trans (SemiprimeD1StackChildGroupFactoryActivationMap.source_map i coordinate rows)
  have hflag:(SemiprimeD1StackOwnerLookup.result query records []).1=[flag]:=
    SemiprimeD1StackChildGroupFactoryActivationMap.lookup_value i coordinate rows [] query j hj
      (by simpa only [SemiprimeBitArithmetic.bitValue,Nat.zero_add] using hvalue)
  exact source_trace owner flag before query unread records hq hmap hc hl (Prod.ext hflag rfl)
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryEndpointFlag
