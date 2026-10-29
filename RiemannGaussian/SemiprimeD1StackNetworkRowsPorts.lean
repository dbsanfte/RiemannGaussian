/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackNetworkRowsLookup
/-! # Actual per-factor port→catalogue scan→binary-owner vector loop
Key and expected-owner lists below are proof descriptions of actual parsed and
returned words. The program accepts ONLYthe original record/count tapes, and
performs every dictionary copy, lookup, singleton test, frame and tally push.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackNetworkRowsPorts
open SemiprimeD1StackNetworkRows SemiprimeD1StackNetworkRowsPrimitives
open SemiprimeD1StackNetworkRowsView SemiprimeD1StackNetworkRowsEncoding SemiprimeD1StackNetworkRowsLookup
open SemiprimeD1StackProcedureTrace
open SemiprimeD1TensorTapeCodec (vectorBits)
open SemiprimeSourceHistogramKeyBits (frame)
local notation "ctl" => Label.local
/-- Paid actual per-query cap in physical dictionary/key bytes and actual acquired owner width. -/
def portBudget (n:Nat) (dictionary key:List Bool) :Nat :=
  100*(key.length+1)*(dictionary.length+1)+5*dictionary.length+9*key.length+19*(n+1)+41
/-- Whole physical port-loop cap, including its final actual FALSEvector-tag pop. -/
def portClock (n:Nat) (dictionary:List Bool) (keys:List (List Bool)) :Nat :=
  (keys.map (portBudget n dictionary)).sum+1
/-- One actual parsed port copies/scans the actual catalogue and counts exactly ONEreturned/validated owner. -/
theorem port_step (index:I.Stack→List Bool) (reader rowHistory history factors occurrences key owner:List Bool)
    (keys:List (List Bool)) (rows:List (List Bool×List Bool)) (n:Nat)
    (hd:index .output=SemiprimeD1StackOwnerFibre.records rows [])
    (hs:SemiprimeD1StackOwnerFibre.values key rows=[owner]) (hw:owner.length≤ n+1) :
    ∃q≤ portBudget n (SemiprimeD1StackOwnerFibre.records rows []) key,
      Runs program q (ctl .portLoop) (view index reader (vectorBits (key::keys)) rowHistory history factors occurrences)
        (ctl .portLoop) (view index reader (vectorBits keys) ((chunk owner).reverse++rowHistory) history factors (true::occurrences)) :=by
  let tail:=vectorBits keys
  let b1:=view index reader (frame key tail) rowHistory history factors occurrences
  let clean:=view index reader tail rowHistory history factors occurrences
  let b2:=Function.update (Function.update clean (aux .key) key) (aux .valid) [true]
  have h0:=pop_run .portLoop (ctl .abort) (ctl .rowSeed) (ctl .keyField) (aux .ports)
    (view index reader (vectorBits (key::keys)) rowHistory history factors occurrences) (true::frame key tail) rfl rfl
  change Runs program 1 (ctl .portLoop) _ (ctl .keyField)
    (Function.update (view index reader (vectorBits (key::keys)) rowHistory history factors occurrences) (aux .ports) (frame key tail)) at h0
  rw [view_ports] at h0
  have h1:=field_call .key .keyField .keyValid rfl b1 key tail rfl rfl rfl rfl
  change Runs program (8*key.length+7) (ctl .keyField) b1 (ctl .keyValid)
    (Function.update (Function.update (Function.update b1 (aux .ports) tail) (aux .key) key) (aux .valid) [true]) at h1
  rw [view_ports] at h1
  have h2:=pop_run .keyValid (ctl .abort) (ctl .abort) (ctl .copyDictionary) (aux .valid) b2 [true] rfl rfl
  have he2:Function.update b2 (aux .valid) []=keyed index reader tail rowHistory history factors occurrences key:=by
    funext k;rcases k with k|k
    · rfl
    · rcases k with k|k
      · rfl
      · cases k <;> rfl
  change Runs program 1 (ctl .keyValid) b2 (ctl .copyDictionary) (Function.update b2 (aux .valid) []) at h2
  rw [he2] at h2
  obtain ⟨b,hb,h3⟩:=lookup_run index reader tail rowHistory history factors occurrences key owner rows hd hs
  have h4:=singleton_run index reader tail rowHistory history factors occurrences key owner
  have h5:=emit_owner index reader tail rowHistory history factors occurrences key owner
  have hh:=join (join (join (join (join h0 h1) h2) h3) h4) h5
  refine ⟨1+(8*key.length+7)+1+b+(8*owner.length+11)+(11*owner.length+key.length+16),?_,hh⟩
  unfold portBudget SemiprimeD1StackOwnerFibreBounds.runBound at *
  omega
/-- One real FALSEvector-tag pop ends the current factor's local port stream. -/
theorem port_end (index:I.Stack→List Bool) (reader rowHistory history factors occurrences:List Bool) :
    Runs program 1 (ctl .portLoop) (view index reader (vectorBits []) rowHistory history factors occurrences)
      (ctl .rowSeed) (view index reader [] rowHistory history factors occurrences) :=by
  have h:=pop_run .portLoop (ctl .abort) (ctl .rowSeed) (ctl .keyField) (aux .ports)
    (view index reader (vectorBits []) rowHistory history factors occurrences) [false] rfl rfl
  rw [view_ports] at h
  exact h
/-- Whole actual port loop, with semantic singleton facts derived later for EVERYoriginal well-formed network. -/
theorem ports_run (index:I.Stack→List Bool) (reader rowHistory history factors occurrences:List Bool)
    (keys owners:List (List Bool)) (rows:List (List Bool×List Bool)) (n:Nat)
    (hd:index .output=SemiprimeD1StackOwnerFibre.records rows [])
    (hp:List.Forall₂ (fun key owner=>SemiprimeD1StackOwnerFibre.values key rows=[owner] ∧ owner.length≤ n+1) keys owners) :
    ∃q≤ portClock n (SemiprimeD1StackOwnerFibre.records rows []) keys,
      Runs program q (ctl .portLoop) (view index reader (vectorBits keys) rowHistory history factors occurrences)
        (ctl .rowSeed)
        (view index reader [] ((payload owners).reverse++rowHistory) history factors (List.replicate owners.length true++occurrences)) :=by
  induction hp generalizing rowHistory occurrences with
  | nil=>
    refine ⟨1,by rfl,?_⟩
    exact port_end index reader rowHistory history factors occurrences
  | @cons key owner keys owners h hp ih=>
    obtain ⟨b,hb,h0⟩:=port_step index reader rowHistory history factors occurrences key owner keys rows n hd h.1 h.2
    obtain ⟨c,hc,h1⟩:=ih ((chunk owner).reverse++rowHistory) (true::occurrences)
    have hh:=join h0 h1
    refine ⟨b+c,?_,?_⟩
    · unfold portClock at *
      simp only [List.map_cons,List.sum_cons]
      omega
    · have hrep:List.replicate owners.length true++true::occurrences=List.replicate (owners.length+1) true++occurrences:=by
        rw [show List.replicate (owners.length+1) true=List.replicate owners.length true++[true] from List.replicate_add _ _ _]
        rw [List.append_assoc]
        rfl
      simpa only [payload,List.foldr_cons,List.reverse_append,List.append_assoc,List.length_cons,hrep] using hh
/-- Fixed physical-byte cap for one actual scan and scalar/port cleanup. -/
theorem portBudget_le (n:Nat) (dictionary key:List Bool) :
    portBudget n dictionary key≤ 500*(n+dictionary.length+2)*(key.length+1) :=by
  unfold portBudget
  nlinarith [Nat.zero_le (n*key.length),Nat.zero_le (dictionary.length*key.length)]
/-- Sum of query costs is charged by ACTUALport tape bytes, not a supplied arity/lookup estimate. -/
theorem portClock_le (n:Nat) (dictionary:List Bool) (keys:List (List Bool)) :
    portClock n dictionary keys≤ 1000*(n+dictionary.length+2)*(vectorBits keys).length :=by
  have hs:(keys.map (portBudget n dictionary)).sum≤ 500*(n+dictionary.length+2)*
      ((keys.map List.length).sum+keys.length):=by
    induction keys with
    | nil=>simp
    | cons key keys ih=>
      have h:=portBudget_le n dictionary key
      simp only [List.map_cons,List.sum_cons,List.length_cons]
      nlinarith only [h,ih]
  have hl:=vector_length keys
  let S:=(keys.map List.length).sum+keys.length
  let K:=500*(n+dictionary.length+2)
  have hK:1≤ K:=by dsimp [K];omega
  have hS:S+1≤(vectorBits keys).length:=by dsimp [S];omega
  calc
    portClock n dictionary keys≤ K*(S+1):=by
      unfold portClock
      rw [Nat.mul_add,Nat.mul_one]
      change (keys.map (portBudget n dictionary)).sum+1≤ 500*(n+dictionary.length+2)*S+K
      change (keys.map (portBudget n dictionary)).sum≤ 500*(n+dictionary.length+2)*S at hs
      omega
    _≤ K*(vectorBits keys).length:=Nat.mul_le_mul_left K hS
    _≤ 1000*(n+dictionary.length+2)*(vectorBits keys).length:=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by decide :500≤ 1000))
end RiemannGaussian.SemiprimeD1StackNetworkRowsPorts
