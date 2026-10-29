/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryFinishPrimitives
/-! # All sixteen actual recovery-helper drains and real returns
Every allocated helper/cache is physically emptied after the final product.
The three original operands and the actual final scalar output are retained.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 65536
namespace RiemannGaussian.SemiprimeD1StackRecoveryFinishCleanup
open SemiprimeD1StackRecoveryFinish SemiprimeD1StackRecoveryFinishState
open SemiprimeD1StackRecoveryFinishPrimitives SemiprimeD1StackProcedureTrace
local notation "ctl"=>Label.local
/-- Exactly sixteen actual helper/cache words are physically drained. -/
theorem cleanup_length:cleanup.length=16:=rfl
/-- No helper/cache address is duplicated. -/
theorem cleanup_nodup:cleanup.Nodup:=by decide
/-- Precisely the two actual original binary source operands are excluded from helper draining. -/
theorem cleanup_mem (a:Aux):a∈cleanup ↔a≠.numerator ∧a≠.denominator:=by cases a <;> simp [cleanup]
/-- Exact full bank after the fixed prefix of actual helper drains. -/
def partialBank (v:Values) (n:Nat):Values
  | .aux a=>if a∈cleanup.take n then [] else v (.aux a)
  | s=>v s
/-- Final full35-role bank preserves actual input/cache/result addresses and clears all sixteen helper fields. -/
def cleared (v:Values):Values
  | .aux .numerator=>v (.aux .numerator) | .aux .denominator=>v (.aux .denominator)
  | .aux _=>[] | s=>v s
/-- Only proof indices describe the fixed finite source position; the actual code has sixteen static sites. -/
def labelAt (n:Nat):Label:=if h:n<16 then ctl (.clear ⟨n,h⟩) else ctl .done
/-- Actual remaining physical word-byte mass, not a native recovery report. -/
def mass (v:Values) (n:Nat):Nat:=((cleanup.drop n).map (fun a=>(v (.aux a)).length)).sum
/-- Initially no helper was drained by an advised operation. -/
theorem partial_zero (v:Values):partialBank v 0=v:=by
  funext s;cases s with
  | aux a=>simp [partialBank]
  | _=>rfl
/-- Complete actual fixed inventory empties every helper field, including copy workspace. -/
theorem partial_full (v:Values):partialBank v 16=cleared v:=by
  funext s;cases s with
  | aux a=>cases a <;> simp [partialBank,cleared,cleanup]
  | _=>rfl
/-- No helper remains after the actual complete fixed inventory. -/
theorem mass_full (v:Values):mass v 16=0:=by
  unfold mass
  rw [←cleanup_length,List.drop_length]
  rfl
/-- The next actual helper has not appeared in any earlier fixed drain site. -/
theorem fresh (n:Nat) (hn:n<16):(cleanup[n]'(by simpa only [cleanup_length] using hn))∉cleanup.take n:=by
  have hl:n<cleanup.length:=by simpa only [cleanup_length] using hn
  have hd:List.Disjoint (cleanup.take n) (cleanup.drop n):=List.disjoint_of_nodup_append (by
    rw [List.take_append_drop]
    exact cleanup_nodup)
  have hm:(cleanup[n]'(by simpa only [cleanup_length] using hn))∈cleanup.drop n:=by rw [List.drop_eq_getElem_cons hl];exact List.mem_cons_self
  exact fun h=>(List.disjoint_left.mp hd) h hm
/-- Every actual drain sees exactly the original remaining physical helper bytes. -/
theorem partial_next (v:Values) (n:Nat) (hn:n<16):partialBank v n (.aux (cleanup[n]'(by simpa only [cleanup_length] using hn)))=v (.aux (cleanup[n]'(by simpa only [cleanup_length] using hn))):=by
  simp only [partialBank,fresh n hn,ite_false]
/-- One actual helper emptying is exactly the next partialBank physical bank. -/
theorem partial_update (v:Values) (n:Nat) (hn:n<16):
    Function.update (partialBank v n) (.aux (cleanup[n]'(by simpa only [cleanup_length] using hn))) []=partialBank v (n+1):=by
  have hl:n<cleanup.length:=by simpa only [cleanup_length] using hn
  have ht:=List.take_succ_eq_append_getElem hl
  funext s
  cases s with
  | aux a=>
    by_cases ha:a=(cleanup[n]'(by simpa only [cleanup_length] using hn))
    · subst a
      simp only [Function.update_same,partialBank,ht,List.mem_append,List.mem_singleton_self,or_true,ite_true]
    · rw [Function.update_of_ne (show Slot.aux a≠Slot.aux (cleanup[n]'(by simpa only [cleanup_length] using hn)) by intro h;exact ha (Slot.aux.inj h))]
      simp only [partialBank,ht,List.mem_append,List.mem_singleton,ha,or_false]
  | _=>rfl
/-- Exact remaining mass decreases by precisely the actual word consumed at this real drain site. -/
theorem mass_step (v:Values) (n:Nat) (hn:n<16):mass v n=(v (.aux (cleanup[n]'(by simpa only [cleanup_length] using hn)))).length+mass v (n+1):=by
  have hl:n<cleanup.length:=by simpa only [cleanup_length] using hn
  unfold mass
  rw [List.drop_eq_getElem_cons hl]
  rfl
/-- Literal next finite code site matches the proof-side successor index. -/
theorem code_at (n:Nat) (hn:n<16):
    program (labelAt n)=.call (.drain (address (.aux (cleanup[n]'(by simpa only [cleanup_length] using hn))))) (labelAt (n+1)):=by
  have hrole:cleanupRole ⟨n,hn⟩=address (.aux (cleanup[n]'(by simpa only [cleanup_length] using hn))):=rfl
  rw [labelAt,dite_eq_left hn,program,hrole]
  by_cases h:n<15
  · have hs:n+1<16:=by omega
    simp only [h,hs,dite_eq_left,labelAt]
  · have hs:¬n+1<16:=by omega
    simp only [h,hs,labelAt]
/-- Full actual cleanup loop pays each helper byte and every real drain call/return. -/
theorem loop (v:Values) (n r:Nat) (hnr:n+r=16):
    Runs program (mass v n+3*r) (labelAt n) (data (partialBank v n)) (ctl .done) (data (cleared v)):=by
  induction r generalizing n with
  | zero=>
    have hn:n=16:=by omega
    subst n
    simp only [mass_full,Nat.mul_zero,Nat.zero_add,partial_full]
    exact runs_refl program (ctl .done) (data (cleared v))
  | succ r ih=>
    have hn:n<16:=by omega
    have h0:=drain_call (labelAt n) (labelAt (n+1)) (.aux (cleanup[n]'(by simpa only [cleanup_length] using hn))) (partialBank v n) (code_at n hn)
    rw [partial_next v n hn,partial_update v n hn] at h0
    have h1:=ih (n+1) (by omega)
    have h:=join h0 h1
    have hm:=mass_step v n hn
    convert h using 1
    omega
/-- Complete actual sixteen-helper cleanup, immediately before the real final halt. -/
theorem source_run (v:Values):
    Runs program (mass v 0+48) (ctl (.clear 0)) (data v) (ctl .done) (data (cleared v)):=by
  have h:=loop v 0 16 (by omega)
  rw [partial_zero] at h
  exact h
end RiemannGaussian.SemiprimeD1StackRecoveryFinishCleanup
