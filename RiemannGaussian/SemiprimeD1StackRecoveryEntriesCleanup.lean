/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryEntriesPrimitives
/-! # All seven actual per-row metadata/cache/payload drains
Every retained row field and selected cache/payload is physically cleared only
after its output chunk was logged. Original tapes and global history remain.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 65536
namespace RiemannGaussian.SemiprimeD1StackRecoveryEntriesCleanup
open SemiprimeD1StackRecoveryEntries SemiprimeD1StackRecoveryEntriesState
open SemiprimeD1StackRecoveryEntriesPrimitives SemiprimeD1StackProcedureTrace
local notation "ctl"=>Label.local
/-- Fixed inventory of seven physically cleared per-row words. -/
def cleanup:List Aux:=[.node,.index,.sign,.magnitude,.denominator,.selectedRow,.child]
/-- Exactly seven actual source words, not a supplied data-dependent cleanup count. -/
theorem cleanup_length:cleanup.length=7:=rfl
/-- No per-row field is omitted through a duplicate drain. -/
theorem cleanup_nodup:cleanup.Nodup:=by decide
/-- Actual partial bank after the fixed prefix of performed physical drains. -/
def partialBank (w:Aux → List Bool) (n:Nat):Aux → List Bool:=fun a=>if a∈cleanup.take n then [] else w a
/-- Actual complete post-row cleanup, retaining all original/logger words. -/
def cleared (w:Aux → List Bool):Aux → List Bool:=fun a=>if a∈cleanup then [] else w a
/-- Proof-only position in the actual seven finite drain sites. -/
def labelAt (n:Nat):Label:=if h:n<7 then ctl (.clear ⟨n,h⟩) else ctl .loop
/-- Actual remaining physical payload bytes, not a legacy arithmetic report. -/
def mass (w:Aux → List Bool) (n:Nat):Nat:=((cleanup.drop n).map (fun a=>(w a).length)).sum
/-- The initial state has no advised cleanup updates. -/
theorem partial_zero (w:Aux → List Bool):partialBank w 0=w:=by funext a;simp [partialBank]
/-- The actual complete static inventory is exactly the final cleared bank. -/
theorem partial_full (w:Aux → List Bool):partialBank w 7=cleared w:=by funext a;cases a <;> rfl
/-- No physical payload remains in the exhausted inventory. -/
theorem mass_full (w:Aux → List Bool):mass w 7=0:=by unfold mass;rw [←cleanup_length,List.drop_length];rfl
/-- Static actual source role at each finite drain site. -/
theorem target_at (part:Fin 7):clearTarget part=aux (cleanup[part.val]'(by simpa only [cleanup_length] using part.isLt)):=by fin_cases part <;> rfl
/-- Exact unread current word has not appeared at any earlier finite drain site. -/
theorem fresh (n:Nat) (hn:n<7):(cleanup[n]'(by simpa only [cleanup_length] using hn))∉cleanup.take n:=by
  have hl:n<cleanup.length:=by simpa only [cleanup_length] using hn
  have hd:List.Disjoint (cleanup.take n) (cleanup.drop n):=List.disjoint_of_nodup_append (by rw [List.take_append_drop];exact cleanup_nodup)
  have hm:(cleanup[n]'(by simpa only [cleanup_length] using hn))∈cleanup.drop n:=by rw [List.drop_eq_getElem_cons hl];exact List.mem_cons_self
  exact fun h=>(List.disjoint_left.mp hd) h hm
/-- Each actual drain sees exactly the corresponding still-live source word. -/
theorem partial_next (w:Aux → List Bool) (n:Nat) (hn:n<7):
    partialBank w n (cleanup[n]'(by simpa only [cleanup_length] using hn))=w (cleanup[n]'(by simpa only [cleanup_length] using hn)):=by
  simp only [partialBank,fresh n hn,ite_false]
/-- One real physical emptying advances exactly one fixed actual inventory site. -/
theorem partial_update (w:Aux → List Bool) (n:Nat) (hn:n<7):
    Function.update (partialBank w n) (cleanup[n]'(by simpa only [cleanup_length] using hn)) []=partialBank w (n+1):=by
  have hl:n<cleanup.length:=by simpa only [cleanup_length] using hn
  have ht:=List.take_succ_eq_append_getElem hl
  funext a
  by_cases ha:a=(cleanup[n]'(by simpa only [cleanup_length] using hn))
  · subst a
    simp only [Function.update_self,partialBank,ht,List.mem_append,List.mem_singleton_self,or_true,ite_true]
  · rw [Function.update_of_ne ha]
    simp only [partialBank,ht,List.mem_append,List.mem_singleton,ha,or_false]
/-- Exact remaining byte mass decreases by precisely the physically consumed word. -/
theorem mass_step (w:Aux → List Bool) (n:Nat) (hn:n<7):
    mass w n=(w (cleanup[n]'(by simpa only [cleanup_length] using hn))).length+mass w (n+1):=by
  have hl:n<cleanup.length:=by simpa only [cleanup_length] using hn
  unfold mass
  rw [List.drop_eq_getElem_cons hl]
  rfl
/-- The real finite program matches each declared next physical drain. -/
theorem code_at (n:Nat) (hn:n<7):
    program (labelAt n)=.base (.pop (aux (cleanup[n]'(by simpa only [cleanup_length] using hn)))
      (labelAt (n+1)) (labelAt n) (labelAt n)):=by
  have hrole:=target_at ⟨n,hn⟩
  change clearTarget ⟨n,hn⟩=aux (cleanup[n]'(by simpa only [cleanup_length] using hn)) at hrole
  rw [labelAt,dite_eq_left hn,program,hrole]
  have hnext:nextClear ⟨n,hn⟩=labelAt (n+1):=by rfl
  rw [hnext]
/-- All seven physical EOF loops pay every byte and each final EOF test. -/
theorem loop (children:List Bool) (w:Aux → List Bool) (n r:Nat) (hnr:n+r=7):
    Runs program (mass w n+r) (labelAt n) (data children (partialBank w n)) (ctl .loop) (data children (cleared w)):=by
  induction r generalizing n with
  | zero=>
    have hn:n=7:=by omega
    subst n
    simp only [mass_full,Nat.add_zero,partial_full]
    exact runs_refl program (ctl .loop) (data children (cleared w))
  | succ r ih=>
    have hn:n<7:=by omega
    have h0:=drain_run (labelAt n) (labelAt (n+1)) (cleanup[n]'(by simpa only [cleanup_length] using hn)) children
      (partialBank w n) (w (cleanup[n]'(by simpa only [cleanup_length] using hn))) (code_at n hn) (partial_next w n hn)
    rw [partial_update w n hn] at h0
    have h1:=ih (n+1) (by omega)
    have h:=join h0 h1
    have hm:=mass_step w n hn
    convert h using 1
    omega
/-- Complete actual post-entry cleanup returns to the row-reader loop. -/
theorem source_run (children:List Bool) (w:Aux → List Bool):
    Runs program (mass w 0+7) (ctl (.clear 0)) (data children w) (ctl .loop) (data children (cleared w)):=by
  have h:=loop children w 0 7 (by omega)
  rw [partial_zero] at h
  exact h
/-- Exact actual post-row logical word view, with all seven per-row acquired words clear. -/
theorem cleared_words (rows reader:List Bool) (fields:Fin 5 → List Bool) (row child valid history buffer out:List Bool):
    cleared (words rows reader fields row child valid history buffer out)=words rows reader (fun _=>[]) [] [] valid history buffer out:=by
  funext a;cases a <;> rfl
end RiemannGaussian.SemiprimeD1StackRecoveryEntriesCleanup
