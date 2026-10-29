/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootPhaseGridEncoding
/-! # Real copied exponent bytes, binary-zero pushes and wrapped enumeration -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1500000
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRootPhaseGridPrimitives
open SemiprimeD1StackRootPhaseGrid SemiprimeD1StackRootPhaseGridEncoding
open SemiprimeD1StackProcedureTrace
local notation "ctl" => (Sum.inl : Control→Label)
/-- Exact composition of actual fragments of the same fixed126-role source. -/
theorem compose {m n:Nat} {pc mid next:Label} {before middle after:Stack→List Bool}
    (h:Runs program m pc before mid middle) (g:Runs program n mid middle next after) :
    Runs program (m+n) pc before next after :=runs_trans program _ _ _ _ _ _ _ _ h g
/-- One actual binary-zero-word push changes only its literal enum word. -/
theorem update_word (root:R.Stack→List Bool) (word counts work out next:List Bool) :
    Function.update (view root word counts work out) (enumStack .word) next=view root next counts work out :=by
  funext k;cases k with
  | inl k=>rfl
  | inr k=>cases k with
    | inl k=>cases k <;> rfl
    | inr i=>rfl
/-- One actual count-byte pop retains every source and enumeration word. -/
theorem update_count (root:R.Stack→List Bool) (word counts work out next:List Bool) :
    Function.update (view root word counts work out) count next=view root word next work out :=by
  funext k;cases k with
  | inl k=>rfl
  | inr k=>cases k with
    | inl k=>cases k <;> rfl
    | inr i=>fin_cases i <;> rfl
/-- Actual true guard bit chooses copying; it is never replaced by an evaluator. -/
theorem branch_true (root:R.Stack→List Bool) (hg:root R.output=[true]) :
    Runs program 1 (ctl .branch) (prepared root) (ctl .copy) (prepared root) :=by
  apply one_base program _ _ (.peek guard (ctl .done) (ctl .done) (ctl .copy)) _ _ rfl
  · change some (SemiprimeD1StackBytecode.choose (ctl .done) (ctl .done) (ctl .copy) (root R.output).head?)=_
    rw [hg];rfl
  · rfl
/-- Actual false guard skips copying, zero construction and every enumeration instruction. -/
theorem branch_false (root:R.Stack→List Bool) (hg:root R.output=[false]) :
    Runs program 1 (ctl .branch) (prepared root) (ctl .done) (prepared root) :=by
  apply one_base program _ _ (.peek guard (ctl .done) (ctl .done) (ctl .copy)) _ _ rfl
  · change some (SemiprimeD1StackBytecode.choose (ctl .done) (ctl .done) (ctl .copy) (root R.output).head?)=_
    rw [hg];rfl
  · rfl
/-- The parent exponent is read from its actual source word and retained by real Copy. -/
theorem copy_exponent (root:R.Stack→List Bool) (word:List Bool)
    (ha:root (R.sourceStack SemiprimeD1StackRootParameters.exponent)=word) :
    Runs program (5*word.length+4) (ctl .copy) (prepared root) (ctl .seed) (view root [] word [] []) :=by
  apply included_call program copyStack copyLabel copy_injective SemiprimeD1StackCopy.code 0
    (fun _=>rfl) (ctl .copy) (ctl .seed) rfl (5*word.length+3)
    (SemiprimeD1StackCopy.state 0 none word [] []) (SemiprimeD1StackCopy.done word (word++[]))
  · rfl
  · rfl
  · exact SemiprimeD1StackCopy.copy_words word [] none
  · constructor
    · intro i;fin_cases i
      · exact ha
      · rfl
      · rfl
    · intro k _;rfl
  · constructor
    · intro i;fin_cases i
      · exact ha
      · change word=word++[];exact (List.append_nil word).symm
      · rfl
    · intro k hk
      cases k with
      | inl k=>rfl
      | inr k=>cases k with
        | inl k=>rfl
        | inr i=>
          fin_cases i
          · exact (hk 1 rfl).elim
          · rfl
/-- One literal false bit seeds a nonempty binary zero word, even for exponent zero. -/
theorem seed_zero (root:R.Stack→List Bool) (counts:List Bool) :
    Runs program 1 (ctl .seed) (view root [] counts [] []) (ctl .fill) (view root [false] counts [] []) :=by
  apply one_base program _ _ (.push (enumStack .word) false (ctl .fill)) _ _ rfl
  · rfl
  · exact update_word _ _ _ _ _ _
/-- Each actual exponent byte is popped and pays one literal false push. The
result has a linear binary width, never a unary2^a initialization. -/
theorem fill_zero (root:R.Stack→List Bool) (n k:Nat) :
    Runs program (2*n+1) (ctl .fill) (view root (List.replicate k false) (List.replicate n true) [] [])
      (ctl .enumerate) (view root (List.replicate (n+k) false) [] [] []) :=by
  induction n generalizing k with
  | zero=>
    apply one_base program _ _ (.pop count (ctl .enumerate) (ctl .zero) (ctl .zero)) _ _ rfl
    · rfl
    · change Function.update (view root (List.replicate k false) [] [] []) count []=
        view root (List.replicate (0+k) false) [] [] []
      simpa only [Nat.zero_add] using update_count root (List.replicate k false) [] [] [] []
  | succ n ih=>
    have h0:Runs program 1 (ctl .fill) (view root (List.replicate k false) (List.replicate (n+1) true) [] [])
        (ctl .zero) (view root (List.replicate k false) (List.replicate n true) [] []):=by
      apply one_base program _ _ (.pop count (ctl .enumerate) (ctl .zero) (ctl .zero)) _ _ rfl
      · rfl
      · change Function.update (view root (List.replicate k false) (List.replicate (n+1) true) [] []) count
          (List.replicate (n+1) true).tail=_
        simp only [List.replicate_succ,List.tail_cons]
        exact update_count _ _ _ _ _ _
    have h1:Runs program 1 (ctl .zero) (view root (List.replicate k false) (List.replicate n true) [] [])
        (ctl .fill) (view root (List.replicate (k+1) false) (List.replicate n true) [] []):=by
      apply one_base program _ _ (.push (enumStack .word) false (ctl .fill)) _ _ rfl
      · rfl
      · change Function.update (view root (List.replicate k false) (List.replicate n true) [] []) (enumStack .word)
          (false::List.replicate k false)=_
        simpa only [List.replicate_succ] using update_word root (List.replicate k false) (List.replicate n true) [] [] (false::List.replicate k false)
    have hh:=compose (compose h0 h1) (ih (k+1))
    simpa only [show 1+1+(2*n+1)=2*(n+1)+1 by omega,show n+(k+1)=(n+1)+k by omega] using hh
/-- The real frozen enumerator logs the binary zero, repeatedly increments to
overflow and emits every phase word in chronological order, clearing all its work. -/
theorem enumerate_call (root:R.Stack→List Bool) (a:Nat) :
    ∃t≤100*(a+2)*2^(a+1)+10, Runs program (t+1) (ctl .enumerate) (ready root a)
      (ctl .done) (finished root true a) :=by
  obtain ⟨t,ht,hr⟩:=SemiprimeD1StackAssignmentEnumerationBounds.zero_source_run (a+1)
  refine ⟨t,by simpa only [Nat.add_assoc] using ht,?_⟩
  apply SemiprimeD1StackProcedureCallsTrace.included_call program enumStack enumLabel
    (by intro i j h;exact Sum.inl.inj (Sum.inr.inj h)) A.code (A.control .bodyCall)
    (fun _=>rfl) (ctl .enumerate) (ctl .done) rfl t
    (SemiprimeD1StackCalls.initial (show A.Stack from .word) (A.control .bodyCall) (List.replicate (a+1) false))
    (SemiprimeD1StackCalls.final (show A.Stack from .output) (grid a)) _ _ rfl rfl rfl rfl hr
  · constructor
    · intro k;cases k <;> rfl
    · intro k _;rfl
  · constructor
    · intro k;cases k <;> rfl
    · intro k hk
      cases k with
      | inl k=>rfl
      | inr k=>cases k with
        | inl k=>exact (hk k rfl).elim
        | inr i=>rfl
end RiemannGaussian.SemiprimeD1StackRootPhaseGridPrimitives
