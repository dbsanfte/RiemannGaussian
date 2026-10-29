/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackBooleanEntry
/-! # Exact real Copy/read/branch/clear traces for all Boolean assignments -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace RiemannGaussian.SemiprimeD1StackBooleanEntryExecution
open SemiprimeD1StackBooleanEntry
open SemiprimeD1StackProcedureFragments (Runs one_base included_call)

/-- Every assignment is physically copied once; no read-only input oracle. -/
theorem copy_call (mode : Mode) (bits : List Bool) :
    Runs program (5*bits.length+4) (.inl (.start mode)) (data bits [] [] [])
      (.inl (.first mode)) (data bits bits [] []) := by
  apply included_call program copyStack copyLabel copyStack_injective
    SemiprimeD1StackCopy.code 0 (fun _=>rfl) (.inl (.start mode)) (.inl (.first mode)) rfl
    (5*bits.length+3) (SemiprimeD1StackCopy.state 0 none bits [] [])
    (SemiprimeD1StackCopy.done bits bits)
  · rfl
  · rfl
  · simpa only [List.append_nil] using SemiprimeD1StackCopy.copy_words bits [] none
  · constructor
    · intro k; fin_cases k <;> rfl
    · intro k hk; rfl
  · constructor
    · intro k; fin_cases k <;> rfl
    · intro k hk
      cases k with
      | assignment => rfl
      | reader => exact False.elim (hk 1 rfl)
      | scratch => rfl
      | output => rfl

/-- One actual data pop; the next label holds ONLY its physically read Boolean. -/
theorem read_one (pc empty : Label) (next : Bool→Label) (assignment : List Bool)
    (bit : Bool) (tail : List Bool)
    (hcode : program pc=.base (.pop .reader empty (next false) (next true))) :
    Runs program 1 pc (data assignment (bit::tail) [] []) (next bit) (data assignment tail [] []) := by
  apply one_base program _ _ (.pop .reader empty (next false) (next true)) _ _ hcode
  · cases bit <;> rfl
  · funext k; cases k <;> rfl

/-- The real empty-reader test is followed by a literal result push. -/
theorem finish_run (assignment : List Bool) (accepted : Bool) :
    Runs program 2 (.inl (.clear accepted)) (data assignment [] [] [])
      (.inl .done) (data assignment [] [] [accepted]) := by
  have h0 : Runs program 1 (.inl (.clear accepted)) (data assignment [] [] [])
      (.inl (.emit accepted)) (data assignment [] [] []) := by
    apply one_base program _ _ (.pop .reader (.inl (.emit accepted))
      (.inl (.clear accepted)) (.inl (.clear accepted))) _ _ rfl
    · rfl
    · funext k; cases k <;> rfl
  have h1 : Runs program 1 (.inl (.emit accepted)) (data assignment [] [] [])
      (.inl .done) (data assignment [] [] [accepted]) := by
    apply one_base program _ _ (.push .output accepted (.inl .done)) _ _ rfl
    · rfl
    · funext k; cases k <;> rfl
  exact h0.trans h1

/-- All three original ordered bits are read and actually checked. -/
theorem or_body (assignment : List Bool) (a b c : Bool) :
    Runs program 5 (.inl (.first .orGate)) (data assignment [a,b,c] [] [])
      (.inl .done) (data assignment [] [] [decide (c=(a || b))]) := by
  have h0:=read_one (.inl (.first .orGate)) (.inl (.clear false)) (afterFirst .orGate)
    assignment a [b,c] rfl
  have h1:=read_one (.inl (.orSecond a)) (.inl (.clear false))
    (fun b=>.inl (.orThird a b)) assignment b [c] rfl
  have h2:=read_one (.inl (.orThird a b)) (.inl (.clear false))
    (fun c=>.inl (.clear (decide (c=(a || b))))) assignment c [] rfl
  exact h0.trans (h1.trans (h2.trans (finish_run assignment _)))

/-- The sole original input-check bit is physically read. -/
theorem input_body (assignment : List Bool) (a : Bool) :
    Runs program 3 (.inl (.first .inputCheck)) (data assignment [a] [] [])
      (.inl .done) (data assignment [] [] [a]) := by
  have h:=read_one (.inl (.first .inputCheck)) (.inl (.clear false)) (afterFirst .inputCheck)
    assignment a [] rfl
  exact h.trans (finish_run assignment a)

/-- Both ordered subdivided equality bits are physically read. -/
theorem equality_body (assignment : List Bool) (a b : Bool) :
    Runs program 4 (.inl (.first .equality)) (data assignment [a,b] [] [])
      (.inl .done) (data assignment [] [] [decide (a=b)]) := by
  have h0:=read_one (.inl (.first .equality)) (.inl (.clear false)) (afterFirst .equality)
    assignment a [b] rfl
  have h1:=read_one (.inl (.equalSecond a)) (.inl (.clear false))
    (fun b=>.inl (.clear (decide (a=b)))) assignment b [] rfl
  exact h0.trans (h1.trans (finish_run assignment _))

/-- Actual halt resets transient flags and clears the whole return stack. -/
theorem halt_after (mode : Mode) (bits : List Bool) (accepted : Bool) (m : ℕ)
    (h : Runs program m (.inl (.start mode)) (data bits [] [] [])
      (.inl .done) (data bits [] [] [accepted])) :
    C.run program (m+1) (initial mode bits)=some (done bits accepted) := by
  obtain ⟨finish,hfinish,hAt⟩:=h [] (initial mode bits) ⟨rfl,rfl,rfl⟩
  rw [SemiprimeD1StackReturnLink.run_add,hfinish,Option.bind_some]
  rcases hAt with ⟨hpc,hd,hframes⟩
  change C.step program finish=some (done bits accepted)
  simp [C.step,SemiprimeD1StackCalls.step,hpc,program,C.execute,SemiprimeD1StackCalls.execute,
    hd,hframes,done]

/-- Closed 25-transition OR gate, with no truth/entry supplier. -/
theorem or_run (a b c : Bool) :
    C.run program 25 (initial .orGate [a,b,c])=some (done [a,b,c] (decide (c=(a || b)))) :=
  halt_after .orGate [a,b,c] _ _ ((copy_call .orGate [a,b,c]).trans (or_body [a,b,c] a b c))

/-- Closed 13-transition input check, including its actual input-preserving copy. -/
theorem input_run (a : Bool) :
    C.run program 13 (initial .inputCheck [a])=some (done [a] a) :=
  halt_after .inputCheck [a] _ _ ((copy_call .inputCheck [a]).trans (input_body [a] a))

/-- Closed 19-transition equality tensor, including real calls and cleanup. -/
theorem equality_run (a b : Bool) :
    C.run program 19 (initial .equality [a,b])=some (done [a,b] (decide (a=b))) :=
  halt_after .equality [a,b] _ _ ((copy_call .equality [a,b]).trans (equality_body [a,b] a b))

end RiemannGaussian.SemiprimeD1StackBooleanEntryExecution
