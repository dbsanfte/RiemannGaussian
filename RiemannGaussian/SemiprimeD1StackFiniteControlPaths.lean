/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackFiniteControlExecution

/-! # Whole-path refinement for finite-register lowering
Each actual source step is expanded into literal bytecode, paying its fixed
syntactic depth. No source report field is converted into machine time.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1StackFiniteControlPaths
open Turing Turing.TM2 SemiprimeD1StackFiniteControl SemiprimeD1StackFiniteControlExecution

/-- Concatenate actual bytecode execution paths. -/
theorem Executes.trans {K G : Type} [DecidableEq K] {C : G → B.Instruction K G}
    {n m : ℕ} {a b c : B.State K G} (h : Executes C n a b) (g : Executes C m b c) :
    Executes C (n+m) a c := by
  induction h with
  | refl => simpa using g
  | @next n a d b hs ht ih =>
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using Executes.next hs (ih g)

/-- Actual bytecode paths give its real source interpreter equation. -/
theorem Executes.iterates {K G : Type} [DecidableEq K] {C : G → B.Instruction K G}
    {n : ℕ} {a b : B.State K G} (h : Executes C n a b) : B.run C n a=some b := by
  induction h with
  | refl => rfl
  | @next n a d b hs ht ih =>
    change ((fun x : Option (B.State K G) => x.bind (B.step C))^[n+1]) (some a)=some b
    rw [Function.iterate_succ_apply]
    simpa only [SemiprimeD1StackBytecode.run,Option.bind_some,hs] using ih

/-- A literal source TM2 transition sequence. -/
inductive SourcePath {K L S : Type} [DecidableEq K] (P : L → Stmt (fun _ : K => Bool) L S) :
    ℕ → Cfg (fun _ : K => Bool) L S → Cfg (fun _ : K => Bool) L S → Prop
  | refl (c) : SourcePath P 0 c c
  | next {n c d e} : TM2.step P c=some d → SourcePath P n d e → SourcePath P (n+1) c e

/-- Recover actual source paths from actual iterate equations, without choosing outputs. -/
theorem sourcePath_of_iterates {K L S : Type} [DecidableEq K] (P : L → Stmt (fun _ : K => Bool) L S)
    (n : ℕ) (a b : Cfg (fun _ : K => Bool) L S)
    (h : ((fun c : Option (Cfg (fun _ : K => Bool) L S) => c.bind (TM2.step P))^[n])
      (some a)=some b) : SourcePath P n a b := by
  induction n generalizing a with
  | zero => cases h; exact .refl _
  | succ n ih =>
    rw [Function.iterate_succ_apply] at h
    cases hs : TM2.step P a with
    | none =>
      have hz : ((fun c : Option (Cfg (fun _ : K => Bool) L S) => c.bind (TM2.step P))^[n])
          none=none := Function.iterate_fixed rfl n
      simp only [Option.bind_some,hs,hz] at h
      cases h
    | some c =>
      apply SourcePath.next hs
      apply ih c
      simpa only [Option.bind_some,hs] using h

/-- Every actual transition expands into fixed literal instructions with exact payload. -/
theorem step_refines {K L S : Type} [DecidableEq K]
    (P : L → Stmt (fun _ : K => Bool) L S) (D : ℕ) (hD : ∀l,depth (P l)≤D)
    (a b : Cfg (fun _ : K => Bool) L S) (hs : TM2.step P a=some b) (initialFlag : Option Bool) :
    ∃n≤D,∃flag,Executes (code P) n (destination (entry P) a initialFlag)
      (destination (entry P) b flag) := by
  rcases a with ⟨pc,v,store⟩
  cases pc with
  | none => simp [TM2.step] at hs
  | some l =>
    simp only [TM2.step,Option.some.injEq] at hs
    subst b
    obtain ⟨n,hn,flag,he⟩ := statement_exec (code P) (entry P) (P l)
      (fun v p => ⟨l,v,p⟩) (fun _ _ => rfl) v store initialFlag
    exact ⟨n,hn.trans (hD l),flag,he⟩

/-- Whole actual paths retain payload and multiply time by only static syntax depth. -/
theorem path_refines {K L S : Type} [DecidableEq K]
    (P : L → Stmt (fun _ : K => Bool) L S) (D : ℕ) (hD : ∀l,depth (P l)≤D)
    {n : ℕ} {a b : Cfg (fun _ : K => Bool) L S} (h : SourcePath P n a b)
    (initialFlag : Option Bool) :
    ∃m≤D*n,∃flag,Executes (code P) m (destination (entry P) a initialFlag)
      (destination (entry P) b flag) := by
  induction h generalizing initialFlag with
  | refl c => exact ⟨0,by omega,initialFlag,.refl _⟩
  | @next n a d b hs ht ih =>
    obtain ⟨m,hm,flag,hfirst⟩ := step_refines P D hD a d hs initialFlag
    obtain ⟨k,hk,finalFlag,hlast⟩ := ih flag
    exact ⟨m+k,by simp only [Nat.mul_add,Nat.mul_one]; omega,finalFlag,Executes.trans hfirst hlast⟩

/-- Actual exact source run to a halted payload yields exact finite bytecode execution. -/
theorem halted_run {K L S : Type} [DecidableEq K]
    (P : L → Stmt (fun _ : K => Bool) L S) (D : ℕ) (hD : ∀l,depth (P l)≤D)
    (main : L) (initial final : S) (input output : K → List Bool) (time : ℕ)
    (h : ((fun c : Option (Cfg (fun _ : K => Bool) L S) => c.bind (TM2.step P))^[time])
      (some ⟨some main,initial,input⟩)=some ⟨none,final,output⟩) :
    ∃m≤D*time,B.run (code P) m ⟨some (entry P main initial),none,input⟩=
      some ⟨none,none,output⟩ := by
  have hp := sourcePath_of_iterates P time _ _ h
  obtain ⟨m,hm,flag,he⟩ := path_refines P D hD hp none
  exact ⟨m,hm,Executes.iterates he⟩

/-- A proof-only time certificate for the ACTUAL compiled finite machine.
Classical selection chooses only the already-proved path length; the executable
code/machine above is entirely computable and has no certificate dependency. -/
noncomputable def haltedInTime {K L S : Type} [DecidableEq K] [Fintype K] [Fintype L] [Fintype S]
    (P : L → Stmt (fun _ : K => Bool) L S) (D : ℕ) (hD : ∀l,depth (P l)≤D)
    (inputStack outputStack : K) (main : L) (initial final : S)
    (input output : K → List Bool) (time : ℕ)
    (h : ((fun c : Option (Cfg (fun _ : K => Bool) L S) => c.bind (TM2.step P))^[time])
      (some ⟨some main,initial,input⟩)=some ⟨none,final,output⟩) :
    StateTransition.EvalsToInTime (machine P inputStack outputStack main initial).step
      (SemiprimeD1StackBytecode.configuration ⟨some (entry P main initial),none,input⟩)
      (some (SemiprimeD1StackBytecode.configuration ⟨none,none,output⟩)) (D*time) := by
  have hx := halted_run P D hD main initial final input output time h
  let m := Classical.choose hx
  have hm := Classical.choose_spec hx
  apply SemiprimeD1StackBytecode.evalsCorrect inputStack outputStack (entry P main initial) (code P)
  exact ⟨⟨m,hm.2⟩,hm.1⟩

end RiemannGaussian.SemiprimeD1StackFiniteControlPaths
