/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackFiniteControl

/-! # Exact execution of finite-register elimination
The semantic induction accounts for every literal push/pop/peek/load/branch,
including the native register flags now held entirely in fixed finite labels.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1StackFiniteControlExecution
open Turing Turing.TM2 SemiprimeD1StackFiniteControl

/-- Exact source-bytecode paths for a fixed instruction table. -/
inductive Executes {K G : Type} [DecidableEq K] (C : G → B.Instruction K G) :
    ℕ → B.State K G → B.State K G → Prop
  | refl (c) : Executes C 0 c c
  | next {n c d e} : B.step C c=some d → Executes C n d e → Executes C (n+1) c e

/-- Source TM2 finite-register state erased into fixed label/data-byte state. -/
def destination {K L S G : Type} (jump : L → S → G)
    (c : Cfg (fun _ : K => Bool) L S) (flag : Option Bool) : B.State K G :=
  match c.l with
  | none => ⟨none,none,c.stk⟩
  | some l => ⟨some (jump l c.var),flag,c.stk⟩

/-- Every statement executes into the literal bytecode at bounded syntactic cost.
The code equation is internal: the final compiler supplies it by reflexivity. -/
theorem statement_exec {K L S G : Type} [DecidableEq K]
    (C : G → B.Instruction K G) (jump : L → S → G)
    (q : Stmt (fun _ : K => Bool) L S) (enter : S → Locations q → G)
    (hc : ∀v p,C (enter v p)=compileLocal jump q enter v p)
    (v : S) (store : K → List Bool) (initialFlag : Option Bool) :
    ∃n≤depth q,∃flag,Executes C n ⟨some (enter v (root q)),initialFlag,store⟩
      (destination jump (TM2.stepAux q v store) flag) := by
  induction q generalizing v store initialFlag with
  | push k f q ih =>
    let ent := fun v p => enter v (Sum.inr p)
    have hd : ∀v p,C (ent v p)=compileLocal jump q ent v p := by
      intro v p
      exact hc v (.inr p)
    obtain ⟨n,hn,flag,he⟩ := ih ent hd v (Function.update store k (f v::store k)) initialFlag
    have hs : B.step C ⟨some (enter v (root (.push k f q))),initialFlag,store⟩=
        some ⟨some (ent v (root q)),initialFlag,Function.update store k (f v::store k)⟩ := by
      simp only [SemiprimeD1StackBytecode.step,Option.map_some]
      rw [hc]
      simp [root,compileLocal,SemiprimeD1StackBytecode.execute,ent]
    refine ⟨n+1,by simp only [depth]; omega,flag,?_⟩
    exact Executes.next hs he
  | peek k f q ih =>
    let ent := fun v p => enter v (Sum.inr p)
    have hd : ∀v p,C (ent v p)=compileLocal jump q ent v p := by
      intro v p
      exact hc v (.inr p)
    obtain ⟨n,hn,flag,he⟩ := ih ent hd (f v (store k).head?) store (store k).head?
    have hs : B.step C ⟨some (enter v (root (.peek k f q))),initialFlag,store⟩=
        some ⟨some (ent (f v (store k).head?) (root q)),(store k).head?,store⟩ := by
      simp only [SemiprimeD1StackBytecode.step,Option.map_some]
      rw [hc]
      simp only [root,compileLocal,SemiprimeD1StackBytecode.execute]
      cases hbit : (store k).head? with
      | none => rfl
      | some b => cases b <;> rfl
    refine ⟨n+1,by simp only [depth]; omega,flag,?_⟩
    exact Executes.next hs he
  | pop k f q ih =>
    let ent := fun v p => enter v (Sum.inr p)
    have hd : ∀v p,C (ent v p)=compileLocal jump q ent v p := by
      intro v p
      exact hc v (.inr p)
    obtain ⟨n,hn,flag,he⟩ := ih ent hd (f v (store k).head?)
      (Function.update store k (store k).tail) (store k).head?
    have hs : B.step C ⟨some (enter v (root (.pop k f q))),initialFlag,store⟩=
        some ⟨some (ent (f v (store k).head?) (root q)),(store k).head?,
          Function.update store k (store k).tail⟩ := by
      simp only [SemiprimeD1StackBytecode.step,Option.map_some]
      rw [hc]
      simp only [root,compileLocal,SemiprimeD1StackBytecode.execute]
      cases hbit : (store k).head? with
      | none => rfl
      | some b => cases b <;> rfl
    refine ⟨n+1,by simp only [depth]; omega,flag,?_⟩
    exact Executes.next hs he
  | load f q ih =>
    let ent := fun v p => enter v (Sum.inr p)
    have hd : ∀v p,C (ent v p)=compileLocal jump q ent v p := by
      intro v p
      exact hc v (.inr p)
    obtain ⟨n,hn,flag,he⟩ := ih ent hd (f v) store initialFlag
    have hs : B.step C ⟨some (enter v (root (.load f q))),initialFlag,store⟩=
        some ⟨some (ent (f v) (root q)),initialFlag,store⟩ := by
      simp only [SemiprimeD1StackBytecode.step,Option.map_some]
      rw [hc]
      simp [root,compileLocal,SemiprimeD1StackBytecode.execute,ent]
    refine ⟨n+1,by simp only [depth]; omega,flag,?_⟩
    exact Executes.next hs he
  | branch f q r ihq ihr =>
    cases hb : f v with
    | false =>
      let ent := fun v p => enter v (Sum.inr (Sum.inr p))
      have hd : ∀v p,C (ent v p)=compileLocal jump r ent v p := by
        intro v p
        exact hc v (.inr (.inr p))
      obtain ⟨n,hn,flag,he⟩ := ihr ent hd v store initialFlag
      have hs : B.step C ⟨some (enter v (root (.branch f q r))),initialFlag,store⟩=
          some ⟨some (ent v (root r)),initialFlag,store⟩ := by
        simp only [SemiprimeD1StackBytecode.step,Option.map_some]
        rw [hc]
        simp [root,compileLocal,SemiprimeD1StackBytecode.execute,ent,hb]
      refine ⟨n+1,by simp only [depth]; omega,flag,?_⟩
      simpa only [TM2.stepAux,hb,Bool.cond_false] using Executes.next hs he
    | true =>
      let ent := fun v p => enter v (Sum.inr (Sum.inl p))
      have hd : ∀v p,C (ent v p)=compileLocal jump q ent v p := by
        intro v p
        exact hc v (.inr (.inl p))
      obtain ⟨n,hn,flag,he⟩ := ihq ent hd v store initialFlag
      have hs : B.step C ⟨some (enter v (root (.branch f q r))),initialFlag,store⟩=
          some ⟨some (ent v (root q)),initialFlag,store⟩ := by
        simp only [SemiprimeD1StackBytecode.step,Option.map_some]
        rw [hc]
        simp [root,compileLocal,SemiprimeD1StackBytecode.execute,ent,hb]
      refine ⟨n+1,by simp only [depth]; omega,flag,?_⟩
      simpa only [TM2.stepAux,hb,Bool.cond_true] using Executes.next hs he
  | goto f =>
    refine ⟨1,le_rfl,initialFlag,Executes.next ?_ (Executes.refl _)⟩
    simp only [SemiprimeD1StackBytecode.step,Option.map_some]
    rw [hc]
    simp [root,compileLocal,SemiprimeD1StackBytecode.execute,destination,TM2.stepAux]
  | halt =>
    refine ⟨1,le_rfl,none,Executes.next ?_ (Executes.refl _)⟩
    simp only [SemiprimeD1StackBytecode.step,Option.map_some]
    rw [hc]
    simp [root,compileLocal,SemiprimeD1StackBytecode.execute,destination,TM2.stepAux]

end RiemannGaussian.SemiprimeD1StackFiniteControlExecution
