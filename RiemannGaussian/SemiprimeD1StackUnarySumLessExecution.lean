/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackUnarySumLess
/-! # Exact execution of the physical radix-digit sum comparison -/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1StackUnarySumLessExecution
open Turing Turing.TM2
open SemiprimeD1StackUnarySumLess
open SemiprimeD1StackUnaryDivmod (unary unary_succ)
open SemiprimeD1StackFiniteControlPaths (SourcePath)

theorem trans {m n : ℕ} {a b c : Cfg Alphabet PC (Option Bool)}
    (h : Executes m a b) (g : Executes n b c) : Executes (m+n) a c := by
  induction h with
  | refl => simpa using g
  | next hs ht ih => simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using SourcePath.next hs (ih g)

/-- Actual draining of rejected digit payloads. -/
theorem reject_exec (m : ℕ) (flag : Option Bool) :
    Executes (m+1) (cfg (some .reject) flag (unary m) [] [] [])
      (cfg (some .fail) none [] [] [] []) := by
  induction m generalizing flag with
  | zero =>
    apply SourcePath.next ?_ (.refl _)
    simp [program,cfg,contents,unary,TM2.step,TM2.stepAux]
  | succ m ih =>
    have hs : TM2.step program (cfg (some .reject) flag (unary (m+1)) [] [] [])=
        some (cfg (some .reject) (some true) (unary m) [] [] []) := by
      simp [program,cfg,contents,unary_succ,TM2.step,TM2.stepAux]
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using SourcePath.next hs (ih (some true))

/-- Actual draining of the unused positive limit tail. -/
theorem clear_exec (d : ℕ) (flag : Option Bool) :
    Executes (d+1) (cfg (some .clear) flag [] [] (unary d) [])
      (cfg (some .accept) none [] [] [] []) := by
  induction d generalizing flag with
  | zero =>
    apply SourcePath.next ?_ (.refl _)
    simp [program,cfg,contents,unary,TM2.step,TM2.stepAux]
  | succ d ih =>
    have hs : TM2.step program (cfg (some .clear) flag [] [] (unary (d+1)) [])=
        some (cfg (some .clear) (some true) [] [] (unary d) []) := by
      simp [program,cfg,contents,unary_succ,TM2.step,TM2.stepAux]
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using SourcePath.next hs (ih (some true))

/-- Exact finite comparison-loop transition count. -/
def compareTime : ℕ→ℕ→ℕ
  | 0,0=>3
  | 0,d+1=>d+5
  | m+1,0=>m+4
  | m+1,d+1=>2+compareTime m d

/-- Exact strict comparison, with the output produced by actual finite control. -/
theorem compare_exec (m d : ℕ) (flag : Option Bool) :
    Executes (compareTime m d) (cfg (some .compare) flag (unary m) [] (unary d) [])
      (cfg none none [] [] [] [decide (m<d)]) := by
  induction m generalizing d flag with
  | zero =>
    cases d with
    | zero =>
      have hs1 : Executes 1 (cfg (some .compare) flag [] [] [] [])
          (cfg (some .test) none [] [] [] []) := by
        apply SourcePath.next ?_ (.refl _)
        simp [program,cfg,contents,TM2.step,TM2.stepAux]
      have hs2 : Executes 1 (cfg (some .test) none [] [] [] [])
          (cfg (some .fail) none [] [] [] []) := by
        apply SourcePath.next ?_ (.refl _)
        simp [program,cfg,contents,TM2.step,TM2.stepAux]
      have hs3 : Executes 1 (cfg (some .fail) none [] [] [] [])
          (cfg none none [] [] [] [false]) := by
        apply SourcePath.next ?_ (.refl _)
        simp [program,cfg,contents,TM2.step,TM2.stepAux]
      simpa [compareTime,unary] using trans hs1 (trans hs2 hs3)
    | succ d =>
      have hs1 : Executes 1 (cfg (some .compare) flag [] [] (unary (d+1)) [])
          (cfg (some .test) none [] [] (unary (d+1)) []) := by
        apply SourcePath.next ?_ (.refl _)
        simp [program,cfg,contents,TM2.step,TM2.stepAux]
      have hs2 : Executes 1 (cfg (some .test) none [] [] (unary (d+1)) [])
          (cfg (some .clear) (some true) [] [] (unary (d+1)) []) := by
        apply SourcePath.next ?_ (.refl _)
        simp [program,cfg,contents,unary_succ,TM2.step,TM2.stepAux]
      have hs3 := clear_exec (d+1) (some true)
      have hs4 : Executes 1 (cfg (some .accept) none [] [] [] [])
          (cfg none none [] [] [] [true]) := by
        apply SourcePath.next ?_ (.refl _)
        simp [program,cfg,contents,TM2.step,TM2.stepAux]
      convert trans hs1 (trans hs2 (trans hs3 hs4)) using 1 <;> simp [compareTime,unary]; omega
  | succ m ih =>
    cases d with
    | zero =>
      have hs1 : Executes 1 (cfg (some .compare) flag (unary (m+1)) [] [] [])
          (cfg (some .consume) (some true) (unary m) [] [] []) := by
        apply SourcePath.next ?_ (.refl _)
        simp [program,cfg,contents,unary_succ,TM2.step,TM2.stepAux]
      have hs2 : Executes 1 (cfg (some .consume) (some true) (unary m) [] [] [])
          (cfg (some .reject) none (unary m) [] [] []) := by
        apply SourcePath.next ?_ (.refl _)
        simp [program,cfg,contents,TM2.step,TM2.stepAux]
      have hs3 := reject_exec m none
      have hs4 : Executes 1 (cfg (some .fail) none [] [] [] [])
          (cfg none none [] [] [] [false]) := by
        apply SourcePath.next ?_ (.refl _)
        simp [program,cfg,contents,TM2.step,TM2.stepAux]
      convert trans hs1 (trans hs2 (trans hs3 hs4)) using 1 <;> simp [compareTime,unary]; omega
    | succ d =>
      have hs1 : Executes 1 (cfg (some .compare) flag (unary (m+1)) [] (unary (d+1)) [])
          (cfg (some .consume) (some true) (unary m) [] (unary (d+1)) []) := by
        apply SourcePath.next ?_ (.refl _)
        simp [program,cfg,contents,unary_succ,TM2.step,TM2.stepAux]
      have hs2 : Executes 1 (cfg (some .consume) (some true) (unary m) [] (unary (d+1)) [])
          (cfg (some .compare) (some true) (unary m) [] (unary d) []) := by
        apply SourcePath.next ?_ (.refl _)
        simp [program,cfg,contents,unary_succ,TM2.step,TM2.stepAux]
      convert trans hs1 (trans hs2 (ih d (some true))) using 1 <;> simp [compareTime]; omega

end RiemannGaussian.SemiprimeD1StackUnarySumLessExecution
