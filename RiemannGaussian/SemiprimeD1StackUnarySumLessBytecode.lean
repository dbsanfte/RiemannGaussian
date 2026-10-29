/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackUnarySumLessExecution
/-! # Actual compiled finite radix-digit comparator -/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1StackUnarySumLessBytecode
open SemiprimeD1StackUnarySumLess SemiprimeD1StackUnarySumLessExecution
open SemiprimeD1StackUnaryDivmod (unary)

theorem compareTime_le (m d : ℕ) : compareTime m d≤3*(m+d+1)+2 := by
  induction m generalizing d with
  | zero => cases d <;> simp [compareTime]; omega
  | succ m ih =>
    cases d with
    | zero => simp [compareTime]
    | succ d => have h:=ih d; simp only [compareTime]; omega

/-- The actual comparison bank is entirely cleared except its physical Boolean result. -/
theorem compare_all (m n d : ℕ) :
    Executes (n+1+compareTime (n+m) d)
      (cfg (some .join) none (unary m) (unary n) (unary d) [])
      (cfg none none [] [] [] [decide (m+n<d)]) := by
  have h:=trans (join_exec m n d none) (compare_exec (n+m) d none)
  simpa only [Nat.add_comm] using h

/-- Finite compiled control locations, fixed before operands. -/
abbrev Label := SemiprimeD1StackFiniteControl.Label program
/-- The literal lowered instruction table. -/
def code := SemiprimeD1StackFiniteControl.code program
/-- The fixed initial join-loop entry. -/
def entry : Label := SemiprimeD1StackFiniteControl.entry program .join none

theorem program_depth (pc : PC) : SemiprimeD1StackFiniteControl.depth (program pc)≤5 := by
  cases pc <;> decide

/-- A fixed included instruction table computes the comparison without native arithmetic. -/
theorem compare_run (m n d : ℕ) :
    ∃t≤30*(m+n+d+1)+10,SemiprimeD1StackBytecode.run code t
      ⟨some entry,none,contents (unary m) (unary n) (unary d) []⟩=
      some ⟨none,none,contents [] [] [] [decide (m+n<d)]⟩ := by
  obtain ⟨t,ht,flag,he⟩ := SemiprimeD1StackFiniteControlPaths.path_refines program 5 program_depth
    (compare_all m n d) none
  have hb:=compareTime_le (n+m) d
  refine ⟨t,by omega,?_⟩
  simpa [SemiprimeD1StackFiniteControlExecution.destination,cfg,code,entry]
    using SemiprimeD1StackFiniteControlPaths.Executes.iterates he

end RiemannGaussian.SemiprimeD1StackUnarySumLessBytecode
