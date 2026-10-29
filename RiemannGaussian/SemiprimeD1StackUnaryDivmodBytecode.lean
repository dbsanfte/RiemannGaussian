/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackUnaryDivmodExecution
import RiemannGaussian.SemiprimeD1StackReturnLink
import RiemannGaussian.SemiprimeD1StackBytecodeBounds

/-! # Actual callable finite unary divmod code -/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1StackUnaryDivmodBytecode
open SemiprimeD1StackUnaryDivmod SemiprimeD1StackUnaryDivmodExecution
namespace F
export SemiprimeD1StackFiniteControl (Label code entry depth)
end F
namespace B
export SemiprimeD1StackBytecode (run State)
end B

/-- Fixed finite literal instruction labels. -/
abbrev Label := F.Label program
/-- Actual computed bytecode, not a native division instruction. -/
def code := F.code program
/-- Fixed initial label specializes the one finite optional-bit register. -/
def entry : Label := F.entry program .entry none

/-- Every fixed source label has elementary syntax depth at most five. -/
theorem program_depth (pc : PC) : F.depth (program pc)≤5 := by
  cases pc <;> decide

/-- Actual primitive bytecode division from original unary operands. -/
theorem divide_run (n d : ℕ) :
    ∃m≤100*(n+d+1),B.run code m
      ⟨some entry,none,contents (unary n) (unary d) [] [] [] []⟩=
      some ⟨none,none,contents [] (unary d) [] [] (unary (n/d)) (unary (n%d))⟩ := by
  obtain ⟨m,hm,hr⟩ := SemiprimeD1StackFiniteControlPaths.halted_run program 5 program_depth
    .entry none none _ _ (totalTime n d) (exec_iterates (divide_exec n d))
  exact ⟨m,by have h:=totalTime_le n d; omega,hr⟩

/-- Actual procedure call/return, including both added frame/control transitions. -/
theorem linked_run (n d : ℕ) :
    ∃m≤100*(n+d+1)+2,
      SemiprimeD1StackCalls.run (SemiprimeD1StackReturnLink.code entry code) m
        (SemiprimeD1StackReturnLink.initial (contents (unary n) (unary d) [] [] [] []))=
      some (SemiprimeD1StackReturnLink.final
        (contents [] (unary d) [] [] (unary (n/d)) (unary (n%d)))) := by
  obtain ⟨m,hm,hr⟩ := divide_run n d
  exact ⟨m+2,by omega,SemiprimeD1StackReturnLink.linked_run entry code m _ _ hr⟩

/-- Every actual source-bytecode prefix has a derived data-stack bound. -/
theorem prefix_width (n d fuel : ℕ) (out : B.State Stack Label)
    (h : B.run code fuel ⟨some entry,none,contents (unary n) (unary d) [] [] [] []⟩=some out) :
    ∀k,(out.store k).length≤n+d+fuel := by
  intro k
  have hh := SemiprimeD1StackBytecodeBounds.run_length code fuel _ out h k
  have hi : (contents (unary n) (unary d) [] [] [] [] k).length≤n+d := by
    cases k <;> simp [contents,unary]
  exact hh.trans (Nat.add_le_add_right hi fuel)

end RiemannGaussian.SemiprimeD1StackUnaryDivmodBytecode
