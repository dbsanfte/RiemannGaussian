/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackJetRouteControl
/-! # Actual complete failure cleanup of the fixed routing stack bank -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
namespace RiemannGaussian.SemiprimeD1StackJetRouteFailure
open SemiprimeD1StackJetRoute SemiprimeD1StackJetRouteCalls
theorem compose {m n : ℕ} {pc mid next : Label} {bank middle result : Stack→List Bool}
    (h : SemiprimeD1StackProcedureTrace.Runs code m pc bank mid middle)
    (g : SemiprimeD1StackProcedureTrace.Runs code n mid middle next result) :
    SemiprimeD1StackProcedureTrace.Runs code (m+n) pc bank next result :=
  SemiprimeD1StackProcedureTrace.runs_trans code m n pc mid next bank middle result h g
local notation "ctl" => SemiprimeD1StackJetRoute.control

theorem fail_instruction (k : Fin 19) : code (ctl (.fail k))=.base (.pop (clearStack k)
    (if h:k.val+1<19 then ctl (.fail ⟨k.val+1,h⟩) else ctl .reject)
    (ctl (.fail k)) (ctl (.fail k))) := by
  fin_cases k <;> rfl

theorem reject_instruction : code (ctl .reject)=.base (.push .valid false (ctl .halt)) := rfl

attribute [local irreducible] SemiprimeD1StackJetRoute.code

/-- Entering the failure path physically clears all nineteen stacks before
emitting false. The width premise bounds actual input bytes, not a solved route. -/
theorem chain {L : Type} (program : L→SemiprimeD1StackCalls.Instruction Stack L)
    {m n : ℕ} {pc mid next : L} {bank middle result : Stack→List Bool}
    (h : SemiprimeD1StackProcedureTrace.Runs program m pc bank mid middle)
    (g : SemiprimeD1StackProcedureTrace.Runs program n mid middle next result) :
    SemiprimeD1StackProcedureTrace.Runs program (m+n) pc bank next result :=
  SemiprimeD1StackProcedureTrace.runs_trans program m n pc mid next bank middle result h g

theorem clear_all {L : Type} (program : L→SemiprimeD1StackCalls.Instruction Stack L)
    (pc : Fin 19→L) (reject halt : L)
    (hcode : ∀k : Fin 19, program (pc k)=.base (.pop (clearStack k)
      (if h:k.val+1<19 then pc ⟨k.val+1,h⟩ else reject) (pc k) (pc k)))
    (hreject : program reject=.base (.push .valid false halt))
    (input : Stack→List Bool) (cap : ℕ)
    (hc : ∀k,(input k).length≤cap) :
    ∃m≤19*(cap+1)+1,Trace.Runs program m (pc 0) input halt
      (bank [] [] [] [] [] [] [] [] [] [] [] [] [false]) := by
  let b0 := input
  have hc0 : ∀k,(b0 k).length≤cap := hc
  generalize hb1 : Function.update b0 .axes [] = b1
  have hc1 : ∀k,(b1 k).length≤cap := by
    intro k
    by_cases hk : k=Stack.axes
    · subst k; rw [←hb1]; simp
    · simpa only [←hb1,Function.update_of_ne hk] using hc0 k
  have hu0 : Function.update b0 .axes (b0 .axes)=b0 := by
    funext k
    by_cases hk : k=Stack.axes <;> simp [hk]
  have h0 := SemiprimeD1StackPhysicalLoops.drain program (pc 0) (pc 1)
    .axes (by simpa [clearStack] using hcode (0 : Fin 19)) b0 (b0 .axes)
  rw [hu0,hb1] at h0
  generalize hb2 : Function.update b1 .reverseAxes [] = b2
  have hc2 : ∀k,(b2 k).length≤cap := by
    intro k
    by_cases hk : k=Stack.reverseAxes
    · subst k; rw [←hb2]; simp
    · simpa only [←hb2,Function.update_of_ne hk] using hc1 k
  have hu1 : Function.update b1 .reverseAxes (b1 .reverseAxes)=b1 := by
    funext k
    by_cases hk : k=Stack.reverseAxes <;> simp [hk]
  have h1 := SemiprimeD1StackPhysicalLoops.drain program (pc 1) (pc 2)
    .reverseAxes (by simpa [clearStack] using hcode (1 : Fin 19)) b1 (b1 .reverseAxes)
  rw [hu1,hb2] at h1
  generalize hb3 : Function.update b2 .axis [] = b3
  have hc3 : ∀k,(b3 k).length≤cap := by
    intro k
    by_cases hk : k=Stack.axis
    · subst k; rw [←hb3]; simp
    · simpa only [←hb3,Function.update_of_ne hk] using hc2 k
  have hu2 : Function.update b2 .axis (b2 .axis)=b2 := by
    funext k
    by_cases hk : k=Stack.axis <;> simp [hk]
  have h2 := SemiprimeD1StackPhysicalLoops.drain program (pc 2) (pc 3)
    .axis (by simpa [clearStack] using hcode (2 : Fin 19)) b2 (b2 .axis)
  rw [hu2,hb3] at h2
  generalize hb4 : Function.update b3 .radix [] = b4
  have hc4 : ∀k,(b4 k).length≤cap := by
    intro k
    by_cases hk : k=Stack.radix
    · subst k; rw [←hb4]; simp
    · simpa only [←hb4,Function.update_of_ne hk] using hc3 k
  have hu3 : Function.update b3 .radix (b3 .radix)=b3 := by
    funext k
    by_cases hk : k=Stack.radix <;> simp [hk]
  have h3 := SemiprimeD1StackPhysicalLoops.drain program (pc 3) (pc 4)
    .radix (by simpa [clearStack] using hcode (3 : Fin 19)) b3 (b3 .radix)
  rw [hu3,hb4] at h3
  generalize hb5 : Function.update b4 .product [] = b5
  have hc5 : ∀k,(b5 k).length≤cap := by
    intro k
    by_cases hk : k=Stack.product
    · subst k; rw [←hb5]; simp
    · simpa only [←hb5,Function.update_of_ne hk] using hc4 k
  have hu4 : Function.update b4 .product (b4 .product)=b4 := by
    funext k
    by_cases hk : k=Stack.product <;> simp [hk]
  have h4 := SemiprimeD1StackPhysicalLoops.drain program (pc 4) (pc 5)
    .product (by simpa [clearStack] using hcode (4 : Fin 19)) b4 (b4 .product)
  rw [hu4,hb5] at h4
  generalize hb6 : Function.update b5 .records [] = b6
  have hc6 : ∀k,(b6 k).length≤cap := by
    intro k
    by_cases hk : k=Stack.records
    · subst k; rw [←hb6]; simp
    · simpa only [←hb6,Function.update_of_ne hk] using hc5 k
  have hu5 : Function.update b5 .records (b5 .records)=b5 := by
    funext k
    by_cases hk : k=Stack.records <;> simp [hk]
  have h5 := SemiprimeD1StackPhysicalLoops.drain program (pc 5) (pc 6)
    .records (by simpa [clearStack] using hcode (5 : Fin 19)) b5 (b5 .records)
  rw [hu5,hb6] at h5
  generalize hb7 : Function.update b6 .scratch [] = b7
  have hc7 : ∀k,(b7 k).length≤cap := by
    intro k
    by_cases hk : k=Stack.scratch
    · subst k; rw [←hb7]; simp
    · simpa only [←hb7,Function.update_of_ne hk] using hc6 k
  have hu6 : Function.update b6 .scratch (b6 .scratch)=b6 := by
    funext k
    by_cases hk : k=Stack.scratch <;> simp [hk]
  have h6 := SemiprimeD1StackPhysicalLoops.drain program (pc 6) (pc 7)
    .scratch (by simpa [clearStack] using hcode (6 : Fin 19)) b6 (b6 .scratch)
  rw [hu6,hb7] at h6
  generalize hb8 : Function.update b7 .valid [] = b8
  have hc8 : ∀k,(b8 k).length≤cap := by
    intro k
    by_cases hk : k=Stack.valid
    · subst k; rw [←hb8]; simp
    · simpa only [←hb8,Function.update_of_ne hk] using hc7 k
  have hu7 : Function.update b7 .valid (b7 .valid)=b7 := by
    funext k
    by_cases hk : k=Stack.valid <;> simp [hk]
  have h7 := SemiprimeD1StackPhysicalLoops.drain program (pc 7) (pc 8)
    .valid (by simpa [clearStack] using hcode (7 : Fin 19)) b7 (b7 .valid)
  rw [hu7,hb8] at h7
  generalize hb9 : Function.update b8 .left [] = b9
  have hc9 : ∀k,(b9 k).length≤cap := by
    intro k
    by_cases hk : k=Stack.left
    · subst k; rw [←hb9]; simp
    · simpa only [←hb9,Function.update_of_ne hk] using hc8 k
  have hu8 : Function.update b8 .left (b8 .left)=b8 := by
    funext k
    by_cases hk : k=Stack.left <;> simp [hk]
  have h8 := SemiprimeD1StackPhysicalLoops.drain program (pc 8) (pc 9)
    .left (by simpa [clearStack] using hcode (8 : Fin 19)) b8 (b8 .left)
  rw [hu8,hb9] at h8
  generalize hb10 : Function.update b9 .right [] = b10
  have hc10 : ∀k,(b10 k).length≤cap := by
    intro k
    by_cases hk : k=Stack.right
    · subst k; rw [←hb10]; simp
    · simpa only [←hb10,Function.update_of_ne hk] using hc9 k
  have hu9 : Function.update b9 .right (b9 .right)=b9 := by
    funext k
    by_cases hk : k=Stack.right <;> simp [hk]
  have h9 := SemiprimeD1StackPhysicalLoops.drain program (pc 9) (pc 10)
    .right (by simpa [clearStack] using hcode (9 : Fin 19)) b9 (b9 .right)
  rw [hu9,hb10] at h9
  generalize hb11 : Function.update b10 .result [] = b11
  have hc11 : ∀k,(b11 k).length≤cap := by
    intro k
    by_cases hk : k=Stack.result
    · subst k; rw [←hb11]; simp
    · simpa only [←hb11,Function.update_of_ne hk] using hc10 k
  have hu10 : Function.update b10 .result (b10 .result)=b10 := by
    funext k
    by_cases hk : k=Stack.result <;> simp [hk]
  have h10 := SemiprimeD1StackPhysicalLoops.drain program (pc 10) (pc 11)
    .result (by simpa [clearStack] using hcode (10 : Fin 19)) b10 (b10 .result)
  rw [hu10,hb11] at h10
  generalize hb12 : Function.update b11 .q [] = b12
  have hc12 : ∀k,(b12 k).length≤cap := by
    intro k
    by_cases hk : k=Stack.q
    · subst k; rw [←hb12]; simp
    · simpa only [←hb12,Function.update_of_ne hk] using hc11 k
  have hu11 : Function.update b11 .q (b11 .q)=b11 := by
    funext k
    by_cases hk : k=Stack.q <;> simp [hk]
  have h11 := SemiprimeD1StackPhysicalLoops.drain program (pc 11) (pc 12)
    .q (by simpa [clearStack] using hcode (11 : Fin 19)) b11 (b11 .q)
  rw [hu11,hb12] at h11
  generalize hb13 : Function.update b12 .d [] = b13
  have hc13 : ∀k,(b13 k).length≤cap := by
    intro k
    by_cases hk : k=Stack.d
    · subst k; rw [←hb13]; simp
    · simpa only [←hb13,Function.update_of_ne hk] using hc12 k
  have hu12 : Function.update b12 .d (b12 .d)=b12 := by
    funext k
    by_cases hk : k=Stack.d <;> simp [hk]
  have h12 := SemiprimeD1StackPhysicalLoops.drain program (pc 12) (pc 13)
    .d (by simpa [clearStack] using hcode (12 : Fin 19)) b12 (b12 .d)
  rw [hu12,hb13] at h12
  generalize hb14 : Function.update b13 .copied [] = b14
  have hc14 : ∀k,(b14 k).length≤cap := by
    intro k
    by_cases hk : k=Stack.copied
    · subst k; rw [←hb14]; simp
    · simpa only [←hb14,Function.update_of_ne hk] using hc13 k
  have hu13 : Function.update b13 .copied (b13 .copied)=b13 := by
    funext k
    by_cases hk : k=Stack.copied <;> simp [hk]
  have h13 := SemiprimeD1StackPhysicalLoops.drain program (pc 13) (pc 14)
    .copied (by simpa [clearStack] using hcode (13 : Fin 19)) b13 (b13 .copied)
  rw [hu13,hb14] at h13
  generalize hb15 : Function.update b14 .divScratch [] = b15
  have hc15 : ∀k,(b15 k).length≤cap := by
    intro k
    by_cases hk : k=Stack.divScratch
    · subst k; rw [←hb15]; simp
    · simpa only [←hb15,Function.update_of_ne hk] using hc14 k
  have hu14 : Function.update b14 .divScratch (b14 .divScratch)=b14 := by
    funext k
    by_cases hk : k=Stack.divScratch <;> simp [hk]
  have h14 := SemiprimeD1StackPhysicalLoops.drain program (pc 14) (pc 15)
    .divScratch (by simpa [clearStack] using hcode (14 : Fin 19)) b14 (b14 .divScratch)
  rw [hu14,hb15] at h14
  generalize hb16 : Function.update b15 .quotLeft [] = b16
  have hc16 : ∀k,(b16 k).length≤cap := by
    intro k
    by_cases hk : k=Stack.quotLeft
    · subst k; rw [←hb16]; simp
    · simpa only [←hb16,Function.update_of_ne hk] using hc15 k
  have hu15 : Function.update b15 .quotLeft (b15 .quotLeft)=b15 := by
    funext k
    by_cases hk : k=Stack.quotLeft <;> simp [hk]
  have h15 := SemiprimeD1StackPhysicalLoops.drain program (pc 15) (pc 16)
    .quotLeft (by simpa [clearStack] using hcode (15 : Fin 19)) b15 (b15 .quotLeft)
  rw [hu15,hb16] at h15
  generalize hb17 : Function.update b16 .remLeft [] = b17
  have hc17 : ∀k,(b17 k).length≤cap := by
    intro k
    by_cases hk : k=Stack.remLeft
    · subst k; rw [←hb17]; simp
    · simpa only [←hb17,Function.update_of_ne hk] using hc16 k
  have hu16 : Function.update b16 .remLeft (b16 .remLeft)=b16 := by
    funext k
    by_cases hk : k=Stack.remLeft <;> simp [hk]
  have h16 := SemiprimeD1StackPhysicalLoops.drain program (pc 16) (pc 17)
    .remLeft (by simpa [clearStack] using hcode (16 : Fin 19)) b16 (b16 .remLeft)
  rw [hu16,hb17] at h16
  generalize hb18 : Function.update b17 .quotRight [] = b18
  have hc18 : ∀k,(b18 k).length≤cap := by
    intro k
    by_cases hk : k=Stack.quotRight
    · subst k; rw [←hb18]; simp
    · simpa only [←hb18,Function.update_of_ne hk] using hc17 k
  have hu17 : Function.update b17 .quotRight (b17 .quotRight)=b17 := by
    funext k
    by_cases hk : k=Stack.quotRight <;> simp [hk]
  have h17 := SemiprimeD1StackPhysicalLoops.drain program (pc 17) (pc 18)
    .quotRight (by simpa [clearStack] using hcode (17 : Fin 19)) b17 (b17 .quotRight)
  rw [hu17,hb18] at h17
  generalize hb19 : Function.update b18 .remRight [] = b19
  have hc19 : ∀k,(b19 k).length≤cap := by
    intro k
    by_cases hk : k=Stack.remRight
    · subst k; rw [←hb19]; simp
    · simpa only [←hb19,Function.update_of_ne hk] using hc18 k
  have hu18 : Function.update b18 .remRight (b18 .remRight)=b18 := by
    funext k
    by_cases hk : k=Stack.remRight <;> simp [hk]
  have h18 := SemiprimeD1StackPhysicalLoops.drain program (pc 18) reject
    .remRight (by simpa [clearStack] using hcode (18 : Fin 19)) b18 (b18 .remRight)
  rw [hu18,hb19] at h18
  have hempty : b19=(fun _=>[]) := by
    rw [←hb19,←hb18,←hb17,←hb16,←hb15,←hb14,←hb13,←hb12,←hb11,←hb10,←hb9,←hb8,←hb7,←hb6,←hb5,←hb4,←hb3,←hb2,←hb1]
    funext k
    cases k <;> simp [b0]
  have hend : Trace.Runs program 1 reject (fun _=>[]) halt
      (bank [] [] [] [] [] [] [] [] [] [] [] [] [false]) := by
    apply Trace.one_base program reject halt
      (.push .valid false halt) _ _ hreject
    · rfl
    · funext k; cases k <;> simp [SemiprimeD1StackBytecode.execute,bank]
  change Trace.Runs program _ _ _ _ b19 at h18
  rw [hempty] at h18
  have h := (chain program h0 (chain program h1 (chain program h2 (chain program h3 (chain program h4 (chain program h5 (chain program h6 (chain program h7 (chain program h8 (chain program h9 (chain program h10 (chain program h11 (chain program h12 (chain program h13 (chain program h14 (chain program h15 (chain program h16 (chain program h17 (chain program h18 hend)))))))))))))))))))
  refine ⟨_,?_,h⟩
  have hw0 := hc0 .axes
  have hw1 := hc1 .reverseAxes
  have hw2 := hc2 .axis
  have hw3 := hc3 .radix
  have hw4 := hc4 .product
  have hw5 := hc5 .records
  have hw6 := hc6 .scratch
  have hw7 := hc7 .valid
  have hw8 := hc8 .left
  have hw9 := hc9 .right
  have hw10 := hc10 .result
  have hw11 := hc11 .q
  have hw12 := hc12 .d
  have hw13 := hc13 .copied
  have hw14 := hc14 .divScratch
  have hw15 := hc15 .quotLeft
  have hw16 := hc16 .remLeft
  have hw17 := hc17 .quotRight
  have hw18 := hc18 .remRight
  have hb := (Nat.add_le_add (Nat.add_le_add_right hw0 1) (Nat.add_le_add (Nat.add_le_add_right hw1 1) (Nat.add_le_add (Nat.add_le_add_right hw2 1) (Nat.add_le_add (Nat.add_le_add_right hw3 1) (Nat.add_le_add (Nat.add_le_add_right hw4 1) (Nat.add_le_add (Nat.add_le_add_right hw5 1) (Nat.add_le_add (Nat.add_le_add_right hw6 1) (Nat.add_le_add (Nat.add_le_add_right hw7 1) (Nat.add_le_add (Nat.add_le_add_right hw8 1) (Nat.add_le_add (Nat.add_le_add_right hw9 1) (Nat.add_le_add (Nat.add_le_add_right hw10 1) (Nat.add_le_add (Nat.add_le_add_right hw11 1) (Nat.add_le_add (Nat.add_le_add_right hw12 1) (Nat.add_le_add (Nat.add_le_add_right hw13 1) (Nat.add_le_add (Nat.add_le_add_right hw14 1) (Nat.add_le_add (Nat.add_le_add_right hw15 1) (Nat.add_le_add (Nat.add_le_add_right hw16 1) (Nat.add_le_add (Nat.add_le_add_right hw17 1) (Nat.add_le_add (Nat.add_le_add_right hw18 1) (Nat.le_refl 1))))))))))))))))))))
  have he : ((cap+1)+((cap+1)+((cap+1)+((cap+1)+((cap+1)+((cap+1)+((cap+1)+((cap+1)+((cap+1)+((cap+1)+((cap+1)+((cap+1)+((cap+1)+((cap+1)+((cap+1)+((cap+1)+((cap+1)+((cap+1)+((cap+1)+1)))))))))))))))))))=19*(cap+1)+1 := by ring
  rw [he] at hb
  exact hb

/-- The actual fixed routing failure entry uses the proved literal drain program. -/
theorem reject_clean (input : Stack→List Bool) (cap : ℕ)
    (hc : ∀k,(input k).length≤cap) :
    ∃m≤19*(cap+1)+1,Trace.Runs code m (ctl (.fail 0)) input (ctl .halt)
      (bank [] [] [] [] [] [] [] [] [] [] [] [] [false]) :=
  clear_all code (fun k=>ctl (.fail k)) (ctl .reject) (ctl .halt)
    fail_instruction reject_instruction input cap hc

end RiemannGaussian.SemiprimeD1StackJetRouteFailure
