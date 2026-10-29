/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackJetRouteDigits
import RiemannGaussian.SemiprimeD1StackPhysicalLoops
/-! # Actual counter replacement and finite control in routing -/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1StackJetRouteControl
open SemiprimeD1StackJetRoute SemiprimeD1StackJetRouteCalls
open SemiprimeD1StackUnaryDivmod (unary)
local notation "ctl" => SemiprimeD1StackJetRoute.control

@[simp] theorem update_radix (axes records left right result radix q d quotLeft remLeft quotRight remRight valid word : List Bool) :
    Function.update (bank axes records left right result radix q d quotLeft remLeft quotRight remRight valid) .radix word = bank axes records left right result word q d quotLeft remLeft quotRight remRight valid := by
  funext k; cases k <;> simp [bank]

@[simp] theorem update_d (axes records left right result radix q d quotLeft remLeft quotRight remRight valid word : List Bool) :
    Function.update (bank axes records left right result radix q d quotLeft remLeft quotRight remRight valid) .d word = bank axes records left right result radix q word quotLeft remLeft quotRight remRight valid := by
  funext k; cases k <;> simp [bank]

@[simp] theorem update_remLeft (axes records left right result radix q d quotLeft remLeft quotRight remRight valid word : List Bool) :
    Function.update (bank axes records left right result radix q d quotLeft remLeft quotRight remRight valid) .remLeft word = bank axes records left right result radix q d quotLeft word quotRight remRight valid := by
  funext k; cases k <;> simp [bank]

@[simp] theorem update_left (axes records left right result radix q d quotLeft remLeft quotRight remRight valid word : List Bool) :
    Function.update (bank axes records left right result radix q d quotLeft remLeft quotRight remRight valid) .left word = bank axes records word right result radix q d quotLeft remLeft quotRight remRight valid := by
  funext k; cases k <;> simp [bank]

@[simp] theorem update_remRight (axes records left right result radix q d quotLeft remLeft quotRight remRight valid word : List Bool) :
    Function.update (bank axes records left right result radix q d quotLeft remLeft quotRight remRight valid) .remRight word = bank axes records left right result radix q d quotLeft remLeft quotRight word valid := by
  funext k; cases k <;> simp [bank]

@[simp] theorem update_right (axes records left right result radix q d quotLeft remLeft quotRight remRight valid word : List Bool) :
    Function.update (bank axes records left right result radix q d quotLeft remLeft quotRight remRight valid) .right word = bank axes records left word result radix q d quotLeft remLeft quotRight remRight valid := by
  funext k; cases k <;> simp [bank]

@[simp] theorem update_valid (axes records left right result radix q d quotLeft remLeft quotRight remRight valid word : List Bool) :
    Function.update (bank axes records left right result radix q d quotLeft remLeft quotRight remRight valid) .valid word = bank axes records left right result radix q d quotLeft remLeft quotRight remRight word := by
  funext k; cases k <;> simp [bank]

/-- The acquired whole rank is physically cleared before digit traversal. -/
theorem clear_rank (records left right result rank : List Bool) :
    Trace.Runs code (rank.length+1) (ctl .clearRank)
      (bank [] records left right result rank [] [] [] [] [] [] [])
      (ctl .recordPeek) (bank [] records left right result [] [] [] [] [] [] [] []) := by
  simpa only [update_radix] using SemiprimeD1StackPhysicalLoops.drain code
    (ctl .clearRank) (ctl .recordPeek) .radix rfl
    (bank [] records left right result rank [] [] [] [] [] [] []) rank

/-- Every visited suffix divisor is physically erased after both actual divisions. -/
theorem clear_denominator (records result d ri rj : List Bool) :
    Trace.Runs code (d.length+1) (ctl .clearD)
      (bank [] records [] [] result [] [] d [] ri [] rj [])
      (ctl .moveLeft) (bank [] records [] [] result [] [] [] [] ri [] rj []) := by
  simpa only [update_d] using SemiprimeD1StackPhysicalLoops.drain code
    (ctl .clearD) (ctl .moveLeft) .d rfl
    (bank [] records [] [] result [] [] d [] ri [] rj []) d

/-- Actual left remainder transfer retains no hidden index register. -/
theorem move_left (n : ℕ) (records result rj : List Bool) :
    Trace.Runs code (2*n+1) (ctl .moveLeft)
      (bank [] records [] [] result [] [] [] [] (unary n) [] rj [])
      (ctl .moveRight) (bank [] records (unary n) [] result [] [] [] [] [] [] rj []) := by
  simpa only [update_left,update_remLeft,List.append_nil,unary] using
    SemiprimeD1StackPhysicalLoops.move_unary code (ctl .moveLeft) (ctl .pushLeft)
      (ctl .moveRight) .remLeft .left (by decide) rfl rfl
      (bank [] records [] [] result [] [] [] [] [] [] rj []) n []

/-- Actual right remainder transfer, then the same acquired-record loop resumes. -/
theorem move_right (n : ℕ) (records result left : List Bool) :
    Trace.Runs code (2*n+1) (ctl .moveRight)
      (bank [] records left [] result [] [] [] [] [] [] (unary n) [])
      (ctl .recordPeek) (bank [] records left (unary n) result [] [] [] [] [] [] [] []) := by
  simpa only [update_right,update_remRight,List.append_nil,unary] using
    SemiprimeD1StackPhysicalLoops.move_unary code (ctl .moveRight) (ctl .pushRight)
      (ctl .recordPeek) .remRight .right (by decide) rfl rfl
      (bank [] records left [] result [] [] [] [] [] [] [] []) n []

end RiemannGaussian.SemiprimeD1StackJetRouteControl
