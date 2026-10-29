/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPackedFactorRecoveryPrimitives
/-! # Physical arithmetic-operand copy views for the fixed recovery controller -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPackedFactorRecoveryCopies
open SemiprimeD1StackPackedFactorRecovery SemiprimeD1StackPackedFactorRecoveryEncoding
open SemiprimeD1StackPackedFactorRecoveryPrimitives SemiprimeD1StackProcedureTrace
/-- Actual preserving copy into the real adder left operand. -/
theorem adder_left (site : Copy) (pc finish : Label) (r m x w v u) (left right scratch output value : List Bool)
    (hc : program pc=.call (copyLabel site 0) finish)
    (hd : copyStack site 1=adder .left) (hv : (view r m (A.store left right scratch output) x w v u) (copyStack site 0)=value) (hs : u .scratch=[]) :
    Runs program (5*value.length+4) pc (view r m (A.store left right scratch output) x w v u) finish (view r m (A.store (value++left) right scratch output) x w v u) := by
  have ht : (view r m (A.store left right scratch output) x w v u) (copyStack site 1)=left := by rw [hd];rfl
  have h:=copy_call site pc finish hc (view r m (A.store left right scratch output) x w v u) value left hv ht hs
  rw [hd,view_adder,SemiprimeD1StackAdder.store_left] at h
  exact h
/-- Actual preserving copy into the real adder right operand. -/
theorem adder_right (site : Copy) (pc finish : Label) (r m x w v u) (left right scratch output value : List Bool)
    (hc : program pc=.call (copyLabel site 0) finish)
    (hd : copyStack site 1=adder .right) (hv : (view r m (A.store left right scratch output) x w v u) (copyStack site 0)=value) (hs : u .scratch=[]) :
    Runs program (5*value.length+4) pc (view r m (A.store left right scratch output) x w v u) finish (view r m (A.store left (value++right) scratch output) x w v u) := by
  have ht : (view r m (A.store left right scratch output) x w v u) (copyStack site 1)=right := by rw [hd];rfl
  have h:=copy_call site pc finish hc (view r m (A.store left right scratch output) x w v u) value right hv ht hs
  rw [hd,view_adder,SemiprimeD1StackAdder.store_right] at h
  exact h
/-- Actual preserving copy into the real multiply input operand. -/
theorem multiply_input (site : Copy) (pc finish : Label) (r m a w v u) (xs ys ds left acc scratch out cp cs value : List Bool)
    (hc : program pc=.call (copyLabel site 0) finish)
    (hd : copyStack site 1=multiply X.input) (hv : (view r m a (X.payload xs ys ds left acc scratch out cp cs) w v u) (copyStack site 0)=value) (hs : u .scratch=[]) :
    Runs program (5*value.length+4) pc (view r m a (X.payload xs ys ds left acc scratch out cp cs) w v u) finish (view r m a (X.payload (value++xs) ys ds left acc scratch out cp cs) w v u) := by
  have ht : (view r m a (X.payload xs ys ds left acc scratch out cp cs) w v u) (copyStack site 1)=xs := by rw [hd];rfl
  have h:=copy_call site pc finish hc (view r m a (X.payload xs ys ds left acc scratch out cp cs) w v u) value xs hv ht hs
  rw [hd,view_multiply,SemiprimeD1StackMultiplierExecution.payload_xs] at h
  exact h
/-- Actual preserving copy into the real multiply factor operand. -/
theorem multiply_factor (site : Copy) (pc finish : Label) (r m a w v u) (xs ys ds left acc scratch out cp cs value : List Bool)
    (hc : program pc=.call (copyLabel site 0) finish)
    (hd : copyStack site 1=multiply X.factor) (hv : (view r m a (X.payload xs ys ds left acc scratch out cp cs) w v u) (copyStack site 0)=value) (hs : u .scratch=[]) :
    Runs program (5*value.length+4) pc (view r m a (X.payload xs ys ds left acc scratch out cp cs) w v u) finish (view r m a (X.payload xs (value++ys) ds left acc scratch out cp cs) w v u) := by
  have ht : (view r m a (X.payload xs ys ds left acc scratch out cp cs) w v u) (copyStack site 1)=ys := by rw [hd];rfl
  have h:=copy_call site pc finish hc (view r m a (X.payload xs ys ds left acc scratch out cp cs) w v u) value ys hv ht hs
  rw [hd,view_multiply,SemiprimeD1StackMultiplierExecution.payload_ys] at h
  exact h
end RiemannGaussian.SemiprimeD1StackPackedFactorRecoveryCopies
