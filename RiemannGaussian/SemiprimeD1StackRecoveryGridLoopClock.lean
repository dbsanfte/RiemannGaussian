/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryGridRowBounds
import RiemannGaussian.SemiprimeD1StackRecoveryGridExecution
/-! # Whole physical grid traversal polynomial from semantic boundary invariants -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryGridLoopClock
namespace Model
export SemiprimeD1StackRecoveryGridModel (Payload one)
end Model
namespace Loop
export SemiprimeD1StackRecoveryGridLoop (iterate rowBound timeBound)
end Loop
namespace Row
export SemiprimeD1StackRecoveryGridRowMeaning (step)
end Row
namespace P
export SemiprimeD1StackRecoveryGridPayloadBounds (Bounded one_bounded step_bounded)
end P
namespace R
export SemiprimeD1StackRecoveryGridResource (resource gridSize resource_pos grid_le index_le)
end R
namespace Dec
export SemiprimeD1StackRecoveryGridDecrement (difference runBound)
end Dec
/-- Every actual loop update preserves fitted/literal widths and the exact visited-row slope-count envelope. -/
theorem iterate_bounded (a M u n v:Nat) (t q width:List Bool) (p:Model.Payload)
    (hp:P.Bounded width p v (SemiprimeD1TaperedLoss.height M u*u)) :
    P.Bounded width (Loop.iterate a M u t width n q p) (v+n) (SemiprimeD1TaperedLoss.height M u*u):=by
  induction n generalizing v q p with
  | zero=>simpa only [Loop.iterate,Nat.add_zero] using hp
  | succ n ih=>
    have hs:=P.step_bounded a M u v t q width p hp
    have h:=ih (v+1) (Dec.difference q) (Row.step a M u t q width p) hs
    simpa only [Loop.iterate,show v+1+n=v+(n+1) by omega] using h
/-- Same actual loop budget, not an old semantic clock, pays every original row/end-test/positive binary decrement. -/
theorem time_le (a M u n v:Nat) (t q width:List Bool) (p:Model.Payload)
    (hp:P.Bounded width p v (SemiprimeD1TaperedLoss.height M u*u))
    (hv:v+n≤R.gridSize a) (hq:q.length=a+2) :
    Loop.timeBound a M u t width n q p≤n*(10^55*(R.resource a M u t width)^8+1000*R.resource a M u t width+2)+1:=by
  induction n generalizing v q p with
  | zero=>simp only [Loop.timeBound,Nat.zero_mul,Nat.zero_add,le_refl]
  | succ n ih=>
    have hr:=SemiprimeD1StackRecoveryGridRowBounds.row_le a M u n v t q width p hp hv hq.le
    change Loop.rowBound a M u n t q width p≤_ at hr
    have hs:=P.step_bounded a M u v t q width p hp
    have hq':(Dec.difference q).length=a+2:=SemiprimeD1StackRecoveryGridLoopPrimitives.difference_width a q hq
    have hi:=ih (v+1) (Dec.difference q) (Row.step a M u t q width p) hs (by omega) hq'
    have hd:=SemiprimeD1StackRecoveryGridDecrement.runBound_le q q
    have hR:=R.resource_pos a M u t width
    have hqR:q.length≤R.resource a M u t width:=hq.le.trans (R.index_le a M u t width)
    have hd':Dec.runBound q q≤1000*R.resource a M u t width:=by omega
    rw [Loop.timeBound,Nat.add_mul,Nat.one_mul]
    split_ifs <;> omega
/-- Whole physically acquired original grid payload has the semantic width/count cap. -/
theorem payload_bounded (a M u:Nat) (t width:List Bool) :
    P.Bounded width (SemiprimeD1StackRecoveryGridExecution.payload a M u t width) (R.gridSize a)
      (SemiprimeD1TaperedLoss.height M u*u):=by
  have h:=iterate_bounded a M u (R.gridSize a) 0 t (SemiprimeD1StackRecoveryGridExecution.firstWord a) width Model.one (P.one_bounded width _)
  simpa only [Nat.zero_add,SemiprimeD1StackRecoveryGridExecution.payload,R.gridSize] using h
/-- Whole original traversal pays N by VALUE and has a fixed ninth-degree input-resource cap. -/
theorem whole_le (a M u:Nat) (t width:List Bool) :
    Loop.timeBound a M u t width (R.gridSize a) (SemiprimeD1StackRecoveryGridExecution.firstWord a) Model.one≤
      10^56*(R.resource a M u t width)^9:=by
  let r:=R.resource a M u t width
  have hR:1≤r:=R.resource_pos a M u t width
  have hn:R.gridSize a≤r:=R.grid_le a M u t width
  have hq:(SemiprimeD1StackRecoveryGridExecution.firstWord a).length=a+2:=SemiprimeD1StackRecoveryGridFront.q_width a M u t width
  have h:=time_le a M u (R.gridSize a) 0 t _ width Model.one (P.one_bounded width _) (by omega) hq
  change _≤R.gridSize a*(10^55*r^8+1000*r+2)+1 at h
  have hm:=Nat.mul_le_mul_right (10^55*r^8+1000*r+2) hn
  have he:r*(10^55*r^8+1000*r+2)=10^55*r^9+1000*r^2+2*r:=by ring
  rw [he] at hm
  have h29:r^2≤r^9:=Nat.pow_le_pow_right hR (by decide:2≤9)
  have h19:r≤r^9:=Nat.le_pow (by decide:0<9)
  have h09:1≤r^9:=Nat.one_le_pow 9 _ hR
  change _≤10^56*r^9
  norm_num1 at h hm ⊢
  omega
end RiemannGaussian.SemiprimeD1StackRecoveryGridLoopClock
