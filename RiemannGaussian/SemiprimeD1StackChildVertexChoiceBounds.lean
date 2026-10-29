/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildVertexChoiceSource
/-! # One fixed whole clock for both actual constructor branches
The resource pays actual header bytes and rank/precision VALUES. No recursively
enlarged elapsed child runtime becomes a rational/table operand width.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildVertexChoiceBounds
open SemiprimeD1StackChildVertexChoice SemiprimeD1StackChildVertexChoiceSpec
open SemiprimeD1StackChildVertexChoiceSource
variable {d : ℕ}
/-- Uniform fixed coefficient and degree, chosen before all original vertices and activity bits. -/
def polynomial (old : SemiprimeD1JetAxes.Context) (extra : List ℕ) (oldp newp : List Bool)
    (parent : SemiprimeD1TensorTables.Table d) (order ports : List ℕ) : ℕ:=
  10^26*(resource old extra oldp newp parent order ports)^2*2^ports.length
/-- Both whole constructor clocks, actual activity consumption, call and halt fit the SAME quadratic envelope. -/
theorem timeBound_le (old : SemiprimeD1JetAxes.Context) (extra : List ℕ) (oldp newp : List Bool)
    (parent : SemiprimeD1TensorTables.Table d) (order ports : List ℕ) (bit : Bool) :
    timeBound old extra oldp newp parent order ports bit≤polynomial old extra oldp newp parent order ports := by
  let r:=resource old extra oldp newp parent order ports
  let e:=2^ports.length
  have hb:=resource_bounds old extra oldp newp parent order ports
  have hr : 1≤r:=hb.1
  have he : 1≤e:=Nat.one_le_pow _ _ (by decide : 1≤(2:ℕ))
  have h1 : 1≤r^2*e:=Nat.mul_le_mul (Nat.one_le_pow _ _ hr) he
  have hs : r^2≤r^2*e:=by simpa only [Nat.mul_one] using Nat.mul_le_mul_left (r^2) he
  have ha : (AB.resource old extra oldp newp parent order ports)^2*e≤r^2*e:=
    Nat.mul_le_mul_right e (Nat.pow_le_pow_left hb.2.1 2)
  have hu : (UB.resource (extra++old.axes) newp+1)^2≤r^2*e:=
    (Nat.pow_le_pow_left hb.2.2 2).trans hs
  unfold polynomial
  rw [Nat.mul_assoc]
  change timeBound old extra oldp newp parent order ports bit≤10^26*(r^2*e)
  cases bit
  · change 10^8*(UB.resource (extra++old.axes) newp+1)^2+3≤10^26*(r^2*e)
    omega
  · change 10^24*(AB.resource old extra oldp newp parent order ports)^2*e+3≤10^26*(r^2*e)
    rw [Nat.mul_assoc]
    omega
/-- Actual whole eight-word source reaches its exact complete stopped169 bank within the fixed cap. -/
theorem source_run_bounded (old : SemiprimeD1JetAxes.Context) (ho : old.Positive)
    (extra : List ℕ) (he : 0<extra.prod) (oldp newp : List Bool)
    (hp : SemiprimeBitArithmetic.bitValue oldp=old.precision)
    (parent : SemiprimeD1TensorTables.Table d) (hg : SemiprimeD1TensorTables.Good old parent)
    (order ports : List ℕ) (bit : Bool) :
    ∃t≤polynomial old extra oldp newp parent order ports,
      SemiprimeD1StackCalls.run program t (originalInitial old extra oldp newp parent order ports bit)=
        some (done old extra oldp newp parent order ports bit) := by
  obtain ⟨t,ht,hr⟩:=source_run old ho extra he oldp newp hp parent hg order ports bit
  exact ⟨t,ht.trans (timeBound_le old extra oldp newp parent order ports bit),hr⟩
/-- Genuine compiled finite169-role source with the SAME whole source clock. -/
noncomputable def machineSource (old : SemiprimeD1JetAxes.Context) (ho : old.Positive)
    (extra : List ℕ) (he : 0<extra.prod) (oldp newp : List Bool)
    (hp : SemiprimeBitArithmetic.bitValue oldp=old.precision)
    (parent : SemiprimeD1TensorTables.Table d) (hg : SemiprimeD1TensorTables.Good old parent)
    (order ports : List ℕ) (bit : Bool) :
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration (originalInitial old extra oldp newp parent order ports bit))
      (some (SemiprimeD1StackCalls.configuration (done old extra oldp newp parent order ports bit)))
      (polynomial old extra oldp newp parent order ports) := by
  apply SemiprimeD1StackCalls.evalsCorrect activity output (.local .start) program
  let h:=source_run_bounded old ho extra he oldp newp hp parent hg order ports bit
  exact ⟨⟨Classical.choose h,(Classical.choose_spec h).2⟩,(Classical.choose_spec h).1⟩
end RiemannGaussian.SemiprimeD1StackChildVertexChoiceBounds
