/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPackedRootInputStorage
/-! # One fixed original-input acquisition rate for the SAME complete source
Only a fixed SUM of actual closed source budgets is used. This does not
assert a primitive recursive contraction or a completed factoring algorithm.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPackedRootInputResources
open SemiprimeD1StackPackedRootInputBounds
/-- Fixed constants precede every original word; old packets, actual marking and context are all paid. -/
theorem runBound_monomial : ∃ A d : ℕ,∀bits : List Bool,
    runBound bits ≤ A*(bits.length+1)^d*2^(114000*SemiprimeMacroParameters.scopeBound bits.length) := by
  obtain ⟨a,d,ha⟩:=SemiprimeD1StackRootPacketInventoryMonomial.runBound_monomial
  obtain ⟨b,e,hb⟩:=SemiprimeD1StackMarkedRootRecordsResources.runBound_monomial
  refine ⟨a+b+3100,d+e+2,?_⟩
  intro bits
  let H:=(bits.length+1)^(d+e+2)
  let E:=(2:ℕ)^(114000*SemiprimeMacroParameters.scopeBound bits.length)
  have hp : 1 ≤ bits.length+1 := by omega
  have he : 1 ≤ E := Nat.one_le_pow _ _ (by decide : 1 ≤ (2:ℕ))
  have hd : (bits.length+1)^d ≤ H := Nat.pow_le_pow_right hp (by omega)
  have hE : (bits.length+1)^e ≤ H := Nat.pow_le_pow_right hp (by omega)
  have h2 : (bits.length+1)^2 ≤ H := Nat.pow_le_pow_right hp (by omega)
  have hpay : H ≤ H*E := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left H he
  have hs : (bits.length+1)^2 ≤ H*E := h2.trans hpay
  have hone : 1 ≤ H*E := by
    have hh : 1 ≤ H := Nat.one_le_pow _ _ hp
    exact hh.trans hpay
  have hr0:=ha bits
  change SemiprimeD1StackRootPacketInventoryBounds.runBound bits ≤ a*(bits.length+1)^d*E at hr0
  have hr : SemiprimeD1StackRootPacketInventoryBounds.runBound bits ≤ a*H*E :=
    hr0.trans (Nat.mul_le_mul_right E (Nat.mul_le_mul_left a hd))
  have hw0:=hb bits
  change SemiprimeD1StackMarkedRootRecordsBounds.runBound bits ≤
    b*(bits.length+1)^e*2^(58*SemiprimeMacroParameters.scopeBound bits.length) at hw0
  have hexp : (2:ℕ)^(58*SemiprimeMacroParameters.scopeBound bits.length) ≤ E :=
    Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) (Nat.mul_le_mul_right _ (by decide : 58 ≤ (114000:ℕ)))
  have hw : SemiprimeD1StackMarkedRootRecordsBounds.runBound bits ≤ b*H*E :=
    hw0.trans (Nat.mul_le_mul (Nat.mul_le_mul_left b hE) hexp)
  change runBound bits ≤ (a+b+3100)*H*E
  unfold runBound
  nlinarith only [hr,hw,hs,hone]
/-- All2505 allocated words and actual return cells admit the SAME fixed original-scope rate. -/
theorem cells_cap_monomial : ∃ A d : ℕ,∀bits : List Bool,
    2506*(bits.length+runBound bits) ≤
      A*(bits.length+1)^d*2^(114000*SemiprimeMacroParameters.scopeBound bits.length) := by
  obtain ⟨a,d,ha⟩:=runBound_monomial
  refine ⟨2506*(a+1),d+1,?_⟩
  intro bits
  let H:=(bits.length+1)^(d+1)
  let E:=(2:ℕ)^(114000*SemiprimeMacroParameters.scopeBound bits.length)
  have hp : 1 ≤ bits.length+1 := by omega
  have he : 1 ≤ E := Nat.one_le_pow _ _ (by decide : 1 ≤ (2:ℕ))
  have hd : (bits.length+1)^d ≤ H := Nat.pow_le_pow_right hp (by omega)
  have hl : bits.length+1 ≤ H := by
    simpa only [pow_one] using Nat.pow_le_pow_right hp (by omega : 1 ≤ d+1)
  have hpay : H ≤ H*E := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left H he
  have hn : bits.length ≤ H*E := (by omega : bits.length ≤ H).trans hpay
  have ht : runBound bits ≤ a*H*E :=
    (ha bits).trans (Nat.mul_le_mul_right E (Nat.mul_le_mul_left a hd))
  change 2506*(bits.length+runBound bits) ≤ (2506*(a+1))*H*E
  nlinarith only [hn,ht]
end RiemannGaussian.SemiprimeD1StackPackedRootInputResources
