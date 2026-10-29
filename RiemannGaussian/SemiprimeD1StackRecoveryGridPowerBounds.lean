/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryGridOperationBounds
import RiemannGaussian.SemiprimeD1StackRecoveryGridWordCaps
import RiemannGaussian.SemiprimeD1StackRecoveryGridPowerSource
/-! # Own whole physical power clocks from semantic cache widths
Each loop iteration uses W-fitted cache words or the literal one seed. Neither
operand lengths nor the number of iterations are inferred from elapsed time.
The actual copied counter markers and every real return are explicitly paid.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryGridPowerBounds
open SemiprimeD1StackRecoveryGrid SemiprimeD1StackRecoveryGridView
namespace Caps
export SemiprimeD1StackRecoveryGridWordCaps (Registers Data auxiliary_data auxiliary_registers put_registers put_data power_width mass_le)
end Caps
namespace PLoop
export SemiprimeD1StackRecoveryGridPowerLoop (loopTime afterPop afterStep)
end PLoop
namespace Whole
export SemiprimeD1StackRecoveryGridPower (runBound)
export SemiprimeD1StackRecoveryGridPowerSeed (seedTime)
end Whole
namespace Source
export SemiprimeD1StackRecoveryGridPowerSource (runBound exponent ready)
end Source
namespace Op
export SemiprimeD1StackRecoveryGridOperation (timeBound)
export SemiprimeD1StackRecoveryGridOperationBounds (time_le)
end Op
/-- One actual counter-read/whole-operation/real-return envelope, with a fixed coefficient before all inputs. -/
def cap (B L:Nat) :Nat:=10^38*(L+B^6+1)
/-- Actual operation cleanup charges retained foreign words additively, while source operands retain their semantic widths. -/
theorem step_cap (q B L:Nat) (hq:q≤10^35*(104*L+B^6+1)) :q+3≤ cap B L:=by
  unfold cap
  omega
/-- Pure arithmetic composition for the same actual loop, abstracting proof-side payload terms only. -/
theorem recursion_cap (q previous C n:Nat) (hq:q+3≤ C) (hp:previous≤ n*C+1) :
    1+(q+2)+previous≤(n+1)*C+1:=by
  simp only [Nat.add_mul,Nat.one_mul]
  omega
attribute [local irreducible] Op.timeBound cap
/-- Every physical power iteration has a uniform own cap from W, actual cache widths and retained words. -/
theorem loop_le (part:PowerSite) (width:List Bool) (x:SemiprimeRationalBits.RationalWord) (k n:Nat) (w:Words) (B L:Nat)
    (hW:width.length+2≤ B) (hBL:B≤ L) (hx:x.numerator.magnitude.length≤ B) (hd:x.denominator.length≤ B)
    (hn:n≤ L) (hr:Caps.Registers w B) (hw:Caps.Data w L) :
    PLoop.loopTime part width x k n w≤ n*cap B L+1:=by
  induction n generalizing k w with
  | zero=>simp only [PLoop.loopTime,Nat.zero_mul,Nat.zero_add,le_refl]
  | succ n ih=>
    let popped:=PLoop.afterPop w n
    have hpR:Caps.Registers popped B:=hr
    have hpD:Caps.Data popped L:=Caps.auxiliary_data w .powerTodo (List.replicate n true) L hw
      (by simp only [List.length_replicate];omega)
    have hpMass:=Caps.mass_le popped L hpD
    have hacc:=Caps.power_width width x k B hW
    let acc:=(SemiprimeD1RecoveryPowerBits.power width x k).word
    have hOp:=Op.time_le (.power part) popped acc.numerator.negative acc.numerator.magnitude acc.denominator
      x.numerator.negative x.numerator.magnitude x.denominator width B (by omega) (by exact Nat.le_trans (Nat.le_add_right _ _) hacc.1)
      hacc.2 hx hd (by omega) (hpR _ false) (hpR _ true)
    have hOp':Op.timeBound (.power part) popped acc.numerator.negative acc.numerator.magnitude acc.denominator
        x.numerator.negative x.numerator.magnitude x.denominator width≤10^35*(104*L+B^6+1):=
      hOp.trans (Nat.mul_le_mul_left _ (by omega))
    have hstep:=step_cap _ B L hOp'
    have hnxt:=Caps.power_width width x (k+1) B hW
    let next:=PLoop.afterStep part width x k n w
    have hnR:Caps.Registers next B:=Caps.put_registers popped (powerDestination part)
      (SemiprimeD1RecoveryPowerBits.power width x (k+1)).word B hpR hnxt.1 hnxt.2
    have hnD:Caps.Data next L:=Caps.put_data popped (powerDestination part)
      (SemiprimeD1RecoveryPowerBits.power width x (k+1)).word L hpD (hnxt.1.trans hBL) (hnxt.2.trans hBL)
    have hnext:=ih (k+1) next (by omega) hnR hnD
    change 1+(Op.timeBound (.power part) popped acc.numerator.negative acc.numerator.magnitude acc.denominator
      x.numerator.negative x.numerator.magnitude x.denominator width+2)+PLoop.loopTime part width x (k+1) n next≤(n+1)*cap B L+1
    exact recursion_cap _ _ _ n hstep hnext
/-- The two old-accumulator drains and three literal seed pushes are charged before any multiply. -/
theorem seed_le (part:PowerSite) (w:Words) (B:Nat) (hr:Caps.Registers w B) :Whole.seedTime part w≤2*B+5:=by
  have hn:=hr (powerDestination part) false
  have hd:=hr (powerDestination part) true
  unfold Whole.seedTime
  omega
/-- The positive fixed physical resource envelope absorbs the literal seed and both EOF branches. -/
theorem seed_cap (B L:Nat) (hBL:B≤ L) :2*B+6≤ cap B L:=by
  unfold cap
  omega
/-- The actual complete helper, including literal n0 oneWord, is paid from the same source-word/marker envelope. -/
theorem helper_le (part:PowerSite) (width:List Bool) (x:SemiprimeRationalBits.RationalWord) (n:Nat) (w:Words) (B L:Nat)
    (hW:width.length+2≤ B) (hBL:B≤ L) (hx:x.numerator.magnitude.length≤ B) (hd:x.denominator.length≤ B)
    (hn:n≤ L) (hr:Caps.Registers w B) (hw:Caps.Data w L) :Whole.runBound part width x n w≤(n+1)*cap B L:=by
  let seeded:=putReg w (powerDestination part) SemiprimeJetBits.oneWord
  have hsR:Caps.Registers seeded B:=Caps.put_registers w _ SemiprimeJetBits.oneWord B hr (by change 2≤ B;omega) (by change 1≤ B;omega)
  have hsD:Caps.Data seeded L:=Caps.put_data w _ SemiprimeJetBits.oneWord L hw (by change 2≤ L;omega) (by change 1≤ L;omega)
  have hloop:=loop_le part width x 0 n seeded B L hW hBL hx hd hn hsR hsD
  have hseed:=seed_le part w B hr
  have hcap:=seed_cap B L hBL
  unfold Whole.runBound
  change Whole.seedTime part w+PLoop.loopTime part width x 0 n seeded≤(n+1)*cap B L
  rw [Nat.add_mul,Nat.one_mul]
  omega
/-- Exact finite alpha selector contributes only one physically pushed count marker. -/
theorem exponent_le (part:PowerSite) (n:Nat) :Source.exponent part n≤ n+1:=by
  unfold Source.exponent
  split <;> omega
/-- Pure actual-copy/call/return accounting, with no payload evaluation in the arithmetic proof. -/
theorem outer_cap (Q n e delta S:Nat) (hQ:Q≤(e+1)*(10^38*S)) (he:e≤ n+1) (hd:delta≤1) (hS:1≤ S) :
    (5*n+4)+delta+Q+2≤10^40*(n+2)*S:=by
  have h1:(e+1)*S≤(n+2)*S:=Nat.mul_le_mul_right S (by omega)
  have h2:n+2≤(n+2)*S:=by simpa only [Nat.mul_one] using Nat.mul_le_mul_left (n+2) hS
  norm_num1 at hQ ⊢
  nlinarith
/-- Whole actual power-source call pays the acquired counter copy, literal alpha marker, helper and both real return transitions. -/
theorem source_le (part:PowerSite) (w:Words) (width:List Bool) (x:SemiprimeRationalBits.RationalWord) (n B L:Nat)
    (hW:width.length+2≤ B) (hBL:B≤ L) (hx:x.numerator.magnitude.length≤ B) (hd:x.denominator.length≤ B)
    (hn:n+1≤ L) (hr:Caps.Registers w B) (hw:Caps.Data w L) :
    Source.runBound part w width x n≤10^40*(n+2)*(L+B^6+1):=by
  have he:=exponent_le part n
  have hreadyR:Caps.Registers (Source.ready part w n) B:=hr
  have hreadyD:Caps.Data (Source.ready part w n) L:=Caps.auxiliary_data w .powerTodo
    (List.replicate (Source.exponent part n) true) L hw (by simp only [List.length_replicate];omega)
  have h:=helper_le part width x (Source.exponent part n) (Source.ready part w n) B L hW hBL hx hd (by omega) hreadyR hreadyD
  have hdlt:(if part=.alpha then 1 else 0)≤1:=by split <;> omega
  unfold Source.runBound
  have hcap:cap B L=10^38*(L+B^6+1):=by unfold cap;rfl
  rw [hcap] at h
  exact outer_cap _ n _ _ _ h he hdlt (by omega)
end RiemannGaussian.SemiprimeD1StackRecoveryGridPowerBounds
