/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryGridPowerLoop
/-! # Complete internal actual power used by the whole original grid source
The only runtime exponent is the physically copied actual marker tape. The
whole-grid caller acquires it from originala or its actual computedm. Zero
count returns the exact literal oneWord even at zero rational width.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryGridPower
open SemiprimeD1StackRecoveryGrid SemiprimeD1StackRecoveryGridView SemiprimeD1StackRecoveryGridCalls
open SemiprimeD1StackRecoveryGridRegisters SemiprimeD1StackRecoveryGridOperationInput
open SemiprimeD1StackRecoveryGridPowerSeed SemiprimeD1StackRecoveryGridPowerLoop
open SemiprimeD1StackProcedureTrace
/-- Own whole helper clock includes both real old-accumulator drains, three literal one cells, actual counter reads and all R36 calls. -/
def runBound (part:PowerSite) (width:List Bool) (x:SemiprimeRationalBits.RationalWord) (n:Nat) (w:Words) :Nat:=
  seedTime part w+loopTime part width x 0 n (putReg w (powerDestination part) SemiprimeJetBits.oneWord)
/-- Actual internal whole power: every fitted multiplication consumes the actual counter and preserves the exact original operand orientation. -/
theorem power_run (part:PowerSite) (width:List Bool) (x:SemiprimeRationalBits.RationalWord) (n:Nat) (w:Words)
    (hr:w.rational=emptyRational width) (hs:w.auxiliary .copyScratch=[])
    (hc:w.auxiliary .powerTodo=List.replicate n true)
    (hx:w.registers (powerBase part,false)=signed x) (hxd:w.registers (powerBase part,true)=x.denominator) :
    ∃q ≤ runBound part width x n w,Runs program q (.power part .clearSigned) (bank w) (.power part .done)
      (bank (finish w part (SemiprimeD1RecoveryPowerBits.power width x n).word)):=by
  let seeded:=putReg w (powerDestination part) SemiprimeJetBits.oneWord
  have h0:=seed_run part w
  have hr1:seeded.rational=emptyRational width:=hr
  have hs1:seeded.auxiliary .copyScratch=[]:=hs
  have hc1:seeded.auxiliary .powerTodo=List.replicate n true:=hc
  have ha1:seeded.registers (powerDestination part,false)=signed (SemiprimeD1RecoveryPowerBits.power width x 0).word:=
    (putReg_fields w (powerDestination part) SemiprimeJetBits.oneWord).1
  have had1:seeded.registers (powerDestination part,true)=(SemiprimeD1RecoveryPowerBits.power width x 0).word.denominator:=
    (putReg_fields w (powerDestination part) SemiprimeJetBits.oneWord).2
  have hx1:seeded.registers (powerBase part,false)=signed x:=
    (power_base_retained w part SemiprimeJetBits.oneWord false).trans hx
  have hxd1:seeded.registers (powerBase part,true)=x.denominator:=
    (power_base_retained w part SemiprimeJetBits.oneWord true).trans hxd
  obtain ⟨q,hq,h1⟩:=loop_run part width x 0 n seeded hr1 hs1 hc1 ha1 had1 hx1 hxd1
  change Runs program q _ _ _ (bank (finish (putReg w (powerDestination part) SemiprimeJetBits.oneWord)
    part (SemiprimeD1RecoveryPowerBits.power width x (0+n)).word)) at h1
  rw [finish_putReg,Nat.zero_add] at h1
  refine ⟨seedTime part w+q,?_,PTrace.join h0 h1⟩
  exact Nat.add_le_add_left hq (seedTime part w)
end RiemannGaussian.SemiprimeD1StackRecoveryGridPower
