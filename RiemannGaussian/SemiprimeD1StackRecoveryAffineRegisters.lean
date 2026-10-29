/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryAffineView
/-! # Exact physical cache updates preserve all unrelated source and array words -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryAffineRegisters
open SemiprimeD1StackRecoveryAffine SemiprimeD1StackRecoveryAffineView
open SemiprimeD1StackRecoveryGrid (Reg)
export SemiprimeD1StackRecoveryAffineView (putReg_fields getReg_putReg)
/-- Only the two actual destination fields can change; raw field padding and all other111 words are retained. -/
theorem putReg_other (w:Words) (r q:Reg) (x:SemiprimeRationalBits.RationalWord) (den:Bool) (hne:q≠r):
    (putReg w r x).registers (q,den)=w.registers (q,den):=
  SemiprimeD1StackRecoveryGridRegisters.putReg_other w.toWords r q x den hne
/-- Two physical overwrites at the same cache preserve only the latest complete actual byte word. -/
theorem putReg_idem (w:Words) (r:Reg) (old x:SemiprimeRationalBits.RationalWord):putReg (putReg w r old) r x=putReg w r x:=by
  have h:=SemiprimeD1StackRecoveryGridRegisters.putReg_idem w.toWords r old x
  exact congrArg (fun base:SemiprimeD1StackRecoveryGridView.Words=>({toWords:=base,added:=w.added}:Words)) h
/-- Actual cache replacement cannot alter the clean real R36 bank or its retained width. -/
theorem putReg_rational (w:Words) (r:Reg) (x:SemiprimeRationalBits.RationalWord):(putReg w r x).rational=w.rational:=rfl
/-- Actual cache replacement retains every old source, counter and framing buffer. -/
theorem putReg_auxiliary (w:Words) (r:Reg) (x:SemiprimeRationalBits.RationalWord):(putReg w r x).auxiliary=w.auxiliary:=rfl
/-- All eight actual q/reader/array/counter words remain byte-identical through a real rational site. -/
theorem putReg_added (w:Words) (r:Reg) (x:SemiprimeRationalBits.RationalWord):(putReg w r x).added=w.added:=rfl
end RiemannGaussian.SemiprimeD1StackRecoveryAffineRegisters
