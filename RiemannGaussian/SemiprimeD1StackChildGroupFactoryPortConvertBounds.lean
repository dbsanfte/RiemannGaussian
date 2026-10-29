/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryPortConvert
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryOperationBounds
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryUnaryScopeBounds
/-! # Both actual port/order conversion clocks exclude accumulated caller logs
The real13-role sweep drains the actual binary operand twice, actual unary
output once and all empty converter-private/shadow fields. No earlier row log
is scanned or reset, and the converter's VALUE cost is explicitly retained.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryPortConvertBounds
open SemiprimeD1StackChildGroupFactoryRoles
namespace C
export SemiprimeD1StackChildGroupFactoryPortConvert (copied converted logged logSite timeBound)
end C
namespace Reuse
export SemiprimeD1StackChildGroupFactoryPortReuse (bankRole role timeBound)
end Reuse
namespace O
export SemiprimeD1StackPortOrdinalStream (result)
end O
open SemiprimeD1TensorTapeCodec (vectorBits)
/-- Exact actual fixed13-role reuse time after either real unary row logger. -/
theorem reuse_time (ordering:Bool) (before:Stack→List Bool) (words:List (List Bool))
    (hw:before (Reuse.bankRole ordering)=vectorBits words):
    Reuse.timeBound ordering (C.logged ordering before words)=
      2*(vectorBits words).length+(O.result words).length+13:=by
  cases ordering <;>
    simp [Reuse.bankRole,aux] at hw <;>
    simp [Reuse.timeBound,Reuse.role,Reuse.bankRole,C.logged,C.logSite,
      SemiprimeD1StackChildGroupFactoryWordLog.historyRole,C.converted,C.copied,
      SemiprimeD1StackChildGroupFactoryCalls.withOrdinal,
      SemiprimeD1StackPortOrdinalStreamExecution.done,SemiprimeD1StackPortOrdinalStreamComponents.data,
      aux,ordinal,hw] <;> omega
/-- Actual binary-width AND actual generated ordinal VALUE are both paid at each fixed conversion site. -/
theorem timeBound_le (ordering:Bool) (before:Stack→List Bool) (words:List (List Bool)) (cap:Nat)
    (hw:before (Reuse.bankRole ordering)=vectorBits words)
    (hl:∀w∈words,w.length≤cap) (hv:∀w∈words,SemiprimeBitArithmetic.bitValue w≤cap):
    C.timeBound ordering before words≤10000*(words.length+1)*(cap+1):=by
  have ht:=SemiprimeD1StackPortOrdinalStreamBounds.timeBound_le words cap hl hv
  have hb:=SemiprimeD1StackPortOrdinalStreamBounds.bank_length words cap hl
  have hu:=SemiprimeD1StackChildGroupFactoryUnaryScopeBounds.unary_length words cap hv
  have hlog:=SemiprimeD1StackChildGroupFactoryOperationBounds.word_log_time (O.result words)
  dsimp only [C.timeBound]
  rw [reuse_time ordering before words hw]
  nlinarith
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryPortConvertBounds
