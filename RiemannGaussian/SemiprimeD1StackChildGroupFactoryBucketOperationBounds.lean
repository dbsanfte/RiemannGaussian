/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryOperationBounds
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryBucketConvert
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryUnaryScopeBounds
/-! # Actual bucket parse/emit/conversion/reuse clocks are paid by their own words
The fifteen-role cleanup contains only actual packet/child/ID/converter bytes;
it never drains or rescans the growing earlier bucket log.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryBucketOperationBounds
open SemiprimeD1StackChildGroupFactoryRoles
namespace E
export SemiprimeD1StackChildGroupFactoryBucketParse (Endpoint payload timeBound)
end E
namespace Emit
export SemiprimeD1StackChildGroupFactoryBucketEmit (payload row portRow timeBound)
end Emit
namespace C
export SemiprimeD1StackChildGroupFactoryBucketConvert (copied converted logged timeBound)
end C
namespace Reuse
export SemiprimeD1StackChildGroupFactoryBucketReuse (timeBound)
end Reuse
namespace Record
export SemiprimeD1StackChildGroupFactoryBucketRecord (payload row timeBound)
end Record
namespace O
export SemiprimeD1StackPortOrdinalStream (result)
end O
namespace Op
export SemiprimeD1StackChildGroupFactoryOperationBounds (endpointBytes)
end Op
open SemiprimeD1TensorTapeCodec (vectorBits)
/-- Real five-field parser plus every validity/tag/EOF inspection is linear in actual raw bytes. -/
theorem parse_time (e:E.Endpoint):E.timeBound e≤1000*Op.endpointBytes e:=by
  simp only [E.timeBound,E.payload,SemiprimeSourceHistogramKeyBits.frame_length,List.length_nil,Op.endpointBytes]
  omega
/-- Actual child and binary-port record logs preserve all original padding and have linear own work. -/
theorem emit_time (e:E.Endpoint) (position:List Bool):Emit.timeBound e position≤1000*(Op.endpointBytes e+position.length+1):=by
  simp only [Emit.timeBound,Emit.payload,Emit.row,Emit.portRow,SemiprimeSourceHistogramKeyBits.frame_length,
    List.length_nil,List.length_cons,Op.endpointBytes]
  omega
/-- Only matched packet identity enters the literal branch; both paths have a paid linear byte bound. -/
theorem visit_time (e:E.Endpoint) (packet position:List Bool):
    SemiprimeD1StackChildGroupFactoryBucketVisit.timeBound e packet position≤
      10000*(Op.endpointBytes e+packet.length+position.length+1):=by
  have hp:=parse_time e
  have he:=emit_time e position
  have hc:=SemiprimeD1StackChildGroupFactoryOperationBounds.compare_time e.packet packet
  have hi:=SemiprimeD1StackChildGroupFactoryOperationBounds.increment_time position
  change SemiprimeD1StackChildGroupFactoryBucketCompare.timeBound e.packet packet≤_ at hc
  change SemiprimeD1StackChildGroupFactoryBucketIncrement.timeBound position≤_ at hi
  by_cases h:e.packet=packet <;>
    simp only [SemiprimeD1StackChildGroupFactoryBucketVisit.timeBound,h,ite_true,ite_false,
      SemiprimeD1StackChildGroupFactoryBucketCleanup.timeBound,Op.endpointBytes] at hp he hc hi ⊢ <;> omega
/-- The three actual final bucket fields have a linear paid preserving-frame/logger clock. -/
theorem record_time (packet children ports:List Bool):Record.timeBound packet children ports≤
    1000*(packet.length+children.length+ports.length+1):=by
  simp only [Record.timeBound,Record.payload,Record.row,SemiprimeSourceHistogramKeyBits.frame_length,
    List.length_nil,List.length_cons]
  omega
/-- Exact actual fifteen-word cleanup cost; retained prior bucket history is absent. -/
theorem reuse_time (before:Stack→List Bool) (packet children:List Bool) (words:List (List Bool))
    (hp:before (aux .packetKey)=packet) (hj:before (aux .jointKey)=children)
    (hw:before (aux .portBank)=vectorBits words):
    Reuse.timeBound (C.logged before packet children words)=packet.length+children.length+
      2*(vectorBits words).length+(O.result words).length+15:=by
  simp only [aux] at hp hj hw
  simp [Reuse.timeBound,C.logged,C.converted,C.copied,SemiprimeD1StackChildGroupFactoryCalls.withOrdinal,
    SemiprimeD1StackPortOrdinalStreamExecution.done,SemiprimeD1StackPortOrdinalStreamComponents.data,
    aux,ordinal,hp,hj,hw]
  omega
/-- Whole actual ordinal conversion/log/reuse clock, with all retained binary and emitted unary bytes paid. -/
theorem convert_time (before:Stack→List Bool) (packet children:List Bool) (words:List (List Bool)) (cap:Nat)
    (hp:before (aux .packetKey)=packet) (hj:before (aux .jointKey)=children)
    (hw:before (aux .portBank)=vectorBits words)
    (hl:∀w∈words,w.length≤cap) (hv:∀w∈words,SemiprimeBitArithmetic.bitValue w≤cap):
    C.timeBound before packet children words≤
      10000*(packet.length+children.length+(words.length+1)*(cap+1)+1):=by
  have ht:=SemiprimeD1StackPortOrdinalStreamBounds.timeBound_le words cap hl hv
  have hb:=SemiprimeD1StackPortOrdinalStreamBounds.bank_length words cap hl
  have hu:=SemiprimeD1StackChildGroupFactoryUnaryScopeBounds.unary_length words cap hv
  have hr:=record_time packet children (O.result words)
  dsimp only [C.timeBound]
  rw [reuse_time before packet children words hp hj hw]
  nlinarith
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryBucketOperationBounds
