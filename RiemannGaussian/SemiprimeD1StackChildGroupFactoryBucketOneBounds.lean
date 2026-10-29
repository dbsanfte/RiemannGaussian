/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryBucketScanBounds
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryBucketOne
/-! # One complete observed-packet source has a uniform paid metadata clock
The bound includes actual packet parse, complete endpoint scan, both reversals,
real unary conversion, bucket record and all15 physical reuse drains. Earlier
accumulated bucket history never enters this iteration's cost.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryBucketOneBounds
open SemiprimeD1StackChildGroupFactoryRoles
namespace One
export SemiprimeD1StackChildGroupFactoryBucketOne (scanned prepared timeBound)
end One
namespace E
export SemiprimeD1StackChildGroupFactoryBucketParse (Endpoint)
end E
namespace View
export SemiprimeD1StackChildGroupFactoryBucketLoopView (selected portWords records)
end View
namespace SV
export SemiprimeD1StackChildGroupFactoryBucketScanView (result_other result_children result_ports)
end SV
namespace Op
export SemiprimeD1StackChildGroupFactoryOperationBounds (endpointBytes)
end Op
/-- Whole actual observed-packet iteration clock; raw/value limits are derived metadata estimates only. -/
theorem timeBound_le (before:Stack→List Bool) (es:List E.Endpoint) (packet tail position:List Bool) (B L G:Nat)
    (hc:∀e∈es,Op.endpointBytes e≤B) (hp:position.length+2*es.length≤L)
    (hv:SemiprimeBitArithmetic.bitValue position+es.length≤G):
    One.timeBound before es packet tail position≤
      100000000*(B+packet.length+L+G+1)*(es.length+1):=by
  have hs:=SemiprimeD1StackChildGroupFactoryBucketScanBounds.source_time es packet position B L hc hp
  have hchildren:=SemiprimeD1StackChildGroupFactoryBucketScanBounds.child_bytes es packet position B L hc hp
  have hwords:(View.portWords es packet position).length≤es.length:=by
    simpa only [View.portWords,List.length_map] using SemiprimeD1StackChildGroupFactoryCounterBounds.selected_length es packet position
  have hlen:∀w∈View.portWords es packet position,w.length≤L+G:=by
    intro w hw
    obtain ⟨p,hp',rfl⟩:=List.mem_map.mp hw
    have h:=(SemiprimeD1StackChildGroupFactoryCounterBounds.selected_word_bounds es packet position p hp').1
    omega
  have hvalue:∀w∈View.portWords es packet position,SemiprimeBitArithmetic.bitValue w≤L+G:=by
    intro w hw
    obtain ⟨p,hp',rfl⟩:=List.mem_map.mp hw
    have h:=(SemiprimeD1StackChildGroupFactoryCounterBounds.selected_word_bounds es packet position p hp').2
    omega
  have hpacket:One.scanned before es packet tail position (aux .packetKey)=packet:=by
    rw [One.scanned,SV.result_other _ _ _ _ _ (by intro j;fin_cases j <;> decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    rfl
  have hjoint:One.scanned before es packet tail position (aux .jointKey)=View.records es packet position++[false]:=
    SV.result_children _ _ _ _
  have hbank:One.scanned before es packet tail position (aux .portBank)=
      SemiprimeD1TensorTapeCodec.vectorBits (View.portWords es packet position):=SV.result_ports _ _ _ _
  have hconvert:=SemiprimeD1StackChildGroupFactoryBucketOperationBounds.convert_time
    (One.scanned before es packet tail position) packet (View.records es packet position++[false])
    (View.portWords es packet position) (L+G) hpacket hjoint hbank hlen hvalue
  simp only [List.length_append,List.length_cons,List.length_nil] at hconvert
  dsimp only [One.timeBound]
  nlinarith
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryBucketOneBounds
