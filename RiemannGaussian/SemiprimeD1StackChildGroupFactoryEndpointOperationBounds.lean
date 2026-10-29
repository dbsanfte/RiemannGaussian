/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryAcquisitionByteBounds
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryActivationMapBounds
/-! # Own endpoint parser/logger/map-lookup clocks from actual acquired bytes
Both possible physical endpoint sides are accounted for, including inactive
lookups and full eleven-role cleanup. No native reader clock is transported.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryEndpointOperationBounds
namespace P
export SemiprimeD1StackChildGroupFactoryEndpointParse (Fields payload timeBound)
end P
namespace Raw
export SemiprimeD1StackChildGroupFactoryAcquisitionByteBounds (fieldBytes)
end Raw
namespace Old
export SemiprimeD1StackChildGroupFactoryEndpointOldLog (oldPoint row timeBound)
end Old
namespace Emit
export SemiprimeD1StackChildGroupFactoryEndpointEmit (endpoint row timeBound)
end Emit
namespace Test
export SemiprimeD1StackChildGroupFactoryEndpointFlag (timeBound)
end Test
namespace Side
export SemiprimeD1StackChildGroupFactoryEndpointSide (timeBound)
end Side
namespace Occ
export SemiprimeD1StackChildGroupFactoryEndpointOccurrence (timeBound)
end Occ
namespace Map
export SemiprimeD1StackOwnerLookup (records)
end Map
/-- All actual paired Field calls, validity pops and complete current payload have a linear byte cost. -/
theorem parse_time (f:P.Fields):P.timeBound f≤1000*Raw.fieldBytes f:=by
  simp only [P.timeBound,P.payload,SemiprimeSourceHistogramKeyBits.frame_length,List.length_nil,
    List.length_cons,Raw.fieldBytes]
  omega
/-- Every old endpoint is physically logged, including inactive and isolated-side metadata. -/
theorem old_log_time (owner:Bool) (v edge:List Bool):Old.timeBound owner v edge≤1000*(v.length+edge.length+1):=by
  simp only [Old.timeBound,Old.oldPoint,Old.row,SemiprimeSourceHistogramKeyBits.frame_length,
    List.length_nil,List.length_cons]
  omega
/-- An active endpoint's actual five-field row logger is linear in the retained source fields. -/
theorem emit_time (owner:Bool) (v packet slot edge:List Bool):
    Emit.timeBound owner v packet slot edge≤1000*(v.length+packet.length+slot.length+edge.length+1):=by
  simp only [Emit.timeBound,Emit.endpoint,Emit.row,SemiprimeSourceHistogramKeyBits.frame_length,
    List.length_nil,List.length_cons]
  omega
/-- Actual numeric lookup, both copies and full eleven-role cleanup have a physical-byte product bound. -/
theorem lookup_time (query:List Bool) (entries:List (List Bool×List Bool)) (unread:List Bool)
    (hu:unread.length≤(Map.records entries []).length):
    Test.timeBound query (Map.records entries []) entries unread≤
      1000*(query.length+1)*((Map.records entries []).length+1):=by
  have ht:=SemiprimeD1StackOwnerLookupBounds.time_le query entries
  dsimp only [SemiprimeD1StackOwnerLookupBounds.runBound] at ht
  dsimp only [Test.timeBound]
  nlinarith
/-- The actual tested side is covered regardless of its computed activation branch. -/
theorem side_time (owner flag:Bool) (v packet slot edge:List Bool)
    (entries:List (List Bool×List Bool)) (unread:List Bool)
    (hu:unread.length≤(Map.records entries []).length):
    Side.timeBound owner flag v packet slot edge (Map.records entries []) unread entries≤
      10000*(v.length+packet.length+slot.length+edge.length+1)*((Map.records entries []).length+1):=by
  have ho:=old_log_time owner v edge
  have he:=emit_time owner v packet slot edge
  have ht:=lookup_time v entries unread hu
  cases flag <;> simp only [Side.timeBound,Bool.false_eq_true,ite_false,ite_true] <;> nlinarith
/-- Complete original occurrence acquisition pays BOTH actual endpoint lookups, possible logs and raw drains. -/
theorem occurrence_time (ownerFlag factorFlag:Bool) (f:P.Fields) (entries:List (List Bool×List Bool))
    (ownerUnread factorUnread:List Bool)
    (ho:ownerUnread.length≤(Map.records entries []).length)
    (hf:factorUnread.length≤(Map.records entries []).length):
    Occ.timeBound ownerFlag factorFlag f (Map.records entries []) ownerUnread factorUnread entries≤
      100000*Raw.fieldBytes f*((Map.records entries []).length+1):=by
  have hp:=parse_time f
  have hl:=side_time true ownerFlag f.owner f.packet f.slot f.edge entries ownerUnread ho
  have hr:=side_time false factorFlag f.factor f.packet f.slot f.edge entries factorUnread hf
  dsimp only [Occ.timeBound,Raw.fieldBytes,SemiprimeD1StackChildGroupFactoryEndpointCleanup.timeBound] at hp ⊢
  nlinarith
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryEndpointOperationBounds
