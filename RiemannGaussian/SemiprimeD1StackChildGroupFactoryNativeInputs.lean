/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryReadyResources
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryNativeFields
import RiemannGaussian.SemiprimeD1StackSourceSelectionAcquireOriginal
/-! # Real retained cache bytes internally supply the entire original factory input ABI
This is a data-boundary theorem, not a runtime getter. Complete stopped63/21
banks plus actual two inventory tapes discharge every parser/key/domain fact.
No decoded field list, selected-colour mask, ordering, permutation or answer is
an input to the fixed258 source. Four context headers are retained separately.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryNativeInputs
namespace R
export SemiprimeD1StackChildGroupFactoryReady (Header sourceInputs)
end R
namespace S
export SemiprimeD1StackChildGroupFactoryReady.S (Stack environmentStack aux)
end S
namespace O
export SemiprimeD1StackChildGroupFactoryReady.P (Stack)
end O
namespace I
export SemiprimeD1StackChildGroupFactoryReady.I (Stack output packets)
end I
namespace N
export SemiprimeD1TensorNetwork (Network arity owner)
end N
namespace Acq
export SemiprimeD1StackSourceSelectionAcquireEncoding (selectorDone occurrenceDone)
end Acq
namespace Fld
export SemiprimeD1StackChildGroupFactoryNativeFields (source fields pairs_original placements_original domains)
end Fld
namespace Act
export SemiprimeD1StackChildGroupFactoryNativeActivation (originalIDs)
end Act
/-- Exact actual stopped-cache interpretation, discharged from producer source theorems. -/
structure CacheMeaning (net:N.Network) (a:Nat) (s:S.Stack→List Bool) (p:O.Stack→List Bool)
    (iv:I.Stack→List Bool):Prop where
  selector:∀k,s k=(Acq.selectorDone net a).data k
  occurrence:∀k,p k=(Acq.occurrenceDone net).data k
  placements:iv I.output=SemiprimeD1TensorTapeCodec.vectorBits
    ((Fld.source net.leftCount net.rows.length a (N.arity net.rows) (N.owner net.rows)).placements.map
      SemiprimeD1StackPacketInventoryEncoding.placementBytes)
  packets:iv I.packets=SemiprimeD1TensorTapeCodec.vectorBits
    (Fld.source net.leftCount net.rows.length a (N.arity net.rows) (N.owner net.rows)).state.packets
/-- All source conditions follow from already reached physical bank words and actual unary colourIndex. -/
theorem valid_original (net:N.Network) (a:Nat) (s:S.Stack→List Bool) (p:O.Stack→List Bool)
    (iv:I.Stack→List Bool) (header:R.Header) (q:Fin a) (hc:CacheMeaning net a s p iv)
    (hq:header.colourIndex=List.replicate q.val true):
    SemiprimeD1StackChildGroupFactoryTraceBounds.Valid (R.sourceInputs s p iv header) a q.val
      (Act.originalIDs net.leftCount net.rows.length a (N.arity net.rows) (N.owner net.rows))
      (Fld.source net.leftCount net.rows.length a (N.arity net.rows) (N.owner net.rows)).state.packets
      (Fld.fields net.leftCount net.rows.length a (N.arity net.rows) (N.owner net.rows)):=by
  constructor
  · exact SemiprimeD1IncidenceSearch.run_valid _ _ _ _ _ _
  · change s (S.environmentStack (SemiprimeD1StackSourceEnvironment.aux .dictionary))=_
    rw [hc.selector]
    rfl
  · change s (S.aux .catalogue)=_
    rw [hc.selector]
    rfl
  · exact hq
  · change (Act.originalIDs net.leftCount net.rows.length a (N.arity net.rows) (N.owner net.rows)).length=
      (s (S.aux .owners)).length+(s (S.aux .factors)).length
    rw [hc.selector,hc.selector]
    change (SemiprimeD1IncidenceSearch.run net.leftCount net.rows.length 64 a (N.arity net.rows) (N.owner net.rows)).value.length=
      (List.replicate net.leftCount true).length+(List.replicate net.rows.length true).length
    rw [List.length_replicate,List.length_replicate]
    exact SemiprimeD1IncidenceSearch.run_length _ _ _ _ _ _
  · change p .output=_
    rw [hc.occurrence]
    change (SemiprimeD1StackSourceOccurrencesOriginal.originalDone net).data .output=_
    rw [SemiprimeD1StackSourceOccurrencesOriginal.output_original,Fld.pairs_original]
    rw [←SemiprimeD1StackSourceIncidenceSelectOccurrences.network_original_keys net a]
    rfl
  · exact hc.placements.trans (Fld.placements_original _ _ _ _ _).symm
  · intro field hf
    have h:=Fld.domains net.leftCount net.rows.length a (N.arity net.rows) (N.owner net.rows) field hf
    have hlen:=SemiprimeD1IncidenceSearch.run_length net.leftCount net.rows.length 64 a (N.arity net.rows) (N.owner net.rows)
    simpa only [Act.originalIDs,hlen] using h
  · exact hc.packets
/-- The original owner/factor count is retained literally by the actual selector bank. -/
theorem count_original (net:N.Network) (a:Nat) (s:S.Stack→List Bool) (p:O.Stack→List Bool)
    (iv:I.Stack→List Bool) (header:R.Header) (hc:CacheMeaning net a s p iv):
    (R.sourceInputs s p iv header).owners.length+(R.sourceInputs s p iv header).factors.length=net.leftCount+net.rows.length:=by
  change (s (S.aux .owners)).length+(s (S.aux .factors)).length=_
  rw [hc.selector,hc.selector]
  change (List.replicate net.leftCount true).length+(List.replicate net.rows.length true).length=_
  simp only [List.length_replicate]
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryNativeInputs
