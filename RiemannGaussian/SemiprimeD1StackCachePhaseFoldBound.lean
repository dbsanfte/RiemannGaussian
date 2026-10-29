/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackCachePhaseMetadataBounds
/-! # The SAME actual prepared fold fits a fixed actual four-input bit polynomial -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackCachePhaseFoldBound
open SemiprimeD1StackCachePhase SemiprimeD1StackCachePhaseProjection
open SemiprimeD1StackCachePhaseInputBounds SemiprimeD1StackCachePhaseMetadataBounds
open SemiprimeD1StackJetFoldWords (Modes)
open SemiprimeD1StackJetFoldInputBounds (workNodes)
/-- Generic monomial identity avoids expanding a concrete original-source expression. -/
theorem scaled_sixth (S:Nat) :
    10000000000000*(100000001*S^2)^6*S=10000000000000*100000001^6*S^13 :=by ring
/-- Own actual fold source clock is paid by actual heap/counter/reference and child tape bits. -/
theorem foldBound_le (banks:List (Fresh.Stack→List Bool)) (i:Fin banks.length) (axes:List Nat)
    (p:List Bool) (q:Nat) (newP:List Bool) (modes:Modes) (hv:ValidCache banks[i.val] axes p q newP) :
    SemiprimeD1StackJetFoldBounds.runBound (q::axes) newP modes ≤ 10^70*(inputSize banks i modes+1)^13 :=by
  have hresource:=fold_resource_le banks i axes p q newP modes hv
  have h1:1 ≤ (inputSize banks i modes+1)^2:=Nat.one_le_pow _ _ (by omega)
  have hr:SemiprimeD1StackJetFoldBounds.resource (q::axes) newP modes+1 ≤
      100000001*(inputSize banks i modes+1)^2:=by omega
  have hn:workNodes modes ≤ inputSize banks i modes+1:=
    (workNodes_le_tape modes).trans (by unfold inputSize;omega)
  have hc:(10000000000000:Nat)*100000001^6 ≤ 10^70:=by norm_num
  calc
    _=10000000000000*(SemiprimeD1StackJetFoldBounds.resource (q::axes) newP modes+1)^6*workNodes modes:=
      SemiprimeD1StackJetFoldBounds.runBound_formula (q::axes) newP modes
    _≤10000000000000*(100000001*(inputSize banks i modes+1)^2)^6*(inputSize banks i modes+1):=by gcongr
    _=10000000000000*100000001^6*(inputSize banks i modes+1)^13:=scaled_sixth _
    _≤10^70*(inputSize banks i modes+1)^13:=Nat.mul_le_mul_right _ hc
end RiemannGaussian.SemiprimeD1StackCachePhaseFoldBound
