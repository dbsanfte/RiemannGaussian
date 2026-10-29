/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryCoordinateOriginalRows
import RiemannGaussian.SemiprimeD1StackRecoveryCoordinateSemanticCaps
import RiemannGaussian.SemiprimeD1PhysicalRecursiveBounds
/-! # Original retained-phase byte caps from semantic shape and working precision
Only native semantic phase/block/old-rank/word-width facts are used. No native
clock or polynomial of the recursive continuation's runtime enters any bound.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 65536
namespace RiemannGaussian.SemiprimeD1StackRecoveryCoordinateOriginalCaps
open SemiprimeD1StackRecoveryCoordinateOriginalRows SemiprimeD1StackRecoveryCoordinateSemanticCaps
open SemiprimeD1StackRecoveryCoordinateEncoding
open SemiprimeD1JetAxes SemiprimeD1TensorNetwork
namespace V
export SemiprimeD1RecursiveRecovery (retained)
end V
namespace B
export SemiprimeD1PhysicalRecursiveBounds (phase_blocks_size)
end B
/-- Original actual phase-bank count is the complete original grid, including rejected phases. -/
theorem retained_count (next:Context→Network→SemiprimeD1JetAffineCoefficient.JetRun)
    (ctx:Context) (net:Network) (a u:Nat):
    (originalPhases (V.retained next ctx net a u)).length=SemiprimeD1WireKernelOriginal.size a:=by
  rw [original_count]
  simp only [V.retained,List.size_toArray,List.length_map,List.length_finRange]
/-- Every actual retained phase derives its block count, old rank and child working-precision cap. -/
theorem retained_shape (next:Context→Network→SemiprimeD1JetAffineCoefficient.JetRun)
    (ctx:Context) (net:Network) (a u:Nat) (hu:u ≤edgeCount net):
    ∀blocks∈originalPhases (V.retained next ctx net a u),blocks.length ≤4*edgeCount net ∧
      ∀words∈blocks,words.length=ctx.rank ∧∀word∈words,word.length ≤
        SemiprimeD1ModeRate.workingPrecision (edgeCount net) u a 0 ctx.precision:=by
  intro blocks hb
  obtain ⟨point,hpoint,rfl⟩:=List.mem_map.mp hb
  have hp:point∈V.retained next ctx net a u:=by simpa using hpoint
  rw [V.retained,List.mem_toArray] at hp
  obtain ⟨t,_,rfl⟩:=List.mem_map.mp hp
  constructor
  · simpa only [phaseWords,Array.length_toList] using B.phase_blocks_size next ctx net a u t hu
  · intro words hw
    have hm:words∈(SemiprimeD1RecursiveCounter.phase next ctx net a u t).blocks:=by simpa only [phaseWords,Array.mem_toList_iff] using hw
    constructor
    · exact (SemiprimeD1RecursivePhaseBounds.phase_blocks_good next ctx net a u t words hm).1
    · intro word hword
      exact SemiprimeD1RecursivePhaseBounds.phase_word_bound next ctx net a u t words hm word hword
/-- Source-derived input phase-bank byte cap: old rank and child working precision remain distinct. -/
theorem original_bank_bytes (next:Context→Network→SemiprimeD1JetAffineCoefficient.JetRun)
    (ctx:Context) (net:Network) (a u:Nat) (hu:u ≤edgeCount net):
    (originalTape (V.retained next ctx net a u)).length ≤bankByteBound
      (SemiprimeD1WireKernelOriginal.size a) (4*edgeCount net) ctx.rank
      (SemiprimeD1ModeRate.workingPrecision (edgeCount net) u a 0 ctx.precision):=by
  have hs:=retained_shape next ctx net a u hu
  exact bank_bytes _ _ _ _ _ (retained_count next ctx net a u).le
    (fun blocks hb=>(hs blocks hb).1) (fun blocks hb words hw=>((hs blocks hb).2 words hw).1.le)
    (fun blocks hb words hw=>((hs blocks hb).2 words hw).2)
/-- Original acquired child-coordinate output has its semantic byte cap without any subtree runtime. -/
theorem original_result_bytes (next:Context→Network→SemiprimeD1JetAffineCoefficient.JetRun)
    (ctx:Context) (net:Network) (a u:Nat) (hu:u ≤edgeCount net) (key:List Bool):
    (result (originalPhases (V.retained next ctx net a u)) key).length ≤
      4*SemiprimeD1WireKernelOriginal.size a*(4*edgeCount net)*
        (SemiprimeD1ModeRate.workingPrecision (edgeCount net) u a 0 ctx.precision+1)+
          4*SemiprimeD1WireKernelOriginal.size a+1:=by
  have hs:=retained_shape next ctx net a u hu
  exact result_bytes _ key _ _ _ (retained_count next ctx net a u).le
    (fun blocks hb=>(hs blocks hb).1) (fun blocks hb words hw=>((hs blocks hb).2 words hw).2)
end RiemannGaussian.SemiprimeD1StackRecoveryCoordinateOriginalCaps
