/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryGridStateCaps
import RiemannGaussian.SemiprimeD1StackRecoveryGridModelBounds
import RiemannGaussian.SemiprimeD1StackRecoveryGridPowerBounds
import RiemannGaussian.SemiprimeD1StackWordFitBounds
/-! # Actual original-input frontend clock and semantic physical boundary caps -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryGridFrontBounds
open SemiprimeD1StackRecoveryGrid SemiprimeD1StackRecoveryGridView
namespace F
export SemiprimeD1StackRecoveryGridFront (result clean centered decremented sizeWord runBound)
end F
namespace Model
export SemiprimeD1StackRecoveryGridModel (view one front_eq)
end Model
namespace R
export SemiprimeD1StackRecoveryGridResource (resource gridSize cacheWidth dataWidth resource_pos a_le M_le u_le t_le width_le grid_le index_le cache_le width_cache cache_data counts_data small_le_cubic)
end R
namespace Caps
export SemiprimeD1StackRecoveryGridWordCaps (Registers Data mass_le put_registers put_data power_width)
end Caps
/-- All actual first-row register/data words satisfy their semantic caps. -/
theorem result_caps (a M u:Nat) (t width:List Bool) :
    Caps.Registers (F.result a M u t width) (R.cacheWidth a width) ∧
    Caps.Data (F.result a M u t width) (R.dataWidth a M u t width):=by
  have hp:=SemiprimeD1StackRecoveryGridPayloadBounds.one_bounded width (SemiprimeD1TaperedLoss.height M u*u)
  have hq:(SemiprimeD1StackRecoveryGridDecrement.difference (F.sizeWord a)).length≤a+2:=by
    exact le_of_eq (SemiprimeD1StackRecoveryGridFront.q_width a M u t width)
  have hr:=SemiprimeD1StackRecoveryGridModelBounds.registers_le a M u (R.gridSize a) 0 t (SemiprimeD1StackRecoveryGridDecrement.difference (F.sizeWord a)) width Model.one hp
  have hd:=SemiprimeD1StackRecoveryGridModelBounds.data_le a M u (R.gridSize a) 0 t (SemiprimeD1StackRecoveryGridDecrement.difference (F.sizeWord a)) width Model.one hp (by omega) hq
  constructor
  · intro r b
    change (bank (F.result a M u t width) (reg r b)).length≤_
    rw [Model.front_eq]
    exact hr r b
  · intro k
    rw [Model.front_eq]
    exact hd k
/-- Before center/alpha construction, those two caches are EMPTY and every other actual word already equals the final frontend bank. -/
theorem clean_word (a M u:Nat) (t width:List Bool) (k:Stack) :
    (bank (F.clean a M u t width) k).length≤(bank (F.result a M u t width) k).length:=by
  rcases k with k|k
  · rfl
  · rcases k with k|k
    · rfl
    · rcases k with k|k
      · rfl
      · rcases k with k|k
        · rfl
        · rcases k with k|k
          · rcases k with ⟨r,b⟩
            cases r <;> cases b <;> first | exact le_refl _ | exact Nat.zero_le _
          · rfl
/-- Actual clean pre-power source words use the same physical caps. -/
theorem clean_caps (a M u:Nat) (t width:List Bool) :
    Caps.Registers (F.clean a M u t width) (R.cacheWidth a width) ∧
    Caps.Data (F.clean a M u t width) (R.dataWidth a M u t width):=by
  obtain ⟨hr,hd⟩:=result_caps a M u t width
  exact ⟨fun r b=>(clean_word a M u t width (reg r b)).trans (hr r b),fun k=>(clean_word a M u t width k).trans (hd k)⟩
/-- The actual acquired initial geometry fields have the same physical linear source cap. -/
theorem geometry_le (a M u:Nat) (t width:List Bool) (k:G.Aux) :
    ((F.decremented a M u t width).geometry k).length≤20000*(a+t.length+1):=by
  have h:=SemiprimeD1StackRecoveryGridStateCaps.geometry_word (List.replicate a true) t (.inr k)
  rw [List.length_replicate] at h
  cases k <;> first | exact Nat.zero_le _ | exact h
/-- All acquired metadata and both counted displaced shadows fit the global actual-word cap before their real drains. -/
theorem decremented_data (a M u:Nat) (t width:List Bool) :Caps.Data (F.decremented a M u t width) (R.dataWidth a M u t width):=by
  have hd:=(clean_caps a M u t width).2
  have ha:=R.a_le a M u t width
  have ht:=R.t_le a M u t width
  have hR:=R.resource_pos a M u t width
  have hg:20000*(a+t.length+1)≤R.dataWidth a M u t width:=
    R.small_le_cubic _ _ hR (by omega)
  intro k
  rcases k with k|k
  · exact hd (rationalStack k)
  · rcases k with k|k
    · exact (geometry_le a M u t width k).trans hg
    · rcases k with k|k
      · exact hd (divisionStack k)
      · rcases k with k|k
        · exact hd (productStack k)
        · rcases k with k|k
          · exact hd (reg k.1 k.2)
          · exact hd (aux k)
/-- The same actual original-input acquisition pays every literal, VALUE doubling, height division, index fit and geometry call. -/
theorem acquisition_le (a M u:Nat) (t width:List Bool) :
    SemiprimeD1StackRecoveryGridAcquisition.runBound a M u t width≤10000*(R.resource a M u t width)^2:=by
  have hR:=R.resource_pos a M u t width
  have ha:=R.a_le a M u t width
  have hM:=R.M_le a M u t width
  have hu:=R.u_le a M u t width
  have ht:=R.t_le a M u t width
  have hN:=R.grid_le a M u t width
  have hi:=R.index_le a M u t width
  have hs:=SemiprimeD1StackRecoveryGridSetup.runBound_le a
  have hf:=SemiprimeD1StackWordFitBounds.totalTime_le t (List.replicate (a+2) false)
  rw [List.length_replicate] at hf
  have hmag:=SemiprimeD1StackPhaseGeometryArithmetic.magnitude_length a t
  have hm:(SemiprimeD1StackPhaseGeometryArithmetic.magnitude a t).length≤2*R.resource a M u t width:=by rw [hmag];omega
  unfold SemiprimeD1StackRecoveryGridAcquisition.runBound SemiprimeD1StackRecoveryGridNode.runBound SemiprimeD1StackPhaseGeometryComponents.runBound
  rw [List.length_replicate]
  change SemiprimeD1StackRecoveryGridSetup.runBound a+1000*(M+u+1)+(5*t.length+4+SemiprimeD1StackWordFitExecution.totalTime t (List.replicate (a+2) false)+1+2)+(5*t.length+4)+(1000*(a+t.length+1)+1+(SemiprimeD1StackPhaseGeometryArithmetic.magnitude a t).length+1)≤_
  have hp:=Nat.mul_le_mul hi (show 2^(a+1)+1≤2*R.resource a M u t width by change R.gridSize a+1≤_;omega)
  nlinarith
/-- The initial real binary decrement is paid by its actual true-size/raw-index words. -/
theorem decrement_le (a M u:Nat) (t width:List Bool) :
    SemiprimeD1StackRecoveryGridDecrement.runBound (F.sizeWord a) t≤300*(R.resource a M u t width):=by
  have h:=SemiprimeD1StackRecoveryGridDecrement.runBound_le (F.sizeWord a) t
  have hl:(F.sizeWord a).length=a+2:=by rw [F.sizeWord,SemiprimeD1StackPhaseGeometryArithmetic.powerWord_length]
  have hi:=R.index_le a M u t width
  have ht:=R.t_le a M u t width
  have hR:=R.resource_pos a M u t width
  rw [hl] at h
  omega
end RiemannGaussian.SemiprimeD1StackRecoveryGridFrontBounds
