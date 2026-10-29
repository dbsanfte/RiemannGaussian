/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackNormalizedInverseStorage
import RiemannGaussian.SemiprimeD1StackNormalizedInverseLegacy
/-! # Original recovery normalized inverse acquired by the SAME actual finite source
Only physical denominator-array bytes, the actually derived q markers and W are
runtime inputs. Original metadata/width facts below derive Valid/Fits internally;
the literal upstream Affine caller join and whole scalar counter remain separate.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackNormalizedInverseOriginal
open SemiprimeD1StackNormalizedInverse SemiprimeD1StackNormalizedInverseView
open SemiprimeD1StackNormalizedInverseBounds SemiprimeD1StackNormalizedInverseEncoding
open SemiprimeD1StackNormalizedInverseStorage SemiprimeD1StackNormalizedInverseLegacy
open SemiprimeD1StackNormalizedInverseReadBuffers
/-- Original q is specified by the actual original geometry/multiplicity, never supplied as a decoded control Nat. -/
def multiplicity (a M u : ℕ) (t : ℕ) : ℕ :=
  SemiprimeD1JetRecoveryGrid.nodeMultiplicity a (SemiprimeD1TaperedLoss.height M u) u t
/-- Complete actual run, exact WHOLE native bytes and mathematical inverse Valid/Bounded follow from original dimensions alone. -/
theorem source_run_original (width : List Bool) (a M u : ℕ) (t : Fin (SemiprimeD1WireKernelOriginal.size a))
    (hM : u≤M) (hW : SemiprimeD1RecoveryNodeBits.width a M≤width.length) :
    let den:=denominator width a M u t
    let q:=multiplicity a M u t.val
    let inv:=SemiprimeNormalizedInverseBits.build width den q
    ∃time≤polynomial den.toList q width,
      SemiprimeD1StackCalls.run program time (initial (tape den.toList) (unary q) width)=some (done den.toList q width) ∧
      (done den.toList q width).data (aux .output)=tape inv.words.toList ∧
      SemiprimeJetBits.decode inv.words=(SemiprimeD1JetRecoveryWeights.acquire a (SemiprimeD1TaperedLoss.height M u) u t.val).inverse.coefficients ∧
      SemiprimeJetBits.Valid inv.words ∧ SemiprimeJetBits.Bounded inv.words width.length := by
  let den:=denominator width a M u t
  let q:=multiplicity a M u t.val
  obtain ⟨time,ht,hr⟩:=source_run_bounded den.toList q width
  exact ⟨time,ht,hr,output_legacy den q width,original_valid width a M u t hM hW⟩
/-- The actual original prepared bank follows the SAME fixed finite58-role machine and OWN polynomial clock. -/
noncomputable def machineOriginal (width : List Bool) (a M u : ℕ) (t : Fin (SemiprimeD1WireKernelOriginal.size a)) :
    let den:=denominator width a M u t
    let q:=multiplicity a M u t.val
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration (initial (tape den.toList) (unary q) width))
      (some (SemiprimeD1StackCalls.configuration (done den.toList q width))) (polynomial den.toList q width) :=
  machineSource (denominator width a M u t).toList (multiplicity a M u t.val) width
/-- Every compiled original-family prefix counts ALL58 data words AND its actual none-label return stack. -/
theorem original_prefix_cells (width : List Bool) (a M u : ℕ) (t : Fin (SemiprimeD1WireKernelOriginal.size a))
    (fuel : ℕ) (cfg : machine.Cfg)
    (hr : (fun z=>z.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration (initial
        (tape (denominator width a M u t).toList) (unary (multiplicity a M u t.val)) width)))=some cfg) :
    (∑k : Stack,(cfg.stk (some k)).length)+(cfg.stk none).length ≤
      cellsPolynomial (denominator width a M u t).toList (multiplicity a M u t.val) width :=
  machine_prefix_cells _ _ _ fuel cfg hr
end RiemannGaussian.SemiprimeD1StackNormalizedInverseOriginal
