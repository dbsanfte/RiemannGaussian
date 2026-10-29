/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryAffineSource
import RiemannGaussian.SemiprimeD1StackRecoveryAffineLoopOriginal
/-! # Original five actual input words discharge every physical affine-loop source premise -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryAffineOriginalInput
open SemiprimeD1StackRecoveryAffine SemiprimeD1StackRecoveryAffineView SemiprimeD1StackProcedureTrace
namespace E
export SemiprimeD1StackRecoveryAffineEncoding (original retained array resultWords)
end E
open SemiprimeD1StackRecoveryAffineSource (counted)
/-- Original complete ordered slope multiset is internally acquired by the SAME actual whole Grid call. -/
def slopes (a M u:Nat) (selected:Fin (2^(a+1))) (width:List Bool):List SemiprimeRationalBits.RationalWord:=
  (SemiprimeD1RecoveryGridBits.acquire width a M u selected).grid.slopes
/-- The actual physically retained table template is the sole nonempty R36 private word. -/
theorem rational_clear (a M u:Nat) (selected:Fin (2^(a+1))) (t width:List Bool):
    (counted a M u selected t width).rational=SemiprimeD1StackRecoveryAffineOperationInput.emptyRational width:=by
  change Function.update (fun _=>[]) (SemiprimeD1StackRationalOperation.aux .template) width=_
  funext slot
  rcases slot with slot|slot
  · rfl
  · rcases slot with slot|slot
    · rfl
    · cases slot <;> rfl
/-- The real slope acquisition reaches exactly the whole affine-loop input with no external q/array/slope advice. -/
theorem slopes_run (a M u:Nat) (selected:Fin (2^(a+1))) (t width:List Bool):
    Runs program (SemiprimeD1StackRecoveryAffineSlopes.runBound (slopes a M u selected width))
      (.local .copySlopes) (bank (counted a M u selected t width))
      (.local .slopeLoop) (bank (SemiprimeD1StackRecoveryAffineLoopView.state (counted a M u selected t width)
        [SemiprimeJetBits.oneWord] (slopes a M u selected width).reverse)):=by
  have h:=SemiprimeD1StackRecoveryAffineSlopes.source_run (counted a M u selected t width)
    (slopes a M u selected width) rfl rfl rfl rfl rfl rfl rfl rfl rfl
  rw [SemiprimeD1StackRecoveryAffineLoopView.slopes_state _ _ rfl] at h
  exact h
/-- Every old Grid104 word and all eight actual additional cells have their exact final original byte values. -/
theorem finished_eq (a M u:Nat) (selected:Fin (2^(a+1))) (t width:List Bool):
    SemiprimeD1StackRecoveryAffineLoopView.finished (counted a M u selected t width)
      (E.array a M u selected width)=E.resultWords a M u selected t width:=by
  dsimp only [SemiprimeD1StackRecoveryAffineLoopView.finished,SemiprimeD1StackRecoveryAffineLoopView.array,
    SemiprimeD1StackRecoveryAffineSlopeRead.tape,counted,E.resultWords]
  congr 1
  funext slot
  cases slot <;> rfl
/-- The actual entire reverse-row/convolution loop computes the ORIGINAL affine build, including q0/W0/empty slopes. -/
theorem loop_run (a M u:Nat) (selected:Fin (2^(a+1))) (t width:List Bool):
    ∃s≤SemiprimeD1StackRecoveryAffineLoop.runBound (counted a M u selected t width) width (E.retained a M u selected)
        (slopes a M u selected width).reverse [SemiprimeJetBits.oneWord],
      Runs program s (.local .slopeLoop)
        (bank (SemiprimeD1StackRecoveryAffineLoopView.state (counted a M u selected t width)
          [SemiprimeJetBits.oneWord] (slopes a M u selected width).reverse))
        (.local .done) (bank (E.resultWords a M u selected t width)):=by
  obtain ⟨s,hs,h⟩:=SemiprimeD1StackRecoveryAffineLoop.source_run (counted a M u selected t width)
    [SemiprimeJetBits.oneWord] (slopes a M u selected width).reverse (E.retained a M u selected) width
    (by simp only [counted,Function.update_self,SemiprimeD1StackRecoveryAffineReadCount.unary]) rfl rfl rfl rfl rfl
    (fun b=>by cases b <;> rfl) (fun b=>by cases b <;> rfl) (fun b=>by cases b <;> rfl)
    (fun b=>by cases b <;> rfl) (fun b=>by cases b <;> rfl) rfl rfl rfl
    (rational_clear a M u selected t width)
  rw [SemiprimeD1StackRecoveryAffineLoopOriginal.fold_original] at h
  change Runs program s _ _ _ (bank (SemiprimeD1StackRecoveryAffineLoopView.finished (counted a M u selected t width)
    (E.array a M u selected width))) at h
  rw [finished_eq] at h
  exact ⟨s,hs,h⟩
end RiemannGaussian.SemiprimeD1StackRecoveryAffineOriginalInput
