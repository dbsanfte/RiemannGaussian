/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackNormalizedInverseView
/-! # Disjoint actual cache writes and preserved signed word views -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackNormalizedInverseRegisterAlgebra
open SemiprimeD1StackNormalizedInverse SemiprimeD1StackNormalizedInverseView
/-- Acquiring another actual coefficient retains this full original signed/denominator word. -/
theorem getReg_other (w : Words) (r other : Reg) (word : SemiprimeRationalBits.RationalWord)
    (h : other≠r) : getReg (putReg w r word) other=getReg w other := by
  dsimp only [getReg]
  rw [putReg_other w r other word false h,putReg_other w r other word true h]
/-- Every actual acquired word has a nonempty signed field, even for zero magnitude. -/
theorem putReg_nonempty (w : Words) (r : Reg) (word : SemiprimeRationalBits.RationalWord) :
    (putReg w r word).registers (r,false)≠[] := by
  rw [(putReg_fields w r word).1]
  exact List.cons_ne_nil _ _
/-- Cache replacement writes over both old fields, without a residual sign/denominator prefix. -/
theorem putReg_idem (w : Words) (r : Reg) (old word : SemiprimeRationalBits.RationalWord) :
    putReg (putReg w r old) r word=putReg w r word := by
  unfold putReg
  congr 1
  funext k
  rcases k with ⟨other,den⟩
  by_cases h:other=r
  · subst other;cases den <;> simp
  · cases den <;> simp [h]
/-- Distinct actual cache fields commute, a proof identity rather than a runtime reorder. -/
theorem putReg_comm (w : Words) (r other : Reg) (x y : SemiprimeRationalBits.RationalWord)
    (h : r≠other) : putReg (putReg w r x) other y=putReg (putReg w other y) r x := by
  unfold putReg
  congr 1
  funext k
  rcases k with ⟨tag,den⟩
  by_cases hr:tag=r
  · subst tag;cases den <;> simp [h]
  · by_cases ho:tag=other
    · subst tag;cases den <;> simp [Ne.symm h]
    · cases den <;> simp [hr,ho]
end RiemannGaussian.SemiprimeD1StackNormalizedInverseRegisterAlgebra
