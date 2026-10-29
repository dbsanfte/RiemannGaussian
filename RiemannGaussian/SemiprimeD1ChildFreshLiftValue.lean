/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1ChildTableCopy
import RiemannGaussian.SemiprimeD1JetBlockPolynomial
import RiemannGaussian.SemiprimeD1JetEmbedding
import RiemannGaussian.SemiprimeD1NetworkDoubleAssignment

/-! # Individual cached-entry copies into the actual fresh-axis ring
The old words are interpreted at the CHILD precision before embedding. This
is a single-entry literal set lift, not an upward ring map from parent residues
and not a lift of an already reduced product of entries.
-/
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1ChildFreshLiftValue
open scoped BigOperators
open SemiprimeD1JetAxes SemiprimeD1JetInterpretation SemiprimeD1JetBoxIndex
open SemiprimeD1JetBlockPolynomial SemiprimeD1JetAlgebra
open SemiprimeD1ChildTableCopy SemiprimeD1JetEmbedding
noncomputable section

/-- Physical reduction of every word preserves its value in the actual
current quotient. No word width or scalar-answer premise is needed. -/
theorem normalize_value (ctx : Context) (words : List (List Bool)) :
    interpret ctx (normalize ctx.precision words).words = interpret ctx words := by
  unfold interpret
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  simp only [SemiprimeD1JetRingBits.coefficient,normalize_words,List.getElem?_map]
  cases hw : words[i.val]? with
  | none => rfl
  | some w =>
    simp only [Option.map_some,Option.getD_some,SemiprimeD1JetScalarBits.reduce_value,
      ZMod.natCast_mod]

/-- An actual cached-entry copy is precisely the legitimate SAME-child-
precision fresh-axis embedding of that individual entry's original bytes. -/
theorem lift_fresh_value (old : Context) (q p : ℕ) (words : List (List Bool))
    (hq : 0 < q) (hshape : words.length = old.rank) :
    interpret ⟨q::old.axes,p⟩ (lift old [q] p words).words =
      actualEmbedding old q p (interpret ⟨old.axes,p⟩ words) := by
  change interpret ⟨q::old.axes,p⟩ (lift old [q] p words).words =
    actualView old q p (outerEmbedding (R:=ZMod (2^p)) q (dims old.axes)
      (interpret ⟨old.axes,p⟩ words))
  have hz := normalize_value (⟨q::old.axes,p⟩ : Context)
    (words++List.replicate (old.rank*(q-1)) [])
  rw [normalize_words] at hz
  rw [lift_words]
  simp only [List.prod_cons,List.prod_nil,Nat.mul_one]
  refine hz.trans ?_
  rw [interpret_series]
  have hs := series_zero_extend (⟨old.axes,p⟩ : Context) words q hq hshape
  refine (congrArg (project (dims (q::old.axes))) hs).trans ?_
  have he := outerEmbedding_project (R:=ZMod (2^p)) q (dims old.axes)
    (series (⟨old.axes,p⟩ : Context) words)
  have ht := dimensionEquiv_project (R:=ZMod (2^p)) _ _ (dims_cons q old.axes).symm
    (MvPowerSeries.rename (axisShift old.axes.length) (series (⟨old.axes,p⟩ : Context) words))
  refine ht.symm.trans ((congrArg (actualView old q p) he).symm.trans ?_)
  exact congrArg (fun value => actualView old q p (outerEmbedding q (dims old.axes) value))
    (interpret_series (⟨old.axes,p⟩ : Context) words).symm

/-- The actual dimension transport also preserves scalar constants, so the
network deformation theorem applies to the very same fresh-axis map. -/
theorem actualEmbedding_constants (old : Context) (q p : ℕ) :
    (actualEmbedding old q p).comp (constants (dims old.axes)) =
      constants (dims (q::old.axes)) := by
  ext r
  change ZMod (2^p) at r
  change actualView old q p (outerEmbedding q (dims old.axes)
    (constants (dims old.axes) r)) = constants (dims (q::old.axes)) r
  rw [SemiprimeD1NetworkDoubleAssignment.outerEmbedding_constants]
  exact dimensionEquiv_project _ _ (dims_cons q old.axes).symm _

end
end RiemannGaussian.SemiprimeD1ChildFreshLiftValue
