/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourcePullbackHeight
import RiemannGaussian.SemiprimeSourceInterpolationHeight
import RiemannGaussian.SemiprimeMaterializedOriginalSource

/-! # Original-input source-array state bounds
The interpolation constructor supplies the common denominator and numerator;
cache copies and every pullback suffix propagate that bound to the actual
original-source caller. No acquired coefficient/height input is assumed.
-/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace RiemannGaussian.SemiprimeSourceAcquiredArrayState
open OAI.Algorithms.SubexponentialSAT
open MulticolorTypes
open SemiprimeJetArray SemiprimeLocalExecutionHeight
open SemiprimeMaterializedSourcePullback SemiprimeSourcePullbackHeight
variable {I : Type} {r Q : ℕ}

/-- Actual universal acquisition supplies its cache invariant from original dimensions. -/
theorem universal_cache_bound (A R : ℕ) (keys : List (UniversalType r Q 1)) :
    CacheBound (SemiprimeMaterializedSourceRows.acquire A R keys).value (R+1)
      (SemiprimeSourceInterpolationHeight.denominator Q R) (SemiprimeSourceInterpolationHeight.numerator A Q R) := by
  rw [SemiprimeMaterializedSourceRows.acquire_value]
  intro row hr a ha
  obtain ⟨u,_,rfl⟩ := List.mem_map.mp hr
  obtain ⟨y,_,rfl⟩ := List.mem_map.mp ha
  exact ⟨SemiprimeSourceCodeArrays.compile_size (R+1) _,SemiprimeSourceInterpolationHeight.universalRow_bound A R u y⟩

/-- Every actual pullback suffix is bounded from the acquired universal constructor. -/
theorem original_suffix_bound [DecidableEq I] {n : ℕ} (R : ℕ) (is : List I)
    (owner : I → Fin n) (as : Addresses I r Q) (keys : List (UniversalType r Q 1))
    (i : I) (v : Fin n) (k : ℕ) :
    ArrayBound (sourceRow R (is.drop k) owner as keys
      (SemiprimeMaterializedSourceRows.acquire (centered r Q R) R keys).value i v).value (R+1)
      (SemiprimeSourceInterpolationHeight.denominator Q R) (is.length*SemiprimeSourceInterpolationHeight.numerator (centered r Q R) Q R) :=
  sourceRow_suffix_bound R _ _ is owner as keys _ i v k
    (SemiprimeSourceInterpolationHeight.denominator_positive Q R) (SemiprimeSourceInterpolationHeight.denominator_le_numerator _ Q R)
    (universal_cache_bound (centered r Q R) R keys)

/-- All returned arrays at actual owner-filtered recursion frames have derived bounds
and an exact total payload-cell count, before any implementation sharing. -/
theorem original_frame_arrays [DecidableEq I] {n : ℕ} (R : ℕ) (is : List I)
    (owner : I → Fin n) (as : Addresses I r Q) (keys : List (UniversalType r Q 1))
    (i : I) (v : Fin n) :
    let cache := (SemiprimeMaterializedSourceRows.acquire (centered r Q R) R keys).value
    let f := fun j => if owner j=v then
      let out := assembled R as keys cache i j
      (⟨out.value,out.work+2⟩ : SemiprimeMaterializedSourceUniversal.Run (Array ℚ))
      else let out := literal (R+1) false; ⟨out.value,out.work+2⟩
    arrayCells (sumFrameArrays (R+1) f is)=(2*is.length+1)*(R+1) ∧
      ∀ a∈sumFrameArrays (R+1) f is, ArrayBound a (R+1)
        (SemiprimeSourceInterpolationHeight.denominator Q R)
        ((is.length+1)*SemiprimeSourceInterpolationHeight.numerator (centered r Q R) Q R) := by
  dsimp only
  have hc := universal_cache_bound (centered r Q R) R keys
  have hd := SemiprimeSourceInterpolationHeight.denominator_positive Q R
  have hB := SemiprimeSourceInterpolationHeight.denominator_le_numerator (centered r Q R) Q R
  constructor
  · apply sumFrameArrays_cells
    intro j _
    split_ifs <;> dsimp only
    · exact (assembled_bound R _ _ as keys _ i j hd hB hc).1
    · exact (literal_bound (R+1) _ _ false hd hB).1
  · apply sumFrameArrays_bound
    intro j _
    split_ifs <;> dsimp only
    · exact (assembled_bound R _ _ as keys _ i j hd hB hc).2
    · exact (literal_bound (R+1) _ _ false hd hB).2

/-- All actual acquired original rows have an original-derived cache bound. -/
theorem pullback_acquire_bound [DecidableEq I] {n : ℕ} (R : ℕ) (is : List I)
    (owner : I → Fin n) (as : Addresses I r Q) (keys : List (UniversalType r Q 1)) :
    CacheBound (acquire R is owner as keys).value (R+1) (SemiprimeSourceInterpolationHeight.denominator Q R)
      (is.length*SemiprimeSourceInterpolationHeight.numerator (centered r Q R) Q R) :=
  acquire_bound R _ _ is owner as keys (SemiprimeSourceInterpolationHeight.denominator_positive Q R)
    (SemiprimeSourceInterpolationHeight.denominator_le_numerator _ Q R) (universal_cache_bound (centered r Q R) R keys)

/-- Paid labels and packing lead to the same state bound for the literal immutable source grid. -/
theorem acquisition_bound [DecidableEq I] {n : ℕ} (R : ℕ) (is : List I)
    (owner : I → Fin n) (keys : List (UniversalType r Q 1))
    (producer : I → SemiprimeMaterializedSourceUniversal.Run (UniversalType r Q 1)) :
    FrozenBound (SemiprimeMaterializedSourceAcquisition.acquire R is owner keys producer).value
      (R+1) (SemiprimeSourceInterpolationHeight.denominator Q R) (is.length*SemiprimeSourceInterpolationHeight.numerator (centered r Q R) Q R) :=
  source_acquisition_bound R _ _ is owner keys producer (SemiprimeSourceInterpolationHeight.denominator_positive Q R)
    (SemiprimeSourceInterpolationHeight.denominator_le_numerator _ Q R) (universal_cache_bound (centered r Q R) R keys)

/-- Actual original-input source constructor, with no producer or array-height premise. -/
theorem original_source_bound {E : Type} [Fintype I] [DecidableEq I] [DecidableEq E]
    {n : ℕ} (owner : I → Fin n) (factor : I → E)
    (en : SemiprimeSourceLayout.Enumerations I (Fin n) E r Q) (eps : ℚ) (R : ℕ) :
    FrozenBound (SemiprimeMaterializedOriginalSource.acquire owner factor en eps R).value
      (R+1) (SemiprimeSourceInterpolationHeight.denominator Q R)
      (en.incidences.values.length*SemiprimeSourceInterpolationHeight.numerator (centered r Q R) Q R) :=
  acquisition_bound R en.incidences.values owner en.types.values _

/-- Exact scalar slots in the full original-input source result. This is a data count,
not a claim that array or pointer allocation is free. -/
theorem original_source_cells {E : Type} [Fintype I] [DecidableEq I] [DecidableEq E]
    {n : ℕ} (owner : I → Fin n) (factor : I → E)
    (en : SemiprimeSourceLayout.Enumerations I (Fin n) E r Q) (eps : ℚ) (R : ℕ) :
    cacheCells ((SemiprimeMaterializedOriginalSource.acquire owner factor en eps R).value.toList.map
      Array.toList)=en.incidences.values.length*n*(R+1) :=
  source_acquisition_cells R en.incidences.values owner en.types.values _

/-- The actual original-incidence getter sees the bound through finite immutable copying. -/
theorem original_read_bound {E : Type} [Fintype I] [DecidableEq I] [DecidableEq E]
    {n : ℕ} (owner : I → Fin n) (factor : I → E)
    (en : SemiprimeSourceLayout.Enumerations I (Fin n) E r Q) (eps : ℚ) (R : ℕ)
    (i : I) (v : Fin n) :
    ArrayBound (SemiprimeSourceArrayAcquisition.read en.incidences
      (SemiprimeMaterializedOriginalSource.acquire owner factor en eps R).value i v)
      (R+1) (SemiprimeSourceInterpolationHeight.denominator Q R)
      (en.incidences.values.length*SemiprimeSourceInterpolationHeight.numerator (centered r Q R) Q R) := by
  change ArrayBound (SemiprimeSourceArrayAcquisition.read en.incidences
    (SemiprimeMaterializedSourceAcquisition.freeze (acquire R en.incidences.values owner
      _ en.types.values).value) i v) _ _ _
  rw [acquire_value,SemiprimeMaterializedSourceAcquisition.read_freeze]
  exact (sourceRow_bound R _ _ en.incidences.values owner _ en.types.values _ i v
    (SemiprimeSourceInterpolationHeight.denominator_positive Q R) (SemiprimeSourceInterpolationHeight.denominator_le_numerator _ Q R)
    (universal_cache_bound (centered r Q R) R en.types.values)).2

/-- Original-derived heights for the actual source coefficient reader, without final-row
cancellation or a source answer oracle. -/
theorem original_read_reduced_bounds {E : Type} [Fintype I] [DecidableEq I] [DecidableEq E]
    {n : ℕ} (owner : I → Fin n) (factor : I → E)
    (en : SemiprimeSourceLayout.Enumerations I (Fin n) E r Q) (eps : ℚ) (R : ℕ)
    (i : I) (v : Fin n) (k : ℕ) (hk : k<R+1) :
    let q := coefficient (SemiprimeSourceArrayAcquisition.read en.incidences
      (SemiprimeMaterializedOriginalSource.acquire owner factor en eps R).value i v) k
    q.den≤SemiprimeSourceInterpolationHeight.denominator Q R ∧
      q.num.natAbs≤en.incidences.values.length*SemiprimeSourceInterpolationHeight.numerator (centered r Q R) Q R :=
  SemiprimeJetArrayHeight.representation_reduced_bound (SemiprimeSourceInterpolationHeight.denominator_positive Q R)
    (original_read_bound owner factor en eps R i v k hk)

end RiemannGaussian.SemiprimeSourceAcquiredArrayState
