import RiemannGaussian.Hybrid.EtaGeometricReflectionMomentGram
import RiemannGaussian.EtaEnergyFiniteWindowRank

/-!
# Reflection-parity compression for the geometric eta metric

The positive mixed-moment carrier from the preceding modules retains the eta
metric `K` and the critical-line reflection permutation `P`, but the spectrum
of `P K` has no distinguished zero channel when `K` is positive definite.
Thus its spectral zero mass cannot be identified with the number of off-line
zeros.

This module constructs the semantically correct parity projections

`E₊ = (I + P) / 2`,  `E₋ = (I - P) / 2`.

They are orthogonal positive-semidefinite projections.  The trace of `E₋` is
exactly the number of upper off-line reflection pairs, while the trace of
`E₊` is the number of critical zeros plus that upper count.  Consequently the
unweighted certificate `1 - 2 * tr(E₋) / N` is exactly the critical-zero
proportion on every nonempty finite window.

Eta arithmetic is retained by compressing the positive zero-index Gram:

`A₊ = E₊ K E₊`,  `A₋ = E₋ K E₋`.

Both matrices are positive semidefinite.  Under positive definiteness of `K`,
the kernel of `A₊` is exactly the reflection-odd subspace.  Their real traces
are, without an inequality, the already checked on-line-plus-real and
off-line-imaginary eta masses.  This supplies a correct count/arithmetic seam
for the certificate program; it does not prove a new zero proportion.
-/

open Complex
open scoped BigOperators Classical ComplexConjugate ComplexOrder Matrix

namespace RiemannGaussian

noncomputable section

/-! ## Reflection parity on the literal zero window -/

/-- The reflection-even projection on the enumerated finite zero window. -/
def pairedEtaZeroWindowReflectionEvenProjection
    (T : ℝ) (hT : 0 ≤ T) :
    Matrix (Fin (spectralZetaZeroWindow T).card)
      (Fin (spectralZetaZeroWindow T).card) ℂ :=
  (1 / 2 : ℂ) • (1 + pairedEtaZeroWindowConjugatePartnerMatrix T hT)

/-- The reflection-odd projection on the enumerated finite zero window. -/
def pairedEtaZeroWindowReflectionOddProjection
    (T : ℝ) (hT : 0 ≤ T) :
    Matrix (Fin (spectralZetaZeroWindow T).card)
      (Fin (spectralZetaZeroWindow T).card) ℂ :=
  (1 / 2 : ℂ) • (1 - pairedEtaZeroWindowConjugatePartnerMatrix T hT)

/-- The critical-line reflection matrix is Hermitian because its permutation
is an involution. -/
theorem pairedEtaZeroWindowConjugatePartnerMatrix_isHermitian
    (T : ℝ) (hT : 0 ≤ T) :
    (pairedEtaZeroWindowConjugatePartnerMatrix T hT).IsHermitian := by
  rw [Matrix.IsHermitian, pairedEtaZeroWindowConjugatePartnerMatrix,
    Matrix.conjTranspose_permMatrix]
  congr 1

/-- The reflection-even parity matrix is Hermitian. -/
theorem pairedEtaZeroWindowReflectionEvenProjection_isHermitian
    (T : ℝ) (hT : 0 ≤ T) :
    (pairedEtaZeroWindowReflectionEvenProjection T hT).IsHermitian := by
  exact
    (Matrix.isHermitian_one.add
      (pairedEtaZeroWindowConjugatePartnerMatrix_isHermitian T hT)).smul
        (by simp)

/-- The reflection-odd parity matrix is Hermitian. -/
theorem pairedEtaZeroWindowReflectionOddProjection_isHermitian
    (T : ℝ) (hT : 0 ≤ T) :
    (pairedEtaZeroWindowReflectionOddProjection T hT).IsHermitian := by
  exact
    (Matrix.isHermitian_one.sub
      (pairedEtaZeroWindowConjugatePartnerMatrix_isHermitian T hT)).smul
        (by simp)

/-- The reflection-even parity matrix is idempotent. -/
theorem pairedEtaZeroWindowReflectionEvenProjection_mul_self
    (T : ℝ) (hT : 0 ≤ T) :
    pairedEtaZeroWindowReflectionEvenProjection T hT *
        pairedEtaZeroWindowReflectionEvenProjection T hT =
      pairedEtaZeroWindowReflectionEvenProjection T hT := by
  unfold pairedEtaZeroWindowReflectionEvenProjection
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
    pairedEtaZeroWindowConjugatePartnerMatrix_mul_self]
  norm_num
  module

/-- The reflection-odd parity matrix is idempotent. -/
theorem pairedEtaZeroWindowReflectionOddProjection_mul_self
    (T : ℝ) (hT : 0 ≤ T) :
    pairedEtaZeroWindowReflectionOddProjection T hT *
        pairedEtaZeroWindowReflectionOddProjection T hT =
      pairedEtaZeroWindowReflectionOddProjection T hT := by
  unfold pairedEtaZeroWindowReflectionOddProjection
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
    pairedEtaZeroWindowConjugatePartnerMatrix_mul_self]
  norm_num
  module

/-- The two reflection-parity projections resolve the identity. -/
theorem pairedEtaZeroWindowReflectionEvenProjection_add_oddProjection
    (T : ℝ) (hT : 0 ≤ T) :
    pairedEtaZeroWindowReflectionEvenProjection T hT +
        pairedEtaZeroWindowReflectionOddProjection T hT = 1 := by
  unfold pairedEtaZeroWindowReflectionEvenProjection
    pairedEtaZeroWindowReflectionOddProjection
  module

/-- The difference of the parity projections recovers the reflection
permutation, so the sign channel has not been discarded. -/
theorem pairedEtaZeroWindowReflectionEvenProjection_sub_oddProjection
    (T : ℝ) (hT : 0 ≤ T) :
    pairedEtaZeroWindowReflectionEvenProjection T hT -
        pairedEtaZeroWindowReflectionOddProjection T hT =
      pairedEtaZeroWindowConjugatePartnerMatrix T hT := by
  unfold pairedEtaZeroWindowReflectionEvenProjection
    pairedEtaZeroWindowReflectionOddProjection
  module

/-- The even projection annihilates the odd projection. -/
theorem pairedEtaZeroWindowReflectionEvenProjection_mul_oddProjection
    (T : ℝ) (hT : 0 ≤ T) :
    pairedEtaZeroWindowReflectionEvenProjection T hT *
        pairedEtaZeroWindowReflectionOddProjection T hT = 0 := by
  unfold pairedEtaZeroWindowReflectionEvenProjection
    pairedEtaZeroWindowReflectionOddProjection
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  simp only [Matrix.add_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
    pairedEtaZeroWindowConjugatePartnerMatrix_mul_self]
  norm_num
  module

/-- The odd projection annihilates the even projection. -/
theorem pairedEtaZeroWindowReflectionOddProjection_mul_evenProjection
    (T : ℝ) (hT : 0 ≤ T) :
    pairedEtaZeroWindowReflectionOddProjection T hT *
        pairedEtaZeroWindowReflectionEvenProjection T hT = 0 := by
  unfold pairedEtaZeroWindowReflectionEvenProjection
    pairedEtaZeroWindowReflectionOddProjection
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  simp only [Matrix.sub_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
    pairedEtaZeroWindowConjugatePartnerMatrix_mul_self]
  norm_num

/-- The reflection-even idempotent is positive semidefinite. -/
theorem pairedEtaZeroWindowReflectionEvenProjection_posSemidef
    (T : ℝ) (hT : 0 ≤ T) :
    (pairedEtaZeroWindowReflectionEvenProjection T hT).PosSemidef := by
  have h := Matrix.posSemidef_conjTranspose_mul_self
    (pairedEtaZeroWindowReflectionEvenProjection T hT)
  rw [(pairedEtaZeroWindowReflectionEvenProjection_isHermitian T hT).eq,
    pairedEtaZeroWindowReflectionEvenProjection_mul_self] at h
  exact h

/-- The reflection-odd idempotent is positive semidefinite. -/
theorem pairedEtaZeroWindowReflectionOddProjection_posSemidef
    (T : ℝ) (hT : 0 ≤ T) :
    (pairedEtaZeroWindowReflectionOddProjection T hT).PosSemidef := by
  have h := Matrix.posSemidef_conjTranspose_mul_self
    (pairedEtaZeroWindowReflectionOddProjection T hT)
  rw [(pairedEtaZeroWindowReflectionOddProjection_isHermitian T hT).eq,
    pairedEtaZeroWindowReflectionOddProjection_mul_self] at h
  exact h

/-- When the eta metric is positive definite, the mixed carrier `P K` is a
unit.  In particular its zero eigenspace cannot encode off-line zeros. -/
theorem pairedEtaGeometricReflectionMixedCarrier_isUnit
    (q : ℕ) {T : ℝ} (hT : 0 ≤ T) (n : ℕ)
    (hK : (pairedEtaGeometricMultiplicityWeightedZeroGram q
      (spectralZetaZeroWindow T) n).PosDef) :
    IsUnit (pairedEtaZeroWindowConjugatePartnerMatrix T hT *
      pairedEtaGeometricMultiplicityWeightedZeroGram q
        (spectralZetaZeroWindow T) n) := by
  apply IsUnit.mul
  · exact isUnit_iff_exists_inv.mpr
      ⟨pairedEtaZeroWindowConjugatePartnerMatrix T hT,
        pairedEtaZeroWindowConjugatePartnerMatrix_mul_self T hT⟩
  · exact hK.isUnit

/-- Positive definiteness of `K` makes the mixed carrier `P K` have trivial
kernel. -/
theorem pairedEtaGeometricReflectionMixedCarrier_mulVec_eq_zero_iff
    (q : ℕ) {T : ℝ} (hT : 0 ≤ T) (n : ℕ)
    (hK : (pairedEtaGeometricMultiplicityWeightedZeroGram q
      (spectralZetaZeroWindow T) n).PosDef)
    (v : Fin (spectralZetaZeroWindow T).card → ℂ) :
    (pairedEtaZeroWindowConjugatePartnerMatrix T hT *
        pairedEtaGeometricMultiplicityWeightedZeroGram q
          (spectralZetaZeroWindow T) n).mulVec v = 0 ↔ v = 0 := by
  have hinj := Matrix.mulVec_injective_iff_isUnit.mpr
    (pairedEtaGeometricReflectionMixedCarrier_isUnit q hT n hK)
  constructor
  · intro hv
    apply hinj
    simpa only [Matrix.mulVec_zero] using hv
  · rintro rfl
    exact Matrix.mulVec_zero _

/-- A Hermitian idempotent has trace equal to its matrix rank. -/
theorem hermitian_idempotent_trace_eq_rank
    {d : Type*} [Fintype d] [DecidableEq d]
    (E : Matrix d d ℂ) (hE : E.IsHermitian) (hE2 : E * E = E) :
    E.trace = (E.rank : ℂ) := by
  have heig (i : d) : hE.eigenvalues i = 0 ∨ hE.eigenvalues i = 1 := by
    let v : d → ℂ := ⇑(hE.eigenvectorBasis i)
    have hv : v ≠ 0 :=
      (WithLp.ofLp_eq_zero (p := 2)).ne.mpr
        (hE.eigenvectorBasis.orthonormal.ne_zero i)
    have hev := hE.mulVec_eigenvectorBasis i
    have hid := congrArg (fun A : Matrix d d ℂ ↦ A.mulVec v) hE2
    rw [← Matrix.mulVec_mulVec, hev, Matrix.mulVec_smul, hev] at hid
    have hscalar : hE.eigenvalues i ^ 2 = hE.eigenvalues i := by
      apply (smul_left_injective ℝ hv)
      simpa only [smul_smul, pow_two] using hid
    have hfactor : hE.eigenvalues i * (hE.eigenvalues i - 1) = 0 := by
      nlinarith
    rcases mul_eq_zero.mp hfactor with hzero | hone
    · exact Or.inl hzero
    · exact Or.inr (sub_eq_zero.mp hone)
  rw [hE.trace_eq_sum_eigenvalues]
  calc
    (∑ i, (hE.eigenvalues i : ℂ)) =
        ∑ i, if hE.eigenvalues i ≠ 0 then (1 : ℂ) else 0 := by
      apply Finset.sum_congr rfl
      intro i _hi
      rcases heig i with hzero | hone
      · simp [hzero]
      · simp [hone]
    _ = ((Finset.univ.filter fun i ↦ hE.eigenvalues i ≠ 0).card : ℂ) := by
      simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
      push_cast
      rfl
    _ = (E.rank : ℂ) := by
      have hrank := hE.rank_eq_card_non_zero_eigs
      rw [Fintype.card_subtype] at hrank
      exact_mod_cast hrank.symm

/-! ## Exact parity counts -/

/-- Fixed indices of the transported reflection are exactly the critical-line
zeros in the same finite spectral window. -/
def pairedEtaZeroWindowReflectionFixedEquivCritical
    (T : ℝ) (hT : 0 ≤ T) :
    Function.fixedPoints (pairedEtaZeroWindowConjugatePartnerPerm T hT) ≃
      ↥(spectralCriticalZetaZeroWindow T) where
  toFun i := by
    let rho : ↥(spectralZetaZeroWindow T) :=
      (etaZeroWindowEquivFin (spectralZetaZeroWindow T)).symm i.1
    refine ⟨rho.1, ?_⟩
    rw [mem_spectralCriticalZetaZeroWindow]
    refine ⟨rho.2, ?_⟩
    have hfixed : pairedEtaZeroWindowConjugatePartnerPerm T hT i.1 = i.1 :=
      Function.mem_fixedPoints_iff.mp i.2
    have hpartner : NontrivialZetaZero.conjugatePartner rho.1 = rho.1 := by
      rw [← etaZeroWindowEquivFin_symm_pairedEtaZeroWindowConjugatePartnerPerm
        T hT i.1, hfixed]
    have hspectral := congrArg
      (fun z : NontrivialZetaZero ↦ zetaSpectralCoordinate z.1) hpartner
    rw [NontrivialZetaZero.spectralCoordinate_conjugatePartner] at hspectral
    exact Complex.conj_eq_iff_im.mp hspectral
  invFun rho := by
    have hwindow : rho.1 ∈ spectralZetaZeroWindow T :=
      (mem_spectralCriticalZetaZeroWindow.mp rho.2).1
    let i := etaZeroWindowEquivFin
      (spectralZetaZeroWindow T) ⟨rho.1, hwindow⟩
    refine ⟨i, Function.mem_fixedPoints_iff.mpr ?_⟩
    apply (etaZeroWindowEquivFin (spectralZetaZeroWindow T)).symm.injective
    apply Subtype.ext
    rw [etaZeroWindowEquivFin_symm_pairedEtaZeroWindowConjugatePartnerPerm]
    dsimp only [i]
    rw [Equiv.symm_apply_apply]
    change NontrivialZetaZero.conjugatePartner rho.1 = rho.1
    apply conjugatePartner_eq_self_of_re_eq_half
    exact (zetaSpectralCoordinate_im_eq_zero_iff rho.1).mp
      (mem_spectralCriticalZetaZeroWindow.mp rho.2).2
  left_inv i := by
    apply Subtype.ext
    change etaZeroWindowEquivFin (spectralZetaZeroWindow T)
        ((etaZeroWindowEquivFin (spectralZetaZeroWindow T)).symm i.1) = i.1
    simp
  right_inv rho := by
    apply Subtype.ext
    change ((etaZeroWindowEquivFin (spectralZetaZeroWindow T)).symm
      (etaZeroWindowEquivFin (spectralZetaZeroWindow T) _)).1 = rho.1
    simp

/-- The reflection fixed-point count is the literal critical-zero count. -/
theorem pairedEtaZeroWindowConjugatePartnerPerm_fixedPoints_ncard
    (T : ℝ) (hT : 0 ≤ T) :
    (Function.fixedPoints
      (pairedEtaZeroWindowConjugatePartnerPerm T hT)).ncard =
        (spectralCriticalZetaZeroWindow T).card := by
  calc
    _ = (spectralCriticalZetaZeroWindow T : Set NontrivialZetaZero).ncard :=
      Set.ncard_congr' (pairedEtaZeroWindowReflectionFixedEquivCritical T hT)
    _ = _ := Set.ncard_coe_finset _

/-- The odd projection trace is exactly the number of upper off-line
reflection pairs. -/
theorem pairedEtaZeroWindowReflectionOddProjection_trace
    (T : ℝ) (hT : 0 ≤ T) :
    (pairedEtaZeroWindowReflectionOddProjection T hT).trace =
      ((spectralUpperZetaZeroWindow T).card : ℂ) := by
  rw [pairedEtaZeroWindowReflectionOddProjection, Matrix.trace_smul,
    Matrix.trace_sub, Matrix.trace_one,
    pairedEtaZeroWindowConjugatePartnerMatrix, Matrix.trace_permutation,
    pairedEtaZeroWindowConjugatePartnerPerm_fixedPoints_ncard T hT]
  have hcard := spectralZetaZeroWindow_card_eq_critical_add_two_mul_upper hT
  rw [hcard]
  simp only [Fintype.card_fin]
  push_cast
  ring

/-- The even projection trace is the critical-zero count plus one direction
from every off-line reflection pair. -/
theorem pairedEtaZeroWindowReflectionEvenProjection_trace
    (T : ℝ) (hT : 0 ≤ T) :
    (pairedEtaZeroWindowReflectionEvenProjection T hT).trace =
      ((spectralCriticalZetaZeroWindow T).card +
        (spectralUpperZetaZeroWindow T).card : ℕ) := by
  rw [pairedEtaZeroWindowReflectionEvenProjection, Matrix.trace_smul,
    Matrix.trace_add, Matrix.trace_one,
    pairedEtaZeroWindowConjugatePartnerMatrix, Matrix.trace_permutation,
    pairedEtaZeroWindowConjugatePartnerPerm_fixedPoints_ncard T hT]
  have hcard := spectralZetaZeroWindow_card_eq_critical_add_two_mul_upper hT
  rw [hcard]
  simp only [Fintype.card_fin]
  push_cast
  ring

/-- The odd projection has rank equal to the number of upper off-line
reflection pairs. -/
theorem pairedEtaZeroWindowReflectionOddProjection_rank
    (T : ℝ) (hT : 0 ≤ T) :
    (pairedEtaZeroWindowReflectionOddProjection T hT).rank =
      (spectralUpperZetaZeroWindow T).card := by
  have htrace := hermitian_idempotent_trace_eq_rank
    (pairedEtaZeroWindowReflectionOddProjection T hT)
    (pairedEtaZeroWindowReflectionOddProjection_isHermitian T hT)
    (pairedEtaZeroWindowReflectionOddProjection_mul_self T hT)
  rw [pairedEtaZeroWindowReflectionOddProjection_trace] at htrace
  exact_mod_cast htrace.symm

/-- The even projection has rank equal to the critical-zero count plus one
direction from every upper off-line pair. -/
theorem pairedEtaZeroWindowReflectionEvenProjection_rank
    (T : ℝ) (hT : 0 ≤ T) :
    (pairedEtaZeroWindowReflectionEvenProjection T hT).rank =
      (spectralCriticalZetaZeroWindow T).card +
        (spectralUpperZetaZeroWindow T).card := by
  have htrace := hermitian_idempotent_trace_eq_rank
    (pairedEtaZeroWindowReflectionEvenProjection T hT)
    (pairedEtaZeroWindowReflectionEvenProjection_isHermitian T hT)
    (pairedEtaZeroWindowReflectionEvenProjection_mul_self T hT)
  rw [pairedEtaZeroWindowReflectionEvenProjection_trace] at htrace
  exact_mod_cast htrace.symm

/-- The count certificate carried by the reflection-odd projection. -/
def pairedEtaZeroWindowReflectionCountCertificate
    (T : ℝ) (hT : 0 ≤ T) : ℝ :=
  1 - 2 * HermitianInertia.rtrace
    (pairedEtaZeroWindowReflectionOddProjection T hT) /
      (spectralZetaZeroWindow T).card

/-- On a nonempty finite window, the reflection-odd count certificate is
exactly the proportion of represented zeros on the critical line. -/
theorem pairedEtaZeroWindowReflectionCountCertificate_eq_criticalFraction
    {T : ℝ} (hT : 0 ≤ T)
    (hwindow : (spectralZetaZeroWindow T).Nonempty) :
    pairedEtaZeroWindowReflectionCountCertificate T hT =
      (spectralCriticalZetaZeroWindow T).card /
        (spectralZetaZeroWindow T).card := by
  have hcardPos : 0 < ((spectralZetaZeroWindow T).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hwindow
  have hcard := spectralZetaZeroWindow_card_eq_critical_add_two_mul_upper hT
  unfold pairedEtaZeroWindowReflectionCountCertificate
    HermitianInertia.rtrace
  rw [pairedEtaZeroWindowReflectionOddProjection_trace]
  change 1 - 2 * ((spectralUpperZetaZeroWindow T).card : ℝ) /
      (spectralZetaZeroWindow T).card =
    (spectralCriticalZetaZeroWindow T).card /
      (spectralZetaZeroWindow T).card
  field_simp [hcardPos.ne']
  have hcardReal : ((spectralZetaZeroWindow T).card : ℝ) =
      (spectralCriticalZetaZeroWindow T).card +
        2 * (spectralUpperZetaZeroWindow T).card := by
    exact_mod_cast hcard
  linarith

/-! ## Positive eta-metric parity compression -/

/-- The positive eta metric compressed to the reflection-even channel. -/
def pairedEtaGeometricReflectionEvenCompressedZeroGram
    (q : ℕ) (T : ℝ) (hT : 0 ≤ T) (n : ℕ) :
    Matrix (Fin (spectralZetaZeroWindow T).card)
      (Fin (spectralZetaZeroWindow T).card) ℂ :=
  pairedEtaZeroWindowReflectionEvenProjection T hT *
    pairedEtaGeometricMultiplicityWeightedZeroGram q
      (spectralZetaZeroWindow T) n *
    pairedEtaZeroWindowReflectionEvenProjection T hT

/-- The positive eta metric compressed to the reflection-odd channel. -/
def pairedEtaGeometricReflectionOddCompressedZeroGram
    (q : ℕ) (T : ℝ) (hT : 0 ≤ T) (n : ℕ) :
    Matrix (Fin (spectralZetaZeroWindow T).card)
      (Fin (spectralZetaZeroWindow T).card) ℂ :=
  pairedEtaZeroWindowReflectionOddProjection T hT *
    pairedEtaGeometricMultiplicityWeightedZeroGram q
      (spectralZetaZeroWindow T) n *
    pairedEtaZeroWindowReflectionOddProjection T hT

/-- Even compression of the actual positive eta metric is positive
semidefinite. -/
theorem pairedEtaGeometricReflectionEvenCompressedZeroGram_posSemidef
    (q : ℕ) (T : ℝ) (hT : 0 ≤ T) (n : ℕ) :
    (pairedEtaGeometricReflectionEvenCompressedZeroGram q T hT n).PosSemidef := by
  have hK := pairedEtaGeometricMultiplicityWeightedZeroGram_posSemidef
    q (spectralZetaZeroWindow T) n
  have hE := pairedEtaZeroWindowReflectionEvenProjection_isHermitian T hT
  simpa only [pairedEtaGeometricReflectionEvenCompressedZeroGram, hE.eq] using
    hK.conjTranspose_mul_mul_same
      (pairedEtaZeroWindowReflectionEvenProjection T hT)

/-- Odd compression of the actual positive eta metric is positive
semidefinite. -/
theorem pairedEtaGeometricReflectionOddCompressedZeroGram_posSemidef
    (q : ℕ) (T : ℝ) (hT : 0 ≤ T) (n : ℕ) :
    (pairedEtaGeometricReflectionOddCompressedZeroGram q T hT n).PosSemidef := by
  have hK := pairedEtaGeometricMultiplicityWeightedZeroGram_posSemidef
    q (spectralZetaZeroWindow T) n
  have hE := pairedEtaZeroWindowReflectionOddProjection_isHermitian T hT
  simpa only [pairedEtaGeometricReflectionOddCompressedZeroGram, hE.eq] using
    hK.conjTranspose_mul_mul_same
      (pairedEtaZeroWindowReflectionOddProjection T hT)

/-- Compressing a positive-definite metric by a Hermitian matrix introduces
exactly the kernel of that matrix. -/
theorem hermitian_compressed_posDef_mulVec_eq_zero_iff
    {d : Type*} [Fintype d]
    (E K : Matrix d d ℂ) (hE : E.IsHermitian) (hK : K.PosDef)
    (v : d → ℂ) :
    (E * K * E).mulVec v = 0 ↔ E.mulVec v = 0 := by
  classical
  constructor
  · intro hA
    by_contra hEv
    have hpos := hK.dotProduct_mulVec_pos hEv
    have hpos' :
        0 < star v ⬝ᵥ ((Eᴴ * K * E).mulVec v) := by
      simpa only [Matrix.star_mulVec, Matrix.dotProduct_mulVec,
        Matrix.vecMul_vecMul, Matrix.mulVec_mulVec, Matrix.mul_assoc] using hpos
    rw [hE.eq] at hpos'
    rw [hA] at hpos'
    simp at hpos'
  · intro hEv
    simp only [← Matrix.mulVec_mulVec, hEv, Matrix.mulVec_zero]

/-- Under eta-feature separation, the zero eigenspace of the even-compressed
positive metric is exactly the reflection-odd subspace. -/
theorem pairedEtaGeometricReflectionEvenCompressedZeroGram_mulVec_eq_zero_iff_odd
    (q : ℕ) {T : ℝ} (hT : 0 ≤ T) (n : ℕ)
    (hK : (pairedEtaGeometricMultiplicityWeightedZeroGram q
      (spectralZetaZeroWindow T) n).PosDef)
    (v : Fin (spectralZetaZeroWindow T).card → ℂ) :
    (pairedEtaGeometricReflectionEvenCompressedZeroGram q T hT n).mulVec v = 0 ↔
      (pairedEtaZeroWindowReflectionOddProjection T hT).mulVec v = v := by
  rw [pairedEtaGeometricReflectionEvenCompressedZeroGram,
    hermitian_compressed_posDef_mulVec_eq_zero_iff _ _
      (pairedEtaZeroWindowReflectionEvenProjection_isHermitian T hT) hK]
  have hresolve := congrArg (fun A : Matrix
      (Fin (spectralZetaZeroWindow T).card)
      (Fin (spectralZetaZeroWindow T).card) ℂ ↦ A.mulVec v)
    (pairedEtaZeroWindowReflectionEvenProjection_add_oddProjection T hT)
  simp only [Matrix.add_mulVec, Matrix.one_mulVec] at hresolve
  constructor
  · intro heven
    simpa only [heven, zero_add] using hresolve
  · intro hodd
    have h := hresolve
    rw [hodd] at h
    exact add_eq_right.mp h

/-- Two finite square matrices with the same nullspace have the same rank. -/
theorem matrixRank_eq_of_mulVec_eq_zero_iff
    {d : Type*} [Fintype d]
    (A B : Matrix d d ℂ)
    (hker : ∀ v : d → ℂ, A.mulVec v = 0 ↔ B.mulVec v = 0) :
    A.rank = B.rank := by
  have hkerEq : LinearMap.ker A.mulVecLin = LinearMap.ker B.mulVecLin := by
    ext v
    simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply]
    exact hker v
  have hA := A.mulVecLin.finrank_range_add_finrank_ker
  have hB := B.mulVecLin.finrank_range_add_finrank_ker
  unfold Matrix.rank
  rw [hkerEq] at hA
  omega

/-- Under eta-feature separation, even compression preserves exactly the
rank of the even parity projector. -/
theorem pairedEtaGeometricReflectionEvenCompressedZeroGram_rank
    (q : ℕ) {T : ℝ} (hT : 0 ≤ T) (n : ℕ)
    (hK : (pairedEtaGeometricMultiplicityWeightedZeroGram q
      (spectralZetaZeroWindow T) n).PosDef) :
    (pairedEtaGeometricReflectionEvenCompressedZeroGram q T hT n).rank =
      (spectralCriticalZetaZeroWindow T).card +
        (spectralUpperZetaZeroWindow T).card := by
  calc
    _ = (pairedEtaZeroWindowReflectionEvenProjection T hT).rank := by
      apply matrixRank_eq_of_mulVec_eq_zero_iff
      intro v
      exact hermitian_compressed_posDef_mulVec_eq_zero_iff _ _
        (pairedEtaZeroWindowReflectionEvenProjection_isHermitian T hT) hK v
    _ = _ := pairedEtaZeroWindowReflectionEvenProjection_rank T hT

/-- The nullity of the positive even-compressed eta carrier is exactly the
number of upper off-line reflection pairs. -/
theorem pairedEtaGeometricReflectionEvenCompressedZeroGram_nullity_eq_upper
    (q : ℕ) {T : ℝ} (hT : 0 ≤ T) (n : ℕ)
    (hK : (pairedEtaGeometricMultiplicityWeightedZeroGram q
      (spectralZetaZeroWindow T) n).PosDef) :
    (spectralZetaZeroWindow T).card -
        (pairedEtaGeometricReflectionEvenCompressedZeroGram q T hT n).rank =
      (spectralUpperZetaZeroWindow T).card := by
  rw [pairedEtaGeometricReflectionEvenCompressedZeroGram_rank q hT n hK,
    spectralZetaZeroWindow_card_eq_critical_add_two_mul_upper hT]
  omega

/-- Under eta-feature separation, odd compression has exactly one positive
direction for every upper off-line reflection pair. -/
theorem pairedEtaGeometricReflectionOddCompressedZeroGram_rank
    (q : ℕ) {T : ℝ} (hT : 0 ≤ T) (n : ℕ)
    (hK : (pairedEtaGeometricMultiplicityWeightedZeroGram q
      (spectralZetaZeroWindow T) n).PosDef) :
    (pairedEtaGeometricReflectionOddCompressedZeroGram q T hT n).rank =
      (spectralUpperZetaZeroWindow T).card := by
  calc
    _ = (pairedEtaZeroWindowReflectionOddProjection T hT).rank := by
      apply matrixRank_eq_of_mulVec_eq_zero_iff
      intro v
      exact hermitian_compressed_posDef_mulVec_eq_zero_iff _ _
        (pairedEtaZeroWindowReflectionOddProjection_isHermitian T hT) hK v
    _ = _ := pairedEtaZeroWindowReflectionOddProjection_rank T hT

/-- The trace of the even-compressed metric is half the positive eta mass
plus the mixed reflection trace. -/
theorem pairedEtaGeometricReflectionEvenCompressedZeroGram_rtrace
    (q : ℕ) (T : ℝ) (hT : 0 ≤ T) (n : ℕ) :
    HermitianInertia.rtrace
        (pairedEtaGeometricReflectionEvenCompressedZeroGram q T hT n) =
      (pairedEtaGeometricZeroGramTraceMass q T n +
        pairedEtaGeometricReflectionMixedTrace q T hT n) / 2 := by
  let E := pairedEtaZeroWindowReflectionEvenProjection T hT
  let K := pairedEtaGeometricMultiplicityWeightedZeroGram q
    (spectralZetaZeroWindow T) n
  have hE2 : E * E = E := by
    simpa only [E] using
      pairedEtaZeroWindowReflectionEvenProjection_mul_self T hT
  have htrace : (E * K * E).trace = (E * K).trace := by
    rw [Matrix.trace_mul_comm (E * K), ← Matrix.mul_assoc, hE2]
  unfold pairedEtaGeometricReflectionEvenCompressedZeroGram
  change HermitianInertia.rtrace (E * K * E) = _
  rw [HermitianInertia.rtrace, htrace]
  unfold E pairedEtaZeroWindowReflectionEvenProjection K
    pairedEtaGeometricZeroGramTraceMass
    pairedEtaGeometricReflectionMixedTrace HermitianInertia.rtrace
  simp only [Matrix.smul_mul, Matrix.add_mul, Matrix.one_mul,
    Matrix.trace_smul, Matrix.trace_add]
  change
    (((1 / 2 : ℂ) *
      ((pairedEtaGeometricMultiplicityWeightedZeroGram q
          (spectralZetaZeroWindow T) n).trace +
        (pairedEtaZeroWindowConjugatePartnerMatrix T hT *
          pairedEtaGeometricMultiplicityWeightedZeroGram q
            (spectralZetaZeroWindow T) n).trace)).re) = _
  simp only [Complex.add_re, Complex.mul_re]
  norm_num
  ring

/-- The trace of the odd-compressed metric is half the positive eta mass
minus the mixed reflection trace. -/
theorem pairedEtaGeometricReflectionOddCompressedZeroGram_rtrace
    (q : ℕ) (T : ℝ) (hT : 0 ≤ T) (n : ℕ) :
    HermitianInertia.rtrace
        (pairedEtaGeometricReflectionOddCompressedZeroGram q T hT n) =
      (pairedEtaGeometricZeroGramTraceMass q T n -
        pairedEtaGeometricReflectionMixedTrace q T hT n) / 2 := by
  let E := pairedEtaZeroWindowReflectionOddProjection T hT
  let K := pairedEtaGeometricMultiplicityWeightedZeroGram q
    (spectralZetaZeroWindow T) n
  have hE2 : E * E = E := by
    simpa only [E] using
      pairedEtaZeroWindowReflectionOddProjection_mul_self T hT
  have htrace : (E * K * E).trace = (E * K).trace := by
    rw [Matrix.trace_mul_comm (E * K), ← Matrix.mul_assoc, hE2]
  unfold pairedEtaGeometricReflectionOddCompressedZeroGram
  change HermitianInertia.rtrace (E * K * E) = _
  rw [HermitianInertia.rtrace, htrace]
  unfold E pairedEtaZeroWindowReflectionOddProjection K
    pairedEtaGeometricZeroGramTraceMass
    pairedEtaGeometricReflectionMixedTrace HermitianInertia.rtrace
  simp only [Matrix.smul_mul, Matrix.sub_mul, Matrix.one_mul,
    Matrix.trace_smul, Matrix.trace_sub]
  change
    (((1 / 2 : ℂ) *
      ((pairedEtaGeometricMultiplicityWeightedZeroGram q
          (spectralZetaZeroWindow T) n).trace -
        (pairedEtaZeroWindowConjugatePartnerMatrix T hT *
          pairedEtaGeometricMultiplicityWeightedZeroGram q
            (spectralZetaZeroWindow T) n).trace)).re) = _
  simp only [Complex.sub_re, Complex.mul_re]
  norm_num
  ring

/-- The reflection-even compressed eta mass is exactly the existing
on-line-plus-real colour channel. -/
theorem pairedEtaGeometricReflectionEvenCompressedZeroGram_rtrace_eq_onLine_add_real
    (q : ℕ) {T : ℝ} (hT : 0 ≤ T) (n : ℕ) :
    HermitianInertia.rtrace
        (pairedEtaGeometricReflectionEvenCompressedZeroGram q T hT n) =
      HermitianInertia.rtrace
          (pairedEtaTopPrefixFiniteZeroWindowOnLineBlock
            (fun j : Fin (spectralZetaZeroWindow T).card ↦
              pairedEtaGeometricHyperbolicCutoff q n j) T) +
        HermitianInertia.rtrace
          (pairedEtaTopPrefixFiniteZeroWindowOffLineRealBlock
            (fun j : Fin (spectralZetaZeroWindow T).card ↦
              pairedEtaGeometricHyperbolicCutoff q n j) T) := by
  rw [pairedEtaGeometricReflectionEvenCompressedZeroGram_rtrace]
  have hledger :=
    pairedEtaGeometricZeroGramTraceMass_add_reflectionMixedTrace_eq_two_onLine_add_real
      q hT n
  linarith

/-- The reflection-odd compressed eta mass is exactly the existing imaginary
off-line colour channel. -/
theorem pairedEtaGeometricReflectionOddCompressedZeroGram_rtrace_eq_offLineImag
    (q : ℕ) {T : ℝ} (hT : 0 ≤ T) (n : ℕ) :
    HermitianInertia.rtrace
        (pairedEtaGeometricReflectionOddCompressedZeroGram q T hT n) =
      HermitianInertia.rtrace
        (pairedEtaTopPrefixFiniteZeroWindowOffLineImagBlock
          (fun j : Fin (spectralZetaZeroWindow T).card ↦
            pairedEtaGeometricHyperbolicCutoff q n j) T) := by
  rw [pairedEtaGeometricReflectionOddCompressedZeroGram_rtrace]
  have hledger :=
    pairedEtaGeometricZeroGramTraceMass_sub_reflectionMixedTrace_eq_two_offLineImag
      q hT n
  linarith

/-- Terminal reflection-parity certificate interface.  On every nonempty
separated eta window, the even-compressed carrier is positive semidefinite,
its nullity is the upper off-line-pair count, the odd-compressed trace is the
literal imaginary off-line eta mass, and the associated unweighted
certificate is exactly the critical-zero proportion. -/
theorem pairedEtaGeometricReflectionParityCertificateInterface
    (q : ℕ) {T : ℝ} (hT : 0 ≤ T) (n : ℕ)
    (hwindow : (spectralZetaZeroWindow T).Nonempty)
    (hK : (pairedEtaGeometricMultiplicityWeightedZeroGram q
      (spectralZetaZeroWindow T) n).PosDef) :
    (pairedEtaGeometricReflectionEvenCompressedZeroGram q T hT n).PosSemidef ∧
      (spectralZetaZeroWindow T).card -
          (pairedEtaGeometricReflectionEvenCompressedZeroGram q T hT n).rank =
        (spectralUpperZetaZeroWindow T).card ∧
      HermitianInertia.rtrace
          (pairedEtaGeometricReflectionOddCompressedZeroGram q T hT n) =
        HermitianInertia.rtrace
          (pairedEtaTopPrefixFiniteZeroWindowOffLineImagBlock
            (fun j : Fin (spectralZetaZeroWindow T).card ↦
              pairedEtaGeometricHyperbolicCutoff q n j) T) ∧
      pairedEtaZeroWindowReflectionCountCertificate T hT =
        (spectralCriticalZetaZeroWindow T).card /
          (spectralZetaZeroWindow T).card := by
  exact
    ⟨pairedEtaGeometricReflectionEvenCompressedZeroGram_posSemidef q T hT n,
      pairedEtaGeometricReflectionEvenCompressedZeroGram_nullity_eq_upper
        q hT n hK,
      pairedEtaGeometricReflectionOddCompressedZeroGram_rtrace_eq_offLineImag
        q hT n,
      pairedEtaZeroWindowReflectionCountCertificate_eq_criticalFraction
        hT hwindow⟩

end

end RiemannGaussian
