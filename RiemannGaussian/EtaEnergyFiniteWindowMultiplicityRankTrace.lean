import RiemannGaussian.EtaEnergyFiniteWindowRankTrace
import RiemannGaussian.HermitianRankTrace.Multiplicity

/-!
# Multiplicity-aware rank--trace ledger for finite eta zero windows

This module specializes the multiplicity-aware strengthening of the
rank--trace theorem to the genuine finite eta matrix.  On the critical line,
reflection fixes each zero and therefore fixes its packed eta feature under
complex conjugation.  The on-line complex-symmetric block is consequently
the ordinary positive Gram matrix required by the general theorem.

Unlike the coarser rank penalty, the resulting scalar ledger retains one
nonlinear `k_c` contribution for every actual critical zero, evaluated at its
analytic multiplicity times its squared packed-feature norm.  No estimate of
that finite arithmetic expression is assumed here.
-/

open Complex
open Matrix Finset
open scoped Classical ComplexConjugate ComplexOrder Matrix

namespace RiemannGaussian

noncomputable section

/-- The multiplicity-aware critical-line penalty in the finite eta
rank--trace ledger. -/
def pairedEtaTopPrefixFiniteZeroWindowCriticalMultiplicityPenalty
    {d : Type*} [Fintype d] (cutoff : d → ℕ) (T c : ℝ) : ℝ :=
  ∑ rho ∈ spectralCriticalZetaZeroWindow T,
    HermitianRankTrace.Multiplicity.kc c
      ((analyticZetaZeroMultiplicity rho : ℝ) *
        ∑ j, ‖pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho j‖ ^ 2)

private theorem onLineBlock_eq_criticalMultiplicityPmat
    {d : Type*} (cutoff : d → ℕ) (T : ℝ) :
    pairedEtaTopPrefixFiniteZeroWindowOnLineBlock cutoff T =
      let ι := ↥(spectralCriticalZetaZeroWindow T)
      let m : ι → ℝ := fun rho ↦ analyticZetaZeroMultiplicity rho.1
      let v : ι → d × Fin 2 → ℂ := fun rho ↦
        pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho.1
      HermitianRankTrace.Multiplicity.Pmat m v := by
  classical
  let ι := ↥(spectralCriticalZetaZeroWindow T)
  let m : ι → ℝ := fun rho ↦ analyticZetaZeroMultiplicity rho.1
  let v : ι → d × Fin 2 → ℂ := fun rho ↦
    pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho.1
  dsimp only
  ext a b
  unfold pairedEtaTopPrefixFiniteZeroWindowOnLineBlock
  rw [HermitianRankTrace.Multiplicity.Pmat_apply
    (fun _ ↦ by positivity) v]
  simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply,
    smul_eq_mul]
  rw [Finset.sum_subtype (spectralCriticalZetaZeroWindow T)
    (fun _ ↦ Iff.rfl)]
  refine Finset.sum_congr rfl fun rho _ ↦ ?_
  have hre : rho.1.1.re = 1 / 2 :=
    (zetaSpectralCoordinate_im_eq_zero_iff rho.1.1).1
      (mem_spectralCriticalZetaZeroWindow.mp rho.2).2
  have hpartner : NontrivialZetaZero.conjugatePartner rho.1 = rho.1 :=
    conjugatePartner_eq_self_of_re_eq_half rho.1 hre
  have hstar :
      star (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho.1) =
        pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho.1 := by
    rw [← topPrefixFiniteCutoffFamilyFeature_conjugatePartner, hpartner]
  have hb := congrFun hstar b
  simp only [Pi.star_apply, RCLike.star_def] at hb
  dsimp only [m, v]
  rw [hb]
  norm_cast

/-- Multiplicity-aware rank--trace closure for the literal finite eta
window.  The critical contribution retains analytic multiplicity and the
actual packed-feature norm instead of being replaced by a cardinality
penalty. -/
theorem pairedEtaTopPrefixFiniteZeroWindow_multiplicityRankTrace_ledger
    {d : Type*} [Fintype d] (cutoff : d → ℕ) {T c : ℝ}
    (hT : 0 ≤ T) (hc : 0 < c) :
    2 * c *
        (pairedEtaTopPrefixFiniteZeroWindowOnLineTraceMass cutoff T +
          pairedEtaTopPrefixFiniteZeroWindowOffLineTraceMass cutoff T) -
      pairedEtaTopPrefixFiniteZeroWindowCoherentFrobeniusMass cutoff T ≤
        pairedEtaTopPrefixFiniteZeroWindowCriticalMultiplicityPenalty
          cutoff T c +
        c ^ 2 * (spectralUpperZetaZeroWindow T).card := by
  classical
  let ι := ↥(spectralCriticalZetaZeroWindow T)
  let m : ι → ℝ := fun rho ↦ analyticZetaZeroMultiplicity rho.1
  let v : ι → d × Fin 2 → ℂ := fun rho ↦
    pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho.1
  let Q := pairedEtaTopPrefixFiniteZeroWindowOffLineRealBlock cutoff T -
    pairedEtaTopPrefixFiniteZeroWindowOffLineImagBlock cutoff T
  have hm : ∀ rho, 0 ≤ m rho := by
    intro rho
    dsimp only [m]
    positivity
  have hQ : Q.IsHermitian :=
    (pairedEtaTopPrefixFiniteZeroWindowOffLineRealBlock_posSemidef
        cutoff T).isHermitian.sub
      (pairedEtaTopPrefixFiniteZeroWindowOffLineImagBlock_posSemidef
        cutoff T).isHermitian
  have hbHermitianInertia :
      HermitianInertia.posIndex hQ ≤
        (spectralUpperZetaZeroWindow T).card := by
    simpa only [Q] using
      pairedEtaTopPrefixFiniteZeroWindowOffLineDifference_posIndex_le_card
        cutoff T
  have hb :
      HermitianRankTrace.posIndex hQ ≤
        (spectralUpperZetaZeroWindow T).card := by
    simpa only [HermitianRankTrace.posIndex, HermitianInertia.posIndex] using
      hbHermitianInertia
  have h := HermitianRankTrace.Multiplicity.rank_trace_mult_k
    hm v hQ hb hc
  have hOnLine :
      pairedEtaTopPrefixFiniteZeroWindowOnLineBlock cutoff T =
        HermitianRankTrace.Multiplicity.Pmat m v := by
    simpa only [ι, m, v] using
      onLineBlock_eq_criticalMultiplicityPmat cutoff T
  have hdecomp :
      pairedEtaTopPrefixFiniteZeroWindowBlock cutoff T =
        HermitianRankTrace.Multiplicity.Pmat m v + Q := by
    rw [pairedEtaTopPrefixFiniteZeroWindowBlock_eq_onLine_add_offLineReal_sub_imag
      cutoff hT, hOnLine]
  rw [← hdecomp] at h
  have hpenalty :
      (∑ rho : ι,
        HermitianRankTrace.Multiplicity.kc c
          (m rho * HermitianRankTrace.Multiplicity.xsq v rho)) =
        pairedEtaTopPrefixFiniteZeroWindowCriticalMultiplicityPenalty
          cutoff T c := by
    unfold pairedEtaTopPrefixFiniteZeroWindowCriticalMultiplicityPenalty
    rw [Finset.sum_subtype (spectralCriticalZetaZeroWindow T)
      (fun _ ↦ Iff.rfl)]
    rfl
  rw [hpenalty] at h
  have htrace :
      HermitianInertia.rtrace
          (pairedEtaTopPrefixFiniteZeroWindowBlock cutoff T) =
        pairedEtaTopPrefixFiniteZeroWindowOnLineTraceMass cutoff T +
          pairedEtaTopPrefixFiniteZeroWindowOffLineTraceMass cutoff T := by
    rw [pairedEtaTopPrefixFiniteZeroWindowBlock_eq_onLine_add_offLineReal_sub_imag
      cutoff hT, HermitianInertia.rtrace_add,
      pairedEtaTopPrefixFiniteZeroWindowOnLineBlock_rtrace_eq_mass,
      pairedEtaTopPrefixFiniteZeroWindowOffLineDifference_rtrace_eq_mass]
  change 2 * c * HermitianInertia.rtrace
      (pairedEtaTopPrefixFiniteZeroWindowBlock cutoff T) -
        HermitianInertia.frobSq
          (pairedEtaTopPrefixFiniteZeroWindowBlock cutoff T) ≤
      pairedEtaTopPrefixFiniteZeroWindowCriticalMultiplicityPenalty
          cutoff T c +
        c ^ 2 * (spectralUpperZetaZeroWindow T).card at h
  rw [htrace,
    pairedEtaTopPrefixFiniteZeroWindowBlock_frobSq_eq_coherentMass] at h
  exact h

/-- The multiplicity-aware eta ledger at `c = 2`. -/
theorem pairedEtaTopPrefixFiniteZeroWindow_multiplicityRankTrace_two_ledger
    {d : Type*} [Fintype d] (cutoff : d → ℕ) {T : ℝ} (hT : 0 ≤ T) :
    4 * (pairedEtaTopPrefixFiniteZeroWindowOnLineTraceMass cutoff T +
        pairedEtaTopPrefixFiniteZeroWindowOffLineTraceMass cutoff T) -
      pairedEtaTopPrefixFiniteZeroWindowCoherentFrobeniusMass cutoff T ≤
        pairedEtaTopPrefixFiniteZeroWindowCriticalMultiplicityPenalty
          cutoff T 2 +
        4 * (spectralUpperZetaZeroWindow T).card := by
  have h := pairedEtaTopPrefixFiniteZeroWindow_multiplicityRankTrace_ledger
    cutoff hT (c := 2) (by norm_num)
  norm_num at h ⊢
  exact h

end

end RiemannGaussian
