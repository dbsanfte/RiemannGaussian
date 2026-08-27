import RiemannGaussian.FiniteToEntireHeatFrontier
import RiemannGaussian.RiemannXiHyperbolicHeat

/-!
# The finite Hardy core inside the full polynomial heat divisor

This file keeps algebraic multiplicity while placing the canonical Hardy
influence core inside the complete upper root divisor of each real polynomial.
At every fixed positive proper time, positivity of the heat kernel then makes
the core heat sum no larger than the complete upper-divisor heat sum.  The
same domination holds for positive truncated proper-time actions and for their
limiting logarithmic masses.
-/

open Filter Metric Polynomial Set
open scoped Topology

namespace RiemannGaussian

noncomputable section

/-- A finite multiplicity-counted fixed-time upper-half-plane heat sum. -/
def finiteUpperHyperbolicHeatSum
    (z : ℂ) (upper : Multiset ℂ) (tau : ℝ) : ℝ :=
  (upper.map fun alpha ↦
    upperHalfPlaneHyperbolicHeatIntegrand z alpha tau).sum

/-- A submultiset has no larger sum when every ambient summand is
nonnegative. -/
theorem multiset_sum_map_le_of_le_of_nonneg
    {alpha : Type*} {s t : Multiset alpha} (f : alpha → ℝ)
    (hst : s ≤ t) (hf : ∀ x ∈ t, 0 ≤ f x) :
    (s.map f).sum ≤ (t.map f).sum := by
  obtain ⟨u, rfl⟩ := Multiset.le_iff_exists_add.mp hst
  rw [Multiset.map_add, Multiset.sum_add]
  apply le_add_of_nonneg_right
  apply Multiset.sum_nonneg
  intro y hy
  obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp hy
  exact hf x (by simp [hx])

/-- A finite heat sum over upper-half-plane points is nonnegative at positive
proper time. -/
theorem finiteUpperHyperbolicHeatSum_nonneg
    {z : ℂ} (hz : 0 < z.im) {upper : Multiset ℂ}
    (halpha : ∀ alpha ∈ upper, 0 < alpha.im)
    {tau : ℝ} (htau : 0 < tau) :
    0 ≤ finiteUpperHyperbolicHeatSum z upper tau := by
  apply Multiset.sum_nonneg
  intro x hx
  obtain ⟨alpha, halphaMem, rfl⟩ := Multiset.mem_map.mp hx
  exact (upperHalfPlaneHyperbolicHeatIntegrand_pos
    hz (halpha alpha halphaMem) htau).le

/-- A nonempty finite upper divisor has strictly positive heat sum at every
positive proper time. -/
theorem finiteUpperHyperbolicHeatSum_pos
    {z : ℂ} (hz : 0 < z.im) {upper : Multiset ℂ}
    (halpha : ∀ alpha ∈ upper, 0 < alpha.im) (hupper : upper ≠ 0)
    {tau : ℝ} (htau : 0 < tau) :
    0 < finiteUpperHyperbolicHeatSum z upper tau := by
  obtain ⟨alpha, halphaMem⟩ := Multiset.exists_mem_of_ne_zero hupper
  obtain ⟨tail, rfl⟩ := Multiset.exists_cons_of_mem halphaMem
  rw [finiteUpperHyperbolicHeatSum, Multiset.map_cons, Multiset.sum_cons]
  apply add_pos_of_pos_of_nonneg
  · exact upperHalfPlaneHyperbolicHeatIntegrand_pos
      hz (halpha alpha (by simp)) htau
  · apply Multiset.sum_nonneg
    intro x hx
    obtain ⟨beta, hbeta, rfl⟩ := Multiset.mem_map.mp hx
    exact (upperHalfPlaneHyperbolicHeatIntegrand_pos
      hz (halpha beta (by simp [hbeta])) htau).le

/-- Fixed-time heat sums are monotone under multiplicity-preserving
submultiset inclusion. -/
theorem finiteUpperHyperbolicHeatSum_mono
    {z : ℂ} (hz : 0 < z.im) {lower upper : Multiset ℂ}
    (hle : lower ≤ upper)
    (halpha : ∀ alpha ∈ upper, 0 < alpha.im)
    {tau : ℝ} (htau : 0 < tau) :
    finiteUpperHyperbolicHeatSum z lower tau ≤
      finiteUpperHyperbolicHeatSum z upper tau := by
  exact multiset_sum_map_le_of_le_of_nonneg
    (fun alpha ↦ upperHalfPlaneHyperbolicHeatIntegrand z alpha tau)
    hle fun alpha halphaMem ↦
      (upperHalfPlaneHyperbolicHeatIntegrand_pos
        hz (halpha alpha halphaMem) htau).le

/-- Positive truncated proper-time heat actions are monotone under
multiplicity-preserving submultiset inclusion. -/
theorem upperHalfPlaneHyperbolicHeatAction_mono
    {z : ℂ} (hz : 0 < z.im) {lower upper : Multiset ℂ}
    (hle : lower ≤ upper)
    (halpha : ∀ alpha ∈ upper, 0 < alpha.im)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    upperHalfPlaneHyperbolicHeatAction z lower (a, b) ≤
      upperHalfPlaneHyperbolicHeatAction z upper (a, b) := by
  apply multiset_sum_map_le_of_le_of_nonneg _ hle
  intro alpha halphaMem
  apply intervalIntegral.integral_nonneg hab
  intro tau htau
  exact (upperHalfPlaneHyperbolicHeatIntegrand_pos hz
    (halpha alpha halphaMem) (ha.trans_le htau.1)).le

/-- The limiting logarithmic heat mass of a finite upper divisor. -/
def finiteUpperHyperbolicHeatMass
    (z : ℂ) (upper : Multiset ℂ) : ℝ :=
  -2 * Real.log
    ((upper.map fun alpha ↦
      upperHalfPlanePseudoHyperbolicDistance z alpha).prod)

/-- The finite logarithmic heat mass is the sum of the individual positive
logarithmic defects. -/
theorem finiteUpperHyperbolicHeatMass_eq_sum
    {z : ℂ} (hz : 0 < z.im) {upper : Multiset ℂ}
    (halpha : ∀ alpha ∈ upper, 0 < alpha.im)
    (hne : ∀ alpha ∈ upper, z ≠ alpha) :
    finiteUpperHyperbolicHeatMass z upper =
      (upper.map fun alpha ↦ -2 * Real.log
        (upperHalfPlanePseudoHyperbolicDistance z alpha)).sum := by
  let radii := upper.map fun alpha ↦
    upperHalfPlanePseudoHyperbolicDistance z alpha
  have hradii : ∀ r ∈ radii, r ≠ 0 := by
    intro r hr
    obtain ⟨alpha, halphaMem, rfl⟩ := Multiset.mem_map.mp hr
    exact (upperHalfPlanePseudoHyperbolicDistance_pos_of_ne
      hz (halpha alpha halphaMem) (hne alpha halphaMem)).ne'
  symm
  change
    (upper.map fun alpha ↦ -2 * Real.log
        (upperHalfPlanePseudoHyperbolicDistance z alpha)).sum =
      -2 * Real.log radii.prod
  rw [Real.log_multiset_prod hradii, ← Multiset.sum_map_mul_left,
    Multiset.map_map]
  rfl

/-- Limiting finite heat masses are monotone under submultiset inclusion. -/
theorem finiteUpperHyperbolicHeatMass_mono
    {z : ℂ} (hz : 0 < z.im) {lower upper : Multiset ℂ}
    (hle : lower ≤ upper)
    (halpha : ∀ alpha ∈ upper, 0 < alpha.im)
    (hne : ∀ alpha ∈ upper, z ≠ alpha) :
    finiteUpperHyperbolicHeatMass z lower ≤
      finiteUpperHyperbolicHeatMass z upper := by
  rw [finiteUpperHyperbolicHeatMass_eq_sum hz
      (fun alpha halphaMem ↦
        halpha alpha (Multiset.mem_of_le hle halphaMem))
      (fun alpha halphaMem ↦
        hne alpha (Multiset.mem_of_le hle halphaMem)),
    finiteUpperHyperbolicHeatMass_eq_sum hz halpha hne]
  apply multiset_sum_map_le_of_le_of_nonneg _ hle
  intro alpha halphaMem
  have hrpos := upperHalfPlanePseudoHyperbolicDistance_pos_of_ne
    hz (halpha alpha halphaMem) (hne alpha halphaMem)
  have hrlt := upperHalfPlanePseudoHyperbolicDistance_lt_one
    hz (halpha alpha halphaMem)
  have hlog := Real.log_neg hrpos hrlt
  nlinarith

/-- The canonical Hardy core is literally a submultiset of the complete
upper root divisor, so this statement preserves algebraic multiplicity. -/
theorem canonicalInsideInfluenceDiskRoots_le_upperRootMultiset
    (A : ℝ[X]) (z : ℂ) :
    canonicalInsideInfluenceDiskRoots A z ≤
      realPolynomialUpperRootMultiset A := by
  exact Multiset.filter_le _ _

/-- The complete fixed-time upper-root heat sum of a real polynomial. -/
def realPolynomialUpperHyperbolicHeatSum
    (A : ℝ[X]) (z : ℂ) (tau : ℝ) : ℝ :=
  finiteUpperHyperbolicHeatSum z
    (realPolynomialUpperRootMultiset A) tau

/-- The complete limiting upper-root logarithmic heat mass of a real
polynomial. -/
def realPolynomialUpperHyperbolicHeatMass
    (A : ℝ[X]) (z : ℂ) : ℝ :=
  finiteUpperHyperbolicHeatMass z (realPolynomialUpperRootMultiset A)

/-- At each positive proper time, the canonical Hardy-core heat sum is
dominated by the complete polynomial upper-divisor heat sum. -/
theorem canonicalInsideInfluenceDiskHeatSum_le_realPolynomialUpper
    {A : ℝ[X]} {z : ℂ} (hz : 0 < z.im)
    {tau : ℝ} (htau : 0 < tau) :
    finiteUpperHyperbolicHeatSum z
        (canonicalInsideInfluenceDiskRoots A z) tau ≤
      realPolynomialUpperHyperbolicHeatSum A z tau := by
  exact finiteUpperHyperbolicHeatSum_mono hz
    (canonicalInsideInfluenceDiskRoots_le_upperRootMultiset A z)
    (realPolynomialUpperRootMultiset_im_pos A) htau

/-- The same canonical-core domination holds for every positive truncated
proper-time interval. -/
theorem canonicalInsideInfluenceDiskHeatAction_le_realPolynomialUpper
    {A : ℝ[X]} {z : ℂ} (hz : 0 < z.im)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    upperHalfPlaneHyperbolicHeatAction z
        (canonicalInsideInfluenceDiskRoots A z) (a, b) ≤
      upperHalfPlaneHyperbolicHeatAction z
        (realPolynomialUpperRootMultiset A) (a, b) := by
  exact upperHalfPlaneHyperbolicHeatAction_mono hz
    (canonicalInsideInfluenceDiskRoots_le_upperRootMultiset A z)
    (realPolynomialUpperRootMultiset_im_pos A) ha hab

/-- At a positive finite-homotopy root, the complete polynomial upper-divisor
heat sum is strictly positive at every positive proper time. -/
theorem realPolynomialUpperHyperbolicHeatSum_pos_of_finiteE_root
    {A : ℝ[X]} (hA : A.Separable) {eta : ℝ} (heta : 0 < eta)
    {z : ℂ} (hz : 0 < z.im)
    (hroot : (finiteEPolynomial A eta).eval z = 0)
    {tau : ℝ} (htau : 0 < tau) :
    0 < realPolynomialUpperHyperbolicHeatSum A z tau := by
  have hcorePos : 0 < finiteUpperHyperbolicHeatSum z
      (canonicalInsideInfluenceDiskRoots A z) tau := by
    apply finiteUpperHyperbolicHeatSum_pos hz
      canonicalInsideInfluenceDiskRoots_im_pos
    · exact Multiset.card_pos.mp
        (canonicalInsideInfluenceDiskRoots_card_pos_of_finiteE_root
          hA heta hz hroot)
    · exact htau
  exact hcorePos.trans_le
    (canonicalInsideInfluenceDiskHeatSum_le_realPolynomialUpper hz htau)

/-- The complete polynomial upper-divisor heat action converges to its full
logarithmic mass at a positive finite-homotopy root. -/
theorem tendsto_realPolynomialUpperHyperbolicHeatAction_of_finiteE_root
    {A : ℝ[X]} (hA : A.Separable) {eta : ℝ} (heta : 0 < eta)
    {z : ℂ} (hz : 0 < z.im)
    (hroot : (finiteEPolynomial A eta).eval z = 0) :
    Tendsto
      (upperHalfPlaneHyperbolicHeatAction z
        (realPolynomialUpperRootMultiset A))
      ((nhdsWithin 0 (Ioi 0)) ×ˢ atTop)
      (nhds (realPolynomialUpperHyperbolicHeatMass A z)) := by
  apply tendsto_upperHalfPlaneHyperbolicHeatAction hz
    (realPolynomialUpperRootMultiset A)
    (realPolynomialUpperRootMultiset_im_pos A)
  intro alpha halphaMem
  exact finiteE_root_ne_upperResidual hA heta hroot
    (realPolynomial_roots_eq_real_add_conjugatePairs A) alpha halphaMem

/-- The canonical Hardy logarithmic mass is dominated by the complete upper
root divisor mass at every positive finite-homotopy root. -/
theorem canonicalInsideInfluenceDiskHeatMass_le_realPolynomialUpper
    {A : ℝ[X]} (hA : A.Separable) {eta : ℝ} (heta : 0 < eta)
    {z : ℂ} (hz : 0 < z.im)
    (hroot : (finiteEPolynomial A eta).eval z = 0) :
    canonicalInsideInfluenceDiskHeatMass A z ≤
      realPolynomialUpperHyperbolicHeatMass A z := by
  have hne : ∀ alpha ∈ realPolynomialUpperRootMultiset A, z ≠ alpha := by
    intro alpha halphaMem
    exact finiteE_root_ne_upperResidual hA heta hroot
      (realPolynomial_roots_eq_real_add_conjugatePairs A) alpha halphaMem
  simpa [canonicalInsideInfluenceDiskHeatMass,
      finiteUpperHyperbolicHeatMass,
      realPolynomialUpperHyperbolicHeatMass] using
    (finiteUpperHyperbolicHeatMass_mono hz
      (canonicalInsideInfluenceDiskRoots_le_upperRootMultiset A z)
      (realPolynomialUpperRootMultiset_im_pos A) hne)

/-- The complete upper polynomial divisor inherits the same explicit positive
mass lower bound as the canonical Hardy core. -/
theorem realPolynomialUpperHyperbolicHeatAction_frontier
    {A : ℝ[X]} (hA : A.Separable) {eta : ℝ} (heta : 0 < eta)
    {z : ℂ} (hz : 0 < z.im)
    (hroot : (finiteEPolynomial A eta).eval z = 0) :
    Tendsto
        (upperHalfPlaneHyperbolicHeatAction z
          (realPolynomialUpperRootMultiset A))
        ((nhdsWithin 0 (Ioi 0)) ×ˢ atTop)
        (nhds (realPolynomialUpperHyperbolicHeatMass A z)) ∧
      0 < -2 * Real.log (pairHyperbolicThreshold eta z.im) ∧
      -2 * Real.log (pairHyperbolicThreshold eta z.im) ≤
        realPolynomialUpperHyperbolicHeatMass A z := by
  have hcore := canonicalInsideInfluenceDiskHeatAction_frontier
    hA heta hz hroot
  exact ⟨tendsto_realPolynomialUpperHyperbolicHeatAction_of_finiteE_root
      hA heta hz hroot,
    hcore.2.1,
    hcore.2.2.trans
      (canonicalInsideInfluenceDiskHeatMass_le_realPolynomialUpper
        hA heta hz hroot)⟩

/-- Failure of RH yields one root-pinned polynomial sequence whose complete
upper divisors dominate their Hardy cores pointwise and retain the same
stage-independent positive total heat-mass bound. -/
theorem exists_uniform_realPolynomialUpperHeat_frontier_of_not_rh
    (hRH : ¬RiemannHypothesis) :
    ∃ eta : ℝ, 0 < eta ∧ ∃ z : ℂ, 0 < z.im ∧
      ∃ B : ℕ → ℝ[X],
        TendstoLocallyUniformlyOn
          (fun n w ↦ ((B n).map Complex.ofRealHom).eval w)
          riemannXiSpectral atTop Set.univ ∧
        (∀ n, CanonicalFiniteHardyFrontier (B n) eta z) ∧
        0 < -2 * Real.log (pairHyperbolicThreshold eta z.im) ∧
        ∀ n,
          (∀ tau : ℝ, 0 < tau →
            0 < realPolynomialUpperHyperbolicHeatSum (B n) z tau ∧
            finiteUpperHyperbolicHeatSum z
                (canonicalInsideInfluenceDiskRoots (B n) z) tau ≤
              realPolynomialUpperHyperbolicHeatSum (B n) z tau) ∧
          Tendsto
              (upperHalfPlaneHyperbolicHeatAction z
                (realPolynomialUpperRootMultiset (B n)))
              ((nhdsWithin 0 (Ioi 0)) ×ˢ atTop)
              (nhds (realPolynomialUpperHyperbolicHeatMass (B n) z)) ∧
          -2 * Real.log (pairHyperbolicThreshold eta z.im) ≤
            realPolynomialUpperHyperbolicHeatMass (B n) z := by
  obtain ⟨eta, heta, z, hz, B, hB, hfrontier⟩ :=
    exists_canonicalFiniteHardyFrontier_sequence_of_not_rh hRH
  have hthreshold := realPolynomialUpperHyperbolicHeatAction_frontier
    (hfrontier 0).separable heta hz (hfrontier 0).homotopyRoot
  refine ⟨eta, heta, z, hz, B, hB, hfrontier, hthreshold.2.1, ?_⟩
  intro n
  have hstage := realPolynomialUpperHyperbolicHeatAction_frontier
    (hfrontier n).separable heta hz (hfrontier n).homotopyRoot
  refine ⟨?_, hstage.1, hstage.2.2⟩
  intro tau htau
  exact ⟨realPolynomialUpperHyperbolicHeatSum_pos_of_finiteE_root
      (hfrontier n).separable heta hz (hfrontier n).homotopyRoot htau,
    canonicalInsideInfluenceDiskHeatSum_le_realPolynomialUpper hz htau⟩

end

end RiemannGaussian
