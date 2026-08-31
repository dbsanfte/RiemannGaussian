import RiemannGaussian.Hybrid.EtaGeometricReflectionSumFullReserveLowerBound

/-!
# Certificate interface for the explicit eta reserve floor

The preceding colour decomposition proves that the named nonnegative
upper-sector expression is eventually below the complete reflection-even
decorrelation reserve.  This module substitutes that proved comparison into
the two existing certificate theorems.

For a nonempty finite spectral window with at least two represented zeros,
Lean selects one odd prime geometric base and discharges positive definiteness
of the literal eta Gram at every sufficiently late block.  At those blocks,
the explicit `13/18` floor inequality implies a critical-zero proportion
strictly above `13/18`, while the endpoint floor inequality implies that every
represented zero is critical.  Both inequalities remain open antecedents;
this module proves no improved zero proportion.
-/

open Complex Matrix Finset Filter Topology
open scoped BigOperators Classical ComplexConjugate ComplexOrder Matrix Real

namespace RiemannGaussian

noncomputable section

/-- The two certificate implications after replacing the complete reserve by
its explicit checked nonnegative upper-sector floor. -/
def PairedEtaGeometricReflectionEvenUpperReserveGapFloorTargets
    (q : ℕ) (T : ℝ) (n : ℕ) (ε : ℝ) : Prop :=
  ((((31 : ℝ) * (spectralZetaZeroWindow T).card - 36) *
        pairedEtaReflectionEvenFramePotential
          (fun j : Fin (spectralZetaZeroWindow T).card ↦
            pairedEtaGeometricHyperbolicCutoff q n j) T <
      36 * pairedEtaGeometricUpperWindowNonnegativeReserveGapLower
        q T n (spectralZetaZeroWindow T).card ε) →
    (13 : ℝ) / 18 <
      (spectralCriticalZetaZeroWindow T).card /
        (spectralZetaZeroWindow T).card) ∧
  (((((spectralZetaZeroWindow T).card : ℝ) - 1) *
        pairedEtaReflectionEvenFramePotential
          (fun j : Fin (spectralZetaZeroWindow T).card ↦
            pairedEtaGeometricHyperbolicCutoff q n j) T ≤
      pairedEtaGeometricUpperWindowNonnegativeReserveGapLower
        q T n (spectralZetaZeroWindow T).card ε) →
    (spectralCriticalZetaZeroWindow T).card =
      (spectralZetaZeroWindow T).card)

/-- Once the explicit floor is below the complete reserve, the two floor
inequalities feed directly into the existing `13/18` and endpoint certificate
theorems. -/
theorem pairedEtaGeometricReflectionEvenUpperReserveGapFloorCertificateInterface
    (q : ℕ) {T : ℝ} (hT : 0 ≤ T) (n : ℕ)
    (hwindow : (spectralZetaZeroWindow T).Nonempty)
    (hK : (pairedEtaGeometricMultiplicityWeightedZeroGram q
      (spectralZetaZeroWindow T) n).PosDef)
    (ε : ℝ)
    (hfloor :
      pairedEtaGeometricUpperWindowNonnegativeReserveGapLower
          q T n (spectralZetaZeroWindow T).card ε ≤
        pairedEtaReflectionEvenFrameDecorrelationReserve
          (fun j : Fin (spectralZetaZeroWindow T).card ↦
            pairedEtaGeometricHyperbolicCutoff q n j) T) :
    PairedEtaGeometricReflectionEvenUpperReserveGapFloorTargets
      q T n ε := by
  unfold PairedEtaGeometricReflectionEvenUpperReserveGapFloorTargets
  constructor
  · intro hthirteen
    apply pairedEtaGeometricReflectionEven_thirteen_eighteen_of_decorrelationReserve
      q hT n hwindow hK
    exact hthirteen.trans_le
      (mul_le_mul_of_nonneg_left hfloor (by norm_num))
  · intro hendpoint
    apply pairedEtaGeometricReflectionEven_allCritical_of_decorrelationReserve
      q hT n hwindow hK
    exact hendpoint.trans hfloor

/-- For one separated odd-base eta family, both explicit-floor certificate
implications are valid at every sufficiently late block. -/
theorem eventually_pairedEtaGeometricReflectionEvenUpperReserveGapFloorCertificateInterface
    {q : ℕ} (hqOdd : Odd q) (hq : 1 < q) {T : ℝ}
    (hT : 0 ≤ T) (hwindow : (spectralZetaZeroWindow T).Nonempty)
    (hcard : 1 < (spectralZetaZeroWindow T).card)
    {ε : ℝ} (hε : 0 < ε)
    (hK : ∀ᶠ n in atTop,
      (pairedEtaGeometricMultiplicityWeightedZeroGram q
        (spectralZetaZeroWindow T) n).PosDef) :
    ∀ᶠ n in atTop,
      PairedEtaGeometricReflectionEvenUpperReserveGapFloorTargets
        q T n ε := by
  have hfloor :=
    eventually_pairedEtaGeometricUpperWindowNonnegativeReserveGapLower_le_fullDecorrelationReserve
      hqOdd hq T hcard hε
  filter_upwards [hK, hfloor] with n hKn hfloorN
  exact
    pairedEtaGeometricReflectionEvenUpperReserveGapFloorCertificateInterface
      q hT n hwindow hKn ε hfloorN

/-- Every eligible finite window admits one odd prime base for which the
literal eta features validate both explicit-floor certificate implications at
all sufficiently late blocks.  The two floor inequalities themselves are not
asserted. -/
theorem exists_prime_eventually_pairedEtaGeometricReflectionEvenUpperReserveGapFloorCertificateInterface
    {T : ℝ} (hT : 0 ≤ T)
    (hwindow : (spectralZetaZeroWindow T).Nonempty)
    (hcard : 1 < (spectralZetaZeroWindow T).card)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ q : ℕ, q.Prime ∧ Odd q ∧ 1 < q ∧
      ∀ᶠ n in atTop,
        PairedEtaGeometricReflectionEvenUpperReserveGapFloorTargets
          q T n ε := by
  obtain ⟨q, hqPrime, hqOdd, hq, hpos⟩ :=
    exists_prime_eventually_posDef_pairedEtaGeometricMultiplicityWeightedZeroGram_and_inv
      (spectralZetaZeroWindow T)
  refine ⟨q, hqPrime, hqOdd, hq, ?_⟩
  exact
    eventually_pairedEtaGeometricReflectionEvenUpperReserveGapFloorCertificateInterface
      hqOdd hq hT hwindow hcard hε (hpos.mono fun _ hn ↦ hn.1)

end

end RiemannGaussian
