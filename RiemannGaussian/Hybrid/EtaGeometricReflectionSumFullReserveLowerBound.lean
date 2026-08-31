import RiemannGaussian.Hybrid.EtaGeometricReflectionSumReserveLowerBound

/-!
# Transporting the upper eta reserve bound into the complete certificate

The quantitative bound from the preceding module is a sum over ordered
distinct upper--upper atom pairs.  The complete reflection-even certificate
also contains critical--critical and both oriented critical--upper sectors.
This module separates those four colours exactly, proves every omitted sector
nonnegative, and identifies the upper sector with the already bounded literal
sum.

Consequently the explicit upper-sector lower bound is also an unconditional
eventual lower bound for the complete decorrelation reserve.  Taking its
maximum with zero retains the independent global nonnegativity theorem.  The
result is still not proved positive or large enough for the certificate
inequalities; no zero-proportion improvement is claimed here.
-/

open Complex Matrix Finset Filter Topology
open scoped BigOperators Classical ComplexConjugate ComplexOrder Matrix Real

namespace RiemannGaussian

noncomputable section

/-- One literal ordered pair summand of the geometric reflection-even frame
reserve, before restricting either atom colour. -/
def pairedEtaGeometricReflectionEvenFramePairReserveTerm
    (q : ℕ) (T : ℝ) (n M : ℕ)
    (a b : PairedEtaReflectionEvenFrameIndex T) : ℝ :=
  pairedEtaReflectionEvenFrameWeight T a *
    pairedEtaReflectionEvenFrameWeight T b *
      (pairedEtaReflectionEvenFrameAtomNormSq
            (fun k : Fin M ↦ pairedEtaGeometricHyperbolicCutoff q n k)
            T a *
          pairedEtaReflectionEvenFrameAtomNormSq
            (fun k : Fin M ↦ pairedEtaGeometricHyperbolicCutoff q n k)
            T b -
        (star (pairedEtaReflectionEvenFrameVector
            (fun k : Fin M ↦ pairedEtaGeometricHyperbolicCutoff q n k)
            T b) ⬝ᵥ
          pairedEtaReflectionEvenFrameVector
            (fun k : Fin M ↦ pairedEtaGeometricHyperbolicCutoff q n k)
            T a).re ^ 2)

/-- Every literal ordered pair reserve term is nonnegative. -/
theorem pairedEtaGeometricReflectionEvenFramePairReserveTerm_nonneg
    (q : ℕ) (T : ℝ) (n M : ℕ)
    (a b : PairedEtaReflectionEvenFrameIndex T) :
    0 ≤ pairedEtaGeometricReflectionEvenFramePairReserveTerm
      q T n M a b := by
  exact pairedEtaReflectionEvenFrameDecorrelationPairTerm_nonneg
    (fun k : Fin M ↦ pairedEtaGeometricHyperbolicCutoff q n k) T a b

/-- A diagonal ordered pair contributes exactly zero reserve. -/
theorem pairedEtaGeometricReflectionEvenFramePairReserveTerm_self
    (q : ℕ) (T : ℝ) (n M : ℕ)
    (a : PairedEtaReflectionEvenFrameIndex T) :
    pairedEtaGeometricReflectionEvenFramePairReserveTerm
      q T n M a a = 0 := by
  unfold pairedEtaGeometricReflectionEvenFramePairReserveTerm
  rw [pairedEtaReflectionEvenFrameCorrelation_self_re]
  ring

/-- The previously named upper--upper reserve is exactly the corresponding
general colour-resolved pair term. -/
theorem pairedEtaGeometricUpperPairWeightedDecorrelationReserve_eq_framePairReserveTerm
    (q : ℕ) {T : ℝ}
    (zeta rho : ↥(spectralUpperZetaZeroWindow T))
    (n M : ℕ) :
    pairedEtaGeometricUpperPairWeightedDecorrelationReserve
        q zeta rho n M =
      pairedEtaGeometricReflectionEvenFramePairReserveTerm
        q T n M (Sum.inr rho) (Sum.inr zeta) := by
  rfl

/-- Erasing diagonal pairs does not change the complete reserve, so it can be
written as a full ordered double sum before splitting the two atom colours. -/
theorem pairedEtaGeometricReflectionEvenFrameDecorrelationReserve_eq_sum_pairReserveTerm
    (q : ℕ) (T : ℝ) (n M : ℕ) :
    pairedEtaReflectionEvenFrameDecorrelationReserve
        (fun k : Fin M ↦ pairedEtaGeometricHyperbolicCutoff q n k) T =
      ∑ a : PairedEtaReflectionEvenFrameIndex T,
        ∑ b : PairedEtaReflectionEvenFrameIndex T,
          pairedEtaGeometricReflectionEvenFramePairReserveTerm
            q T n M a b := by
  unfold pairedEtaReflectionEvenFrameDecorrelationReserve
  change
    (∑ a : PairedEtaReflectionEvenFrameIndex T,
      ∑ b ∈ (Finset.univ :
          Finset (PairedEtaReflectionEvenFrameIndex T)).erase a,
        pairedEtaGeometricReflectionEvenFramePairReserveTerm
          q T n M a b) = _
  apply Finset.sum_congr rfl
  intro a _ha
  let f : PairedEtaReflectionEvenFrameIndex T → ℝ := fun b ↦
    pairedEtaGeometricReflectionEvenFramePairReserveTerm q T n M a b
  have hfa : f a = 0 :=
    pairedEtaGeometricReflectionEvenFramePairReserveTerm_self q T n M a
  calc
    ∑ b ∈ (Finset.univ :
        Finset (PairedEtaReflectionEvenFrameIndex T)).erase a,
        pairedEtaGeometricReflectionEvenFramePairReserveTerm q T n M a b =
      f a + ∑ b ∈ (Finset.univ :
          Finset (PairedEtaReflectionEvenFrameIndex T)).erase a, f b := by
        rw [hfa, zero_add]
    _ = ∑ b, f b :=
      Finset.add_sum_erase Finset.univ f (Finset.mem_univ a)
    _ = ∑ b, pairedEtaGeometricReflectionEvenFramePairReserveTerm
        q T n M a b := rfl

/-- Critical--critical colour sector of the complete geometric frame reserve. -/
def pairedEtaGeometricCriticalCriticalWindowWeightedDecorrelationReserve
    (q : ℕ) (T : ℝ) (n M : ℕ) : ℝ :=
  ∑ rho : ↥(spectralCriticalZetaZeroWindow T),
    ∑ zeta : ↥(spectralCriticalZetaZeroWindow T),
      pairedEtaGeometricReflectionEvenFramePairReserveTerm
        q T n M (Sum.inl rho) (Sum.inl zeta)

/-- Oriented critical--upper colour sector of the complete geometric frame
reserve. -/
def pairedEtaGeometricCriticalUpperWindowWeightedDecorrelationReserve
    (q : ℕ) (T : ℝ) (n M : ℕ) : ℝ :=
  ∑ rho : ↥(spectralCriticalZetaZeroWindow T),
    ∑ zeta : ↥(spectralUpperZetaZeroWindow T),
      pairedEtaGeometricReflectionEvenFramePairReserveTerm
        q T n M (Sum.inl rho) (Sum.inr zeta)

/-- Oriented upper--critical colour sector of the complete geometric frame
reserve. -/
def pairedEtaGeometricUpperCriticalWindowWeightedDecorrelationReserve
    (q : ℕ) (T : ℝ) (n M : ℕ) : ℝ :=
  ∑ rho : ↥(spectralUpperZetaZeroWindow T),
    ∑ zeta : ↥(spectralCriticalZetaZeroWindow T),
      pairedEtaGeometricReflectionEvenFramePairReserveTerm
        q T n M (Sum.inr rho) (Sum.inl zeta)

/-- Upper--upper colour sector with its harmless zero diagonal retained. -/
def pairedEtaGeometricUpperUpperWindowWeightedDecorrelationReserve
    (q : ℕ) (T : ℝ) (n M : ℕ) : ℝ :=
  ∑ rho : ↥(spectralUpperZetaZeroWindow T),
    ∑ zeta : ↥(spectralUpperZetaZeroWindow T),
      pairedEtaGeometricReflectionEvenFramePairReserveTerm
        q T n M (Sum.inr rho) (Sum.inr zeta)

/-- Exact four-colour decomposition of the complete reflection-even
decorrelation reserve. -/
theorem pairedEtaGeometricReflectionEvenFrameDecorrelationReserve_eq_colourSectors
    (q : ℕ) (T : ℝ) (n M : ℕ) :
    pairedEtaReflectionEvenFrameDecorrelationReserve
        (fun k : Fin M ↦ pairedEtaGeometricHyperbolicCutoff q n k) T =
      pairedEtaGeometricCriticalCriticalWindowWeightedDecorrelationReserve
          q T n M +
        pairedEtaGeometricCriticalUpperWindowWeightedDecorrelationReserve
          q T n M +
        pairedEtaGeometricUpperCriticalWindowWeightedDecorrelationReserve
          q T n M +
        pairedEtaGeometricUpperUpperWindowWeightedDecorrelationReserve
          q T n M := by
  rw [pairedEtaGeometricReflectionEvenFrameDecorrelationReserve_eq_sum_pairReserveTerm]
  unfold pairedEtaGeometricCriticalCriticalWindowWeightedDecorrelationReserve
    pairedEtaGeometricCriticalUpperWindowWeightedDecorrelationReserve
    pairedEtaGeometricUpperCriticalWindowWeightedDecorrelationReserve
    pairedEtaGeometricUpperUpperWindowWeightedDecorrelationReserve
  simp only [Fintype.sum_sum_type, Finset.sum_add_distrib]
  ring

/-- The critical--critical reserve sector is nonnegative. -/
theorem pairedEtaGeometricCriticalCriticalWindowWeightedDecorrelationReserve_nonneg
    (q : ℕ) (T : ℝ) (n M : ℕ) :
    0 ≤ pairedEtaGeometricCriticalCriticalWindowWeightedDecorrelationReserve
      q T n M := by
  unfold pairedEtaGeometricCriticalCriticalWindowWeightedDecorrelationReserve
  exact Finset.sum_nonneg fun rho _hrho ↦
    Finset.sum_nonneg fun zeta _hzeta ↦
      pairedEtaGeometricReflectionEvenFramePairReserveTerm_nonneg
        q T n M (Sum.inl rho) (Sum.inl zeta)

/-- The critical--upper reserve sector is nonnegative. -/
theorem pairedEtaGeometricCriticalUpperWindowWeightedDecorrelationReserve_nonneg
    (q : ℕ) (T : ℝ) (n M : ℕ) :
    0 ≤ pairedEtaGeometricCriticalUpperWindowWeightedDecorrelationReserve
      q T n M := by
  unfold pairedEtaGeometricCriticalUpperWindowWeightedDecorrelationReserve
  exact Finset.sum_nonneg fun rho _hrho ↦
    Finset.sum_nonneg fun zeta _hzeta ↦
      pairedEtaGeometricReflectionEvenFramePairReserveTerm_nonneg
        q T n M (Sum.inl rho) (Sum.inr zeta)

/-- The upper--critical reserve sector is nonnegative. -/
theorem pairedEtaGeometricUpperCriticalWindowWeightedDecorrelationReserve_nonneg
    (q : ℕ) (T : ℝ) (n M : ℕ) :
    0 ≤ pairedEtaGeometricUpperCriticalWindowWeightedDecorrelationReserve
      q T n M := by
  unfold pairedEtaGeometricUpperCriticalWindowWeightedDecorrelationReserve
  exact Finset.sum_nonneg fun rho _hrho ↦
    Finset.sum_nonneg fun zeta _hzeta ↦
      pairedEtaGeometricReflectionEvenFramePairReserveTerm_nonneg
        q T n M (Sum.inr rho) (Sum.inl zeta)

/-- The upper--upper reserve sector is nonnegative. -/
theorem pairedEtaGeometricUpperUpperWindowWeightedDecorrelationReserve_nonneg
    (q : ℕ) (T : ℝ) (n M : ℕ) :
    0 ≤ pairedEtaGeometricUpperUpperWindowWeightedDecorrelationReserve
      q T n M := by
  unfold pairedEtaGeometricUpperUpperWindowWeightedDecorrelationReserve
  exact Finset.sum_nonneg fun rho _hrho ↦
    Finset.sum_nonneg fun zeta _hzeta ↦
      pairedEtaGeometricReflectionEvenFramePairReserveTerm_nonneg
        q T n M (Sum.inr rho) (Sum.inr zeta)

/-- Removing the zero diagonal identifies the upper colour sector with the
ordered-distinct reserve sum bounded in the preceding module. -/
theorem pairedEtaGeometricUpperUpperWindowWeightedDecorrelationReserve_eq_distinct
    (q : ℕ) (T : ℝ) (n M : ℕ) :
    pairedEtaGeometricUpperUpperWindowWeightedDecorrelationReserve q T n M =
      pairedEtaGeometricUpperWindowWeightedDecorrelationReserve q T n M := by
  unfold pairedEtaGeometricUpperUpperWindowWeightedDecorrelationReserve
    pairedEtaGeometricUpperWindowWeightedDecorrelationReserve
  apply Finset.sum_congr rfl
  intro rho _hrho
  let f : ↥(spectralUpperZetaZeroWindow T) → ℝ := fun zeta ↦
    pairedEtaGeometricReflectionEvenFramePairReserveTerm
      q T n M (Sum.inr rho) (Sum.inr zeta)
  have hfrho : f rho = 0 :=
    pairedEtaGeometricReflectionEvenFramePairReserveTerm_self
      q T n M (Sum.inr rho)
  calc
    ∑ zeta : ↥(spectralUpperZetaZeroWindow T),
        pairedEtaGeometricReflectionEvenFramePairReserveTerm
          q T n M (Sum.inr rho) (Sum.inr zeta) =
      f rho + ∑ zeta ∈ (Finset.univ :
          Finset ↥(spectralUpperZetaZeroWindow T)).erase rho, f zeta :=
        (Finset.add_sum_erase Finset.univ f (Finset.mem_univ rho)).symm
    _ = ∑ zeta ∈ (Finset.univ :
          Finset ↥(spectralUpperZetaZeroWindow T)).erase rho, f zeta := by
      rw [hfrho, zero_add]
    _ = ∑ zeta ∈ (Finset.univ :
        Finset ↥(spectralUpperZetaZeroWindow T)).erase rho,
          pairedEtaGeometricUpperPairWeightedDecorrelationReserve
            q zeta rho n M := by
      apply Finset.sum_congr rfl
      intro zeta _hzeta
      exact
        (pairedEtaGeometricUpperPairWeightedDecorrelationReserve_eq_framePairReserveTerm
          q zeta rho n M).symm

/-- The complete colour-resolved reserve dominates its actual upper--upper
ordered-distinct sector. -/
theorem pairedEtaGeometricUpperWindowWeightedDecorrelationReserve_le_full
    (q : ℕ) (T : ℝ) (n M : ℕ) :
    pairedEtaGeometricUpperWindowWeightedDecorrelationReserve q T n M ≤
      pairedEtaReflectionEvenFrameDecorrelationReserve
        (fun k : Fin M ↦ pairedEtaGeometricHyperbolicCutoff q n k) T := by
  rw [pairedEtaGeometricReflectionEvenFrameDecorrelationReserve_eq_colourSectors,
    ← pairedEtaGeometricUpperUpperWindowWeightedDecorrelationReserve_eq_distinct]
  have hcriticalCritical :=
    pairedEtaGeometricCriticalCriticalWindowWeightedDecorrelationReserve_nonneg
      q T n M
  have hcriticalUpper :=
    pairedEtaGeometricCriticalUpperWindowWeightedDecorrelationReserve_nonneg
      q T n M
  have hupperCritical :=
    pairedEtaGeometricUpperCriticalWindowWeightedDecorrelationReserve_nonneg
      q T n M
  linarith

/-- Simultaneously for late geometric blocks, the explicit upper-sector
coercivity-minus-envelope sum is a lower bound for the complete certificate
reserve. -/
theorem eventually_pairedEtaGeometricUpperWindowWeightedReserveGapLower_le_fullDecorrelationReserve
    {q : ℕ} (hqOdd : Odd q) (hq : 1 < q) (T : ℝ)
    {M : ℕ} (hM : 1 < M) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop,
      pairedEtaGeometricUpperWindowWeightedReserveGapLower q T n M ε ≤
        pairedEtaReflectionEvenFrameDecorrelationReserve
          (fun k : Fin M ↦ pairedEtaGeometricHyperbolicCutoff q n k) T := by
  have hupper :=
    eventually_pairedEtaGeometricUpperWindowWeightedReserveGapLower_le_decorrelationReserve
      hqOdd hq T hM hε
  filter_upwards [hupper] with n hn
  exact hn.trans
    (pairedEtaGeometricUpperWindowWeightedDecorrelationReserve_le_full
      q T n M)

/-- Nonnegative form of the explicit upper-sector reserve lower bound. -/
def pairedEtaGeometricUpperWindowNonnegativeReserveGapLower
    (q : ℕ) (T : ℝ) (n M : ℕ) (ε : ℝ) : ℝ :=
  max 0 (pairedEtaGeometricUpperWindowWeightedReserveGapLower
    q T n M ε)

/-- The nonnegative upper-sector lower bound remains below the complete
certificate reserve on every sufficiently late geometric block. -/
theorem eventually_pairedEtaGeometricUpperWindowNonnegativeReserveGapLower_le_fullDecorrelationReserve
    {q : ℕ} (hqOdd : Odd q) (hq : 1 < q) (T : ℝ)
    {M : ℕ} (hM : 1 < M) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop,
      pairedEtaGeometricUpperWindowNonnegativeReserveGapLower
          q T n M ε ≤
        pairedEtaReflectionEvenFrameDecorrelationReserve
          (fun k : Fin M ↦ pairedEtaGeometricHyperbolicCutoff q n k) T := by
  have hlower :=
    eventually_pairedEtaGeometricUpperWindowWeightedReserveGapLower_le_fullDecorrelationReserve
      hqOdd hq T hM hε
  filter_upwards [hlower] with n hn
  unfold pairedEtaGeometricUpperWindowNonnegativeReserveGapLower
  exact max_le
    (pairedEtaReflectionEvenFrameDecorrelationReserve_nonneg
      (fun k : Fin M ↦ pairedEtaGeometricHyperbolicCutoff q n k) T)
    hn

end

end RiemannGaussian
