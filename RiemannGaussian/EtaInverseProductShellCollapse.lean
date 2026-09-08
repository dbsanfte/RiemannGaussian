import RiemannGaussian.EtaLeadingFluxSignedInversePartialSum

/-!
# Complete product cuts preserve the entire inverse energy

An inverse cell at `(d,e)` is the inner Möbius sign `mu(e)` times
the unchanged completed moment atom at the product `d*e`. Every complete
positive product fiber therefore has coefficient `sum_(e|n) mu(e)`, the
identity for Dirichlet convolution. Any positive complete product cutoff
already reconstructs the whole physical prefix, at its original center
and cutoff. Its moving high-product complement is exactly zero.

The same identity holds with arbitrary complex product weights: only their
value at one survives. Thus the suggested low-product region is not a
smaller arithmetic carrier. Its reflected energy and signed partial sum
retain the entire known off-critical lower power. This audit supplies no
independent upper bound and does not rule out cuts through product fibers.
-/

open Complex Filter Topology
open scoped Classical ComplexConjugate ArithmeticFunction.Moebius

namespace RiemannGaussian

noncomputable section

/-- A product fiber wholly inside the inverse hyperbola contains every
positive factorization of that product. -/
theorem pairedEtaInverseHyperbolicRegion_productFiber {T n : ℕ}
    (hn : n ∈ Finset.Icc 1 T) :
    (pairedEtaInverseHyperbolicRegion T).filter (fun p ↦ p.1 * p.2 = n) =
      n.divisorsAntidiagonal := by
  ext p
  constructor
  · intro hp
    exact Nat.mem_divisorsAntidiagonal.mpr
      ⟨(Finset.mem_filter.mp hp).2, by have := (Finset.mem_Icc.mp hn).1; omega⟩
  · intro hp
    obtain ⟨hd, he⟩ := Nat.ne_zero_of_mem_divisorsAntidiagonal hp
    have hprod := (Nat.mem_divisorsAntidiagonal.mp hp).1
    exact Finset.mem_filter.mpr
      ⟨mem_pairedEtaInverseHyperbolicRegion.mpr
        ⟨Nat.one_le_iff_ne_zero.mpr hd, Nat.one_le_iff_ne_zero.mpr he,
          hprod.le.trans (Finset.mem_Icc.mp hn).2⟩, hprod⟩

/-- The complete inverse coefficient is exactly the Dirichlet identity:
one at product one, zero at every other included positive product. -/
theorem pairedEtaInverseRegionCoefficient_full_product {T n : ℕ}
    (hn : n ∈ Finset.Icc 1 T) :
    pairedEtaInverseRegionCoefficient (pairedEtaInverseHyperbolicRegion T) n =
      if n = 1 then 1 else 0 := by
  rw [pairedEtaInverseRegionCoefficient, pairedEtaInverseHyperbolicRegion_productFiber hn,
    Nat.sum_divisorsAntidiagonal' (fun _ e ↦ (μ e : ℤ)),
    ← ArithmeticFunction.coe_zeta_mul_apply, ArithmeticFunction.coe_zeta_mul_moebius,
    ArithmeticFunction.one_apply]

/-- Product-only weighting preserves the complete physical prefix,
multiplied by the weight at one. This is a complex identity before any
norm, and retains arbitrary moment orders and the actual translated center. -/
theorem pairedEtaCompletedMomentInverseRegion_productWeight_eq_prefix
    (rho : NontrivialZetaZero) (k : ℕ) (a : ℝ) (M : ℕ)
    {T : ℕ} (hT : 1 ≤ T) (w : ℕ → ℂ) :
    (∑ p ∈ pairedEtaInverseHyperbolicRegion T, w (p.1 * p.2) *
      ((p.1 : ℂ) ^ (-rho.1) * pairedEtaCompletedMomentMoebiusTerm rho k
        (a - Real.log p.1) (M / p.1) p.2)) =
      w 1 * ((pairedEtaXiCompletionFactor rho.1 * rho.1) *
        pairedEtaUnpairedCenteredMomentPrefix k rho.1 a M) := by
  calc
    _ = ∑ p ∈ pairedEtaInverseHyperbolicRegion T,
        (μ p.2 : ℂ) * (w (p.1 * p.2) * pairedEtaMomentDivisorAtom rho k a M (p.1 * p.2)) := by
      apply Finset.sum_congr rfl
      intro p hp
      obtain ⟨hd, he, _⟩ := mem_pairedEtaInverseHyperbolicRegion.mp hp
      rw [pairedEtaMomentInverseCell_eq_atom rho k a M hd he]
      ring
    _ = ∑ n ∈ Finset.Icc 1 T,
        (pairedEtaInverseRegionCoefficient (pairedEtaInverseHyperbolicRegion T) n : ℂ) *
          (w n * pairedEtaMomentDivisorAtom rho k a M n) :=
      (sum_pairedEtaInverseRegionCoefficient_mul (Finset.Subset.refl _)
        (fun n ↦ w n * pairedEtaMomentDivisorAtom rho k a M n)).symm
    _ = ∑ n ∈ Finset.Icc 1 T, if n = 1 then w n * pairedEtaMomentDivisorAtom rho k a M n else 0 := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [pairedEtaInverseRegionCoefficient_full_product hn]
      split <;> simp
    _ = w 1 * pairedEtaMomentDivisorAtom rho k a M 1 := by
      simp only [Finset.sum_ite_eq', Finset.mem_Icc, le_refl, hT, and_self, ite_true]
    _ = _ := by simp [pairedEtaMomentDivisorAtom]

/-- Even a short complete product cutoff reconstructs the entire
physical moment. The physical cutoff is still `M`, not the product cutoff. -/
theorem pairedEtaCompletedMomentInverseRegion_productCutoff_eq_prefix
    (rho : NontrivialZetaZero) (k : ℕ) (a : ℝ) (M : ℕ)
    {T : ℕ} (hT : 1 ≤ T) :
    pairedEtaCompletedMomentInverseRegion rho k a M (pairedEtaInverseHyperbolicRegion T) =
      (pairedEtaXiCompletionFactor rho.1 * rho.1) * pairedEtaUnpairedCenteredMomentPrefix k rho.1 a M := by
  simpa only [one_mul, pairedEtaCompletedMomentInverseRegion] using
    pairedEtaCompletedMomentInverseRegion_productWeight_eq_prefix rho k a M hT (fun _ ↦ 1)

/-- The proposed low-product region retains complete product fibers of
the original inverse, clipped only by their product. -/
def pairedEtaInverseLowProductRegion (M T : ℕ) : Finset (ℕ × ℕ) :=
  (pairedEtaInverseHyperbolicRegion M).filter (fun p ↦ p.1 * p.2 ≤ T)

/-- Below the physical cutoff, the low-product region is exactly a
complete smaller hyperbola. -/
theorem pairedEtaInverseLowProductRegion_eq {M T : ℕ} (hTM : T ≤ M) :
    pairedEtaInverseLowProductRegion M T = pairedEtaInverseHyperbolicRegion T := by
  ext p
  simp only [pairedEtaInverseLowProductRegion, Finset.mem_filter, mem_pairedEtaInverseHyperbolicRegion]
  constructor
  · rintro ⟨⟨hd, he, _⟩, hprod⟩
    exact ⟨hd, he, hprod⟩
  · rintro ⟨hd, he, hprod⟩
    exact ⟨⟨hd, he, hprod.trans hTM⟩, hprod⟩

/-- The selected low-product complex carrier is the full original
inverse exactly, for every positive admissible cutoff. -/
theorem pairedEtaCompletedMomentInverseRegion_lowProduct_eq_full
    (rho : NontrivialZetaZero) (k : ℕ) (a : ℝ) {M T : ℕ}
    (hT : 1 ≤ T) (hTM : T ≤ M) :
    pairedEtaCompletedMomentInverseRegion rho k a M (pairedEtaInverseLowProductRegion M T) =
      pairedEtaCompletedMomentInverseRegion rho k a M (pairedEtaInverseHyperbolicRegion M) := by
  rw [pairedEtaInverseLowProductRegion_eq hTM,
    pairedEtaCompletedMomentInverseRegion_productCutoff_eq_prefix rho k a M hT,
    pairedEtaCompletedMomentInverseRegion_full]

/-- The complete high-product complement is zero as a complex carrier.
Its norm and both ordered cross terms therefore vanish exactly; no
discarded-complement estimate is needed for this particular split. -/
theorem pairedEtaCompletedMomentInverseRegion_highProduct_eq_zero
    (rho : NontrivialZetaZero) (k : ℕ) (a : ℝ) {M T : ℕ}
    (hT : 1 ≤ T) (hTM : T ≤ M) :
    pairedEtaCompletedMomentInverseRegion rho k a M
      (pairedEtaInverseHyperbolicRegion M \ pairedEtaInverseLowProductRegion M T) = 0 := by
  have h := pairedEtaCompletedMomentInverseRegion_complement_add rho k a M
    (show pairedEtaInverseLowProductRegion M T ⊆ pairedEtaInverseHyperbolicRegion M from Finset.filter_subset _ _)
  rw [pairedEtaCompletedMomentInverseRegion_lowProduct_eq_full rho k a hT hTM] at h
  apply add_right_cancel (b := pairedEtaCompletedMomentInverseRegion rho k a M (pairedEtaInverseHyperbolicRegion M))
  simpa only [zero_add] using h

/-- The actual reflected energy restricted to the proposed low-product
region, with every completion coefficient and physical cutoff retained. -/
def pairedEtaCurrentLowProductInverseEnergy (rho : NontrivialZetaZero) (N T : ℕ) : ℝ :=
  let V := fun z ↦ pairedEtaCompletedMomentInverseRegion z 0
    (pairedEtaLogTailCutoff (N + 2)) (2 * (N + 2))
      (pairedEtaInverseLowProductRegion (2 * (N + 2)) T)
  2 * pairedEtaLogTailShiftIncrement (N + 1) *
    ((pairedEtaCurrentZeroEnergyCoefficient (NontrivialZetaZero.conjugatePartner rho)).re *
        ‖V (NontrivialZetaZero.conjugatePartner rho)‖ ^ 2 -
      (pairedEtaCurrentZeroEnergyCoefficient rho).re * ‖V rho‖ ^ 2)

/-- Taking the low-product cut in both reflected channels leaves their
full signed energy unchanged, before any bound on either channel. -/
theorem pairedEtaCurrentLowProductInverseEnergy_eq_full (rho : NontrivialZetaZero) (N : ℕ)
    {T : ℕ} (hT : 1 ≤ T) (hTM : T ≤ 2 * (N + 2)) :
    pairedEtaCurrentLowProductInverseEnergy rho N T = pairedEtaCurrentFullInverseEnergy rho N := by
  simp only [pairedEtaCurrentLowProductInverseEnergy, pairedEtaCurrentFullInverseEnergy,
    pairedEtaCompletedMomentInverseRegion_lowProduct_eq_full _ _ _ hT hTM]

/-- Every admissible moving low-product schedule retains the entire
signed inverse sum. Shrinking or growing its product cutoff gives no saving. -/
theorem pairedEtaCurrentLowProductInverseEnergy_signed_sum_eq_full
    (rho : NontrivialZetaZero) (T : ℕ → ℕ)
    (hT : ∀ N, 1 ≤ T N ∧ T N ≤ 2 * (N + 2)) (K : ℕ) :
    (∑ N ∈ Finset.range K, (2 * N + 1 : ℝ) * pairedEtaCurrentLowProductInverseEnergy rho N (T N)) =
      pairedEtaFullInverseEnergySignedPartialSum rho K := by
  unfold pairedEtaFullInverseEnergySignedPartialSum
  apply Finset.sum_congr rfl
  intro N _
  rw [pairedEtaCurrentLowProductInverseEnergy_eq_full rho N (hT N).1 (hT N).2]

/-- The suggested low-product part already carries the full off-critical
lower power for every positive moving schedule. Proving a relative upper
saving for that part is therefore still the whole arithmetic obstruction. -/
theorem pairedEtaCurrentLowProductInverseEnergy_signed_sum_power_lower_eventually
    (rho : NontrivialZetaZero) (hrho : rho.1.re ≠ 1 / 2) (T : ℕ → ℕ)
    (hT : ∀ N, 1 ≤ T N ∧ T N ≤ 2 * (N + 2)) : ∀ᶠ K : ℕ in atTop,
      (pairedEtaCurrentReturnGrowthLowerCoefficient rho / 2) *
        (K + 1 : ℝ) ^ pairedEtaCurrentHorizontalDisplacement rho ≤
          pairedEtaLeadingFluxSide rho *
            ∑ N ∈ Finset.range K, (2 * N + 1 : ℝ) * pairedEtaCurrentLowProductInverseEnergy rho N (T N) := by
  simpa only [pairedEtaCurrentLowProductInverseEnergy_signed_sum_eq_full rho T hT] using
    pairedEtaFullInverseEnergySignedPartialSum_power_lower_eventually rho hrho

end

end RiemannGaussian
