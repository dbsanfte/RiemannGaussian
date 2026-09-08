import RiemannGaussian.EtaInverseProductShellCollapse

/-!
# Sparse signed fibres from an outer-divisibility cut

Restricting the outer inverse divisor to multiples of `q` leaves just the
product coefficient at `q`. Its complete moving complement has coefficients
at products one and `q`, with opposite signs. The local-gap weighted
coefficient energy is therefore exactly `q+3` for `q>1`, independently of
the larger product cutoff. The literal moment atoms and their full mixed
interaction remain available; sparsity alone does not bound the current.
-/

open Complex
open scoped Classical ComplexConjugate ArithmeticFunction.Moebius

namespace RiemannGaussian

noncomputable section

/-- Every selected inverse region and its full complement retain the
complete signed coefficient at each product, before any coefficient norm. -/
theorem pairedEtaInverseRegionCoefficient_complement_add
    {S H : Finset (ℕ × ℕ)} (hS : S ⊆ H) (n : ℕ) :
    pairedEtaInverseRegionCoefficient (H \ S) n + pairedEtaInverseRegionCoefficient S n =
      pairedEtaInverseRegionCoefficient H n := by
  unfold pairedEtaInverseRegionCoefficient
  have heq : (H \ S).filter (fun p ↦ p.1 * p.2 = n) =
      H.filter (fun p ↦ p.1 * p.2 = n) \ S.filter (fun p ↦ p.1 * p.2 = n) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_sdiff]
    tauto
  rw [heq]
  exact Finset.sum_sdiff (Finset.filter_subset_filter _ hS)

/-- Outside product one, a selected inverse fibre and its full moving
complement have exactly opposite signed coefficients. -/
theorem pairedEtaInverseRegionCoefficient_complement_eq_neg
    {T n : ℕ} {S : Finset (ℕ × ℕ)} (hS : S ⊆ pairedEtaInverseHyperbolicRegion T)
    (hn : n ∈ Finset.Icc 1 T) (hn1 : n ≠ 1) :
    pairedEtaInverseRegionCoefficient (pairedEtaInverseHyperbolicRegion T \ S) n =
      -pairedEtaInverseRegionCoefficient S n := by
  have h := pairedEtaInverseRegionCoefficient_complement_add hS n
  rw [pairedEtaInverseRegionCoefficient_full_product hn, if_neg hn1] at h
  exact eq_neg_of_add_eq_zero_left h

/-- The literal inverse region cut by divisibility of its outer divisor. -/
def pairedEtaInverseOuterDivisible (T q : ℕ) : Finset (ℕ × ℕ) :=
  (pairedEtaInverseHyperbolicRegion T).filter (fun p ↦ q ∣ p.1)

/-- The outer-divisibility selection stays inside its original product region. -/
theorem pairedEtaInverseOuterDivisible_subset (T q : ℕ) :
    pairedEtaInverseOuterDivisible T q ⊆ pairedEtaInverseHyperbolicRegion T :=
  Finset.filter_subset _ _

private theorem full_fibre_sum {T : ℕ} (hT : 1 ≤ T) (f : ℕ → ℂ) :
    (∑ p ∈ pairedEtaInverseHyperbolicRegion T, (μ p.2 : ℂ) * f (p.1 * p.2)) = f 1 := by
  rw [← sum_pairedEtaInverseRegionCoefficient_mul (Finset.Subset.refl _) f]
  calc
    _ = ∑ n ∈ Finset.Icc 1 T, if n = 1 then f n else 0 := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [pairedEtaInverseRegionCoefficient_full_product hn]
      split <;> simp
    _ = _ := by simp [Finset.sum_ite_eq', hT]

/-- Scaling only the outer factor is an exact bijection of the selected
inverse region with its divided hyperbola. Every inner Möbius sign survives. -/
theorem sum_pairedEtaInverseOuterDivisible_mul {q : ℕ} (hq : 1 ≤ q)
    (T : ℕ) (f : ℕ → ℂ) :
    (∑ p ∈ pairedEtaInverseOuterDivisible T q, (μ p.2 : ℂ) * f (p.1 * p.2)) =
      ∑ p ∈ pairedEtaInverseHyperbolicRegion (T / q), (μ p.2 : ℂ) * f (q * (p.1 * p.2)) := by
  symm
  apply Finset.sum_bij (fun p _ ↦ (q * p.1, p.2))
  · intro p hp
    obtain ⟨hd, he, hprod⟩ := mem_pairedEtaInverseHyperbolicRegion.mp hp
    apply Finset.mem_filter.mpr
    refine ⟨mem_pairedEtaInverseHyperbolicRegion.mpr ⟨by nlinarith, he, ?_⟩, dvd_mul_right q p.1⟩
    have h := (Nat.le_div_iff_mul_le hq).mp hprod
    simpa only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h
  · intro p hp p' hp' heq
    have hfirst := congrArg Prod.fst heq
    have hsecond := congrArg Prod.snd heq
    exact Prod.ext (Nat.eq_of_mul_eq_mul_left hq hfirst) hsecond
  · intro p hp
    obtain ⟨hpH, hpq⟩ := Finset.mem_filter.mp hp
    obtain ⟨d, hd⟩ := hpq
    obtain ⟨hp1, hp2, hprod⟩ := mem_pairedEtaInverseHyperbolicRegion.mp hpH
    have hdp : 1 ≤ d := by
      by_contra h
      have hd0 : d = 0 := by omega
      simp only [hd0, mul_zero] at hd
      omega
    refine ⟨(d, p.2), mem_pairedEtaInverseHyperbolicRegion.mpr ⟨hdp, hp2, ?_⟩, Prod.ext hd.symm rfl⟩
    apply (Nat.le_div_iff_mul_le hq).mpr
    simpa only [hd, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hprod
  · intro p hp
    simp only [Nat.mul_assoc]

/-- The selected outer-divisibility family leaves exactly its product-q
atom against any complex product test, with no area or divisor-count cost. -/
theorem sum_pairedEtaInverseOuterDivisible_mul_eq {T q : ℕ}
    (hq : 1 ≤ q) (hqT : q ≤ T) (f : ℕ → ℂ) :
    (∑ p ∈ pairedEtaInverseOuterDivisible T q, (μ p.2 : ℂ) * f (p.1 * p.2)) = f q := by
  rw [sum_pairedEtaInverseOuterDivisible_mul hq T f]
  have hdiv : 1 ≤ T / q := (Nat.le_div_iff_mul_le hq).mpr (by simpa using hqT)
  simpa only [mul_one] using full_fibre_sum hdiv (fun n ↦ f (q * n))

/-- The full selected fibre coefficient is one at product q and zero
elsewhere, including products outside the original physical range. -/
theorem pairedEtaInverseRegionCoefficient_outerDivisible {T q : ℕ}
    (hq : 1 ≤ q) (hqT : q ≤ T) (n : ℕ) :
    pairedEtaInverseRegionCoefficient (pairedEtaInverseOuterDivisible T q) n =
      if n = q then 1 else 0 := by
  have h := sum_pairedEtaInverseOuterDivisible_mul_eq hq hqT (fun m ↦ if m = n then 1 else 0)
  have heq : (pairedEtaInverseRegionCoefficient (pairedEtaInverseOuterDivisible T q) n : ℂ) =
      ∑ p ∈ pairedEtaInverseOuterDivisible T q, (μ p.2 : ℂ) * (if p.1 * p.2 = n then 1 else 0) := by
    simp only [pairedEtaInverseRegionCoefficient, Int.cast_sum, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p hp
    split <;> simp
  rw [← heq] at h
  have hh : (pairedEtaInverseRegionCoefficient (pairedEtaInverseOuterDivisible T q) n : ℂ) =
      ((if n = q then 1 else 0 : ℤ) : ℂ) := by
    simpa only [Int.cast_ite, Int.cast_one, Int.cast_zero, eq_comm] using h
  exact_mod_cast hh

/-- Every remaining cell after the outer-divisibility cut, with the full
original hyperbolic range retained. -/
def pairedEtaInverseOuterNondivisible (T q : ℕ) : Finset (ℕ × ℕ) :=
  pairedEtaInverseHyperbolicRegion T \ pairedEtaInverseOuterDivisible T q

/-- The complementary region has exactly two signed product coefficients:
the original product-one coefficient minus the selected product-q coefficient. -/
theorem pairedEtaInverseRegionCoefficient_outerNondivisible {T q n : ℕ}
    (hq : 1 ≤ q) (hqT : q ≤ T) (hn : n ∈ Finset.Icc 1 T) :
    pairedEtaInverseRegionCoefficient (pairedEtaInverseOuterNondivisible T q) n =
      (if n = 1 then 1 else 0) - (if n = q then 1 else 0) := by
  have h := pairedEtaInverseRegionCoefficient_complement_add (pairedEtaInverseOuterDivisible_subset T q) n
  rw [pairedEtaInverseRegionCoefficient_full_product hn,
    pairedEtaInverseRegionCoefficient_outerDivisible hq hqT n] at h
  exact (eq_sub_iff_add_eq).mpr h

/-- The entire weighted fibre energy of the complementary outer cut is
exactly q+3. In particular it is independent of the larger product cutoff;
the generic area bound is unnecessary for this actual signed family. -/
theorem pairedEtaInverseOuterNondivisible_weighted_coefficient_energy {T q : ℕ}
    (hq : 2 ≤ q) (hqT : q ≤ T) :
    (∑ n ∈ Finset.Icc 1 T, (n + 1 : ℝ) *
      (pairedEtaInverseRegionCoefficient (pairedEtaInverseOuterNondivisible T q) n : ℝ) ^ 2) = q + 3 := by
  have hq1 : 1 ≤ q := by omega
  have hT1 : 1 ≤ T := hq1.trans hqT
  calc
    _ = ∑ n ∈ Finset.Icc 1 T,
        ((if n = 1 then (2 : ℝ) else 0) + (if n = q then (q + 1 : ℝ) else 0)) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [pairedEtaInverseRegionCoefficient_outerNondivisible hq1 hqT hn]
      by_cases hn1 : n = 1
      · subst n
        norm_num [show (1 : ℕ) ≠ q by omega]
      · by_cases hnq : n = q
        · subst n
          simp [hn1]
        · simp [hn1, hnq]
    _ = _ := by
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_ite_eq', Finset.mem_Icc, le_refl, hT1, hq1, hqT, and_self, ite_true]
      ring

/-- The outer-divisibility carrier is its one surviving completed atom,
at the original divided physical cutoff and translated center. -/
theorem pairedEtaCompletedMomentInverseRegion_outerDivisible_eq_atom
    (rho : NontrivialZetaZero) (k : ℕ) (a : ℝ) (M : ℕ) {T q : ℕ}
    (hq : 1 ≤ q) (hqT : q ≤ T) :
    pairedEtaCompletedMomentInverseRegion rho k a M (pairedEtaInverseOuterDivisible T q) =
      pairedEtaMomentDivisorAtom rho k a M q := by
  calc
    _ = ∑ p ∈ pairedEtaInverseOuterDivisible T q,
        (μ p.2 : ℂ) * pairedEtaMomentDivisorAtom rho k a M (p.1 * p.2) := by
      apply Finset.sum_congr rfl
      intro p hp
      obtain ⟨hd, he, _⟩ := mem_pairedEtaInverseHyperbolicRegion.mp ((pairedEtaInverseOuterDivisible_subset T q) hp)
      exact pairedEtaMomentInverseCell_eq_atom rho k a M hd he
    _ = _ := sum_pairedEtaInverseOuterDivisible_mul_eq hq hqT (pairedEtaMomentDivisorAtom rho k a M)

/-- The complementary carrier is the exact signed difference of its
two surviving atoms, with no norm or physical endpoint discarded. -/
theorem pairedEtaCompletedMomentInverseRegion_outerNondivisible_eq_atoms
    (rho : NontrivialZetaZero) (k : ℕ) (a : ℝ) (M : ℕ) {T q : ℕ}
    (hq : 1 ≤ q) (hqT : q ≤ T) :
    pairedEtaCompletedMomentInverseRegion rho k a M (pairedEtaInverseOuterNondivisible T q) =
      pairedEtaMomentDivisorAtom rho k a M 1 - pairedEtaMomentDivisorAtom rho k a M q := by
  have h : pairedEtaCompletedMomentInverseRegion rho k a M (pairedEtaInverseOuterNondivisible T q) +
      pairedEtaCompletedMomentInverseRegion rho k a M (pairedEtaInverseOuterDivisible T q) =
      pairedEtaCompletedMomentInverseRegion rho k a M (pairedEtaInverseHyperbolicRegion T) := by
    unfold pairedEtaCompletedMomentInverseRegion pairedEtaInverseOuterNondivisible
    exact Finset.sum_sdiff (pairedEtaInverseOuterDivisible_subset T q)
  rw [pairedEtaCompletedMomentInverseRegion_outerDivisible_eq_atom rho k a M hq hqT,
    pairedEtaCompletedMomentInverseRegion_productCutoff_eq_prefix rho k a M (hq.trans hqT)] at h
  apply (eq_sub_iff_add_eq).mpr
  simpa only [pairedEtaMomentDivisorAtom, Nat.cast_one, Complex.one_cpow, one_mul,
    Real.log_one, sub_zero, Nat.div_one] using h

/-- Both reflected channels retain the complete two-atom quadratic of
the divisibility cut. The small coefficient energy does not remove its
product-one diagonal or any of the two mixed interactions. -/
theorem pairedEtaCurrentFullInverseEnergy_eq_divisibility_split
    (rho : NontrivialZetaZero) (N : ℕ) {q : ℕ} (hq : 1 ≤ q) (hqM : q ≤ 2 * (N + 2)) :
    let A := fun z ↦ pairedEtaMomentDivisorAtom z 0 (pairedEtaLogTailCutoff (N + 2)) (2 * (N + 2)) 1
    let B := fun z ↦ pairedEtaMomentDivisorAtom z 0 (pairedEtaLogTailCutoff (N + 2)) (2 * (N + 2)) q
    let rp := NontrivialZetaZero.conjugatePartner rho
    pairedEtaCurrentFullInverseEnergy rho N = 2 * pairedEtaLogTailShiftIncrement (N + 1) *
      ((pairedEtaCurrentZeroEnergyCoefficient rp).re *
          (‖A rp - B rp‖ ^ 2 + ‖B rp‖ ^ 2 + 2 * ((A rp - B rp) * starRingEnd ℂ (B rp)).re) -
        (pairedEtaCurrentZeroEnergyCoefficient rho).re *
          (‖A rho - B rho‖ ^ 2 + ‖B rho‖ ^ 2 + 2 * ((A rho - B rho) * starRingEnd ℂ (B rho)).re)) := by
  have hS := pairedEtaInverseOuterDivisible_subset (2 * (N + 2)) q
  have h := pairedEtaCurrentFullInverseEnergy_eq_split rho N hS hS
  have hc (z : NontrivialZetaZero) := pairedEtaCompletedMomentInverseRegion_outerNondivisible_eq_atoms z 0
    (pairedEtaLogTailCutoff (N + 2)) (2 * (N + 2)) hq hqM
  simp only [pairedEtaInverseOuterNondivisible] at hc
  simpa only [pairedEtaCompletedMomentInverseRegion_outerDivisible_eq_atom _ _ _ _ hq hqM, hc] using h

end

end RiemannGaussian
