/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszTriplePeriod
import RiemannGaussian.ZetaRieszPositiveFiveWholeBudget
import RiemannGaussian.ZetaRieszPositiveFiveBoundary
import RiemannGaussian.ZetaRieszJointOwnerPayment

/-!
# Spending signed triple cancellation in the existing whole ledger

The literal triple population is disjoint from every previously paid
three/four/five-prime and owner population. Its signed period bound is
spent once, preserving the complementary sum and favorable observations.
-/

namespace RiemannGaussian.ZetaRieszJointTriplePayment
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszTriplePeriod ZetaRieszAllowancePrimeBoxes

/-- A five-prime supply cell has five prime factors counted with
multiplicity, even before its ordering and squarefree masks are used. -/
theorem supply_count {t h y : ℝ} {lo H : Fin 4 → ℝ} {n : ℕ}
    (hn : n ∈ ZetaRieszJointPrimeCells.supplyCell t h y lo H) :
    ArithmeticFunction.cardFactors n = 5 := by
  unfold ZetaRieszJointPrimeCells.supplyCell at hn
  split_ifs at hn with hphase
  · obtain ⟨a,ha,hn⟩ := Finset.mem_biUnion.mp hn
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hn
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp ha
    have hqs (i : Fin 4) : (q i).Prime :=
      (logPrimes_bounds ((Fintype.mem_piFinset.mp hq) i)).1
    have hps := (logPrimes_bounds hp).1
    have hnz : (∏ i, q i : ℕ) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr (fun i _ => (hqs i).ne_zero)
    rw [ArithmeticFunction.cardFactors_mul hnz hps.ne_zero,
      ArithmeticFunction.cardFactors_apply_prime hps]
    simp [Fin.prod_univ_four,ArithmeticFunction.cardFactors_mul,
      (hqs 0).ne_zero,(hqs 1).ne_zero,(hqs 2).ne_zero,(hqs 3).ne_zero,
      ArithmeticFunction.cardFactors_apply_prime (hqs 0),
      ArithmeticFunction.cardFactors_apply_prime (hqs 1),
      ArithmeticFunction.cardFactors_apply_prime (hqs 2),
      ArithmeticFunction.cardFactors_apply_prime (hqs 3)]
  · simp only [Finset.notMem_empty] at hn

/-- The new squarefree triple population cannot overlap any supply cell,
without adding an ordering or numerical-cover premise. -/
theorem disjoint_supply {v y : ℝ} (hv : 100 ≤ v) (hy : 54 ≤ |y|)
    (t h z : ℝ) (lo H : Fin 4 → ℝ) :
    Disjoint (population v y) (ZetaRieszJointPrimeCells.supplyCell t h z lo H) := by
  apply Finset.disjoint_left.mpr
  intro n hn hs
  have hd := population_data hv hy hn
  have hcard : n.primeFactors.card = n.primeFactorsList.length :=
    List.toFinset_card_of_nodup hd.1.nodup_primeFactorsList
  have hc := supply_count hs
  rw [ArithmeticFunction.cardFactors_apply,← hcard,hd.2.1] at hc
  omega

/-- Four-prime payments and the new triple payment have distinct labels. -/
theorem disjoint_adverse {v y : ℝ} (hv : 100 ≤ v) (hy : 54 ≤ |y|)
    (S : Finset ℕ) (L t h z a : ℝ) :
    Disjoint (population v y) (ZetaRieszFourBoundaryCover.adversePopulation S L t h z a) := by
  apply Finset.disjoint_left.mpr
  intro n hn hf
  have hc := (population_data hv hy hn).2.1
  have hf := (Finset.mem_filter.mp hf).2.2.1
  omega

/-- Full positive-five interior payments have no triple labels. -/
theorem disjoint_interior {v y : ℝ} (hv : 100 ≤ v) (hy : 54 ≤ |y|)
    (S : Finset ℕ) (L v' z δ : ℝ) (m : ℕ) :
    Disjoint (population v y)
      (ZetaRieszPositiveFiveSignedPayment.periodPopulation S L v' z m δ) := by
  apply Finset.disjoint_left.mpr
  intro n hn hf
  obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hf
  have hc := (population_data hv hy hn).2.1
  have hf := (Finset.mem_filter.mp hi).2.2.1
  omega

/-- The small-prime five-factor boundary is disjoint from the triples. -/
theorem disjoint_head {v y : ℝ} (hv : 100 ≤ v) (hy : 54 ≤ |y|)
    (S : Finset ℕ) (L v' z : ℝ) (m : ℕ) :
    Disjoint (population v y)
      (ZetaRieszPositiveFiveBoundary.periodPopulation S L v' z m) := by
  apply Finset.disjoint_left.mpr
  intro n hn hf
  obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hf
  have hc := (population_data hv hy hn).2.1
  have hf := (Finset.mem_filter.mp hi).2.2.1
  omega

/-- Every prime share of the new rectangle is below the paid owner band. -/
theorem disjoint_owner {v y : ℝ} (hv : 100 ≤ v) (hy : 54 ≤ |y|)
    (S A : Finset ℕ) :
    Disjoint (population v y) (ZetaRieszJointOwnerPayment.population S A) := by
  apply Finset.disjoint_left.mpr
  intro n hn hf
  obtain ⟨_,_,hn1,_,p,hp,_,_,hlo,_⟩ := Finset.mem_filter.mp hf
  have hc := (population_data hv hy hn).2.2.2.2.1 p hp
  have hnlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn1)
  nlinarith

/-- A signed payment retains the favorable lower observation. Only the
real part of the coupled sum is bounded; no sum of atom norms is needed. -/
theorem scaled_floor_after_signed_payment {S D : Finset ℕ} (f : ℕ → ℂ)
    {a d g whole : ℝ} (hD : D ⊆ S)
    (hcost : |a*(∑ n ∈ D, f n).re| ≤ d)
    (hpaid : a*(∑ n ∈ S, f n).re+g ≤ whole) :
    a*((∑ n ∈ S\D, f n).re+max (∑ n ∈ D, f n).re 0)+g-d ≤ whole := by
  have he := congrArg Complex.re (Finset.sum_sdiff hD (f := f))
  simp only [Complex.add_re] at he
  have he' := congrArg (fun t => a*t) he
  by_cases hq : 0 ≤ (∑ n ∈ D, f n).re
  · rw [max_eq_left hq]
    have hd := (abs_nonneg _).trans hcost
    nlinarith only [he',hpaid,hd]
  · rw [max_eq_right (le_of_not_ge hq)]
    have hc := (abs_le.mp hcost).1
    nlinarith only [he',hpaid,hc]

/-- The same exact signed debit preserves the favorable upper observation. -/
theorem scaled_ceiling_after_signed_payment {S D : Finset ℕ} (f : ℕ → ℂ)
    {a d g whole : ℝ} (hD : D ⊆ S)
    (hcost : |a*(∑ n ∈ D, f n).re| ≤ d)
    (hpaid : whole ≤ a*(∑ n ∈ S, f n).re-g) :
    whole ≤ a*((∑ n ∈ S\D, f n).re+min (∑ n ∈ D, f n).re 0)-g+d := by
  have he := congrArg Complex.re (Finset.sum_sdiff hD (f := f))
  simp only [Complex.add_re] at he
  have he' := congrArg (fun t => a*t) he
  by_cases hq : (∑ n ∈ D, f n).re ≤ 0
  · rw [min_eq_left hq]
    have hd := (abs_nonneg _).trans hcost
    nlinarith only [he',hpaid,hd]
  · rw [min_eq_right (le_of_not_ge hq)]
    have hc := (abs_le.mp hcost).2
    nlinarith only [he',hpaid,hc]

/-- The literal rectangle lies inside the unchanged core at every
sufficiently large dyadic order and every admissible complete period. -/
theorem eventually_subset_core {u : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54 ≤ |y|) :
    ∀ᶠ j : ℕ in atTop, ∀ v : ℝ,
      let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
      let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
      (39/20 : ℝ)*N ≤ v-Real.pi/|y| → v+Real.pi/|y| ≤ (203/100 : ℝ)*N →
      population v y ⊆ ZetaRieszParityPacket.coreBand u N K := by
  have hroom : u < Real.exp (-(137/200 : ℝ)) :=
    hU.trans_lt (ZetaRieszWideOwnerAudit.radius_lt_source.trans
      (Real.exp_lt_exp.mpr (by norm_num)))
  filter_upwards [ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
    (ZetaRieszLowerDegreeBounds.eventually_length_ge_exponent
      (show 0 < u by linarith) (by norm_num : (0 : ℝ) ≤ 137/200) hroom),
    ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
      (eventually_ge_atTop (1000 : ℕ)),eventually_ge_atTop (32 : ℕ)] with j hL hN hj
  intro v
  dsimp only
  intro hlo hhi
  have hNR : (1000 : ℝ) ≤ ZetaRieszPrimeCountFrequency.dyadicMomentOrder j := by exact_mod_cast hN
  have hπ : 0 ≤ Real.pi/|y| := by positivity
  apply population_subset_core j hj hu hU hy (by linarith) ?_ hlo hhi
  nlinarith only [hL,hNR]

/-- The actual coupled residual sum, including its old allocation, has
the proved signed cost. This is the payment used in the combined ledger. -/
theorem eventually_signed_population_bound {u : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) {m : ℕ} (hm : 0 < m)
    {y : ℝ} (hy : 54 ≤ |y|)
    (hsmall : Real.pi/(4*m*|y|) ≤ 1/100000)
    (hphase : |y| * (Real.pi/(4*m*|y|)) ≤ 1/10000) :
    ∀ᶠ j : ℕ in atTop, ∀ v : ℝ,
      let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
      let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
      Real.cos (y*v) = -1 →
      (39/20 : ℝ)*N ≤ v-Real.pi/|y| → v+Real.pi/|y| ≤ (203/100 : ℝ)*N →
      population v y ⊆ ZetaRieszParityPacket.coreBand u N K ∧
      ∃ V : ℝ, 0 < V ∧ V ≤ Real.exp (-v/2)*v^N/N.factorial ∧
        |u^(N+1)*(∑ n ∈ population v y,
          ZetaRieszJointAllocation.residualCoefficient (ZetaRieszAnnulusJoint.intermediatePrimes u N)
            (SquarefreeVaughanLogSource.length u N) N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re| ≤
          u^(N+1)*((m : ℝ)/6250*V*(Real.pi/(4*m*|y|)))+allocationBound N := by
  filter_upwards [eventually_subset_core hu hU hy,
    eventually_core_joint_bound hu hU hm hy hsmall hphase] with j hsub hbound
  intro v
  dsimp only
  intro hv hlo hhi
  have hQ := hsub v hlo hhi
  obtain ⟨V,hV,hbase,_,hc⟩ := hbound v hv hlo hhi
  refine ⟨hQ,V,hV,hbase,?_⟩
  have he := Finset.sum_sdiff hQ (f := fun n =>
    ZetaRieszJointAllocation.residualCoefficient
      (ZetaRieszAnnulusJoint.intermediatePrimes u (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j))
      (SquarefreeVaughanLogSource.length u (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j))
      (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j) n*
        zetaPrimeLogKernel (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j) (3/2+Complex.I*y) n)
  unfold ZetaRieszParityPacket.coreResponse at hc
  rw [← he,add_sub_cancel_left] at hc
  simpa only [← Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero] using hc

end
end RiemannGaussian.ZetaRieszJointTriplePayment
