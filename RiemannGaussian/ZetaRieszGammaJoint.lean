/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszGammaComplement
import RiemannGaussian.ZetaRieszJointFloor

/-!
# Joining the physical rectangle and the actual signed complement

The unsaturated selected boundary has a geometric bound. Consequently the
whole shifted response and the literal complement recombine into full
factorial mass on the saturated band, with the precise remaining masks
still signed. No selected-mode-only transfer is asserted.
-/

namespace RiemannGaussian.ZetaRieszGammaJoint
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszJointAllocation ZetaRieszGammaComplement ZetaRieszGammaCollapse
open ZetaRieszJointBoundary ZetaRieszParityPacket ZetaRieszPrimeEndpoint
open ZetaRieszAnnulusJoint ZetaRieszWideOwnerAudit ZetaRieszParityOrderTail

/-- The actual matched band in the Gamma/complement ledger. -/
def saturatedBand (u : ℝ) (N K : ℕ) : Finset ℕ :=
  (ZetaRieszLeastBoundary.fullBand u N K).filter (fun n =>
    Real.log (n/largestPrime n : ℕ) ≤ SquarefreeVaughanLogSource.length u N)

/-- Unsaturation forces a largest share below one third on the core.
This is a support fact, not an approximation to the factorial rectangle. -/
theorem unsaturated_share {u : ℝ} {N K n : ℕ}
    (hn : n ∈ ZetaRieszLeastBoundary.fullBand u N K)
    (hL : (11/8 : ℝ)*N ≤ SquarefreeVaughanLogSource.length u N)
    (hnot : n ∉ saturatedBand u N K) :
    Real.log (largestPrime n)/Real.log n < 1/3 := by
  obtain ⟨hcore,hs,hn1,_hc,hp,_⟩ := Finset.mem_filter.mp hn
  have hwindow : Real.log n ≤ (203/100 : ℝ)*N :=
    (Finset.mem_filter.mp hcore).2.2
  have hsat : ¬Real.log (n/largestPrime n : ℕ) ≤ SquarefreeVaughanLogSource.length u N := by
    intro h
    exact hnot (Finset.mem_filter.mpr ⟨hn,h⟩)
  have hln : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn1)
  apply (div_lt_iff₀ hln).mpr
  by_contra h
  exact hsat (cofactor_saturated_on_core (by omega) (Nat.prime_of_mem_primeFactors hp)
    (Nat.dvd_of_mem_primeFactors hp) hL hwindow (by linarith))

/-- A rational tilt for precisely this unmatched rectangle boundary. -/
theorem unsaturated_tilt :
    Real.log (4/3 : ℝ)-(21/40)*Real.log 2 ≤ -(1/16) := by
  have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 8/9)
  rw [show (8/9 : ℝ) = (4/3)^2/2 by norm_num,
    Real.log_div (by norm_num) (by norm_num),Real.log_pow] at h
  linarith [Real.log_two_gt_d9]

/-- All original rectangle slots are retained. Only a marked share below
one third is used for this strict factorial saving. -/
theorem weight_small_mark {n : ℕ} (hn : Squarefree n) (hn1 : 1 < n)
    (hp : largestPrime n ∈ n.primeFactors) (N : ℕ)
    (hshare : Real.log (largestPrime n)/Real.log n ≤ 1/3) :
    weight N n ≤ 3*Real.exp (-(N : ℝ)/16) := by
  let x : ℕ → ℝ := fun p => Real.log p/Real.log n
  have hx (p : ℕ) (_hp : p ∈ n.primeFactors) : 0 ≤ x p :=
    div_nonneg (Real.log_natCast_nonneg _) (Real.log_natCast_nonneg _)
  have hw := allocationWeight_nonneg n.primeFactors x hx
  have ht := coordinate_upper_tail n.primeFactors x hx (shares_sum hn hn1) hp
    (a := 21/40) (b := 4/3) (q := 2) (c := 1/16) (D := 1)
    (by norm_num) (by norm_num) (by dsimp [x]; linarith) unsaturated_tilt N
  have hsub : rectangleAllocations N n ⊆
      (Finset.piAntidiag n.primeFactors (N+1)).filter
        (fun d => (21/40 : ℝ)*N-1 < d (largestPrime n)) := by
    intro d hd
    obtain ⟨ha,hr⟩ := Finset.mem_filter.mp hd
    have hj : (21 : ℝ)*N ≤ 40*d (largestPrime n) := by
      exact_mod_cast (Finset.mem_filter.mp hr).2.2.1
    exact Finset.mem_filter.mpr ⟨ha,by linarith⟩
  apply (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun d _ _ => hw d)).trans
  apply ht.trans
  rw [one_mul,Real.exp_log (by norm_num : (0 : ℝ) < 2),
    show -(1/16 : ℝ)*N = -(N : ℝ)/16 by ring]
  nlinarith [Real.exp_pos (-(N : ℝ)/16)]

/-- A source-scale bound for the exact unmatched rectangle. Arbitrary
height, physical masks, old allocation and the Riesz coefficient survive;
this is not an estimate of the unselected boundary. -/
theorem unsaturatedPacket_bound {u : ℝ} (hu : 0 ≤ u) (hU : u ≤ radiusCeiling)
    (N K : ℕ) (y : ℝ)
    (hL : (11/8 : ℝ)*N ≤ SquarefreeVaughanLogSource.length u N) :
    ‖(u : ℂ)^(N+1)*∑ n ∈ ZetaRieszLeastBoundary.fullBand u N K\saturatedBand u N K,
        atom u y N n‖ ≤
      2*(19/20 : ℝ)^N*zetaMoebiusLogMajorantMass (1+1/256) := by
  have hr : radiusCeiling*(127/256 : ℝ)⁻¹*Real.exp (-(1/16)) ≤ 19/20 := by
    rw [Real.exp_neg,← div_eq_mul_inv]
    apply (div_le_iff₀ (Real.exp_pos _)).mpr
    have := Real.add_one_le_exp (1/16 : ℝ)
    norm_num [radiusCeiling] at *
    linarith
  have hb : 3*radiusCeiling ≤ (2 : ℝ) := by norm_num [radiusCeiling]
  have ha (n : ℕ)
      (hn : n ∈ ZetaRieszLeastBoundary.fullBand u N K\saturatedBand u N K) :
      ‖(u : ℂ)^(N+1)*atom u y N n‖ ≤
        2*(19/20 : ℝ)^N*(zetaMoebiusLogMajorant n*zetaPrimeExpWeight (1+1/256) n) := by
    obtain ⟨hf,hnot⟩ := Finset.mem_sdiff.mp hn
    have h := (Finset.mem_filter.mp hf).2
    have hw := weight_small_mark h.1 h.2.1 h.2.2.2.1 N (unsaturated_share hf hL hnot).le
    have hc := norm_residualCoefficient_le (intermediatePrimes u N)
      (SquarefreeVaughanLogSource.length_pos u N) N n
    have hk : ‖zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ ≤
        (127/256 : ℝ)⁻¹^N*zetaPrimeExpWeight (1+1/256) n := by
      convert norm_zetaPrimeLogKernel_le N (3/2+Complex.I*y) n
        (by norm_num : (0 : ℝ) < 127/256) using 1
      norm_num
    have he : Real.exp (-(N : ℝ)/16) = Real.exp (-(1/16 : ℝ))^N := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    rw [atom,norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg hu,
      norm_mul,Complex.norm_real,Real.norm_of_nonneg (weight_bounds h.1 h.2.1 N).1,norm_mul]
    calc
      _ ≤ radiusCeiling^(N+1)*((3*Real.exp (-(N : ℝ)/16))*
          (zetaMoebiusLogMajorant n*((127/256 : ℝ)⁻¹^N*
            zetaPrimeExpWeight (1+1/256) n))) := by
        gcongr
        · exact mul_nonneg (weight_bounds h.1 h.2.1 N).1
            (mul_nonneg (norm_nonneg _) (norm_nonneg _))
        · unfold radiusCeiling; positivity
        · exact zetaMoebiusLogMajorant_nonneg n
      _ = (3*radiusCeiling)*(radiusCeiling*(127/256 : ℝ)⁻¹*
          Real.exp (-(1/16 : ℝ)))^N*
          (zetaMoebiusLogMajorant n*zetaPrimeExpWeight (1+1/256) n) := by
        rw [he,mul_pow,mul_pow,pow_succ]
        ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _
          (mul_nonneg (zetaMoebiusLogMajorant_nonneg n) (Real.exp_pos _).le)
        exact mul_le_mul hb (pow_le_pow_left₀ (by unfold radiusCeiling; positivity) hr N)
          (by unfold radiusCeiling; positivity) (by norm_num)
  rw [Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ n ∈ ZetaRieszLeastBoundary.fullBand u N K\saturatedBand u N K,
        2*(19/20 : ℝ)^N*(zetaMoebiusLogMajorant n*zetaPrimeExpWeight (1+1/256) n) :=
      Finset.sum_le_sum ha
    _ ≤ _ := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left
        (Summable.sum_le_tsum _ (fun n _ => mul_nonneg (zetaMoebiusLogMajorant_nonneg n)
          (Real.exp_pos _).le) (summable_zetaMoebiusLogMajorant (by norm_num))) (by positivity)

/-- The translated physical atom already appearing in the matched ledger,
with full factorial mass and the original unassigned fraction and phase. -/
def translatedAtom (u y : ℝ) (N n : ℕ) : ℂ :=
  ((N+1 : ℕ) : ℂ)/(SquarefreeVaughanLogSource.length u N : ℂ)*
    ((1-boundedShare (intermediatePrimes u N) N n : ℝ) : ℂ)*
    (VaughanLogAverage.riesz
      (SquarefreeVaughanLogSource.length u N-Real.log (largestPrime n))
      (n/largestPrime n) : ℂ)*zetaPrimeLogKernel (N+1) (3/2+Complex.I*y) n

theorem translatedAtom_eq_original {u : ℝ} {N K n : ℕ}
    (hn : n ∈ saturatedBand u N K) (y : ℝ) :
    translatedAtom u y N n =
      residualCoefficient (intermediatePrimes u N) (SquarefreeVaughanLogSource.length u N) N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n := by
  obtain ⟨hf,hsat⟩ := Finset.mem_filter.mp hn
  obtain ⟨_,hs,_hn1,hc,hp,_⟩ := Finset.mem_filter.mp hf
  have hm := Nat.mul_div_cancel' (Nat.dvd_of_mem_primeFactors hp)
  obtain ⟨_,ha1,hanp,_⟩ := ZetaRieszMarkedSaturation.cofactor_data hs hc hp
  have he := literal_joint_atom_translated (Nat.prime_of_mem_primeFactors hp)
    (by rwa [hm]) ha1 hanp u y N K hsat
  rw [hm,← add_mul,← Complex.ofReal_add] at he
  simp only [add_sub_cancel,Complex.ofReal_one,one_mul] at he
  rw [he]
  unfold translatedAtom zetaPrimeLogKernel
  push_cast
  ring

/-- Precisely the full-mass physical sum plus the UNCHANGED signed
unmatched complement from `rest_physical_ledger`. This is the existing
joint carrier's matched formula, not a new allocation. -/
def joinedPhysical (u y : ℝ) (N K : ℕ) : ℂ :=
  (∑ n ∈ saturatedBand u N K, translatedAtom u y N n)+
    ∑ n ∈ coreBand u N K\saturatedBand u N K,
      ((1-ZetaRieszLeastBoundary.selection u N K n : ℝ) : ℂ)*
        (residualCoefficient (intermediatePrimes u N) (SquarefreeVaughanLogSource.length u N) N n*
          zetaPrimeLogKernel N (3/2+Complex.I*y) n)

/-- After joining the literal complement, the ONLY difference to the
full physical mass is the unsaturated selected boundary. The unmatched
signed complement is retained, not bounded or silently removed. -/
theorem core_sub_joined (u y : ℝ) (N K : ℕ) :
    coreResponse u y N K-joinedPhysical u y N K =
      ∑ n ∈ ZetaRieszLeastBoundary.fullBand u N K\saturatedBand u N K, atom u y N n := by
  let f := fun n => residualCoefficient (intermediatePrimes u N)
    (SquarefreeVaughanLogSource.length u N) N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
  have hD : saturatedBand u N K ⊆ coreBand u N K :=
    (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
  have hF : ZetaRieszLeastBoundary.fullBand u N K ⊆ coreBand u N K := Finset.filter_subset _ _
  have he : (∑ n ∈ saturatedBand u N K, translatedAtom u y N n) =
      ∑ n ∈ saturatedBand u N K, f n :=
    Finset.sum_congr rfl (fun n hn => translatedAtom_eq_original hn y)
  unfold coreResponse joinedPhysical
  rw [he,← Finset.sum_sdiff hD]
  change (∑ n ∈ coreBand u N K\saturatedBand u N K, f n)+
    (∑ n ∈ saturatedBand u N K, f n)-
    ((∑ n ∈ saturatedBand u N K, f n)+
      ∑ n ∈ coreBand u N K\saturatedBand u N K,
        ((1-ZetaRieszLeastBoundary.selection u N K n : ℝ) : ℂ)*f n) = _
  rw [show (∑ n ∈ coreBand u N K\saturatedBand u N K, f n)+
      (∑ n ∈ saturatedBand u N K, f n)-
      ((∑ n ∈ saturatedBand u N K, f n)+
        ∑ n ∈ coreBand u N K\saturatedBand u N K,
          ((1-ZetaRieszLeastBoundary.selection u N K n : ℝ) : ℂ)*f n) =
        (∑ n ∈ coreBand u N K\saturatedBand u N K, f n)-
        ∑ n ∈ coreBand u N K\saturatedBand u N K,
          ((1-ZetaRieszLeastBoundary.selection u N K n : ℝ) : ℂ)*f n by ring,
    ← Finset.sum_sub_distrib]
  have hsub : ZetaRieszLeastBoundary.fullBand u N K\saturatedBand u N K ⊆
      coreBand u N K\saturatedBand u N K := Finset.sdiff_subset_sdiff hF (Finset.Subset.refl _)
  rw [← Finset.sum_subset hsub (f := fun n =>
    f n-((1-ZetaRieszLeastBoundary.selection u N K n : ℝ) : ℂ)*f n)]
  · apply Finset.sum_congr rfl
    intro n hn
    rw [ZetaRieszLeastBoundary.selection,if_pos (Finset.mem_sdiff.mp hn).1,atom]
    dsimp only [f]
    push_cast
    ring
  · intro n hn hnot
    have hnF : n ∉ ZetaRieszLeastBoundary.fullBand u N K := by
      intro hh
      exact hnot (Finset.mem_sdiff.mpr ⟨hh,(Finset.mem_sdiff.mp hn).2⟩)
    simp [ZetaRieszLeastBoundary.selection,hnF]

/-- An independent geometric estimate for the recombination error in
the WHOLE original core, with both signs and all remaining masks retained. -/
theorem core_joined_bound {u : ℝ} (hu : 0 ≤ u) (hU : u ≤ radiusCeiling)
    (N K : ℕ) (y : ℝ)
    (hL : (11/8 : ℝ)*N ≤ SquarefreeVaughanLogSource.length u N) :
    ‖(u : ℂ)^(N+1)*(coreResponse u y N K-joinedPhysical u y N K)‖ ≤
      2*(19/20 : ℝ)^N*zetaMoebiusLogMajorantMass (1+1/256) := by
  rw [core_sub_joined]
  exact unsaturatedPacket_bound hu hU N K y hL

/-- No three-prime label in the full band has this unmatched cofactor
boundary. The unselected boundary may still contain other mask failures. -/
theorem unsaturated_count_ge_four {u : ℝ} {N K n : ℕ}
    (hn : n ∈ ZetaRieszLeastBoundary.fullBand u N K)
    (hL : (11/8 : ℝ)*N ≤ SquarefreeVaughanLogSource.length u N)
    (hnot : n ∉ saturatedBand u N K) : 4 ≤ n.primeFactors.card := by
  obtain ⟨_,hs,hn1,hc,hp,_⟩ := Finset.mem_filter.mp hn
  have hln : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn1)
  have hshare := (div_lt_iff₀ hln).mp (unsaturated_share hn hL hnot)
  by_contra h
  have hcard : n.primeFactors.card = 3 := by omega
  have hsum : Real.log n ≤ (n.primeFactors.card : ℝ)*Real.log (largestPrime n) := by
    rw [CoprimeEulerPhase.squarefree_log_eq_prime_sum hs]
    calc
      _ ≤ ∑ _p ∈ n.primeFactors, Real.log (largestPrime n) := by
        apply Finset.sum_le_sum
        intro p hp'
        apply Real.log_le_log (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp').pos)
        have hh : p ≤ largestPrime n := by
          rw [largestPrime,dif_pos ⟨p,hp'⟩]
          exact Finset.le_max' _ _ hp'
        exact_mod_cast hh
      _ = _ := by rw [Finset.sum_const,nsmul_eq_mul]
  rw [hcard] at hsum
  norm_num at hsum
  linarith

/-- Geometric recombination for arbitrary moving counts and heights,
with the original physical length and no zero hypothesis. -/
theorem tendsto_core_sub_joined {u : ℝ} (hu : 0 < u) (hU : u ≤ radiusCeiling)
    (heights : ℕ → ℝ) (orders counts : ℕ → ℕ) (ho : Tendsto orders atTop atTop) :
    Tendsto (fun t => (u : ℂ)^(orders t+1)*
      (coreResponse u (heights t) (orders t) (counts t)-
        joinedPhysical u (heights t) (orders t) (counts t))) atTop (𝓝 0) := by
  have hL := ZetaRieszLowerDegreeBounds.eventually_length_ge_exponent hu
    (by norm_num : (0 : ℝ) ≤ 11/16) (lt_of_le_of_lt hU radius_lt_source)
  have hp := ((tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num : (0 : ℝ) ≤ 19/20) (by norm_num : (19/20 : ℝ) < 1)).comp ho).const_mul
      (2*zetaMoebiusLogMajorantMass (1+1/256))
  simp only [mul_zero] at hp
  apply squeeze_zero_norm' ?_ hp
  filter_upwards [ho.eventually hL] with t ht
  have hLt : (11/8 : ℝ)*orders t ≤ SquarefreeVaughanLogSource.length u (orders t) := by
    nlinarith
  convert core_joined_bound hu.le hU (orders t) (counts t) (heights t) hLt using 1
  dsimp only [Function.comp_def]
  ring

/-- The existing J+C has full factorial mass in the matched physical
sum, up to independently paid errors. Neither signed term on the physical
side is bounded separately. No prime mode is assumed to exhaust J. -/
theorem tendsto_joint_sub_joined {u : ℝ} (hu : 0 < u) (hU : u ≤ radiusCeiling)
    (heights : ℕ → ℝ) (orders counts : ℕ → ℕ) (ho : Tendsto orders atTop atTop) :
    Tendsto (fun t => (u : ℂ)^(orders t+1)*
      (ZetaRieszLeastOrderOverflow.lowerThresholdPacket u (heights t) (orders t) (counts t)-
        ZetaRieszLeastOrderOverflow.shortOverflowPacket u (heights t) (orders t) (counts t)+
        ZetaRieszLeastBoundary.rest u (heights t) (orders t) (counts t)-
        joinedPhysical u (heights t) (orders t) (counts t))) atTop (𝓝 0) := by
  have he := ZetaRieszLeastOrderOverflow.tendsto_full_sub_joint_boundary
    hu.le hU heights orders counts ho
  have h := he.neg.add (tendsto_core_sub_joined hu hU heights orders counts ho)
  simp only [neg_zero,zero_add] at h
  apply h.congr'
  filter_upwards [] with t
  rw [ZetaRieszLeastBoundary.core_ledger]
  ring

/-- Under the original exposure hypotheses, keep the COMPLETE shifted
response coupled to the exact signed rest. This is a physical recombination
theorem, not a norm payment of the selected source. Multiplicity is free. -/
theorem tendsto_shifted_joint_sub_joined (rho : NontrivialZetaZero)
    (hrho : 1/2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3/2-rho.1.re < ‖(3/2+Complex.I*rho.1.im)-tau.1‖)
    (hU : 3/2-rho.1.re ≤ radiusCeiling) :
    Tendsto (fun j => ((3/2-rho.1.re : ℝ) : ℂ)^
      (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j+1)*
      (ZetaRieszUnshiftedLogPayment.shiftedMain (3/2-rho.1.re) rho.1.im
        (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)+
        ZetaRieszLeastBoundary.rest (3/2-rho.1.re) rho.1.im
          (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)
          (ZetaRieszPrimeCountFrequency.dyadicPrimeCount j)-
        joinedPhysical (3/2-rho.1.re) rho.1.im
          (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)
          (ZetaRieszPrimeCountFrequency.dyadicPrimeCount j))) atTop (𝓝 0) := by
  have hu : 0 < 3/2-rho.1.re := by linarith [NontrivialZetaZero.re_lt_one rho]
  have h := (ZetaRieszUnshiftedLogPayment.tendsto_shifted_sub_current rho hrho hexposed hU).add
    (tendsto_joint_sub_joined hu hU (fun _ => rho.1.im)
      ZetaRieszPrimeCountFrequency.dyadicMomentOrder ZetaRieszPrimeCountFrequency.dyadicPrimeCount
      ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder)
  simp only [add_zero] at h
  exact h.congr' (Eventually.of_forall fun _ => by ring)

/-- The virtual-to-literal selected discrepancy and the REMAINING shifted
channels are the same joint error just paid above. This does not pay either
one separately or infer selected-mode exhaustion through a share mask. -/
theorem selected_discrepancy_eq_joint (u y : ℝ) (N K m : ℕ) (A : Finset ℕ) :
    ((m : ℂ)*ZetaRieszSelectedCofactor.selectedResponse A N u y
        (SquarefreeVaughanLogSource.length u N)-
      ∑ n ∈ saturatedBand u N K,
        (continuousRectangleMass N (Real.log (largestPrime n)) (Real.log n.minFac)
          (Real.log n-Real.log (largestPrime n)-Real.log n.minFac) : ℂ)*translatedAtom u y N n)+
    (ZetaRieszUnshiftedLogPayment.shiftedMain u y N-
      (m : ℂ)*ZetaRieszSelectedCofactor.selectedResponse A N u y
        (SquarefreeVaughanLogSource.length u N)) =
    ZetaRieszUnshiftedLogPayment.shiftedMain u y N+
      ZetaRieszLeastBoundary.rest u y N K-joinedPhysical u y N K := by
  have he := joint_matched_ledger u y N K m A
  change (m : ℂ)*ZetaRieszSelectedCofactor.selectedResponse A N u y
      (SquarefreeVaughanLogSource.length u N)+ZetaRieszLeastBoundary.rest u y N K =
    joinedPhysical u y N K+
      ((m : ℂ)*ZetaRieszSelectedCofactor.selectedResponse A N u y
        (SquarefreeVaughanLogSource.length u N)-
        ∑ n ∈ saturatedBand u N K,
          (continuousRectangleMass N (Real.log (largestPrime n)) (Real.log n.minFac)
            (Real.log n-Real.log (largestPrime n)-Real.log n.minFac) : ℂ)*translatedAtom u y N n) at he
  linear_combination -he

end
end RiemannGaussian.ZetaRieszGammaJoint
