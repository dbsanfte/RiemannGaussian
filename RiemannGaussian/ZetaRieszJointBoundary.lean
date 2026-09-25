/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszJointShiftError
import RiemannGaussian.ZetaRieszParityMaskTails

/-!
# Paying exterior share boundaries in the literal joint carrier

The original factorial rectangle is kept exactly. Adjacent shares are
joined with their original signed weights. Outside 1/2 < largestShare < 3/5,
the rectangle itself has an exponential tail that beats the source envelope.
This removes those exterior hard boundaries independently of prime phases.
It does not estimate the signed interior or complete any prime cofactor.
-/

namespace RiemannGaussian.ZetaRieszJointBoundary
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszJointAllocation ZetaRieszParityOrderTail ZetaRieszParityPacket
open ZetaRieszSkewAllocation ZetaRieszPrimeEndpoint ZetaRieszAnnulusJoint
open ZetaRieszWideOwnerAudit

/-- All original rectangle allocations, with no individual order deletion. -/
def weight (N n : ℕ) : ℝ :=
  ∑ d ∈ rectangleAllocations N n,
    allocationWeight n.primeFactors (fun p => Real.log p/Real.log n) d

theorem shares_sum {n : ℕ} (hn : Squarefree n) (hn1 : 1 < n) :
    (∑ p ∈ n.primeFactors, Real.log p/Real.log n) = 1 := by
  rw [← Finset.sum_div, ← CoprimeEulerPhase.squarefree_log_eq_prime_sum hn,
    div_self (Real.log_pos (by exact_mod_cast hn1)).ne']

theorem weight_bounds {n : ℕ} (hn : Squarefree n) (hn1 : 1 < n) (N : ℕ) :
    0 ≤ weight N n ∧ weight N n ≤ 1 := by
  have hx (p : ℕ) (_hp : p ∈ n.primeFactors) : 0 ≤ Real.log p/Real.log n :=
    div_nonneg (Real.log_natCast_nonneg _) (Real.log_natCast_nonneg _)
  have hw := allocationWeight_nonneg n.primeFactors _ hx
  refine ⟨Finset.sum_nonneg (fun d _ => hw d), ?_⟩
  calc
    _ ≤ ∑ d ∈ Finset.piAntidiag n.primeFactors (N+1),
        allocationWeight n.primeFactors (fun p => Real.log p/Real.log n) d :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun d _ _ => hw d)
    _ = 1 := by
      simp only [allocationWeight]
      rw [← Finset.sum_pow_eq_sum_piAntidiag, shares_sum hn hn1, one_pow]

/-- Agreement with the EXISTING packet's correlated finite weight. -/
theorem weight_eq_rectangle {n : ℕ} (hn : FullParityBox n) (N : ℕ) :
    weight N n = rectangleMass N (1-Real.log (largestPrime n)/Real.log n)
      (Real.log n.minFac/(Real.log n-Real.log (largestPrime n))) := by
  have h := rectangleMass_eq_good_add_bad hn N
  rw [goodRectangleMass, badRectangleMass, Finset.sum_filter_add_sum_filter_not] at h
  exact h.symm

theorem exterior_tilt_rates :
    Real.log (21/20 : ℝ)-(21/40)*Real.log (11/10) ≤ -(1/1600) ∧
      Real.log (47/50 : ℝ)-(29/50)*Real.log (9/10) ≤ -(1/1600) := by
  constructor
  · exact log_rate_of_power (by norm_num) (by norm_num) 21 40 (by decide) (by norm_num)
  · exact log_rate_of_power (by norm_num) (by norm_num) 29 50 (by decide) (by norm_num)

/-- This is a bound on literal factorial mass, not a modal endpoint assumption. -/
theorem weight_exterior {n : ℕ} (hn : Squarefree n) (hn1 : 1 < n)
    (hp : largestPrime n ∈ n.primeFactors) (N : ℕ) (hN : 1 ≤ N)
    (hedge : Real.log (largestPrime n)/Real.log n ≤ 1/2 ∨
      3/5 ≤ Real.log (largestPrime n)/Real.log n) :
    weight N n ≤ 2*Real.exp (-(N : ℝ)/1600) := by
  let x : ℕ → ℝ := fun p => Real.log p/Real.log n
  have hx (p : ℕ) (_hp : p ∈ n.primeFactors) : 0 ≤ x p :=
    div_nonneg (Real.log_natCast_nonneg _) (Real.log_natCast_nonneg _)
  have hs : ∑ p ∈ n.primeFactors, x p = 1 := shares_sum hn hn1
  have hw := allocationWeight_nonneg n.primeFactors x hx
  have hNR : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  rcases hedge with hl | hr
  · have ht := coordinate_upper_tail n.primeFactors x hx hs hp
      (a := 21/40) (b := 21/20) (q := 11/10) (c := 1/1600) (D := 1)
      (by norm_num) (by norm_num) (by dsimp [x]; linarith)
      exterior_tilt_rates.1 N
    have hsub : rectangleAllocations N n ⊆
        (Finset.piAntidiag n.primeFactors (N+1)).filter
          (fun d => (21/40 : ℝ)*N-1 < d (largestPrime n)) := by
      intro d hd
      obtain ⟨ha, hr⟩ := Finset.mem_filter.mp hd
      have hj := (Finset.mem_filter.mp hr).2.2.1
      have hjR : (21 : ℝ)*N ≤ 40*d (largestPrime n) := by exact_mod_cast hj
      exact Finset.mem_filter.mpr ⟨ha, by linarith⟩
    apply (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun d _ _ => hw d)).trans
    apply ht.trans
    rw [one_mul, Real.exp_log (by norm_num : (0 : ℝ) < 11/10)]
    rw [show -(1/1600 : ℝ)*N = -(N : ℝ)/1600 by ring]
    nlinarith [Real.exp_pos (-(N : ℝ)/1600)]
  · have ht := coordinate_lower_tail n.primeFactors x hx hs hp
      (a := 29/50) (b := 47/50) (q := 9/10) (c := 1/1600)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by dsimp [x]; linarith) exterior_tilt_rates.2 N
    have hsub : rectangleAllocations N n ⊆
        (Finset.piAntidiag n.primeFactors (N+1)).filter
          (fun d => (d (largestPrime n) : ℝ) < (29/50)*N) := by
      intro d hd
      obtain ⟨ha, hr⟩ := Finset.mem_filter.mp hd
      have hj := (Finset.mem_filter.mp hr).2.2.2.1
      have hjR : (40 : ℝ)*d (largestPrime n) ≤ 23*N := by exact_mod_cast hj
      exact Finset.mem_filter.mpr ⟨ha, by linarith⟩
    apply (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun d _ _ => hw d)).trans
    rw [show -(1/1600 : ℝ)*N = -(N : ℝ)/1600 by ring] at ht
    exact ht.trans (by nlinarith [Real.exp_pos (-(N : ℝ)/1600)])

/-- Exactly the old support conditions except the two largest-share cuts.
The adjacent pieces belong to the existing unpaid rest. -/
structure JointBox (n : ℕ) : Prop where
  squarefree : Squarefree n
  nontrivial : 1 < n
  count_lower : 3 ≤ n.primeFactors.card
  largest_mem : largestPrime n ∈ n.primeFactors
  least_lower : (3/250 : ℝ)*Real.log n ≤ Real.log n.minFac
  least_upper : Real.log n.minFac ≤ (7/250 : ℝ)*Real.log n

/-- The literal core with the original least-share and physical masks. -/
def band (u : ℝ) (N K : ℕ) : Finset ℕ :=
  (coreBand u N K).filter (fun n => JointBox n ∧
    ∀ p ∈ n.primeFactors, p ∈ intermediatePrimes u N)

/-- The original signed atom times its exact rectangle allocation. -/
def atom (u y : ℝ) (N n : ℕ) : ℂ :=
  (weight N n : ℂ)*(residualCoefficient (intermediatePrimes u N)
    (SquarefreeVaughanLogSource.length u N) N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n)

/-- The joined packet before imposing any largest-share cut. -/
def packet (u y : ℝ) (N K : ℕ) : ℂ := ∑ n ∈ band u N K, atom u y N n

/-- The two exterior boundaries lie outside the selected factorial orders. -/
def interior (n : ℕ) : Prop :=
  (1/2 : ℝ) < Real.log (largestPrime n)/Real.log n ∧
    Real.log (largestPrime n)/Real.log n < (3/5 : ℝ)

/-- The joined packet between the independently paid exterior boundaries. -/
def interiorPacket (u y : ℝ) (N K : ℕ) : ℂ :=
  ∑ n ∈ (band u N K).filter interior, atom u y N n

/-- The full signed exterior error, with all remaining masks retained. -/
def exteriorPacket (u y : ℝ) (N K : ℕ) : ℂ :=
  ∑ n ∈ (band u N K).filter (fun n => ¬interior n), atom u y N n

theorem exterior_ledger (u y : ℝ) (N K : ℕ) :
    packet u y N K = interiorPacket u y N K+exteriorPacket u y N K := by
  exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm

/-- Source growth and factorial tilt after paying the exterior tail. -/
def exteriorRate : ℝ :=
  radiusCeiling*(131071/262144 : ℝ)⁻¹*Real.exp (-(1/1600 : ℝ))

theorem exteriorRate_bounds : 0 ≤ exteriorRate ∧ exteriorRate < 1 := by
  constructor
  · unfold exteriorRate radiusCeiling; positivity
  · rw [exteriorRate, Real.exp_neg, mul_inv_lt_iff₀ (Real.exp_pos _), one_mul]
    have h := Real.add_one_le_exp (1/1600 : ℝ)
    norm_num [radiusCeiling] at h ⊢
    linarith

/-- Independent source-scale bound with every other literal mask intact. -/
theorem exteriorPacket_bound {u : ℝ} (hu : 0 ≤ u) (hU : u ≤ radiusCeiling)
    (y : ℝ) (N K : ℕ) (hN : 1 ≤ N) :
    ‖(u : ℂ)^(N+1)*exteriorPacket u y N K‖ ≤
      (2*radiusCeiling)*exteriorRate^N*zetaMoebiusLogMajorantMass (1+1/262144) := by
  have ha (n : ℕ) (hn : n ∈ (band u N K).filter (fun n => ¬interior n)) :
      ‖(u : ℂ)^(N+1)*atom u y N n‖ ≤
        (2*radiusCeiling)*exteriorRate^N*
          (zetaMoebiusLogMajorant n*zetaPrimeExpWeight (1+1/262144) n) := by
    have hb := (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).2.1
    have he : Real.log (largestPrime n)/Real.log n ≤ 1/2 ∨
        3/5 ≤ Real.log (largestPrime n)/Real.log n := by
      have := (Finset.mem_filter.mp hn).2
      simp only [interior, not_and_or, not_lt] at this
      exact this
    have hw := weight_exterior hb.squarefree hb.nontrivial hb.largest_mem N hN he
    have hc := norm_residualCoefficient_le (intermediatePrimes u N)
      (SquarefreeVaughanLogSource.length_pos u N) N n
    have hk : ‖zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ ≤
        (131071/262144 : ℝ)⁻¹^N*zetaPrimeExpWeight (1+1/262144) n := by
      convert norm_zetaPrimeLogKernel_le N (3/2+Complex.I*y) n
        (by norm_num : (0 : ℝ) < 131071/262144) using 1
      norm_num
    have hexp : Real.exp (-(N : ℝ)/1600) = Real.exp (-(1/1600 : ℝ))^N := by
      rw [← Real.exp_nat_mul]; congr 1; ring
    rw [atom, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hu,
      norm_mul, Complex.norm_real, Real.norm_of_nonneg (weight_bounds hb.squarefree hb.nontrivial N).1,
      norm_mul]
    calc
      _ ≤ radiusCeiling^(N+1)*((2*Real.exp (-(N : ℝ)/1600))*
          (zetaMoebiusLogMajorant n*((131071/262144 : ℝ)⁻¹^N*
            zetaPrimeExpWeight (1+1/262144) n))) := by
        gcongr
        · exact mul_nonneg (weight_bounds hb.squarefree hb.nontrivial N).1
            (mul_nonneg (norm_nonneg _) (norm_nonneg _))
        · unfold radiusCeiling; positivity
        · exact zetaMoebiusLogMajorant_nonneg n
      _ = _ := by rw [hexp, exteriorRate, mul_pow, mul_pow, pow_succ]; ring
  rw [exteriorPacket, Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ n ∈ (band u N K).filter (fun n => ¬interior n), (2*radiusCeiling)*exteriorRate^N*
        (zetaMoebiusLogMajorant n*zetaPrimeExpWeight (1+1/262144) n) :=
      Finset.sum_le_sum ha
    _ ≤ _ := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left
        (Summable.sum_le_tsum _ (fun n _ => mul_nonneg (zetaMoebiusLogMajorant_nonneg n)
          (Real.exp_pos _).le) (summable_zetaMoebiusLogMajorant (by norm_num)))
        (mul_nonneg (by unfold radiusCeiling; positivity) (pow_nonneg exteriorRate_bounds.1 _))

theorem tendsto_exteriorPacket {u : ℝ} (hu : 0 ≤ u) (hU : u ≤ radiusCeiling)
    (heights : ℕ → ℝ) (orders counts : ℕ → ℕ) (ho : Tendsto orders atTop atTop) :
    Tendsto (fun t => (u : ℂ)^(orders t+1)*
      exteriorPacket u (heights t) (orders t) (counts t)) atTop (𝓝 0) := by
  have ht := (((tendsto_pow_atTop_nhds_zero_of_lt_one exteriorRate_bounds.1
    exteriorRate_bounds.2).const_mul (2*radiusCeiling)).mul_const
      (zetaMoebiusLogMajorantMass (1+1/262144))).comp ho
  simp only [mul_zero, zero_mul, Function.comp_def] at ht
  apply squeeze_zero_norm' _ ht
  filter_upwards [ho.eventually (eventually_ge_atTop 1)] with t ht
  exact exteriorPacket_bound hu hU _ _ _ ht

theorem fullParityBand_subset (u : ℝ) (N K : ℕ) : fullParityBand u N K ⊆ band u N K := by
  intro n hn
  obtain ⟨hc, hb, hphys⟩ := Finset.mem_filter.mp hn
  exact Finset.mem_filter.mpr ⟨hc,
    ⟨hb.squarefree, hb.nontrivial, hb.count_lower, hb.largest_mem, hb.least_lower, hb.least_upper⟩,
    hphys⟩

theorem fullParityPacket_eq_atoms (u y : ℝ) (N K : ℕ) :
    fullParityPacket u y N K = ∑ n ∈ fullParityBand u N K, atom u y N n := by
  have he : fullParityPacket u y N K = ∑ n ∈ fullParityBand u N K,
      (fullParitySelection u N K n : ℂ)*
        (residualCoefficient (intermediatePrimes u N) (SquarefreeVaughanLogSource.length u N) N n*
          zetaPrimeLogKernel N (3/2+Complex.I*y) n) := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro n _ hn
    change n ∉ fullParityBand u N K at hn
    rw [fullParitySelection, if_neg hn, Complex.ofReal_zero, zero_mul]
  rw [he]
  apply Finset.sum_congr rfl
  intro n hn
  rw [atom, weight_eq_rectangle (Finset.mem_filter.mp hn).2.1, fullParitySelection, if_pos hn]

/-- These exact neighbors are taken from the old unpaid rest, not added
as a free reserve and not estimated separately by positive allowances. -/
def neighbors (u y : ℝ) (N K : ℕ) : ℂ :=
  ∑ n ∈ band u N K \ fullParityBand u N K, atom u y N n

theorem joint_ledger (u y : ℝ) (N K : ℕ) :
    packet u y N K = fullParityPacket u y N K+neighbors u y N K := by
  rw [fullParityPacket_eq_atoms, neighbors, packet]
  simpa only [add_comm] using (Finset.sum_sdiff (f := atom u y N)
    (fullParityBand_subset u N K)).symm

/-- A genuine suballocation of the old core, with a nonnegative weight
at most one. This says nothing about the sign of its complex atom. -/
def selection (u : ℝ) (N K n : ℕ) : ℝ := if n ∈ band u N K then weight N n else 0

theorem selection_bounds (u : ℝ) (N K n : ℕ) :
    0 ≤ selection u N K n ∧ selection u N K n ≤ 1 := by
  unfold selection
  split_ifs with hn
  · have hb := (Finset.mem_filter.mp hn).2.1
    exact weight_bounds hb.squarefree hb.nontrivial N
  · norm_num

/-- The exact complementary fraction of the original direct core. -/
def rest (u y : ℝ) (N K : ℕ) : ℂ :=
  ∑ n ∈ coreBand u N K, ((1-selection u N K n : ℝ) : ℂ)*
    (residualCoefficient (intermediatePrimes u N) (SquarefreeVaughanLogSource.length u N) N n*
      zetaPrimeLogKernel N (3/2+Complex.I*y) n)

theorem core_ledger (u y : ℝ) (N K : ℕ) :
    coreResponse u y N K = packet u y N K+rest u y N K := by
  have he : packet u y N K = ∑ n ∈ coreBand u N K, (selection u N K n : ℂ)*
      (residualCoefficient (intermediatePrimes u N) (SquarefreeVaughanLogSource.length u N) N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n) := by
    rw [packet]
    symm
    rw [← Finset.sum_subset (show band u N K ⊆ coreBand u N K from Finset.filter_subset _ _)
      (f := fun n =>
      (selection u N K n : ℂ)*(residualCoefficient (intermediatePrimes u N)
        (SquarefreeVaughanLogSource.length u N) N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n))]
    · exact Finset.sum_congr rfl (fun n hn => by rw [selection, if_pos hn]; rfl)
    · intro n _ hn
      change n ∉ band u N K at hn
      rw [selection, if_neg hn, Complex.ofReal_zero, zero_mul]
  rw [he, rest, ← Finset.sum_add_distrib, coreResponse]
  exact Finset.sum_congr rfl (fun n _ => by push_cast; ring)

theorem old_rest_ledger (u y : ℝ) (N K : ℕ) :
    fullParityRest u y N K = neighbors u y N K+rest u y N K := by
  have h := fullParity_direct_ledger u y N K
  rw [core_ledger, joint_ledger] at h
  linear_combination -h

/-- Literal joint transfer: no separate norm of the original packet or
its neighbors, and every unremoved mask remains inside both sums. -/
theorem joint_transfer_bound {u : ℝ} (hu : 0 ≤ u) (hU : u ≤ radiusCeiling)
    (y : ℝ) (N K : ℕ) (hN : 1 ≤ N) :
    ‖(u : ℂ)^(N+1)*(fullParityPacket u y N K+neighbors u y N K-
      interiorPacket u y N K)‖ ≤
      (2*radiusCeiling)*exteriorRate^N*zetaMoebiusLogMajorantMass (1+1/262144) := by
  rw [← joint_ledger, exterior_ledger, add_sub_cancel_left]
  exact exteriorPacket_bound hu hU y N K hN

end
end RiemannGaussian.ZetaRieszJointBoundary
