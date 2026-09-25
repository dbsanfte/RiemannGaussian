/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszJointAllocationError

/-!
# Paying the least-share exterior with the literal factorial weights

The least prime retains its original shifted rectangle order. Joining its
neighboring shares uses an exact part of the old unpaid rest. Outside
1/200 < leastShare < 3/50, the entire literal rectangle mass has an
independent geometric bound. No small individual order is deleted.
-/

namespace RiemannGaussian.ZetaRieszLeastBoundary
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszParityOrderTail ZetaRieszJointAllocation ZetaRieszJointBoundary
open ZetaRieszParityPacket ZetaRieszSkewAllocation ZetaRieszPrimeEndpoint
open ZetaRieszAnnulusJoint ZetaRieszWideOwnerAudit
open ZetaRieszJointOwnerTransfer ZetaRieszJointAllocationError

theorem least_tilt_rates :
    Real.log (401/400 : ℝ)-(1/100)*Real.log (3/2) ≤ -(1/1600) ∧
      Real.log (49/50 : ℝ)-(1/25)*Real.log (2/3) ≤ -(1/1600) := by
  constructor
  · simpa using log_rate_of_power (q := 3/2) (b := 401/400) (c := 1/1600)
      (by norm_num) (by norm_num) 1 100 (by decide) (by norm_num)
  · simpa using log_rate_of_power (q := 2/3) (b := 49/50) (c := 1/1600)
      (by norm_num) (by norm_num) 1 25 (by decide) (by norm_num)

/-- The derivative shift h+1 is kept in the actual finite selection. -/
theorem weight_least_exterior {n : ℕ} (hn : Squarefree n) (hn1 : 1 < n) (N : ℕ)
    (hedge : Real.log n.minFac/Real.log n ≤ 1/200 ∨
      3/50 ≤ Real.log n.minFac/Real.log n) :
    weight N n ≤ 3*Real.exp (-(N : ℝ)/1600) := by
  let x : ℕ → ℝ := fun p => Real.log p/Real.log n
  have hx (p : ℕ) (_hp : p ∈ n.primeFactors) : 0 ≤ x p :=
    div_nonneg (Real.log_natCast_nonneg _) (Real.log_natCast_nonneg _)
  have hs : ∑ p ∈ n.primeFactors, x p = 1 := shares_sum hn hn1
  have hp : n.minFac ∈ n.primeFactors :=
    (Nat.minFac_prime hn1.ne').mem_primeFactors (Nat.minFac_dvd n) hn.ne_zero
  have hw := allocationWeight_nonneg n.primeFactors x hx
  rcases hedge with hl | hr
  · have ht := coordinate_upper_tail n.primeFactors x hx hs hp
      (a := 1/100) (b := 401/400) (q := 3/2) (c := 1/1600) (D := 2)
      (by norm_num) (by norm_num) (by dsimp [x]; linarith) least_tilt_rates.1 N
    have hsub : rectangleAllocations N n ⊆
        (Finset.piAntidiag n.primeFactors (N+1)).filter
          (fun d => (1/100 : ℝ)*N-2 < d n.minFac) := by
      intro d hd
      obtain ⟨ha, hr⟩ := Finset.mem_filter.mp hd
      have h := (Finset.mem_filter.mp hr).2.2.2.2.1
      have hR : (N : ℝ) ≤ 100*((d n.minFac : ℝ)+1) := by exact_mod_cast h
      exact Finset.mem_filter.mpr ⟨ha, by linarith⟩
    apply (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun d _ _ => hw d)).trans
    apply ht.trans
    rw [show (2 : ℝ)*Real.log (3/2) = Real.log ((3/2 : ℝ)^2) by
      rw [Real.log_pow]; norm_num, Real.exp_log (by norm_num)]
    rw [show -(1/1600 : ℝ)*N = -(N : ℝ)/1600 by ring]
    nlinarith [Real.exp_pos (-(N : ℝ)/1600)]
  · have ht := coordinate_lower_tail n.primeFactors x hx hs hp
      (a := 1/25) (b := 49/50) (q := 2/3) (c := 1/1600)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by dsimp [x]; linarith) least_tilt_rates.2 N
    have hsub : rectangleAllocations N n ⊆
        (Finset.piAntidiag n.primeFactors (N+1)).filter
          (fun d => (d n.minFac : ℝ) < (1/25)*N) := by
      intro d hd
      obtain ⟨ha, hr⟩ := Finset.mem_filter.mp hd
      have h := (Finset.mem_filter.mp hr).2.2.2.2.2
      have hR : (100 : ℝ)*((d n.minFac : ℝ)+1) ≤ 4*N := by exact_mod_cast h
      exact Finset.mem_filter.mpr ⟨ha, by linarith⟩
    apply (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun d _ _ => hw d)).trans
    rw [show -(1/1600 : ℝ)*N = -(N : ℝ)/1600 by ring] at ht
    exact ht.trans (by nlinarith [Real.exp_pos (-(N : ℝ)/1600)])

/-- The same core and prime support, with neither log-share interval imposed.
The original finite rectangle, canonical least prime and all low orders remain. -/
def fullBand (u : ℝ) (N K : ℕ) : Finset ℕ :=
  (coreBand u N K).filter (fun n => Squarefree n ∧ 1 < n ∧
    3 ≤ n.primeFactors.card ∧ largestPrime n ∈ n.primeFactors ∧
    ∀ p ∈ n.primeFactors, p ∈ intermediatePrimes u N)

/-- The original signed rectangle sum after joining both share directions. -/
def fullPacket (u y : ℝ) (N K : ℕ) : ℂ :=
  ∑ n ∈ fullBand u N K, atom u y N n

/-- Boundaries placed strictly outside both selected factorial order bands. -/
def interior (n : ℕ) : Prop := ZetaRieszJointBoundary.interior n ∧
  (1/200 : ℝ) < Real.log n.minFac/Real.log n ∧
    Real.log n.minFac/Real.log n < (3/50 : ℝ)

/-- The literal surviving interior, not a completed-prime surrogate. -/
def interiorPacket (u y : ℝ) (N K : ℕ) : ℂ :=
  ∑ n ∈ (fullBand u N K).filter interior, atom u y N n

/-- All exterior labels with their original correlated signed weights. -/
def exteriorPacket (u y : ℝ) (N K : ℕ) : ℂ :=
  ∑ n ∈ (fullBand u N K).filter (fun n => ¬interior n), atom u y N n

theorem full_exterior_ledger (u y : ℝ) (N K : ℕ) :
    fullPacket u y N K = interiorPacket u y N K+exteriorPacket u y N K := by
  exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm

theorem weight_joint_exterior {n : ℕ} (hn : Squarefree n) (hn1 : 1 < n)
    (hp : largestPrime n ∈ n.primeFactors) (N : ℕ) (hN : 1 ≤ N) (he : ¬interior n) :
    weight N n ≤ 3*Real.exp (-(N : ℝ)/1600) := by
  by_cases hm : ZetaRieszJointBoundary.interior n
  · have h : Real.log n.minFac/Real.log n ≤ 1/200 ∨
        3/50 ≤ Real.log n.minFac/Real.log n := by
      simpa only [interior, hm, true_and, not_and_or, not_lt] using he
    exact weight_least_exterior hn hn1 N h
  · have h : Real.log (largestPrime n)/Real.log n ≤ 1/2 ∨
        3/5 ≤ Real.log (largestPrime n)/Real.log n := by
      simpa only [ZetaRieszJointBoundary.interior, not_and_or, not_lt] using hm
    exact (weight_exterior hn hn1 hp N hN h).trans
      (by nlinarith [Real.exp_pos (-(N : ℝ)/1600)])

/-- Both exterior share errors beat the source, uniformly in height and count.
The Riesz coefficient, old allocation and physical prime masks are untouched. -/
theorem exteriorPacket_bound {u : ℝ} (hu : 0 ≤ u) (hU : u ≤ radiusCeiling)
    (y : ℝ) (N K : ℕ) (hN : 1 ≤ N) :
    ‖(u : ℂ)^(N+1)*exteriorPacket u y N K‖ ≤
      (3*radiusCeiling)*exteriorRate^N*zetaMoebiusLogMajorantMass (1+1/262144) := by
  have ha (n : ℕ) (hn : n ∈ (fullBand u N K).filter (fun n => ¬interior n)) :
      ‖(u : ℂ)^(N+1)*atom u y N n‖ ≤
        (3*radiusCeiling)*exteriorRate^N*
          (zetaMoebiusLogMajorant n*zetaPrimeExpWeight (1+1/262144) n) := by
    have hb := (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).2
    have hw := weight_joint_exterior hb.1 hb.2.1 hb.2.2.2.1 N hN (Finset.mem_filter.mp hn).2
    have hc := norm_residualCoefficient_le (intermediatePrimes u N)
      (SquarefreeVaughanLogSource.length_pos u N) N n
    have hk : ‖zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ ≤
        (131071/262144 : ℝ)⁻¹^N*zetaPrimeExpWeight (1+1/262144) n := by
      convert norm_zetaPrimeLogKernel_le N (3/2+Complex.I*y) n
        (by norm_num : (0 : ℝ) < 131071/262144) using 1
      norm_num
    have he : Real.exp (-(N : ℝ)/1600) = Real.exp (-(1/1600 : ℝ))^N := by
      rw [← Real.exp_nat_mul]; congr 1; ring
    rw [atom, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hu,
      norm_mul, Complex.norm_real, Real.norm_of_nonneg (weight_bounds hb.1 hb.2.1 N).1,
      norm_mul]
    calc
      _ ≤ radiusCeiling^(N+1)*((3*Real.exp (-(N : ℝ)/1600))*
          (zetaMoebiusLogMajorant n*((131071/262144 : ℝ)⁻¹^N*
            zetaPrimeExpWeight (1+1/262144) n))) := by
        gcongr
        · exact mul_nonneg (weight_bounds hb.1 hb.2.1 N).1
            (mul_nonneg (norm_nonneg _) (norm_nonneg _))
        · unfold radiusCeiling; positivity
        · exact zetaMoebiusLogMajorant_nonneg n
      _ = _ := by rw [he, exteriorRate, mul_pow, mul_pow, pow_succ]; ring
  rw [exteriorPacket, Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ n ∈ (fullBand u N K).filter (fun n => ¬interior n), (3*radiusCeiling)*exteriorRate^N*
        (zetaMoebiusLogMajorant n*zetaPrimeExpWeight (1+1/262144) n) := Finset.sum_le_sum ha
    _ ≤ _ := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left
        (Summable.sum_le_tsum _ (fun n _ => mul_nonneg (zetaMoebiusLogMajorant_nonneg n)
          (Real.exp_pos _).le) (summable_zetaMoebiusLogMajorant (by norm_num)))
        (mul_nonneg (by unfold radiusCeiling; positivity) (pow_nonneg exteriorRate_bounds.1 _))

theorem band_subset_fullBand (u : ℝ) (N K : ℕ) : band u N K ⊆ fullBand u N K := by
  intro n hn
  obtain ⟨hc,hb,hphys⟩ := Finset.mem_filter.mp hn
  exact Finset.mem_filter.mpr ⟨hc,hb.squarefree,hb.nontrivial,hb.count_lower,hb.largest_mem,hphys⟩

/-- Newly joined least shares are explicitly taken from the previous rest. -/
def leastNeighbors (u y : ℝ) (N K : ℕ) : ℂ :=
  ∑ n ∈ fullBand u N K \ band u N K, atom u y N n

theorem full_joint_ledger (u y : ℝ) (N K : ℕ) :
    fullPacket u y N K = packet u y N K+leastNeighbors u y N K := by
  rw [fullPacket, packet, leastNeighbors]
  simpa only [add_comm] using (Finset.sum_sdiff (f := atom u y N)
    (band_subset_fullBand u N K)).symm

/-- Exact fractional selection of the original core. -/
def selection (u : ℝ) (N K n : ℕ) : ℝ := if n ∈ fullBand u N K then weight N n else 0

theorem selection_bounds (u : ℝ) (N K n : ℕ) :
    0 ≤ selection u N K n ∧ selection u N K n ≤ 1 := by
  unfold selection
  split_ifs with h
  · have hb := (Finset.mem_filter.mp h).2
    exact weight_bounds hb.1 hb.2.1 N
  · norm_num

/-- The exact remaining part of coreResponse; no signed floor is asserted. -/
def rest (u y : ℝ) (N K : ℕ) : ℂ :=
  ∑ n ∈ coreBand u N K, ((1-selection u N K n : ℝ) : ℂ)*
    (residualCoefficient (intermediatePrimes u N) (SquarefreeVaughanLogSource.length u N) N n*
      zetaPrimeLogKernel N (3/2+Complex.I*y) n)

theorem core_ledger (u y : ℝ) (N K : ℕ) :
    coreResponse u y N K = fullPacket u y N K+rest u y N K := by
  have hp : fullPacket u y N K = ∑ n ∈ coreBand u N K,
      (selection u N K n : ℂ)*(residualCoefficient (intermediatePrimes u N)
        (SquarefreeVaughanLogSource.length u N) N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n) := by
    have hsub : fullBand u N K ⊆ coreBand u N K := Finset.filter_subset _ _
    rw [fullPacket, ← Finset.sum_subset hsub (f := fun n =>
      (selection u N K n : ℂ)*(residualCoefficient (intermediatePrimes u N)
        (SquarefreeVaughanLogSource.length u N) N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n))]
    · apply Finset.sum_congr rfl
      intro n hn
      rw [selection, if_pos hn, atom]
    · intro n _ hn
      rw [selection, if_neg hn, Complex.ofReal_zero, zero_mul]
  rw [hp, rest, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  push_cast
  ring

theorem old_rest_ledger (u y : ℝ) (N K : ℕ) :
    ZetaRieszJointBoundary.rest u y N K = leastNeighbors u y N K+rest u y N K := by
  have h := core_ledger u y N K
  rw [ZetaRieszJointBoundary.core_ledger, full_joint_ledger] at h
  linear_combination h

theorem tendsto_full_sub_interior {u : ℝ} (hu : 0 ≤ u) (hU : u ≤ radiusCeiling)
    (heights : ℕ → ℝ) (orders counts : ℕ → ℕ) (ho : Tendsto orders atTop atTop) :
    Tendsto (fun t => (u : ℂ)^(orders t+1)*(fullPacket u (heights t) (orders t) (counts t)-
      interiorPacket u (heights t) (orders t) (counts t))) atTop (𝓝 0) := by
  simp_rw [full_exterior_ledger, add_sub_cancel_left]
  have ht := (((tendsto_pow_atTop_nhds_zero_of_lt_one exteriorRate_bounds.1
    exteriorRate_bounds.2).const_mul (3*radiusCeiling)).mul_const
      (zetaMoebiusLogMajorantMass (1+1/262144))).comp ho
  simp only [mul_zero, zero_mul, Function.comp_def] at ht
  apply squeeze_zero_norm' _ ht
  filter_upwards [ho.eventually (eventually_ge_atTop 1)] with t ht
  exact exteriorPacket_bound hu hU _ _ _ ht


/-- The new interior uses its own ceiling, not the obsolete 39 or 83. -/
theorem interior_count_le {u : ℝ} {N K n : ℕ}
    (hn : n ∈ (fullBand u N K).filter interior) : n.primeFactors.card ≤ 200 := by
  have hb := (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).2
  have hi := (Finset.mem_filter.mp hn).2
  have hl : 0 < Real.log n := Real.log_pos (by exact_mod_cast hb.2.1)
  have hr : (1/200 : ℝ)*Real.log n ≤ Real.log n.minFac :=
    ((lt_div_iff₀ hl).mp hi.2.1).le
  have hs : (∑ _p ∈ n.primeFactors, (1/200 : ℝ)*Real.log n) ≤
      ∑ p ∈ n.primeFactors, Real.log p := by
    apply Finset.sum_le_sum
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    exact hr.trans (Real.log_le_log
      (by exact_mod_cast (Nat.minFac_prime hb.2.1.ne').pos)
      (by exact_mod_cast Nat.minFac_le_of_dvd hpp.two_le (Nat.dvd_of_mem_primeFactors hp)))
  rw [Finset.sum_const, nsmul_eq_mul, ← CoprimeEulerPhase.squarefree_log_eq_prime_sum hb.1] at hs
  by_contra hc
  have hcR : (201 : ℝ) ≤ n.primeFactors.card := by exact_mod_cast (by omega : 201 ≤ n.primeFactors.card)
  nlinarith

/-- The exact error in simultaneously removing ownership and the old
allocation is wrongWeight + boundedShare*weight. -/
def cleanupWeight (u : ℝ) (N n : ℕ) : ℝ :=
  wrongWeight N n+boundedShare (intermediatePrimes u N) N n*weight N n

theorem cleanupWeight_bound {u : ℝ} {N K n : ℕ}
    (hn : n ∈ (fullBand u N K).filter interior) :
    0 ≤ cleanupWeight u N n ∧ cleanupWeight u N n ≤ 600*Real.exp (-(N : ℝ)/3200) := by
  have hb := (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).2
  have hw0 : 0 ≤ wrongWeight N n := Finset.sum_nonneg (fun p _ => markedWeight_nonneg N n p)
  have hw : wrongWeight N n ≤ 400*Real.exp (-(N : ℝ)/1600) := by
    calc
      _ ≤ ∑ _p ∈ n.primeFactors.erase (largestPrime n), 2*Real.exp (-(N : ℝ)/1600) := by
        apply Finset.sum_le_sum
        intro p hp
        obtain ⟨hne,hp⟩ := Finset.mem_erase.mp hp
        exact markedWeight_small_share hb.1 hb.2.1 hp N
          (wrong_owner_share hb.1 hb.2.1 hb.2.2.2.1 hp hne)
      _ ≤ _ := by
        rw [Finset.sum_const, nsmul_eq_mul]
        have hc : (n.primeFactors.erase (largestPrime n)).card ≤ 200 :=
          Finset.card_erase_le.trans (interior_count_le hn)
        have hcR : ((n.primeFactors.erase (largestPrime n)).card : ℝ) ≤ 200 := by exact_mod_cast hc
        nlinarith [Real.exp_pos (-(N : ℝ)/1600)]
  have hnp : ¬n.Prime := by
    intro h
    have hc := hb.2.2.1
    rw [h.primeFactors, Finset.card_singleton] at hc
    omega
  have ha := old_allocation_weight_card (intermediatePrimes u N) hb.1 hb.2.1 hnp hb.2.2.2.1 N
  have hcR : (n.primeFactors.card : ℝ) ≤ 200 := by exact_mod_cast interior_count_le hn
  have he : Real.exp (-(N : ℝ)/1600) ≤ Real.exp (-(N : ℝ)/3200) :=
    Real.exp_le_exp.mpr (by have := Nat.cast_nonneg (α := ℝ) N; linarith)
  refine ⟨add_nonneg hw0 (mul_nonneg (boundedShare_bounds _ _ _).1 (weight_bounds hb.1 hb.2.1 N).1), ?_⟩
  dsimp [cleanupWeight]
  nlinarith [Real.exp_pos (-(N : ℝ)/3200)]

/-- The literal finite raw marked sum on the newly paid interior. -/
def rawInteriorPacket (u y : ℝ) (N K : ℕ) : ℂ :=
  ∑ n ∈ (fullBand u N K).filter interior,
    ((∑ p ∈ n.primeFactors, markedWeight N n p : ℝ) : ℂ)*
      (SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n)

/-- Both cleanup errors keep the coefficient and phase in the same atom. -/
def cleanupError (u y : ℝ) (N K : ℕ) : ℂ :=
  ∑ n ∈ (fullBand u N K).filter interior, (cleanupWeight u N n : ℂ)*
    (SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n*
      zetaPrimeLogKernel N (3/2+Complex.I*y) n)

theorem raw_interior_ledger (u y : ℝ) (N K : ℕ) :
    rawInteriorPacket u y N K = interiorPacket u y N K+cleanupError u y N K := by
  rw [rawInteriorPacket, interiorPacket, cleanupError, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  have hb := (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).2
  rw [incidence_weight_ledger hb.2.2.2.1, atom, residualCoefficient, cleanupWeight]
  push_cast
  ring


/-- An independent source-scale bound for both cleanup errors on the
enlarged least-share interior. It is uniform in the full phase height. -/
theorem cleanupError_bound {u : ℝ} (hu : 0 ≤ u) (hU : u ≤ radiusCeiling)
    (y : ℝ) (N K : ℕ) :
    ‖(u : ℂ)^(N+1)*cleanupError u y N K‖ ≤
      (600*radiusCeiling)*rectangleAllocationRate^N*zetaMoebiusLogMajorantMass (1+1/262144) := by
  have ha (n : ℕ) (hn : n ∈ (fullBand u N K).filter interior) :
      ‖(u : ℂ)^(N+1)*((cleanupWeight u N n : ℂ)*
        (SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n*
          zetaPrimeLogKernel N (3/2+Complex.I*y) n))‖ ≤
        (600*radiusCeiling)*rectangleAllocationRate^N*
          (zetaMoebiusLogMajorant n*zetaPrimeExpWeight (1+1/262144) n) := by
    have hw := cleanupWeight_bound hn
    have hc := SquarefreeVaughanLogSource.norm_coefficient_le (SquarefreeVaughanLogSource.length_pos u N) n
    have hk : ‖zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ ≤
        (131071/262144 : ℝ)⁻¹^N*zetaPrimeExpWeight (1+1/262144) n := by
      convert norm_zetaPrimeLogKernel_le N (3/2+Complex.I*y) n
        (by norm_num : (0 : ℝ) < 131071/262144) using 1
      norm_num
    have he : Real.exp (-(N : ℝ)/3200) = Real.exp (-(1/3200 : ℝ))^N := by
      rw [← Real.exp_nat_mul]; congr 1; ring
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hu,
      norm_mul, Complex.norm_real, Real.norm_of_nonneg hw.1, norm_mul]
    calc
      _ ≤ radiusCeiling^(N+1)*((600*Real.exp (-(N : ℝ)/3200))*
          (zetaMoebiusLogMajorant n*((131071/262144 : ℝ)⁻¹^N*
            zetaPrimeExpWeight (1+1/262144) n))) := by
        gcongr
        · exact mul_nonneg hw.1 (mul_nonneg (norm_nonneg _) (norm_nonneg _))
        · unfold radiusCeiling; positivity
        · exact hw.2
        · exact zetaMoebiusLogMajorant_nonneg n
      _ = _ := by rw [he, rectangleAllocationRate, mul_pow, mul_pow, pow_succ]; ring
  rw [cleanupError, Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ n ∈ (fullBand u N K).filter interior, (600*radiusCeiling)*rectangleAllocationRate^N*
        (zetaMoebiusLogMajorant n*zetaPrimeExpWeight (1+1/262144) n) := Finset.sum_le_sum ha
    _ ≤ _ := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left
        (Summable.sum_le_tsum _ (fun n _ => mul_nonneg (zetaMoebiusLogMajorant_nonneg n)
          (Real.exp_pos _).le) (summable_zetaMoebiusLogMajorant (by norm_num)))
        (mul_nonneg (by unfold radiusCeiling; positivity) (pow_nonneg rectangleAllocationRate_bounds.1 _))

/-- Exact direct-core ledger after both share extensions and cleanup. -/
theorem raw_core_ledger (u y : ℝ) (N K : ℕ) :
    coreResponse u y N K = rawInteriorPacket u y N K+rest u y N K-
      cleanupError u y N K+exteriorPacket u y N K := by
  rw [core_ledger, full_exterior_ledger, raw_interior_ledger]
  ring

theorem tendsto_raw_sub_full {u : ℝ} (hu : 0 ≤ u) (hU : u ≤ radiusCeiling)
    (heights : ℕ → ℝ) (orders counts : ℕ → ℕ) (ho : Tendsto orders atTop atTop) :
    Tendsto (fun t => (u : ℂ)^(orders t+1)*(rawInteriorPacket u (heights t) (orders t) (counts t)-
      fullPacket u (heights t) (orders t) (counts t))) atTop (𝓝 0) := by
  have ht := (((tendsto_pow_atTop_nhds_zero_of_lt_one rectangleAllocationRate_bounds.1
    rectangleAllocationRate_bounds.2).const_mul (600*radiusCeiling)).mul_const
      (zetaMoebiusLogMajorantMass (1+1/262144))).comp ho
  simp only [mul_zero, zero_mul, Function.comp_def] at ht
  have he := squeeze_zero_norm (fun t => cleanupError_bound hu hU (heights t) (orders t) (counts t)) ht
  have h := he.sub (tendsto_full_sub_interior hu hU heights orders counts ho)
  simp only [sub_zero] at h
  convert h using 1
  ext t
  rw [raw_interior_ledger]
  ring

/-- The remaining target is still the literal signed Riesz sum over actual
prime factors, with the full correlated allocation inside each summand. -/
theorem rawInteriorPacket_riesz_expansion (u y : ℝ) (N K : ℕ) :
    rawInteriorPacket u y N K = ∑ n ∈ (fullBand u N K).filter interior,
      (-((N+1 : ℕ) : ℂ)/(SquarefreeVaughanLogSource.length u N : ℂ))*
        (VaughanLogAverage.riesz (SquarefreeVaughanLogSource.length u N) n : ℂ)*
      ∑ p ∈ n.primeFactors, ∑ d ∈ markedAllocations N n p,
        ∏ q ∈ n.primeFactors, zetaPrimeLogKernel (d q) (3/2+Complex.I*y) q := by
  apply Finset.sum_congr rfl
  intro n hn
  have hb := (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).2
  have hnp : ¬n.Prime := by
    intro hp
    have hc := hb.2.2.1
    rw [hp.primeFactors, Finset.card_singleton] at hc
    omega
  have hlog : (Real.log n : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.log_pos (by exact_mod_cast hb.2.1)).ne'
  have hL : (SquarefreeVaughanLogSource.length u N : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (SquarefreeVaughanLogSource.length_pos u N).ne'
  rw [Complex.ofReal_sum, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  rw [show (markedWeight N n p : ℂ)*
      (SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n) =
      SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n*
        ((markedWeight N n p : ℂ)*zetaPrimeLogKernel N (3/2+Complex.I*y) n) by ring,
    marked_kernel hb.1 hb.2.1,
    SquarefreeVaughanLogSource.coefficient, if_pos ⟨hb.1, hnp⟩]
  simp only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_neg]
  field_simp [hlog, hL]

/-- Widen just the radial window, keeping the original nondominant support,
physical primes, exact rectangle and the independently paid share interior.
This is still a finite arithmetic sum, not a continuum completion. -/
def rawRadialBand (u : ℝ) (N K : ℕ) : Finset ℕ :=
  (ZetaRieszDominantAllocation.nondominantBand u N K).filter (fun n =>
    (Squarefree n ∧ 1 < n ∧ 3 ≤ n.primeFactors.card ∧
      largestPrime n ∈ n.primeFactors ∧
      ∀ p ∈ n.primeFactors, p ∈ intermediatePrimes u N) ∧ interior n)

theorem radialBand_core (u : ℝ) (N K : ℕ) :
    LogarithmicDeviation.deviationBand (rawRadialBand u N K) (39/20) (203/100) N =
      (fullBand u N K).filter interior := by
  ext n
  simp only [rawRadialBand, fullBand, coreBand, ZetaRieszTypeII.narrowBand,
    LogarithmicDeviation.deviationBand, Finset.mem_filter]
  constructor
  · rintro ⟨⟨hn,hs,hi⟩,hl,hh⟩
    refine ⟨⟨⟨⟨hn,hl,?_⟩,hl,hh⟩,hs⟩,hi⟩
    have := Nat.cast_nonneg (α := ℝ) N
    linarith
  · rintro ⟨⟨⟨⟨hn,_,_⟩,hl,hh⟩,hs⟩,hi⟩
    exact ⟨⟨hn,hs,hi⟩,hl,hh⟩

/-- The same marked Riesz atoms before the final two radial localizations. -/
def rawRadialPacket (u y : ℝ) (N K : ℕ) : ℂ :=
  ∑ n ∈ rawRadialBand u N K,
    ((∑ p ∈ n.primeFactors, markedWeight N n p : ℝ) : ℂ)*
      (SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n)

/-- Radial completion costs a genuinely geometric arithmetic error. The
constant and rate are uniform in height, count and the source radius.
No modal approximation or cancellation assumption enters this estimate. -/
theorem exists_raw_radial_error :
    ∃ r C : ℝ, 0 ≤ r ∧ r < 1 ∧ 0 ≤ C ∧
      ∀ (N K : ℕ), 21 ≤ N → ∀ (y u : ℝ), 0 ≤ u → u ≤ radiusCeiling →
        ‖(u : ℂ)^(N+1)*(rawRadialPacket u y N K-rawInteriorPacket u y N K)‖ ≤ r^N*C := by
  obtain ⟨r,C,hr0,hr1,hC,h⟩ := ZetaArithmeticDeviationBounds.exists_uniform_deviation_bound
    (1 : Polynomial ℂ) (by norm_num [radiusCeiling])
    (by norm_num : (0 : ℝ) < 39/20) (by norm_num) (by norm_num : (2 : ℝ) < 203/100)
    core_window_costs.1 core_window_costs.2
  refine ⟨r,C,hr0,hr1,hC,?_⟩
  intro N K hN y u hu hU
  have ha (n : ℕ) (hn : n ∈ rawRadialBand u N K) :
      ‖((∑ p ∈ n.primeFactors, markedWeight N n p : ℝ) : ℂ)*
        SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n‖ ≤
          zetaMoebiusLogMajorant n := by
    have hb := (Finset.mem_filter.mp hn).2.1
    have hw : 0 ≤ ∑ p ∈ n.primeFactors, markedWeight N n p :=
      Finset.sum_nonneg (fun p _ => markedWeight_nonneg N n p)
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hw]
    exact (mul_le_of_le_one_left (norm_nonneg _) (marked_mass_le_one hb.1 hb.2.1 N hN)).trans
      (SquarefreeVaughanLogSource.norm_coefficient_le (SquarefreeVaughanLogSource.length_pos u N) n)
  simpa only [rawRadialPacket, rawInteriorPacket, radialBand_core, mul_assoc,
    SquarefreeEulerQuadratic.primeFilterKernel_one, zetaPrimeLogKernel] using
    h N (rawRadialBand u N K) (fun n =>
      ((∑ p ∈ n.primeFactors, markedWeight N n p : ℝ) : ℂ)*
        SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n)
      ha y u hu hU

theorem tendsto_rawRadial_sub_interior {u : ℝ} (hu : 0 ≤ u) (hU : u ≤ radiusCeiling)
    (heights : ℕ → ℝ) (orders counts : ℕ → ℕ) (ho : Tendsto orders atTop atTop) :
    Tendsto (fun t => (u : ℂ)^(orders t+1)*(rawRadialPacket u (heights t) (orders t) (counts t)-
      rawInteriorPacket u (heights t) (orders t) (counts t))) atTop (𝓝 0) := by
  obtain ⟨r,C,hr0,hr1,_,hb⟩ := exists_raw_radial_error
  have ht := ((tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).mul_const C).comp ho
  simp only [zero_mul, Function.comp_def] at ht
  apply squeeze_zero_norm' _ ht
  filter_upwards [ho.eventually (eventually_ge_atTop 21)] with t hN
  exact hb _ _ hN _ _ hu hU

/-- The wider radial sum and the literal joined packet have the same
source-scale asymptotics. This does not assert that either one is small. -/
theorem tendsto_rawRadial_sub_full {u : ℝ} (hu : 0 ≤ u) (hU : u ≤ radiusCeiling)
    (heights : ℕ → ℝ) (orders counts : ℕ → ℕ) (ho : Tendsto orders atTop atTop) :
    Tendsto (fun t => (u : ℂ)^(orders t+1)*(rawRadialPacket u (heights t) (orders t) (counts t)-
      fullPacket u (heights t) (orders t) (counts t))) atTop (𝓝 0) := by
  have h := (tendsto_rawRadial_sub_interior hu hU heights orders counts ho).add
    (tendsto_raw_sub_full hu hU heights orders counts ho)
  simp only [zero_add] at h
  convert h using 1
  ext t
  ring

/-- On the retained interior, sixty-four factors force the least share
below 1/126, using the largest share as well as squarefreeness. -/
theorem high_count_least_share {u : ℝ} {N K n : ℕ}
    (hn : n ∈ (fullBand u N K).filter interior) (hc : 64 ≤ n.primeFactors.card) :
    Real.log n.minFac/Real.log n ≤ 1/126 := by
  have hb := (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).2
  have hi := (Finset.mem_filter.mp hn).2
  have hl : 0 < Real.log n := Real.log_pos (by exact_mod_cast hb.2.1)
  have hp : (1/2 : ℝ)*Real.log n < Real.log (largestPrime n) :=
    (lt_div_iff₀ hl).mp hi.1.1
  have hs : (∑ _p ∈ n.primeFactors.erase (largestPrime n), Real.log n.minFac) ≤
      ∑ p ∈ n.primeFactors.erase (largestPrime n), Real.log p := by
    apply Finset.sum_le_sum
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hp)
    exact Real.log_le_log (by exact_mod_cast (Nat.minFac_prime hb.2.1.ne').pos)
      (by exact_mod_cast (Nat.minFac_le_of_dvd hpp.two_le
        (Nat.dvd_of_mem_primeFactors (Finset.mem_of_mem_erase hp))))
  have he := Finset.sum_erase_add n.primeFactors (fun p : ℕ => Real.log p) hb.2.2.2.1
  rw [← CoprimeEulerPhase.squarefree_log_eq_prime_sum hb.1] at he
  rw [Finset.sum_const, nsmul_eq_mul, Finset.card_erase_of_mem hb.2.2.2.1,
    Nat.cast_sub (by omega : 1 ≤ n.primeFactors.card), Nat.cast_one] at hs
  have hcR : (64 : ℝ) ≤ n.primeFactors.card := by exact_mod_cast hc
  have hmin := Real.log_natCast_nonneg n.minFac
  apply (div_le_iff₀ hl).mpr
  nlinarith

theorem count_tail_tilt :
    Real.log (505/504 : ℝ)-(1/100)*Real.log (5/4) ≤ -(1/5000) := by
  simpa using log_rate_of_power (q := 5/4) (b := 505/504) (c := 1/5000)
    (by norm_num) (by norm_num) 1 100 (by decide) (by norm_num)

/-- All marked incidences retain the least-prime order, so the same
one-coordinate tilt pays each one. No factorial atom is replaced by a phase. -/
theorem markedWeight_least_tail {n : ℕ} (hn : Squarefree n) (hn1 : 1 < n)
    (N p : ℕ) (hsmall : Real.log n.minFac/Real.log n ≤ 1/126) :
    markedWeight N n p ≤ 2*Real.exp (-(N : ℝ)/5000) := by
  let x : ℕ → ℝ := fun q => Real.log q/Real.log n
  have hx (q : ℕ) (_hq : q ∈ n.primeFactors) : 0 ≤ x q :=
    div_nonneg (Real.log_natCast_nonneg _) (Real.log_natCast_nonneg _)
  have hp : n.minFac ∈ n.primeFactors :=
    (Nat.minFac_prime hn1.ne').mem_primeFactors (Nat.minFac_dvd n) hn.ne_zero
  have hw := allocationWeight_nonneg n.primeFactors x hx
  have ht := coordinate_upper_tail n.primeFactors x hx (shares_sum hn hn1) hp
    (a := 1/100) (b := 505/504) (q := 5/4) (c := 1/5000) (D := 2)
    (by norm_num) (by norm_num) (by dsimp [x]; linarith) count_tail_tilt N
  have hsub : markedAllocations N n p ⊆
      (Finset.piAntidiag n.primeFactors (N+1)).filter
        (fun d => (1/100 : ℝ)*N-2 < d n.minFac) := by
    intro d hd
    obtain ⟨ha,hr⟩ := Finset.mem_filter.mp hd
    have h := (Finset.mem_filter.mp hr).2.2.2.2.1
    have hR : (N : ℝ) ≤ 100*((d n.minFac : ℝ)+1) := by exact_mod_cast h
    exact Finset.mem_filter.mpr ⟨ha, by linarith⟩
  apply (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun d _ _ => hw d)).trans
  apply ht.trans
  rw [show (2 : ℝ)*Real.log (5/4) = Real.log ((5/4 : ℝ)^2) by
    rw [Real.log_pow]; norm_num, Real.exp_log (by norm_num)]
  rw [show -(1/5000 : ℝ)*N = -(N : ℝ)/5000 by ring]
  nlinarith [Real.exp_pos (-(N : ℝ)/5000)]

/-- The high-count factorial saving after paying the arithmetic source envelope. -/
def countTailRate : ℝ := radiusCeiling*(131071/262144 : ℝ)⁻¹*Real.exp (-(1/5000))

theorem countTailRate_bounds : 0 ≤ countTailRate ∧ countTailRate < 1 := by
  constructor
  · unfold countTailRate radiusCeiling; positivity
  · have h : radiusCeiling*(131071/262144 : ℝ)⁻¹ < Real.exp (1/5000) :=
      lt_of_lt_of_le (by norm_num [radiusCeiling]) (Real.add_one_le_exp (1/5000))
    simpa only [countTailRate, Real.exp_neg, ← div_eq_mul_inv] using
      (div_lt_one (Real.exp_pos (1/5000))).mpr h

/-- The literal high-count part of the retained signed prime sum. -/
def highCountPacket (u y : ℝ) (N K : ℕ) : ℂ :=
  ∑ n ∈ ((fullBand u N K).filter interior).filter (fun n => 64 ≤ n.primeFactors.card),
    ((∑ p ∈ n.primeFactors, markedWeight N n p : ℝ) : ℂ)*
      (SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n)

/-- Counts 64 and above have an independent geometric arithmetic bound,
uniform in height and in the literal moving count cutoff. -/
theorem highCountPacket_bound {u : ℝ} (hu : 0 ≤ u) (hU : u ≤ radiusCeiling)
    (y : ℝ) (N K : ℕ) :
    ‖(u : ℂ)^(N+1)*highCountPacket u y N K‖ ≤
      (400*radiusCeiling)*countTailRate^N*zetaMoebiusLogMajorantMass (1+1/262144) := by
  have ha (n : ℕ) (hn : n ∈ ((fullBand u N K).filter interior).filter
      (fun n => 64 ≤ n.primeFactors.card)) :
      ‖(u : ℂ)^(N+1)*(((∑ p ∈ n.primeFactors, markedWeight N n p : ℝ) : ℂ)*
        (SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n*
          zetaPrimeLogKernel N (3/2+Complex.I*y) n))‖ ≤
        (400*radiusCeiling)*countTailRate^N*
          (zetaMoebiusLogMajorant n*zetaPrimeExpWeight (1+1/262144) n) := by
    have hi := (Finset.mem_filter.mp hn).1
    have hb := (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).2
    have hsmall := high_count_least_share hi (Finset.mem_filter.mp hn).2
    have hcR : (n.primeFactors.card : ℝ) ≤ 200 := by exact_mod_cast interior_count_le hi
    have hw0 : 0 ≤ ∑ p ∈ n.primeFactors, markedWeight N n p :=
      Finset.sum_nonneg (fun p _ => markedWeight_nonneg N n p)
    have hw : (∑ p ∈ n.primeFactors, markedWeight N n p) ≤
        400*Real.exp (-(N : ℝ)/5000) := by
      have hh := Finset.sum_le_sum (fun p (_hp : p ∈ n.primeFactors) =>
        markedWeight_least_tail hb.1 hb.2.1 N p hsmall)
      simp only [Finset.sum_const, nsmul_eq_mul] at hh
      nlinarith [Real.exp_pos (-(N : ℝ)/5000)]
    have hc := SquarefreeVaughanLogSource.norm_coefficient_le (SquarefreeVaughanLogSource.length_pos u N) n
    have hk : ‖zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ ≤
        (131071/262144 : ℝ)⁻¹^N*zetaPrimeExpWeight (1+1/262144) n := by
      convert norm_zetaPrimeLogKernel_le N (3/2+Complex.I*y) n
        (by norm_num : (0 : ℝ) < 131071/262144) using 1
      norm_num
    have he : Real.exp (-(N : ℝ)/5000) = Real.exp (-(1/5000 : ℝ))^N := by
      rw [← Real.exp_nat_mul]; congr 1; ring
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hu,
      norm_mul, Complex.norm_real, Real.norm_of_nonneg hw0, norm_mul]
    calc
      _ ≤ radiusCeiling^(N+1)*((400*Real.exp (-(N : ℝ)/5000))*
          (zetaMoebiusLogMajorant n*((131071/262144 : ℝ)⁻¹^N*
            zetaPrimeExpWeight (1+1/262144) n))) := by
        gcongr
        all_goals first | exact zetaMoebiusLogMajorant_nonneg n | (unfold radiusCeiling; positivity)
      _ = _ := by rw [he, countTailRate, mul_pow, mul_pow, pow_succ]; ring
  rw [highCountPacket, Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ n ∈ ((fullBand u N K).filter interior).filter (fun n => 64 ≤ n.primeFactors.card),
        (400*radiusCeiling)*countTailRate^N*
          (zetaMoebiusLogMajorant n*zetaPrimeExpWeight (1+1/262144) n) := Finset.sum_le_sum ha
    _ ≤ _ := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left
        (Summable.sum_le_tsum _ (fun n _ => mul_nonneg (zetaMoebiusLogMajorant_nonneg n)
          (Real.exp_pos _).le) (summable_zetaMoebiusLogMajorant (by norm_num)))
        (mul_nonneg (by unfold radiusCeiling; positivity) (pow_nonneg countTailRate_bounds.1 _))

/-- The remaining low-count sum keeps all signs, not separate count allowances. -/
def lowCountPacket (u y : ℝ) (N K : ℕ) : ℂ :=
  ∑ n ∈ ((fullBand u N K).filter interior).filter (fun n => n.primeFactors.card < 64),
    ((∑ p ∈ n.primeFactors, markedWeight N n p : ℝ) : ℂ)*
      (SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n)

theorem count_ledger (u y : ℝ) (N K : ℕ) :
    rawInteriorPacket u y N K = lowCountPacket u y N K+highCountPacket u y N K := by
  simpa only [rawInteriorPacket, lowCountPacket, highCountPacket, not_lt] using
    (Finset.sum_filter_add_sum_filter_not ((fullBand u N K).filter interior)
      (fun n => n.primeFactors.card < 64) (fun n =>
        ((∑ p ∈ n.primeFactors, markedWeight N n p : ℝ) : ℂ)*
          (SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n*
            zetaPrimeLogKernel N (3/2+Complex.I*y) n))).symm

theorem tendsto_highCountPacket {u : ℝ} (hu : 0 ≤ u) (hU : u ≤ radiusCeiling)
    (heights : ℕ → ℝ) (orders counts : ℕ → ℕ) (ho : Tendsto orders atTop atTop) :
    Tendsto (fun t => (u : ℂ)^(orders t+1)*highCountPacket u (heights t) (orders t) (counts t))
      atTop (𝓝 0) := by
  have ht := (((tendsto_pow_atTop_nhds_zero_of_lt_one countTailRate_bounds.1
    countTailRate_bounds.2).const_mul (400*radiusCeiling)).mul_const
      (zetaMoebiusLogMajorantMass (1+1/262144))).comp ho
  simp only [mul_zero, zero_mul, Function.comp_def] at ht
  exact squeeze_zero_norm (fun t => highCountPacket_bound hu hU _ _ _) ht


theorem joint_count_tilt_rate :
    (19/40 : ℝ)*Real.log (341/340)-(1/100)*Real.log (79/68) ≤ -(1/9700) := by
  have hpow : (341/340 : ℝ)^95/(79/68)^2 ≤ 95/97 := by norm_num
  have he : (341/340 : ℝ)^95/(79/68)^2 ≤ Real.exp (-(2/97)) :=
    hpow.trans (by linarith [Real.add_one_le_exp (-(2/97 : ℝ))])
  have hl := Real.log_le_log (by positivity : (0 : ℝ) < (341/340)^95/(79/68)^2) he
  rw [Real.log_div (by positivity) (by positivity), Real.log_pow, Real.log_pow,
    Real.log_exp] at hl
  norm_num at hl
  linarith

theorem prime_least_joint_share {n p : ℕ} (hn : Squarefree n) (hn1 : 1 < n)
    (hp : p ∈ n.primeFactors) (hc : 56 ≤ n.primeFactors.card) :
    Real.log p/Real.log n+55*(Real.log n.minFac/Real.log n) ≤ 1 := by
  have hl : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn1)
  have hs : (∑ _q ∈ n.primeFactors.erase p, Real.log n.minFac) ≤
      ∑ q ∈ n.primeFactors.erase p, Real.log q := by
    apply Finset.sum_le_sum
    intro q hq
    have hqq := Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hq)
    exact Real.log_le_log (by exact_mod_cast (Nat.minFac_prime hn1.ne').pos)
      (by exact_mod_cast (Nat.minFac_le_of_dvd hqq.two_le
        (Nat.dvd_of_mem_primeFactors (Finset.mem_of_mem_erase hq))))
  have he := Finset.sum_erase_add n.primeFactors (fun q : ℕ => Real.log q) hp
  rw [← CoprimeEulerPhase.squarefree_log_eq_prime_sum hn] at he
  rw [Finset.sum_const, nsmul_eq_mul, Finset.card_erase_of_mem hp,
    Nat.cast_sub (by omega : 1 ≤ n.primeFactors.card), Nat.cast_one] at hs
  have hcR : (56 : ℝ) ≤ n.primeFactors.card := by exact_mod_cast hc
  have hm := Real.log_natCast_nonneg n.minFac
  have h : Real.log p+55*Real.log n.minFac ≤ Real.log n := by nlinarith
  calc
    _ = (Real.log p+55*Real.log n.minFac)/Real.log n := by ring
    _ ≤ 1 := (div_le_one hl).mpr h

/-- The least prime cannot simultaneously occupy the large-order slot. -/
theorem markedWeight_least_eq_zero (N n : ℕ) : markedWeight N n n.minFac = 0 := by
  have he : markedAllocations N n n.minFac = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro d hd
    have hr := (Finset.mem_filter.mp (Finset.mem_filter.mp hd).2).2
    omega
  simp [markedWeight, he]

/-- The joint owner/least tilt uses the same correlated factorial allocation.
No signed prime leg is completed or replaced by its norm. -/
theorem markedWeight_joint_count_tail {n p : ℕ} (hn : Squarefree n) (hn1 : 1 < n)
    (hp : p ∈ n.primeFactors) (hc : 56 ≤ n.primeFactors.card) (N : ℕ) :
    markedWeight N n p ≤ 2*Real.exp (-(N : ℝ)/9700) := by
  by_cases hpr : p = n.minFac
  · subst p
    rw [markedWeight_least_eq_zero]
    positivity
  let S := n.primeFactors
  let x : ℕ → ℝ := fun q => Real.log q/Real.log n
  let v : ℕ → ℝ := fun q => if q = p then 341/340 else if q = n.minFac then 79/68 else 1
  let y : ℕ → ℝ := fun q => v q*x q
  have hpS : p ∈ S := hp
  have hr : n.minFac ∈ S :=
    (Nat.minFac_prime hn1.ne').mem_primeFactors (Nat.minFac_dvd n) hn.ne_zero
  have hx (q : ℕ) : 0 ≤ x q := div_nonneg (Real.log_natCast_nonneg _) (Real.log_natCast_nonneg _)
  have hv (q : ℕ) : 0 < v q := by dsimp [v]; split_ifs <;> norm_num
  have hy (q : ℕ) : 0 ≤ y q := mul_nonneg (hv q).le (hx q)
  have hsum : ∑ q ∈ S, x q = 1 := shares_sum hn hn1
  have hbase : ∑ q ∈ S, y q ≤ 341/340 := by
    have hi (q : ℕ) : y q = x q+
        (if q = p then (1/340)*x q else 0)+
        (if q = n.minFac then (11/68)*x q else 0) := by
      dsimp [y,v]
      split_ifs with hq hq'
      · exact False.elim (hpr (hq.symm.trans hq'))
      all_goals ring
    simp_rw [hi]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hsum]
    simp only [Finset.sum_ite_eq', if_pos hpS, if_pos hr]
    have hh := prime_least_joint_share hn hn1 hp hc
    change x p+55*x n.minFac ≤ 1 at hh
    linarith
  have hm (d : ℕ → ℕ) : allocationWeight S y d =
      ((341/340 : ℝ)^(d p)*(79/68 : ℝ)^(d n.minFac))*allocationWeight S x d := by
    have hpv : ∏ q ∈ S, v q^(d q) = (341/340 : ℝ)^(d p)*(79/68 : ℝ)^(d n.minFac) := by
      have hi (q : ℕ) : v q^(d q) =
          (if q = p then (341/340 : ℝ)^(d q) else 1)*
          (if q = n.minFac then (79/68 : ℝ)^(d q) else 1) := by
        dsimp [v]
        split_ifs with hq hq'
        · exact False.elim (hpr (hq.symm.trans hq'))
        all_goals simp
      simp_rw [hi]
      rw [Finset.prod_mul_distrib]
      simp only [Finset.prod_ite_eq', if_pos hpS, if_pos hr]
    simp only [allocationWeight, y, mul_pow, Finset.prod_mul_distrib]
    rw [hpv]
    ring
  let B := Real.exp (-((21/40 : ℝ)*N*Real.log (341/340)+
    ((N : ℝ)/100-1)*Real.log (79/68)))
  have ht (d : ℕ → ℕ) (hd : d ∈ markedAllocations N n p) :
      allocationWeight S x d ≤ B*allocationWeight S y d := by
    have hh := (Finset.mem_filter.mp (Finset.mem_filter.mp hd).2).2
    have hj : (21 : ℝ)*N ≤ 40*d p := by exact_mod_cast hh.2.1
    have hk : (N : ℝ) ≤ 100*((d n.minFac : ℝ)+1) := by exact_mod_cast hh.2.2.2.1
    have hlq : 0 ≤ Real.log (341/340 : ℝ) := Real.log_nonneg (by norm_num)
    have hlr : 0 ≤ Real.log (79/68 : ℝ) := Real.log_nonneg (by norm_num)
    have htilt : 1 ≤ B*((341/340 : ℝ)^(d p)*(79/68 : ℝ)^(d n.minFac)) := by
      rw [show (341/340 : ℝ)^(d p) = Real.exp ((d p : ℝ)*Real.log (341/340)) by
        rw [Real.exp_nat_mul, Real.exp_log (by norm_num)],
        show (79/68 : ℝ)^(d n.minFac) = Real.exp ((d n.minFac : ℝ)*Real.log (79/68)) by
          rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]]
      dsimp [B]
      rw [← Real.exp_add, ← Real.exp_add]
      apply Real.one_le_exp_iff.mpr
      nlinarith [mul_nonneg hlq (show 0 ≤ (d p : ℝ)-(21/40)*N by linarith),
        mul_nonneg hlr (show 0 ≤ (d n.minFac : ℝ)-((N : ℝ)/100-1) by linarith)]
    rw [hm, ← mul_assoc]
    exact le_mul_of_one_le_left (allocationWeight_nonneg S x (fun q _ => hx q) d) htilt
  calc
    _ ≤ ∑ d ∈ markedAllocations N n p, B*allocationWeight S y d := Finset.sum_le_sum ht
    _ ≤ ∑ d ∈ Finset.piAntidiag S (N+1), B*allocationWeight S y d :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun d _ _ => mul_nonneg (Real.exp_pos _).le
          (allocationWeight_nonneg S y (fun q _ => hy q) d))
    _ = B*(∑ q ∈ S, y q)^(N+1) := by
      rw [← Finset.mul_sum]
      congr 1
      exact (Finset.sum_pow_eq_sum_piAntidiag S y (N+1)).symm
    _ ≤ B*(341/340 : ℝ)^(N+1) := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (Finset.sum_nonneg (fun q _ => hy q)) hbase _) (Real.exp_pos _).le
    _ = (341/340 : ℝ)*(79/68)*Real.exp
        (((19/40)*Real.log (341/340)-(1/100)*Real.log (79/68))*N) := by
      dsimp [B]
      rw [show (341/340 : ℝ)^(N+1) = Real.exp (((N+1 : ℕ) : ℝ)*Real.log (341/340)) by
        rw [Real.exp_nat_mul, Real.exp_log (by norm_num)], ← Real.exp_add]
      conv_rhs => rw [← Real.exp_log (by norm_num : (0 : ℝ) < 341/340),
        ← Real.exp_log (by norm_num : (0 : ℝ) < 79/68)]
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      push_cast
      simp only [Real.log_exp]
      ring
    _ ≤ _ := by
      have he := Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_right joint_count_tilt_rate (Nat.cast_nonneg (α := ℝ) N))
      rw [show -(1/9700 : ℝ)*N = -(N : ℝ)/9700 by ring] at he
      exact (mul_le_mul_of_nonneg_left he (by norm_num)).trans
        (mul_le_mul_of_nonneg_right (by norm_num) (Real.exp_pos _).le)


/-- The joint count tilt uses a finer arithmetic majorant exponent.
The rational comparison proves this rate is below one. -/
def jointCountTailRate : ℝ := radiusCeiling*(524287/1048576 : ℝ)⁻¹*Real.exp (-(1/9700))

theorem jointCountTailRate_bounds : 0 ≤ jointCountTailRate ∧ jointCountTailRate < 1 := by
  constructor
  · unfold jointCountTailRate radiusCeiling; positivity
  · have h : radiusCeiling*(524287/1048576 : ℝ)⁻¹ < Real.exp (1/9700) :=
      lt_of_lt_of_le (by norm_num [radiusCeiling]) (Real.add_one_le_exp (1/9700))
    simpa only [jointCountTailRate, Real.exp_neg, ← div_eq_mul_inv] using
      (div_lt_one (Real.exp_pos (1/9700))).mpr h

/-- The improved literal tail, starting at fifty-six prime factors. -/
def jointHighCountPacket (u y : ℝ) (N K : ℕ) : ℂ :=
  ∑ n ∈ ((fullBand u N K).filter interior).filter (fun n => 56 ≤ n.primeFactors.card),
    ((∑ p ∈ n.primeFactors, markedWeight N n p : ℝ) : ℂ)*
      (SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n)

/-- Counts 56 and above have an independent geometric arithmetic bound,
uniform in height and in the literal moving count cutoff. -/
theorem jointHighCountPacket_bound {u : ℝ} (hu : 0 ≤ u) (hU : u ≤ radiusCeiling)
    (y : ℝ) (N K : ℕ) :
    ‖(u : ℂ)^(N+1)*jointHighCountPacket u y N K‖ ≤
      (400*radiusCeiling)*jointCountTailRate^N*zetaMoebiusLogMajorantMass (1+1/1048576) := by
  have ha (n : ℕ) (hn : n ∈ ((fullBand u N K).filter interior).filter
      (fun n => 56 ≤ n.primeFactors.card)) :
      ‖(u : ℂ)^(N+1)*(((∑ p ∈ n.primeFactors, markedWeight N n p : ℝ) : ℂ)*
        (SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n*
          zetaPrimeLogKernel N (3/2+Complex.I*y) n))‖ ≤
        (400*radiusCeiling)*jointCountTailRate^N*
          (zetaMoebiusLogMajorant n*zetaPrimeExpWeight (1+1/1048576) n) := by
    have hi := (Finset.mem_filter.mp hn).1
    have hb := (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).2
    have hcR : (n.primeFactors.card : ℝ) ≤ 200 := by exact_mod_cast interior_count_le hi
    have hw0 : 0 ≤ ∑ p ∈ n.primeFactors, markedWeight N n p :=
      Finset.sum_nonneg (fun p _ => markedWeight_nonneg N n p)
    have hw : (∑ p ∈ n.primeFactors, markedWeight N n p) ≤
        400*Real.exp (-(N : ℝ)/9700) := by
      have hh := Finset.sum_le_sum (fun p (hp : p ∈ n.primeFactors) =>
        markedWeight_joint_count_tail hb.1 hb.2.1 hp (Finset.mem_filter.mp hn).2 N)
      simp only [Finset.sum_const, nsmul_eq_mul] at hh
      nlinarith [Real.exp_pos (-(N : ℝ)/9700)]
    have hc := SquarefreeVaughanLogSource.norm_coefficient_le (SquarefreeVaughanLogSource.length_pos u N) n
    have hk : ‖zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ ≤
        (524287/1048576 : ℝ)⁻¹^N*zetaPrimeExpWeight (1+1/1048576) n := by
      convert norm_zetaPrimeLogKernel_le N (3/2+Complex.I*y) n
        (by norm_num : (0 : ℝ) < 524287/1048576) using 1
      norm_num
    have he : Real.exp (-(N : ℝ)/9700) = Real.exp (-(1/9700 : ℝ))^N := by
      rw [← Real.exp_nat_mul]; congr 1; ring
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hu,
      norm_mul, Complex.norm_real, Real.norm_of_nonneg hw0, norm_mul]
    calc
      _ ≤ radiusCeiling^(N+1)*((400*Real.exp (-(N : ℝ)/9700))*
          (zetaMoebiusLogMajorant n*((524287/1048576 : ℝ)⁻¹^N*
            zetaPrimeExpWeight (1+1/1048576) n))) := by
        gcongr
        all_goals first | exact zetaMoebiusLogMajorant_nonneg n | (unfold radiusCeiling; positivity)
      _ = _ := by rw [he, jointCountTailRate, mul_pow, mul_pow, pow_succ]; ring
  rw [jointHighCountPacket, Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ n ∈ ((fullBand u N K).filter interior).filter (fun n => 56 ≤ n.primeFactors.card),
        (400*radiusCeiling)*jointCountTailRate^N*
          (zetaMoebiusLogMajorant n*zetaPrimeExpWeight (1+1/1048576) n) := Finset.sum_le_sum ha
    _ ≤ _ := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left
        (Summable.sum_le_tsum _ (fun n _ => mul_nonneg (zetaMoebiusLogMajorant_nonneg n)
          (Real.exp_pos _).le) (summable_zetaMoebiusLogMajorant (by norm_num)))
        (mul_nonneg (by unfold radiusCeiling; positivity) (pow_nonneg jointCountTailRate_bounds.1 _))

/-- The remaining low-count sum keeps all signs, not separate count allowances. -/
def jointLowCountPacket (u y : ℝ) (N K : ℕ) : ℂ :=
  ∑ n ∈ ((fullBand u N K).filter interior).filter (fun n => n.primeFactors.card < 56),
    ((∑ p ∈ n.primeFactors, markedWeight N n p : ℝ) : ℂ)*
      (SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n)

theorem joint_count_ledger (u y : ℝ) (N K : ℕ) :
    rawInteriorPacket u y N K = jointLowCountPacket u y N K+jointHighCountPacket u y N K := by
  simpa only [rawInteriorPacket, jointLowCountPacket, jointHighCountPacket, not_lt] using
    (Finset.sum_filter_add_sum_filter_not ((fullBand u N K).filter interior)
      (fun n => n.primeFactors.card < 56) (fun n =>
        ((∑ p ∈ n.primeFactors, markedWeight N n p : ℝ) : ℂ)*
          (SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n*
            zetaPrimeLogKernel N (3/2+Complex.I*y) n))).symm

theorem tendsto_jointHighCountPacket {u : ℝ} (hu : 0 ≤ u) (hU : u ≤ radiusCeiling)
    (heights : ℕ → ℝ) (orders counts : ℕ → ℕ) (ho : Tendsto orders atTop atTop) :
    Tendsto (fun t => (u : ℂ)^(orders t+1)*jointHighCountPacket u (heights t) (orders t) (counts t))
      atTop (𝓝 0) := by
  have ht := (((tendsto_pow_atTop_nhds_zero_of_lt_one jointCountTailRate_bounds.1
    jointCountTailRate_bounds.2).const_mul (400*radiusCeiling)).mul_const
      (zetaMoebiusLogMajorantMass (1+1/1048576))).comp ho
  simp only [mul_zero, zero_mul, Function.comp_def] at ht
  exact squeeze_zero_norm (fun t => jointHighCountPacket_bound hu hU _ _ _) ht

/-- Exact signed reduction of the joined packet to counts three through
fifty-five. Every difference on the right has an independent arithmetic
estimate; this identity does not estimate the remaining low-count sum. -/
theorem full_joint_low_ledger (u y : ℝ) (N K : ℕ) :
    fullPacket u y N K-jointLowCountPacket u y N K =
      jointHighCountPacket u y N K-cleanupError u y N K+exteriorPacket u y N K := by
  have hr := raw_interior_ledger u y N K
  rw [joint_count_ledger] at hr
  rw [full_exterior_ledger]
  linear_combination -hr

/-- All paid errors in the reduction are displayed with their actual
rates. The lower-count signed expression has not been given an allowance. -/
theorem fullPacket_sub_jointLow_bound {u : ℝ} (hu : 0 ≤ u) (hU : u ≤ radiusCeiling)
    (y : ℝ) (N K : ℕ) (hN : 1 ≤ N) :
    ‖(u : ℂ)^(N+1)*(fullPacket u y N K-jointLowCountPacket u y N K)‖ ≤
      (400*radiusCeiling)*jointCountTailRate^N*zetaMoebiusLogMajorantMass (1+1/1048576)+
      (600*radiusCeiling)*rectangleAllocationRate^N*zetaMoebiusLogMajorantMass (1+1/262144)+
      (3*radiusCeiling)*exteriorRate^N*zetaMoebiusLogMajorantMass (1+1/262144) := by
  rw [full_joint_low_ledger, mul_add, mul_sub]
  exact (norm_add_le _ _).trans (add_le_add
    ((norm_sub_le _ _).trans (add_le_add (jointHighCountPacket_bound hu hU y N K)
      (cleanupError_bound hu hU y N K))) (exteriorPacket_bound hu hU y N K hN))

theorem tendsto_full_sub_jointLow {u : ℝ} (hu : 0 ≤ u) (hU : u ≤ radiusCeiling)
    (heights : ℕ → ℝ) (orders counts : ℕ → ℕ) (ho : Tendsto orders atTop atTop) :
    Tendsto (fun t => (u : ℂ)^(orders t+1)*(fullPacket u (heights t) (orders t) (counts t)-
      jointLowCountPacket u (heights t) (orders t) (counts t))) atTop (𝓝 0) := by
  have h := (tendsto_jointHighCountPacket hu hU heights orders counts ho).sub
    (tendsto_raw_sub_full hu hU heights orders counts ho)
  simp only [sub_zero] at h
  convert h using 1
  ext t
  rw [joint_count_ledger]
  ring

/-- The wider radial target has exactly the same source asymptotics as
the explicit signed three-through-fifty-five-prime sum. -/
theorem tendsto_rawRadial_sub_jointLow {u : ℝ} (hu : 0 ≤ u) (hU : u ≤ radiusCeiling)
    (heights : ℕ → ℝ) (orders counts : ℕ → ℕ) (ho : Tendsto orders atTop atTop) :
    Tendsto (fun t => (u : ℂ)^(orders t+1)*(rawRadialPacket u (heights t) (orders t) (counts t)-
      jointLowCountPacket u (heights t) (orders t) (counts t))) atTop (𝓝 0) := by
  have h := (tendsto_rawRadial_sub_full hu hU heights orders counts ho).add
    (tendsto_full_sub_jointLow hu hU heights orders counts ho)
  simp only [zero_add] at h
  convert h using 1
  ext t
  ring

end
end RiemannGaussian.ZetaRieszLeastBoundary
