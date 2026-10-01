/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszClippedOwnerPeriodFloor
import RiemannGaussian.ZetaRieszReducedCountPayment

/-!
# Global payment of prime periods clipped by the current radial endpoints

Both fixed-width endpoint layers of the CURRENT signed floor carrier are
independently source-geometric, across every count, allocation and retained
divisor mask. Only these exterior layers are norm-paid; the central signed
main remains untouched.
-/

noncomputable section
open Filter Topology Real
open scoped BigOperators Classical ArithmeticFunction.Moebius
namespace RiemannGaussian.ZetaRieszRadialPeriodPayment
open ZetaRieszLowerRadialPayment ZetaRieszPrimeEndpoint ZetaRieszParityPacket
open ZetaRieszSignedConvolution ZetaRieszUnsignedDivisorError ZetaRieszShortDivisorOrbits
open ZetaRieszHingeAllocationPayment ZetaRieszReducedCountPayment ZetaRieszPrimeCountFrequency

/-- A fixed explicit saving for both literal endpoint layers. -/
def edgeRate : ℝ := exp (-(1/1000000 : ℝ))

theorem edgeRate_bounds : 0 < edgeRate ∧ edgeRate < 1 := by
  exact ⟨exp_pos _,exp_lt_one_iff.mpr (by norm_num [edgeRate])⟩

/-- Exact rational power certification of the enlarged lower endpoint.
The exploratory floating exponent is not used in Lean. -/
theorem lower_log_certificate :
    log (ZetaRieszWideOwnerAudit.radiusCeiling*(1971/1000)) ≤ -(14505/1000000 : ℝ) := by
  have hq : (0 : ℝ)<99985495/100000000 := by norm_num
  have hp : ZetaRieszWideOwnerAudit.radiusCeiling*(1971/1000) ≤
      (99985495/100000000 : ℝ)^100 := by
    norm_num [ZetaRieszWideOwnerAudit.radiusCeiling]
  have hh := log_le_log
    (by norm_num [ZetaRieszWideOwnerAudit.radiusCeiling] :
      (0 : ℝ)<ZetaRieszWideOwnerAudit.radiusCeiling*(1971/1000)) hp
  rw [log_pow] at hh
  have hl := log_le_sub_one_of_pos hq
  nlinarith only [hh,hl]

/-- The current upper endpoint admits the SAME explicit saving. -/
theorem upper_log_certificate :
    log (ZetaRieszWideOwnerAudit.radiusCeiling*(2029/1000)) ≤ (14497/1000000 : ℝ) := by
  have hq : (0 : ℝ)<100014497/100000000 := by norm_num
  have hp : ZetaRieszWideOwnerAudit.radiusCeiling*(2029/1000) ≤
      (100014497/100000000 : ℝ)^100 := by
    norm_num [ZetaRieszWideOwnerAudit.radiusCeiling]
  have hh := log_le_log
    (by norm_num [ZetaRieszWideOwnerAudit.radiusCeiling] :
      (0 : ℝ)<ZetaRieszWideOwnerAudit.radiusCeiling*(2029/1000)) hp
  rw [log_pow] at hh
  have hl := log_le_sub_one_of_pos hq
  nlinarith only [hh,hl]

theorem normalized_lower_rate {u : ℝ}
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) :
    u*zetaLogMomentRate (3/2-referenceExponent) (1971/1000) ≤ edgeRate := by
  have hlog : log (ZetaRieszWideOwnerAudit.radiusCeiling*(1971/1000))+
      (1-(3/2-referenceExponent)*(1971/1000)) ≤ -(1/1000000 : ℝ) := by
    have h := lower_log_certificate
    norm_num [referenceExponent] at *
    linarith
  have he := exp_le_exp.mpr hlog
  rw [exp_add,exp_log (by norm_num [ZetaRieszWideOwnerAudit.radiusCeiling] :
    (0 : ℝ)<ZetaRieszWideOwnerAudit.radiusCeiling*(1971/1000))] at he
  calc
    _ ≤ ZetaRieszWideOwnerAudit.radiusCeiling*
        zetaLogMomentRate (3/2-referenceExponent) (1971/1000) :=
      mul_le_mul_of_nonneg_right hU (by unfold zetaLogMomentRate; positivity)
    _ ≤ _ := by simpa only [zetaLogMomentRate,edgeRate,mul_assoc] using he

theorem normalized_upper_rate {u : ℝ}
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) :
    u*zetaLogMomentRate (3/2-referenceExponent) (2029/1000) ≤ edgeRate := by
  have hlog : log (ZetaRieszWideOwnerAudit.radiusCeiling*(2029/1000))+
      (1-(3/2-referenceExponent)*(2029/1000)) ≤ -(1/1000000 : ℝ) := by
    have h := upper_log_certificate
    norm_num [referenceExponent] at *
    linarith
  have he := exp_le_exp.mpr hlog
  rw [exp_add,exp_log (by norm_num [ZetaRieszWideOwnerAudit.radiusCeiling] :
    (0 : ℝ)<ZetaRieszWideOwnerAudit.radiusCeiling*(2029/1000))] at he
  calc
    _ ≤ ZetaRieszWideOwnerAudit.radiusCeiling*
        zetaLogMomentRate (3/2-referenceExponent) (2029/1000) :=
      mul_le_mul_of_nonneg_right hU (by unfold zetaLogMomentRate; positivity)
    _ ≤ _ := by simpa only [zetaLogMomentRate,edgeRate,mul_assoc] using he

/-- One independent bound for arbitrary dominated lower-edge selections. -/
theorem norm_lower_edge_sum_bound (S : Finset ℕ) (c : ℕ → ℂ) {H u : ℝ}
    (hH : 0 ≤ H) (hu : 0 ≤ u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (N : ℕ) (y : ℝ)
    (hc : ∀ n ∈ S, ‖c n‖ ≤ H*zetaMoebiusLogMajorant n)
    (hS : ∀ n ∈ S, log n ≤ (1971/1000 : ℝ)*N) :
    ‖(u : ℂ)^(N+1)*∑ n ∈ S, c n*zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ ≤
      H*ZetaRieszWideOwnerAudit.radiusCeiling*
        zetaMoebiusLogMajorantMass referenceExponent*edgeRate^N := by
  have hker n (hn : n ∈ S) := norm_zetaPrimeLogKernel_le_lower_chernoff
    N 0 n (3/2+Complex.I*y) (τ := referenceExponent) (by norm_num : (0 : ℝ)<1971/1000)
    (by norm_num [referenceExponent] :
      ((3/2+Complex.I*(y : ℂ)).re-referenceExponent)*(1971/1000) ≤ 1) (hS n hn)
  have hs := summable_zetaMoebiusLogMajorant
    (by norm_num [referenceExponent] : (1 : ℝ)<referenceExponent)
  have hmass : (∑ n ∈ S, zetaMoebiusLogMajorant n*zetaPrimeExpWeight referenceExponent n) ≤
      zetaMoebiusLogMajorantMass referenceExponent := by
    exact hs.sum_le_tsum S (fun n _ =>
      mul_nonneg (zetaMoebiusLogMajorant_nonneg n) (exp_pos _).le)
  have hsum : ‖∑ n ∈ S, c n*zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ ≤
      H*(zetaLogMomentRate (3/2-referenceExponent) (1971/1000))^N*
        zetaMoebiusLogMajorantMass referenceExponent := by
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ n ∈ S, H*zetaMoebiusLogMajorant n*
          ((zetaLogMomentRate (3/2-referenceExponent) (1971/1000))^N*
            zetaPrimeExpWeight referenceExponent n) := by
        apply Finset.sum_le_sum
        intro n hn
        rw [norm_mul]
        exact mul_le_mul (hc n hn) (by simpa using hker n hn)
          (norm_nonneg _) (mul_nonneg hH (zetaMoebiusLogMajorant_nonneg n))
      _ = H*(zetaLogMomentRate (3/2-referenceExponent) (1971/1000))^N*
          ∑ n ∈ S, zetaMoebiusLogMajorant n*zetaPrimeExpWeight referenceExponent n := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n _
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hmass (by
        unfold zetaLogMomentRate
        positivity)
  rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hu]
  apply (mul_le_mul_of_nonneg_left hsum (pow_nonneg hu _)).trans
  have hr := pow_le_pow_left₀ (by unfold zetaLogMomentRate; positivity :
    0 ≤ u*zetaLogMomentRate (3/2-referenceExponent) (1971/1000))
    (normalized_lower_rate hU) N
  have hm := mul_le_mul hU hr (pow_nonneg (by unfold zetaLogMomentRate; positivity) N)
    (by norm_num [ZetaRieszWideOwnerAudit.radiusCeiling] :
      0 ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
  have hf := mul_le_mul_of_nonneg_left hm
    (mul_nonneg hH (zetaMoebiusLogMajorantMass_nonneg referenceExponent))
  convert hf using 1
  · rw [pow_succ,mul_pow]
    ring
  · ring

/-- The upper-edge payment retains every original phase and selection. -/
theorem norm_upper_edge_sum_bound (S : Finset ℕ) (c : ℕ → ℂ) {H u : ℝ}
    (hH : 0 ≤ H) (hu : 0 ≤ u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (N : ℕ) (y : ℝ)
    (hc : ∀ n ∈ S, ‖c n‖ ≤ H*zetaMoebiusLogMajorant n)
    (hS : ∀ n ∈ S, (2029/1000 : ℝ)*N ≤ log n) :
    ‖(u : ℂ)^(N+1)*∑ n ∈ S, c n*zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ ≤
      H*ZetaRieszWideOwnerAudit.radiusCeiling*
        zetaMoebiusLogMajorantMass referenceExponent*edgeRate^N := by
  have hker n (hn : n ∈ S) := norm_zetaPrimeLogKernel_le_upper_chernoff
    N 0 n (3/2+Complex.I*y) (τ := referenceExponent) (by norm_num : (0 : ℝ)<2029/1000)
    (by norm_num [referenceExponent] :
      1 ≤ ((3/2+Complex.I*(y : ℂ)).re-referenceExponent)*(2029/1000)) (hS n hn)
  have hs := summable_zetaMoebiusLogMajorant
    (by norm_num [referenceExponent] : (1 : ℝ)<referenceExponent)
  have hmass : (∑ n ∈ S, zetaMoebiusLogMajorant n*zetaPrimeExpWeight referenceExponent n) ≤
      zetaMoebiusLogMajorantMass referenceExponent := by
    exact hs.sum_le_tsum S (fun n _ =>
      mul_nonneg (zetaMoebiusLogMajorant_nonneg n) (exp_pos _).le)
  have hsum : ‖∑ n ∈ S, c n*zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ ≤
      H*(zetaLogMomentRate (3/2-referenceExponent) (2029/1000))^N*
        zetaMoebiusLogMajorantMass referenceExponent := by
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ n ∈ S, H*zetaMoebiusLogMajorant n*
          ((zetaLogMomentRate (3/2-referenceExponent) (2029/1000))^N*
            zetaPrimeExpWeight referenceExponent n) := by
        apply Finset.sum_le_sum
        intro n hn
        rw [norm_mul]
        exact mul_le_mul (hc n hn) (by simpa using hker n hn)
          (norm_nonneg _) (mul_nonneg hH (zetaMoebiusLogMajorant_nonneg n))
      _ = H*(zetaLogMomentRate (3/2-referenceExponent) (2029/1000))^N*
          ∑ n ∈ S, zetaMoebiusLogMajorant n*zetaPrimeExpWeight referenceExponent n := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n _
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hmass (by
        unfold zetaLogMomentRate
        positivity)
  rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hu]
  apply (mul_le_mul_of_nonneg_left hsum (pow_nonneg hu _)).trans
  have hr := pow_le_pow_left₀ (by unfold zetaLogMomentRate; positivity :
    0 ≤ u*zetaLogMomentRate (3/2-referenceExponent) (2029/1000))
    (normalized_upper_rate hU) N
  have hm := mul_le_mul hU hr (pow_nonneg (by unfold zetaLogMomentRate; positivity) N)
    (by norm_num [ZetaRieszWideOwnerAudit.radiusCeiling] :
      0 ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
  have hf := mul_le_mul_of_nonneg_left hm
    (mul_nonneg hH (zetaMoebiusLogMajorantMass_nonneg referenceExponent))
  convert hf using 1
  · rw [pow_succ,mul_pow]
    ring
  · ring

/-- Both dominated edge populations are paid jointly at ONE explicit
rate, with no upper bound on their prime count or changing coefficient masks. -/
theorem norm_edges_sum_bound (S : Finset ℕ) (c : ℕ → ℂ) {H u : ℝ}
    (hH : 0 ≤ H) (hu : 0 ≤ u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (N : ℕ) (y : ℝ)
    (hc : ∀ n ∈ S, ‖c n‖ ≤ H*zetaMoebiusLogMajorant n)
    (hS : ∀ n ∈ S, log n ≤ (1971/1000 : ℝ)*N ∨ (2029/1000 : ℝ)*N ≤ log n) :
    ‖(u : ℂ)^(N+1)*∑ n ∈ S, c n*zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ ≤
      2*H*ZetaRieszWideOwnerAudit.radiusCeiling*
        zetaMoebiusLogMajorantMass referenceExponent*edgeRate^N := by
  let B := S.filter (fun n : ℕ => log n ≤ (1971/1000 : ℝ)*N)
  have hB : B ⊆ S := Finset.filter_subset _ _
  have hlo := norm_lower_edge_sum_bound B c hH hu hU N y
    (fun n hn => hc n (hB hn)) (fun n hn => (Finset.mem_filter.mp hn).2)
  have hhi := norm_upper_edge_sum_bound (S\B) c hH hu hU N y
    (fun n hn => hc n (Finset.mem_sdiff.mp hn).1) (by
      intro n hn
      obtain ⟨hn,hnB⟩ := Finset.mem_sdiff.mp hn
      exact (hS n hn).resolve_left (fun hh => hnB (Finset.mem_filter.mpr ⟨hn,hh⟩)))
  have he := Finset.sum_sdiff hB (f := fun n =>
    c n*zetaPrimeLogKernel N (3/2+Complex.I*y) n)
  rw [← he,mul_add]
  exact (norm_add_le _ _).trans ((add_le_add hhi hlo).trans_eq (by ring))

/-- A fixed-width layer at either current radial endpoint lies inside
the exactly certified slightly enlarged edge region. -/
theorem edge_geometry {N : ℕ} (hN : 1000 ≤ N) {T : ℝ}
    (hT : T ≤ (197/100 : ℝ)*N+1 ∨ (203/100 : ℝ)*N-1 ≤ T) :
    T ≤ (1971/1000 : ℝ)*N ∨ (2029/1000 : ℝ)*N ≤ T := by
  have hNR : (1000 : ℝ) ≤ N := by exact_mod_cast hN
  rcases hT with hT | hT
  · exact Or.inl (by linarith)
  · exact Or.inr (by linarith)

/-- The phase period is shorter than the paid fixed-width radial buffer.
The height is the original actual height, not a frozen phase surrogate. -/
theorem period_width_le {y : ℝ} (hy : 54 ≤ y) :
    2*Real.pi/y ≤ 1/8 := by
  have hy0 : 0 < y := by linarith
  apply (div_le_iff₀ hy0).mpr
  nlinarith [Real.pi_lt_d4]

/-- A retained label away from the two paid endpoint buffers has its
ENTIRE total-log phase period inside the same central radial window. -/
theorem whole_period_central {N : ℕ} {y v T T' : ℝ} (hy : 54 ≤ y)
    (hT : (197/100 : ℝ)*N+1 < T ∧ T < (203/100 : ℝ)*N-1)
    (hv : v-Real.pi/y < T ∧ T ≤ v+Real.pi/y)
    (hv' : v-Real.pi/y < T' ∧ T' ≤ v+Real.pi/y) :
    (197/100 : ℝ)*N < T' ∧ T' ≤ (203/100 : ℝ)*N := by
  have hp := period_width_le hy
  have he : 2*Real.pi/y=2*(Real.pi/y) := by ring
  rw [he] at hp
  constructor <;> linarith [hT.1,hT.2,hv.1,hv.2,hv'.1,hv'.2]

/-- Only a subset mask of the CURRENT central physical population.
It is not a new scalar carrier or completion. -/
def periodEdgeLabels (u : ℝ) (N K : ℕ) : Finset ℕ :=
  (((coreBand u N K).filter (fun n : ℕ => (197/100 : ℝ)*N<log n)).filter Squarefree).filter
    (fun n => log n ≤ (197/100 : ℝ)*N+1 ∨ (203/100 : ℝ)*N-1 ≤ log n)

/-- One source-geometric price for both original endpoint layers. -/
def edgeBudget (N : ℕ) : ℝ :=
  4*ZetaRieszWideOwnerAudit.radiusCeiling*
    zetaMoebiusLogMajorantMass referenceExponent*edgeRate^N

theorem tendsto_edgeBudget : Tendsto edgeBudget atTop (𝓝 0) := by
  have hh := (tendsto_pow_atTop_nhds_zero_of_lt_one edgeRate_bounds.1.le
    edgeRate_bounds.2).const_mul
      (4*ZetaRieszWideOwnerAudit.radiusCeiling*zetaMoebiusLogMajorantMass referenceExponent)
  change Tendsto (fun N : ℕ => 4*ZetaRieszWideOwnerAudit.radiusCeiling*
    zetaMoebiusLogMajorantMass referenceExponent*edgeRate^N) atTop (𝓝 0)
  simpa only [mul_zero] using hh

/-- Actual selected original owner-divisor incidences on both radial
edge layers are paid globally. All counts, arbitrary retained divisor
submasks and label-dependent allocations stay inside the literal sum. -/
theorem norm_literal_period_edge_sum_bound (S : Finset ℕ) (A : ℕ → Finset ℕ)
    (D : ℕ → Finset (ℕ×ℕ)) (N K : ℕ) {u : ℝ}
    (hu : 0 ≤ u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hN : 1000 ≤ N) (hS : S ⊆ periodEdgeLabels u N K)
    (hL : (11/8 : ℝ)*N ≤ SquarefreeVaughanLogSource.length u N)
    (hD : ∀ n ∈ S, D n ⊆ (n/largestPrime n).divisorsAntidiagonal) (y : ℝ) :
    ‖(u : ℂ)^(N+1)*∑ n ∈ S,
      partialCoefficient (A n) (SquarefreeVaughanLogSource.length u N) N
        (largestPrime n) (n/largestPrime n) (D n)*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ ≤ edgeBudget N := by
  unfold edgeBudget
  rw [show (4 : ℝ)=2*2 by norm_num]
  apply norm_edges_sum_bound S _ (by norm_num : (0 : ℝ) ≤ 2) hu hU N y
  · intro n hn
    obtain ⟨hnc,hT⟩ := Finset.mem_filter.mp (hS hn)
    obtain ⟨hnc,hs⟩ := Finset.mem_filter.mp hnc
    have hc := (Finset.mem_filter.mp hnc).1
    have hg := ZetaRieszClippedOwnerPeriodFloor.canonical_owner_data hs
      (ZetaRieszJointPrimeEnergy.core_count hc)
    have hprod := hg.2.1
    have hp0 := hg.1.pos
    have ha0 := Nat.pos_of_ne_zero hg.2.2.1.ne_zero
    have hlog := (central_log_bounds hnc).2
    have hT2 : log n ≤ 2*SquarefreeVaughanLogSource.length u N := by
      nlinarith [Nat.cast_nonneg (α := ℝ) N]
    have hb := partialCoefficient_bound (A n) N hp0 ha0 (D n) (hD n hn)
      (SquarefreeVaughanLogSource.length_pos u N)
      (by simpa only [hprod] using hT2)
    simpa only [hprod] using hb
  · intro n hn
    exact edge_geometry hN (Finset.mem_filter.mp (hS hn)).2

/-- Exact crop of ANY original coefficient population. Its intersection
with the actual endpoint layers is paid; everything else is retained. -/
theorem norm_period_edge_crop_bound (S : Finset ℕ) (A : ℕ → Finset ℕ)
    (D : ℕ → Finset (ℕ×ℕ)) (N K : ℕ) {u : ℝ}
    (hu : 0 ≤ u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hN : 1000 ≤ N) (hL : (11/8 : ℝ)*N ≤ SquarefreeVaughanLogSource.length u N)
    (hD : ∀ n ∈ S, D n ⊆ (n/largestPrime n).divisorsAntidiagonal) (y : ℝ) :
    ‖(u : ℂ)^(N+1)*((∑ n ∈ S,
      partialCoefficient (A n) (SquarefreeVaughanLogSource.length u N) N
        (largestPrime n) (n/largestPrime n) (D n)*zetaPrimeLogKernel N (3/2+Complex.I*y) n)-
      ∑ n ∈ S\periodEdgeLabels u N K,
        partialCoefficient (A n) (SquarefreeVaughanLogSource.length u N) N
          (largestPrime n) (n/largestPrime n) (D n)*zetaPrimeLogKernel N (3/2+Complex.I*y) n)‖ ≤
        edgeBudget N := by
  let B := S ∩ periodEdgeLabels u N K
  have hb := norm_literal_period_edge_sum_bound B A D N K hu hU hN
    Finset.inter_subset_right hL (fun n hn => hD n (Finset.mem_inter.mp hn).1) y
  have he := Finset.sum_sdiff (show B ⊆ S from Finset.inter_subset_left)
    (f := fun n => partialCoefficient (A n) (SquarefreeVaughanLogSource.length u N) N
      (largestPrime n) (n/largestPrime n) (D n)*zetaPrimeLogKernel N (3/2+Complex.I*y) n)
  have hs : S\B=S\periodEdgeLabels u N K := by
    ext n
    simp only [B,Finset.mem_sdiff,Finset.mem_inter]
    tauto
  rw [hs] at he
  rw [← he,add_sub_cancel_left]
  exact hb

/-- The same GLOBAL payment acts directly on the literal retained
incidence sum, not on a surrogate whole coefficient or a completed row. -/
theorem norm_retained_period_edge_crop_bound (S : Finset ℕ) (A : ℕ → Finset ℕ)
    (D : ℕ → Finset (ℕ×ℕ)) (N K : ℕ) {u : ℝ}
    (hu : 0 ≤ u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hN : 1000 ≤ N)
    (hS : S ⊆ ((coreBand u N K).filter
      (fun n : ℕ => (197/100 : ℝ)*N<log n)).filter Squarefree)
    (hL : (11/8 : ℝ)*N ≤ SquarefreeVaughanLogSource.length u N)
    (hD : ∀ n ∈ S, D n ⊆ (n/largestPrime n).divisorsAntidiagonal) (y : ℝ) :
    let f := fun n => ∑ db ∈ D n,
      phaseWeight (A n) (SquarefreeVaughanLogSource.length u N) N y
        (n/largestPrime n) (largestPrime n)*(μ db.2 : ℂ)*
          (pairHinge (SquarefreeVaughanLogSource.length u N) (largestPrime n) db.2 : ℂ);
    ‖(u : ℂ)^(N+1)*((∑ n ∈ S, f n)-
      ∑ n ∈ S\periodEdgeLabels u N K, f n)‖ ≤ edgeBudget N := by
  dsimp only
  have hb := norm_period_edge_crop_bound S A D N K hu hU hN hL hD y
  have hf n (hn : n ∈ S) :
      partialCoefficient (A n) (SquarefreeVaughanLogSource.length u N) N
        (largestPrime n) (n/largestPrime n) (D n)*zetaPrimeLogKernel N (3/2+Complex.I*y) n=
      ∑ db ∈ D n, phaseWeight (A n) (SquarefreeVaughanLogSource.length u N) N y
        (n/largestPrime n) (largestPrime n)*(μ db.2 : ℂ)*
          (pairHinge (SquarefreeVaughanLogSource.length u N) (largestPrime n) db.2 : ℂ) := by
    obtain ⟨hnc,hs⟩ := Finset.mem_filter.mp (hS hn)
    have hc := (Finset.mem_filter.mp hnc).1
    have hg := ZetaRieszClippedOwnerPeriodFloor.canonical_owner_data hs
      (ZetaRieszJointPrimeEnergy.core_count hc)
    have he := partial_atom_eq_original_incidences (A n)
      (SquarefreeVaughanLogSource.length u N) N (largestPrime n) (n/largestPrime n) (D n) y
    rw [hg.2.1] at he
    exact he
  have h₁ := Finset.sum_congr rfl hf
  have h₂ := Finset.sum_congr rfl (fun n (hn : n ∈ S\periodEdgeLabels u N K) =>
    hf n (Finset.mem_sdiff.mp hn).1)
  rwa [h₁,h₂] at hb

/-- The unpaid inner population has a full radial phase period available
around every retained label. This does not fill other prime masks. -/
theorem retained_radial_period_interior {u : ℝ} {N K n : ℕ}
    (hn : n ∈ (((coreBand u N K).filter
      (fun n : ℕ => (197/100 : ℝ)*N<log n)).filter Squarefree)\periodEdgeLabels u N K) :
    (197/100 : ℝ)*N+1 < log n ∧ log n < (203/100 : ℝ)*N-1 := by
  obtain ⟨hn,hnot⟩ := Finset.mem_sdiff.mp hn
  have hh : ¬(log n ≤ (197/100 : ℝ)*N+1 ∨ (203/100 : ℝ)*N-1 ≤ log n) := by
    intro h
    exact hnot (Finset.mem_filter.mpr ⟨hn,h⟩)
  push Not at hh
  exact hh

/-- Concrete whole-floor-ledger saving: the exact unpaid main now omits
BOTH radial period clips at one source-geometric cost. Old allocation/count
payments and every prior credit are unchanged and subtracted once. -/
theorem eventually_remaining_period_interior_bounds {u : ℝ} (hu : 1/2<u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (y : ℝ) :
    ∀ᶠ j : ℕ in atTop,
    let N := dyadicMomentOrder j
    let K := dyadicPrimeCount j
    let C := ((coreBand u N K).filter (fun n : ℕ => (197/100 : ℝ)*N<log n)).filter Squarefree
    let D := fun n => (n/largestPrime n).divisorsAntidiagonal \
      (cancelledOrbitDivisors u N n ∪ ZetaRieszCrossingOrbitCancellation.affineDivisors u N n)
    let U := (∑ n ∈ (C\reducedCountLabels u N K)\periodEdgeLabels u N K, ∑ db ∈ D n,
      phaseWeight (if n ∈ hingeLabels u N K then ∅ else
        ZetaRieszAnnulusJoint.intermediatePrimes u N ∩ {largestPrime n})
        (SquarefreeVaughanLogSource.length u N) N y (n/largestPrime n) (largestPrime n)*
          (μ db.2 : ℂ)*(pairHinge (SquarefreeVaughanLogSource.length u N) (largestPrime n) db.2 : ℂ)).re-
      (ZetaRieszUnifiedSignedRows.largeOwnerIncidences u y N K).re-
      (ZetaRieszOwnerGapRows.ownerGapLiteralRows u y j+ZetaRieszOwnerGapRows.ownerGapEndpointRows u y j)-
      ZetaRieszPolynomialCutoffRows.literalCutoffPacket u y j
    let E := (503/500 : ℝ)*zetaMoebiusLogMajorantMass (2049/2048)*hingeAllocationRate^N+
      ((203/50 : ℝ)*(10001/20000))*((N : ℝ)+1)*paidCountRate^N+edgeBudget N;
    u^(N+1)*U-E ≤ u^(N+1)*ZetaRieszPolynomialCutoffRows.polynomialCentralRemaining u y j ∧
      u^(N+1)*ZetaRieszPolynomialCutoffRows.polynomialCentralRemaining u y j ≤ u^(N+1)*U+E := by
  have hlen := ZetaRieszLowerDegreeBounds.eventually_length_ge_exponent
    (by linarith : 0<u) (by norm_num : (0 : ℝ)≤11/16)
    (hU.trans_lt ZetaRieszWideOwnerAudit.radius_lt_source)
  filter_upwards [eventually_remaining_reducedCount_bounds hu hU y,
    tendsto_dyadicMomentOrder.eventually hlen,
    tendsto_dyadicMomentOrder.eventually (eventually_ge_atTop (1000 : ℕ))]
    with j hold hLN hN
  let N := dyadicMomentOrder j
  let K := dyadicPrimeCount j
  let C := ((coreBand u N K).filter (fun n : ℕ => (197/100 : ℝ)*N<log n)).filter Squarefree
  let D := fun n => (n/largestPrime n).divisorsAntidiagonal \
    (cancelledOrbitDivisors u N n ∪ ZetaRieszCrossingOrbitCancellation.affineDivisors u N n)
  let A := fun n => if n ∈ hingeLabels u N K then ∅ else
    ZetaRieszAnnulusJoint.intermediatePrimes u N ∩ {largestPrime n}
  let f := fun n => ∑ db ∈ D n, phaseWeight (A n) (SquarefreeVaughanLogSource.length u N)
    N y (n/largestPrime n) (largestPrime n)*(μ db.2 : ℂ)*
      (pairHinge (SquarefreeVaughanLogSource.length u N) (largestPrime n) db.2 : ℂ)
  let B := (ZetaRieszUnifiedSignedRows.largeOwnerIncidences u y N K).re+
    (ZetaRieszOwnerGapRows.ownerGapLiteralRows u y j+ZetaRieszOwnerGapRows.ownerGapEndpointRows u y j)+
    ZetaRieszPolynomialCutoffRows.literalCutoffPacket u y j
  let E₀ := (503/500 : ℝ)*zetaMoebiusLogMajorantMass (2049/2048)*hingeAllocationRate^N+
    ((203/50 : ℝ)*(10001/20000))*((N : ℝ)+1)*paidCountRate^N
  have hL : (11/8 : ℝ)*N ≤ SquarefreeVaughanLogSource.length u N := by
    dsimp [N]
    nlinarith only [hLN]
  have hb := norm_retained_period_edge_crop_bound (C\reducedCountLabels u N K)
    A D N K (by linarith : 0≤u) hU hN Finset.sdiff_subset hL
      (fun _ _ => Finset.sdiff_subset) y
  change ‖(u : ℂ)^(N+1)*((∑ n ∈ C\reducedCountLabels u N K, f n)-
    ∑ n ∈ (C\reducedCountLabels u N K)\periodEdgeLabels u N K, f n)‖ ≤ edgeBudget N at hb
  have hr := abs_le.mp ((Complex.abs_re_le_norm _).trans hb)
  rw [← Complex.ofReal_pow,Complex.re_ofReal_mul] at hr
  simp only [Complex.sub_re] at hr
  have hB : (∑ n ∈ C\reducedCountLabels u N K, f n).re-
      (ZetaRieszUnifiedSignedRows.largeOwnerIncidences u y N K).re-
      (ZetaRieszOwnerGapRows.ownerGapLiteralRows u y j+ZetaRieszOwnerGapRows.ownerGapEndpointRows u y j)-
      ZetaRieszPolynomialCutoffRows.literalCutoffPacket u y j =
        (∑ n ∈ C\reducedCountLabels u N K, f n).re-B := by dsimp [B]; ring
  change u^(N+1)*((∑ n ∈ C\reducedCountLabels u N K, f n).re-
      (ZetaRieszUnifiedSignedRows.largeOwnerIncidences u y N K).re-
      (ZetaRieszOwnerGapRows.ownerGapLiteralRows u y j+ZetaRieszOwnerGapRows.ownerGapEndpointRows u y j)-
      ZetaRieszPolynomialCutoffRows.literalCutoffPacket u y j)-E₀ ≤
        u^(N+1)*ZetaRieszPolynomialCutoffRows.polynomialCentralRemaining u y j ∧
    u^(N+1)*ZetaRieszPolynomialCutoffRows.polynomialCentralRemaining u y j ≤
      u^(N+1)*((∑ n ∈ C\reducedCountLabels u N K, f n).re-
      (ZetaRieszUnifiedSignedRows.largeOwnerIncidences u y N K).re-
      (ZetaRieszOwnerGapRows.ownerGapLiteralRows u y j+ZetaRieszOwnerGapRows.ownerGapEndpointRows u y j)-
      ZetaRieszPolynomialCutoffRows.literalCutoffPacket u y j)+E₀ at hold
  rw [hB] at hold
  dsimp only
  change u^(N+1)*((∑ n ∈ (C\reducedCountLabels u N K)\periodEdgeLabels u N K, f n).re-
      (ZetaRieszUnifiedSignedRows.largeOwnerIncidences u y N K).re-
      (ZetaRieszOwnerGapRows.ownerGapLiteralRows u y j+ZetaRieszOwnerGapRows.ownerGapEndpointRows u y j)-
      ZetaRieszPolynomialCutoffRows.literalCutoffPacket u y j)-(E₀+edgeBudget N) ≤
        u^(N+1)*ZetaRieszPolynomialCutoffRows.polynomialCentralRemaining u y j ∧
    u^(N+1)*ZetaRieszPolynomialCutoffRows.polynomialCentralRemaining u y j ≤
      u^(N+1)*((∑ n ∈ (C\reducedCountLabels u N K)\periodEdgeLabels u N K, f n).re-
      (ZetaRieszUnifiedSignedRows.largeOwnerIncidences u y N K).re-
      (ZetaRieszOwnerGapRows.ownerGapLiteralRows u y j+ZetaRieszOwnerGapRows.ownerGapEndpointRows u y j)-
      ZetaRieszPolynomialCutoffRows.literalCutoffPacket u y j)+(E₀+edgeBudget N)
  have hB' : (∑ n ∈ (C\reducedCountLabels u N K)\periodEdgeLabels u N K, f n).re-
      (ZetaRieszUnifiedSignedRows.largeOwnerIncidences u y N K).re-
      (ZetaRieszOwnerGapRows.ownerGapLiteralRows u y j+ZetaRieszOwnerGapRows.ownerGapEndpointRows u y j)-
      ZetaRieszPolynomialCutoffRows.literalCutoffPacket u y j =
      (∑ n ∈ (C\reducedCountLabels u N K)\periodEdgeLabels u N K, f n).re-B := by
    dsimp [B]
    ring
  rw [hB']
  constructor <;> nlinarith only [hold.1,hold.2,hr.1,hr.2]

/-- The entire displayed ledger error remains independently source-o(1)
on the ORIGINAL cofinal schedule after the new global boundary payment. -/
theorem tendsto_combined_period_error :
    Tendsto (fun j : ℕ => (503/500 : ℝ)*zetaMoebiusLogMajorantMass (2049/2048)*
      hingeAllocationRate^dyadicMomentOrder j+
      ((203/50 : ℝ)*(10001/20000))*((dyadicMomentOrder j : ℝ)+1)*
        paidCountRate^dyadicMomentOrder j+edgeBudget (dyadicMomentOrder j)) atTop (𝓝 0) := by
  have hh := tendsto_combined_reducedCount_error.add
    (tendsto_edgeBudget.comp tendsto_dyadicMomentOrder)
  simpa only [Function.comp_def,zero_add] using hh

/-- Crossing the hinge-selector boundary inside a complete total-log
period does not change the small-owner geometry. The cofactor is the SAME
original cofactor and both labels remain in the literal central population. -/
theorem hinge_same_period_owner_share {u : ℝ} {N K n n₀ : ℕ} {v y : ℝ}
    (hN : 1000 ≤ N) (hn₀ : n₀ ∈ hingeLabels u N K)
    (hn : n ∈ ((coreBand u N K).filter
      (fun n : ℕ => (197/100 : ℝ)*N<log n)).filter Squarefree)
    (ha : n/largestPrime n=n₀/largestPrime n₀)
    (hL : (11/8 : ℝ)*N ≤ SquarefreeVaughanLogSource.length u N) (hy : 54 ≤ y)
    (hT₀ : v-Real.pi/y < log n₀ ∧ log n₀ ≤ v+Real.pi/y)
    (hT : v-Real.pi/y < log n ∧ log n ≤ v+Real.pi/y) :
    log (largestPrime n) ≤ log n/6 := by
  obtain ⟨hcentral₀,hs₀,e,he,hhinge,hgap⟩ := Finset.mem_filter.mp hn₀
  obtain ⟨hcentral,hs⟩ := Finset.mem_filter.mp hn
  have hc₀ := (Finset.mem_filter.mp hcentral₀).1
  have hc := (Finset.mem_filter.mp hcentral).1
  have hg₀ := ZetaRieszClippedOwnerPeriodFloor.canonical_owner_data hs₀
    (ZetaRieszJointPrimeEnergy.core_count hc₀)
  have hg := ZetaRieszClippedOwnerPeriodFloor.canonical_owner_data hs
    (ZetaRieszJointPrimeEnergy.core_count hc)
  have hprod₀ : log n₀=log (largestPrime n₀)+log (n₀/largestPrime n₀ : ℕ) := by
    conv_lhs => rw [← hg₀.2.1,Nat.cast_mul,log_mul
      (by exact_mod_cast hg₀.1.ne_zero) (by exact_mod_cast hg₀.2.2.1.ne_zero)]
  have hprod : log n=log (largestPrime n)+log (n₀/largestPrime n₀ : ℕ) := by
    conv_lhs => rw [← hg.2.1,Nat.cast_mul,log_mul
      (by exact_mod_cast hg.1.ne_zero) (by exact_mod_cast hg.2.2.1.ne_zero)]
    rw [ha]
  have hP := hinge_owner_log_le hc₀ hs₀ he hhinge hgap hL
  have hlow := (central_log_bounds hcentral₀).1
  have hw := period_width_le hy
  have hwidth : log n-log n₀ ≤ 1/8 := by
    have heq : 2*Real.pi/y=2*(Real.pi/y) := by ring
    rw [heq] at hw
    linarith [hT₀.1,hT.2]
  have hNR : (1000 : ℝ) ≤ N := by exact_mod_cast hN
  nlinarith only [hwidth,hP,hlow,hprod₀,hprod,hNR]

/-- GLOBAL source-geometric payment for the allocation switch on any
literal population whose cofactor rows meet a genuine hinge in the same
period. Neither the number of rows nor their prime counts is charged.
This removes a selector obstruction without filling prime or credit masks. -/
theorem completed_hinge_owner_sum_bound (S : Finset ℕ) (A : ℕ → Finset ℕ)
    (D : ℕ → Finset (ℕ×ℕ)) (w : ℕ → ℂ) (N K : ℕ) {u : ℝ}
    (hu : 0 ≤ u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (hN : 1000 ≤ N)
    (hS : S ⊆ ((coreBand u N K).filter
      (fun n : ℕ => (197/100 : ℝ)*N<log n)).filter Squarefree)
    (hL : (11/8 : ℝ)*N ≤ SquarefreeVaughanLogSource.length u N)
    (hD : ∀ n ∈ S, D n ⊆ (n/largestPrime n).divisorsAntidiagonal)
    (hw : ∀ n ∈ S, ‖w n‖ ≤ 1) (y : ℝ) (hy : 54 ≤ y)
    (hmatch : ∀ n ∈ S, ∃ n₀ : ℕ, ∃ v : ℝ,
      n₀ ∈ hingeLabels u N K ∧ n/largestPrime n=n₀/largestPrime n₀ ∧
      (v-Real.pi/y < log n₀ ∧ log n₀ ≤ v+Real.pi/y) ∧
      (v-Real.pi/y < log n ∧ log n ≤ v+Real.pi/y)) :
    ‖(u : ℂ)^(N+1)*∑ n ∈ S, w n*
      (partialCoefficient (A n ∩ {largestPrime n}) (SquarefreeVaughanLogSource.length u N)
        N (largestPrime n) (n/largestPrime n) (D n)-
      partialCoefficient ∅ (SquarefreeVaughanLogSource.length u N)
        N (largestPrime n) (n/largestPrime n) (D n))*
          zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ ≤
      (503/500 : ℝ)*zetaMoebiusLogMajorantMass (2049/2048)*hingeAllocationRate^N := by
  have hg n (hn : n ∈ S) :=
    ZetaRieszClippedOwnerPeriodFloor.canonical_owner_data
      (Finset.mem_filter.mp (hS hn)).2
      (ZetaRieszJointPrimeEnergy.core_count (Finset.mem_filter.mp
        (Finset.mem_filter.mp (hS hn)).1).1)
  apply partial_owner_sum_bound S A largestPrime (fun n => n/largestPrime n) D w N
    (SquarefreeVaughanLogSource.length_pos u N)
  · intro n hn
    have hc := ZetaRieszJointPrimeEnergy.core_count (Finset.mem_filter.mp
      (Finset.mem_filter.mp (hS hn)).1).1
    exact ZetaRieszOwnedCells.largestPrime_mem_of_two (by omega)
  · intro n hn
    exact Nat.pos_of_ne_zero (hg n hn).2.2.1.ne_zero
  · intro n hn
    exact (hg n hn).2.1
  · intro n hn
    obtain ⟨n₀,v,hn₀,ha,hT₀,hT⟩ := hmatch n hn
    exact hinge_same_period_owner_share hN hn₀ (hS hn) ha hL hy hT₀ hT
  · exact hD
  · intro n hn
    have hlog := (central_log_bounds (Finset.mem_filter.mp (hS hn)).1).2
    nlinarith [Nat.cast_nonneg (α := ℝ) N]
  · exact hw
  · exact hu
  · exact hU

end RiemannGaussian.ZetaRieszRadialPeriodPayment
