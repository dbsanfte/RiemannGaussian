/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszPairLowOrderPayment

/-!
# Pay the whole signed pair completion boundary

The symmetric prefix has no hard prime-share mask. Every genuine pair in
the strict total-log interior already belongs to the literal joined support.
Complete only this whole signed pair sum; the added labels and original
radial flag are independently paid at an explicit geometric rate. No bound
on the central signed convolution is assumed or proved by completion.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open Real Filter Topology
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszPairWholeCompletion
open LogarithmicDeviation ZetaArithmeticLogWindow
open ZetaRieszGlobalCentralPayment ZetaRieszGlobalBoundaryPruning
open ZetaRieszGlobalHeadCentralPayment ZetaRieszBalancedRadialPayment
open ZetaRieszPrimeCountFrequency ZetaRieszGlobalPeriodEdgePayment
open ZetaRieszPairPrefixPayment ZetaRieszSignedSelbergPayment
open ZetaRieszOwnerMaximal ZetaRieszPrimeEndpoint ZetaRieszHeadOrders
open ZetaRieszLowCountSignedBoundary ZetaRieszGlobalBulkPayment
open ZetaRieszPrimePairConvolution ZetaRieszLowCountSelbergAudit

/-- Tilt bound with a FIXED additive displacement in total logarithm.
The displacement changes only the finite constant, not the geometric rate. -/
theorem norm_filter_with_offset (P : Polynomial ℂ) (S : Finset ℕ) (a : ℕ→ℂ)
    (ha : ∀ n∈S,‖a n‖≤zetaMoebiusLogMajorant n)
    {N : ℕ} (hN : 0<N) (y : ℝ) {U x σ D : ℝ}
    (hU : 0<U) (hx : 0<x) (hσ : 1<σ)
    (hlog : ∀ n∈S,(σ-3/2+x⁻¹)*log n≤
      (N : ℝ)*((σ-3/2+x⁻¹)*x)+D) :
    ‖(U : ℂ)^(N+1)*∑ n∈S,a n*zetaPrimeFilterKernel P N (3/2+Complex.I*y) n‖≤
      (U*(x*exp ((σ-3/2+x⁻¹)*x)))^N*
        (exp D*(U*tiltConstant P x⁻¹ σ)) := by
  have hNr : (N : ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hN
  have hb := norm_sum_filter_of_log_bound S a ha P N y σ x⁻¹
    (((σ-3/2+x⁻¹)*x)+D/N) hσ (inv_pos.mpr hx) (by
      intro n hn
      convert hlog n hn using 1
      field_simp [hNr])
  simp only [inv_inv] at hb
  have he : (exp (((σ-3/2+x⁻¹)*x)+D/N))^N=
      (exp ((σ-3/2+x⁻¹)*x))^N*exp D := by
    rw [←exp_nat_mul,←exp_nat_mul,←exp_add]
    congr 1
    field_simp [hNr]
  rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg hU.le]
  have hm := mul_le_mul_of_nonneg_left hb (pow_nonneg hU.le (N+1))
  apply hm.trans_eq
  rw [pow_succ,mul_pow,he,mul_pow]
  ring

/-- ONE constant pays everything outside the strict interior, uniformly
over heights and finite masks, for this fixed polynomial kernel. -/
theorem exists_filter_edge_bound (P : Polynomial ℂ) :
    ∃ C : ℝ,0≤C ∧ ∀ (N : ℕ) (S : Finset ℕ) (a : ℕ→ℂ),
      64≤N → (∀ n∈S,‖a n‖≤zetaMoebiusLogMajorant n) →
      ∀ (y u : ℝ),0≤u → u≤ZetaRieszWideOwnerAudit.radiusCeiling →
        ‖(u : ℂ)^(N+1)*((∑ n∈S,a n*zetaPrimeFilterKernel P N (3/2+Complex.I*y) n)-
          ∑ n∈interiorLabels S N,a n*zetaPrimeFilterKernel P N (3/2+Complex.I*y) n)‖≤
            ZetaRieszLargeOrderCore.rate^N*C := by
  let U := ZetaRieszWideOwnerAudit.radiusCeiling
  let σ := ZetaRieszLargeOrderCore.sigma
  let b₀ : ℝ := 1971/1000
  let b₁ : ℝ := 2029/1000
  let a₀ := σ-3/2+b₀⁻¹
  let a₁ := σ-3/2+b₁⁻¹
  let C₀ := exp a₀*(U*tiltConstant P b₀⁻¹ σ)
  let C₁ := exp (-a₁)*(U*tiltConstant P b₁⁻¹ σ)
  have hU : 0<U := by norm_num [U,ZetaRieszWideOwnerAudit.radiusCeiling]
  have hσ : 1<σ := by norm_num [σ,ZetaRieszLargeOrderCore.sigma]
  have hC₀ : 0≤C₀ := by
    dsimp only [C₀]
    exact mul_nonneg (exp_pos _).le (mul_nonneg hU.le (tiltConstant_nonneg _ (by norm_num [b₀])))
  have hC₁ : 0≤C₁ := by
    dsimp only [C₁]
    exact mul_nonneg (exp_pos _).le (mul_nonneg hU.le (tiltConstant_nonneg _ (by norm_num [b₁])))
  refine ⟨C₀+C₁,add_nonneg hC₀ hC₁,?_⟩
  intro N S a hN ha y u hu huU
  let low : Finset ℕ := S.filter (fun n => log (n : ℝ)≤b₀*N+1)
  let high : Finset ℕ := S.filter (fun n => b₁*N-1<log (n : ℝ))
  have hl := norm_filter_with_offset P low a
    (fun n hn => ha n (Finset.mem_filter.mp hn).1) (by omega : 0<N) y hU
    (by norm_num [b₀] : 0<b₀) hσ (D:=a₀) (by
      intro n hn
      have h := mul_le_mul_of_nonneg_left (Finset.mem_filter.mp hn).2
        (by norm_num [a₀,b₀,σ,ZetaRieszLargeOrderCore.sigma] : 0≤a₀)
      change a₀*log n≤(N : ℝ)*(a₀*b₀)+a₀
      nlinarith only [h])
  have hh := norm_filter_with_offset P high a
    (fun n hn => ha n (Finset.mem_filter.mp hn).1) (by omega : 0<N) y hU
    (by norm_num [b₁] : 0<b₁) hσ (D:=-a₁) (by
      intro n hn
      have h := mul_le_mul_of_nonpos_left (Finset.mem_filter.mp hn).2.le
        (by norm_num [a₁,b₁,σ,ZetaRieszLargeOrderCore.sigma] : a₁≤0)
      change a₁*log n≤(N : ℝ)*(a₁*b₁)-a₁
      nlinarith only [h])
  have he : (∑ n∈S,a n*zetaPrimeFilterKernel P N (3/2+Complex.I*y) n)-
      ∑ n∈interiorLabels S N,a n*zetaPrimeFilterKernel P N (3/2+Complex.I*y) n=
        (∑ n∈low,a n*zetaPrimeFilterKernel P N (3/2+Complex.I*y) n)+
        ∑ n∈high,a n*zetaPrimeFilterKernel P N (3/2+Complex.I*y) n := by
    have hn : (64 : ℝ)≤N := by exact_mod_cast hN
    have hn0 : (N : ℝ)≠0 := by linarith only [hn]
    have h₀ : (b₀+1/(N : ℝ))*N=b₀*N+1 := by field_simp
    have h₁ : (b₁-1/(N : ℝ))*N=b₁*N-1 := by field_simp
    have hab : b₀+1/(N : ℝ)≤b₁-1/(N : ℝ) := by
      apply (mul_le_mul_iff_left₀ (show (0 : ℝ)<N by linarith only [hn])).mp
      rw [h₀,h₁]
      dsimp only [b₀,b₁]
      nlinarith only [hn]
    have he := sum_sub_deviationBand S
      (fun n => a n*zetaPrimeFilterKernel P N (3/2+Complex.I*y) n) hab N
    simpa only [interiorLabels,low,high,deviationBand,h₀,h₁,b₀,b₁] using he
  apply (sourceScale_norm_mono hu huU N _).trans
  rw [he,mul_add]
  apply (norm_add_le _ _).trans
  have h₀ := pow_le_pow_left₀ (by positivity) ZetaRieszLargeOrderCore.lower_rate_lt.le N
  have h₁ := pow_le_pow_left₀ (by positivity) ZetaRieszLargeOrderCore.upper_rate_lt.le N
  calc
    _ ≤ _ := add_le_add hl hh
    _ ≤ ZetaRieszLargeOrderCore.rate^N*C₀+ZetaRieszLargeOrderCore.rate^N*C₁ :=
      add_le_add (mul_le_mul_of_nonneg_right h₀ hC₀) (mul_le_mul_of_nonneg_right h₁ hC₁)
    _ = _ := by ring

/-- The fixed polynomial `X` shifts the factorial kernel by exactly one. -/
theorem filter_X (N n : ℕ) (s : ℂ) :
    zetaPrimeFilterKernel (Polynomial.X : Polynomial ℂ) N s n =
      zetaPrimeLogKernel (N+1) s n := by
  simp [filterKernel_eq_moments]

/-- The intercept of the exact prefix, with its signed Selberg term kept. -/
def prefixIntercept (N n : ℕ) : ℂ :=
  ((show ℝ from log n*(1-lowerMass (N+1) (13*N/32)
      (log (ZetaRieszOwnedCells.ownerCofactor n)/log n)-
    lowerMass (N+1) (13*N/32) (log (largestPrime n)/log n))) : ℂ)-
    selbergCoefficient n

/-- The slope of the exact prefix; the moving length is outside it. -/
def prefixSlope (N n : ℕ) : ℂ :=
  ((show ℝ from -(log n-log (largestPrime n)*lowerMass (N+1) (13*N/32)
      (log (ZetaRieszOwnedCells.ownerCofactor n)/log n)-
    log (ZetaRieszOwnedCells.ownerCofactor n)*lowerMass (N+1) (13*N/32)
      (log (largestPrime n)/log n))) : ℂ)

private theorem pair_logs {n : ℕ} (hn : OrdinaryLabel n) (hnot : ¬n.Prime) :
    log n=log (largestPrime n)+log (ZetaRieszOwnedCells.ownerCofactor n) ∧
      0<log n := by
  obtain ⟨p,q,hp,hq,hne,he⟩ := (ordinaryLabel_pair hn).resolve_left hnot
  have hs (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hqp : q<p) :
      largestPrime (p*q)=p ∧ ZetaRieszOwnedCells.ownerCofactor (p*q)=q := by
    have hm : ∀ r∈q.primeFactors,r<p := by
      intro r hr
      rw [hq.primeFactors,Finset.mem_singleton] at hr
      subst r
      exact hqp
    exact ⟨ZetaRieszPrimeIntervals.largestPrime_mul p q hp hq.ne_zero hm,
      ZetaRieszPrimeIntervals.ownerCofactor_mul p q hp hq.ne_zero hm⟩
  have hlog : log n=log p+log q := by
    rw [←he,Nat.cast_mul,log_mul (by exact_mod_cast hp.ne_zero)
      (by exact_mod_cast hq.ne_zero)]
  refine ⟨?_,?_⟩
  · rcases lt_or_gt_of_ne hne with hlt | hgt
    · have h := hs q p hq hp hlt
      rw [mul_comm,he] at h
      rw [h.1,h.2,hlog]
      ring
    · have h := hs p q hp hq hgt
      rw [he] at h
      rw [h.1,h.2]
      exact hlog
  · rw [hlog]
    have hp0 := log_pos (show (1 : ℝ)<p by exact_mod_cast hp.one_lt)
    have hq0 := log_pos (show (1 : ℝ)<q by exact_mod_cast hq.one_lt)
    linarith only [hp0,hq0]

/-- Both prefix probabilities remain in `[0,1]` on every actual pair,
including pairs arbitrarily far outside the central radial band. -/
theorem pair_prefix_bounds (N : ℕ) {n : ℕ}
    (hn : OrdinaryLabel n) (hnot : ¬n.Prime) :
    0≤lowerMass (N+1) (13*N/32) (log (largestPrime n)/log n) ∧
    lowerMass (N+1) (13*N/32) (log (largestPrime n)/log n)≤1 ∧
    0≤lowerMass (N+1) (13*N/32) (log (ZetaRieszOwnedCells.ownerCofactor n)/log n) ∧
    lowerMass (N+1) (13*N/32) (log (ZetaRieszOwnedCells.ownerCofactor n)/log n)≤1 := by
  obtain ⟨ht,ht0⟩ := pair_logs hn hnot
  have hx := log_natCast_nonneg (largestPrime n)
  have hz := log_natCast_nonneg (ZetaRieszOwnedCells.ownerCofactor n)
  have hp := lowerMass_bounds (N+1) (13*N/32) (div_nonneg hx ht0.le)
    ((div_le_one ht0).mpr (by linarith only [ht,hz]))
  have hq := lowerMass_bounds (N+1) (13*N/32) (div_nonneg hz ht0.le)
    ((div_le_one ht0).mpr (by linarith only [ht,hx]))
  exact ⟨hp.1,hp.2,hq.1,hq.2⟩

/-- Only the completion boundary will be estimated by this majorant. -/
theorem norm_prefixIntercept_le (N : ℕ) {n : ℕ}
    (hn : OrdinaryLabel n) (hnot : ¬n.Prime) :
    ‖prefixIntercept N n‖≤2*zetaMoebiusLogMajorant n := by
  obtain ⟨hp0,hp1,hq0,hq1⟩ := pair_prefix_bounds N hn hnot
  have hT := log_natCast_nonneg n
  have ha : |log n*(1-lowerMass (N+1) (13*N/32)
      (log (ZetaRieszOwnedCells.ownerCofactor n)/log n)-
    lowerMass (N+1) (13*N/32) (log (largestPrime n)/log n))|≤log n := by
    apply abs_le.mpr
    constructor <;> nlinarith only [hp0,hp1,hq0,hq1,hT]
  unfold prefixIntercept
  apply (norm_sub_le _ _).trans
  rw [Complex.norm_real,Real.norm_eq_abs]
  calc
    _ ≤ log n+log n := add_le_add ha (norm_selbergCoefficient_le hn)
    _ ≤ _ := by linarith only [ZetaRieszCentralWindow.log_le_divisor_majorant n]

/-- The successor-kernel slope is bounded independently of `L` and `N`. -/
theorem norm_prefixSlope_le (N : ℕ) {n : ℕ}
    (hn : OrdinaryLabel n) (hnot : ¬n.Prime) :
    ‖prefixSlope N n‖≤zetaMoebiusLogMajorant n := by
  obtain ⟨hp0,hp1,hq0,hq1⟩ := pair_prefix_bounds N hn hnot
  obtain ⟨ht,_⟩ := pair_logs hn hnot
  have hx := log_natCast_nonneg (largestPrime n)
  have hz := log_natCast_nonneg (ZetaRieszOwnedCells.ownerCofactor n)
  have hx0 := mul_nonneg hx hq0
  have hz0 := mul_nonneg hz hp0
  have hx1 := mul_le_of_le_one_right hx hq1
  have hz1 := mul_le_of_le_one_right hz hp1
  unfold prefixSlope
  rw [Complex.norm_real,Real.norm_eq_abs]
  apply (abs_le.mpr ⟨?_,?_⟩).trans (ZetaRieszCentralWindow.log_le_divisor_majorant n)
  · linarith only [hx0,hz0]
  · linarith only [ht,hx1,hz1,hx,hz]

/-- Exact affine-in-length decomposition before paying any boundary.
The full phase and every factorial order remain in these two kernels. -/
theorem prefix_atom_split (N : ℕ) {n : ℕ}
    (hn : OrdinaryLabel n) (hnot : ¬n.Prime) (L : ℝ) (hL : L≠0) (s : ℂ) :
    ((prefixLogCoefficient N L (log (largestPrime n))
      (log (ZetaRieszOwnedCells.ownerCofactor n)) : ℂ)-selbergCoefficient n)*
        zetaPrimeLogKernel N s n =
      prefixIntercept N n*zetaPrimeLogKernel N s n+
        ((N+1 : ℕ) : ℂ)/(L : ℂ)*prefixSlope N n*zetaPrimeLogKernel (N+1) s n := by
  have ht := (pair_logs hn hnot).1
  have hreal : prefixLogCoefficient N L (log (largestPrime n))
      (log (ZetaRieszOwnedCells.ownerCofactor n))=
      log n*(1-lowerMass (N+1) (13*N/32)
        (log (ZetaRieszOwnedCells.ownerCofactor n)/log n)-
        lowerMass (N+1) (13*N/32) (log (largestPrime n)/log n))+
      log n/L* (-(log n-log (largestPrime n)*lowerMass (N+1) (13*N/32)
        (log (ZetaRieszOwnedCells.ownerCofactor n)/log n)-
        log (ZetaRieszOwnedCells.ownerCofactor n)*lowerMass (N+1) (13*N/32)
        (log (largestPrime n)/log n))) := by
    unfold prefixLogCoefficient
    rw [←ht]
    field_simp [hL]
    ring
  have he : ((prefixLogCoefficient N L (log (largestPrime n))
      (log (ZetaRieszOwnedCells.ownerCofactor n)) : ℂ)-selbergCoefficient n)=
      prefixIntercept N n+(log n : ℂ)/(L : ℂ)*prefixSlope N n := by
    rw [hreal]
    unfold prefixIntercept prefixSlope
    simp only [Complex.ofReal_add,Complex.ofReal_div,Complex.ofReal_mul]
    ring
  rw [he,add_mul]
  have hk := log_mul_kernel N n s
  calc
    _ = prefixIntercept N n*zetaPrimeLogKernel N s n+
        prefixSlope N n/(L : ℂ)*((log n : ℂ)*zetaPrimeLogKernel N s n) := by ring
    _ = _ := by rw [hk]; ring

private theorem paired_ordinary_not_prime (A : Finset ℕ) (hA : ∀ p∈A,p.Prime)
    {n : ℕ} (hn : n∈ZetaRieszRemainingPrefix.pairedLabels A) :
    OrdinaryLabel n ∧ ¬n.Prime := by
  refine ⟨finiteLabels_ordinary A hA (Finset.mem_union.mpr (Or.inr hn)),?_⟩
  obtain ⟨⟨p,q⟩,hpq,rfl⟩ := Finset.mem_image.mp hn
  obtain ⟨hpq,_⟩ := Finset.mem_filter.mp hpq
  obtain ⟨hp,hq⟩ := Finset.mem_product.mp hpq
  exact Nat.not_prime_mul (hA p hp).ne_one (hA q hq).ne_one

/-- All literal pairs enter the exhaustive finite prime prefix. This
does not replace any original support before its boundary is paid. -/
theorem literal_pairs_eventually_prefix {u : ℝ} (hu : 1/2≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {N : ℕ} (hN : 65536≤N)
    (y : ℝ) : ∀ᶠ P : ℕ in atTop,
    (completePeriodLabels (joinedLabels u N) N y).filter (fun n => ¬n.Prime)⊆
      ZetaRieszRemainingPrefix.pairedLabels (primePrefix P) := by
  apply (eventually_all_finset _).mpr
  intro n hn
  obtain ⟨hn,hnot⟩ := Finset.mem_filter.mp hn
  have ho := joinedLabels_ordinary hu hU hN (Finset.mem_filter.mp hn).1
  filter_upwards [ordinaryLabel_eventually_prefix ho] with P hP
  rcases Finset.mem_union.mp hP with hp | hpair
  · exact (hnot (Finset.mem_filter.mp hp).2).elim
  · exact hpair

/-- No newly added pair lies in the strict central interior. In
particular this completion adds no hard-share boundary in the main term. -/
theorem missing_pairs_interior_empty (u y : ℝ) (N P : ℕ) (hy : 54≤|y|) :
    interiorLabels (ZetaRieszRemainingPrefix.pairedLabels (primePrefix P)\
      (completePeriodLabels (joinedLabels u N) N y).filter (fun n => ¬n.Prime)) N=∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro n hn
  obtain ⟨hn,hl,hh⟩ := Finset.mem_filter.mp hn
  obtain ⟨hn,hnotS⟩ := Finset.mem_sdiff.mp hn
  obtain ⟨ho,hnot⟩ := paired_ordinary_not_prime _
    (fun p hp => (Finset.mem_filter.mp hp).2) hn
  have hi := interior_ordinary_mem_joined (u:=u) ho hl hh
  have hperiod := interiorLabels_subset_completePeriods (joinedLabels u N) N hy
    (Finset.mem_filter.mpr ⟨hi,hl,hh⟩)
  exact hnotS (Finset.mem_filter.mpr ⟨hperiod,hnot⟩)

private theorem interior_pair_mem_semiprime {N n : ℕ}
    (hn : OrdinaryLabel n) (hnot : ¬n.Prime)
    (hl : (1971/1000 : ℝ)*N+1<log n)
    (hh : log n≤(2029/1000 : ℝ)*N-1) : n∈semiprimeLabels N := by
  have hn0 : 0<n := by
    by_contra h
    have hnz : n=0 := by omega
    simp only [hnz,Nat.cast_zero,log_zero] at hl
    nlinarith only [hl,Nat.cast_nonneg (α:=ℝ) N]
  have hf : n∈centralFullLabels N := by
    apply Finset.mem_filter.mpr
    refine ⟨(ZetaRieszOwnerLatticePhase.coreFloor_membership N 0 hn0).mpr ⟨?_,?_⟩,?_,?_⟩
    · simp only [zero_add]
      nlinarith only [hl,Nat.cast_nonneg (α:=ℝ) N]
    · simp only [zero_add]
      nlinarith only [hh,Nat.cast_nonneg (α:=ℝ) N]
    · linarith only [hl]
    · linarith only [hh]
  exact Finset.mem_filter.mpr ⟨hf,hn.resolve_left hnot⟩

/-- The exhaustive finite signed prefix. It contains only actual
ordinary-prime pairs; the diagonal is handled by the convolution theorem. -/
def finitePrefixPairDefect (u y : ℝ) (N P : ℕ) : ℂ :=
  (u : ℂ)^(N+1)*∑ n∈ZetaRieszRemainingPrefix.pairedLabels (primePrefix P),
    ((prefixLogCoefficient N (SquarefreeVaughanLogSource.length u N)
      (log (largestPrime n)) (log (ZetaRieszOwnedCells.ownerCofactor n)) : ℂ)-
      selbergCoefficient n)*zetaPrimeLogKernel N (3/2+Complex.I*y) n

/-- One independent geometric budget pays the ENTIRE completion of the
literal symmetric pair sum, including its exact radial endpoint flag.
The signed central quadratic remains in the main term, not in this cost. -/
theorem exists_whole_pair_completion_bound :
    ∃ C : ℝ,0≤C ∧ ∀ u y : ℝ,1/2≤u→
      u≤ZetaRieszWideOwnerAudit.radiusCeiling→54≤|y|→∀ N : ℕ,65536≤N→
      ∀ᶠ P : ℕ in atTop,
        ‖finitePrefixPairDefect u y N P-prefixPairDefect u y N‖≤
          ZetaRieszLargeOrderCore.rate^N*C := by
  obtain ⟨C,hC,hb⟩ := exists_displaced_edge_bound
  obtain ⟨D,hD,hd⟩ := exists_filter_edge_bound (Polynomial.X : Polynomial ℂ)
  refine ⟨3*C+D,by positivity,?_⟩
  intro u y hu hU hy N hN
  have hu0 : 0≤u := by linarith only [hu]
  have hL := SquarefreeVaughanLogSource.length_pos u N
  let S := (completePeriodLabels (joinedLabels u N) N y).filter (fun n => ¬n.Prime)
  have hS : ∀ n∈S,OrdinaryLabel n ∧ ¬n.Prime := by
    intro n hn
    obtain ⟨hn,hnot⟩ := Finset.mem_filter.mp hn
    exact ⟨joinedLabels_ordinary hu hU hN (Finset.mem_filter.mp hn).1,hnot⟩
  let r : ℕ→ℂ := fun n => if n∈primeLabels N∪semiprimeLabels N then 0
    else completedCoefficient (SquarefreeVaughanLogSource.length u N) n
  have hrmaj : ∀ n∈S,‖r n‖≤zetaMoebiusLogMajorant n := by
    intro n _
    dsimp only [r]
    split_ifs
    · simpa only [norm_zero] using zetaMoebiusLogMajorant_nonneg n
    · exact completedCoefficient_norm_le hL n
  have hrzero : ∑ n∈interiorLabels S N,r n*zetaPrimeLogKernel N (3/2+Complex.I*y) n=0 := by
    apply Finset.sum_eq_zero
    intro n hn
    obtain ⟨hn,hl,hh⟩ := Finset.mem_filter.mp hn
    obtain ⟨ho,hnot⟩ := hS n hn
    have hi := interior_pair_mem_semiprime ho hnot hl hh
    simp only [r,Finset.mem_union.mpr (Or.inr hi),if_true,zero_mul]
  have hr := hb N S r (by omega : 64≤N) hrmaj y u hu0 hU
  rw [hrzero,sub_zero] at hr
  have hratio : ‖((N+1 : ℕ) : ℂ)/(SquarefreeVaughanLogSource.length u N : ℂ)‖≤1 := by
    rw [norm_div,Complex.norm_natCast,Complex.norm_real,Real.norm_of_nonneg hL.le]
    apply (div_le_one hL).mpr
    have hlo := ZetaRieszPostHingeEnergy.length_ge_rational hN
      (by linarith only [hu] : 0<u) hU
    have hn : (65536 : ℝ)≤N := by exact_mod_cast hN
    push_cast
    nlinarith only [hlo,hn]
  filter_upwards [literal_pairs_eventually_prefix hu hU hN y] with P hP
  let G := ZetaRieszRemainingPrefix.pairedLabels (primePrefix P)
  let E := G\S
  have hE : ∀ n∈E,OrdinaryLabel n ∧ ¬n.Prime := fun n hn =>
    paired_ordinary_not_prime _ (fun p hp => (Finset.mem_filter.mp hp).2)
      (Finset.mem_sdiff.mp hn).1
  have he : interiorLabels E N=∅ := missing_pairs_interior_empty u y N P hy
  have hhalf : ∀ n∈E,‖prefixIntercept N n/2‖≤zetaMoebiusLogMajorant n := by
    intro n hn
    rw [norm_div]
    norm_num
    have ht := norm_prefixIntercept_le N (hE n hn).1 (hE n hn).2
    exact (div_le_iff₀ (by norm_num : (0 : ℝ)<2)).mpr (by linarith only [ht])
  have hi := hb N E (fun n => prefixIntercept N n/2) (by omega : 64≤N)
    hhalf y u hu0 hU
  rw [he,Finset.sum_empty,sub_zero] at hi
  have hieq : (u : ℂ)^(N+1)*∑ n∈E,prefixIntercept N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n=
      2*((u : ℂ)^(N+1)*∑ n∈E,(prefixIntercept N n/2)*zetaPrimeLogKernel N (3/2+Complex.I*y) n) := by
    simp only [div_mul_eq_mul_div,←Finset.sum_div]
    ring
  have hi2 : ‖(u : ℂ)^(N+1)*∑ n∈E,prefixIntercept N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n‖≤
      ZetaRieszLargeOrderCore.rate^N*(2*C) := by
    calc
      _ = 2*‖(u : ℂ)^(N+1)*∑ n∈E,(prefixIntercept N n/2)*
          zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ := by rw [hieq,norm_mul]; norm_num
      _ ≤ 2*(ZetaRieszLargeOrderCore.rate^N*C) :=
        mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ)≤2)
      _ = _ := by ring
  have hs := hd N E (prefixSlope N) (by omega : 64≤N)
    (fun n hn => norm_prefixSlope_le N (hE n hn).1 (hE n hn).2) y u hu0 hU
  simp only [filter_X,he,Finset.sum_empty,sub_zero] at hs
  have hsum := Finset.sum_sdiff hP
    (f:=fun n => ((prefixLogCoefficient N (SquarefreeVaughanLogSource.length u N)
      (log (largestPrime n)) (log (ZetaRieszOwnedCells.ownerCofactor n)) : ℂ)-selbergCoefficient n)*
      zetaPrimeLogKernel N (3/2+Complex.I*y) n)
  have hsplit : (∑ n∈E,((prefixLogCoefficient N (SquarefreeVaughanLogSource.length u N)
      (log (largestPrime n)) (log (ZetaRieszOwnedCells.ownerCofactor n)) : ℂ)-selbergCoefficient n)*
      zetaPrimeLogKernel N (3/2+Complex.I*y) n)=
      (∑ n∈E,prefixIntercept N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n)+
      ((N+1 : ℕ) : ℂ)/(SquarefreeVaughanLogSource.length u N : ℂ)*
        ∑ n∈E,prefixSlope N n*zetaPrimeLogKernel (N+1) (3/2+Complex.I*y) n := by
    simp only [Finset.mul_sum,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    simpa only [mul_assoc] using prefix_atom_split N (hE n hn).1 (hE n hn).2 _ hL.ne' _
  have hliteral : prefixPairDefect u y N=
      (u : ℂ)^(N+1)*((∑ n∈S,((prefixLogCoefficient N (SquarefreeVaughanLogSource.length u N)
        (log (largestPrime n)) (log (ZetaRieszOwnedCells.ownerCofactor n)) : ℂ)-selbergCoefficient n)*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n)-
        ∑ n∈S,r n*zetaPrimeLogKernel N (3/2+Complex.I*y) n) := by
    simp only [prefixPairDefect,prefixCoefficient,S,r,mul_sub,Finset.mul_sum,
      ←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n _
    ring
  have hdiff : finitePrefixPairDefect u y N P-prefixPairDefect u y N=
      ((u : ℂ)^(N+1)*∑ n∈E,prefixIntercept N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n)+
      ((N+1 : ℕ) : ℂ)/(SquarefreeVaughanLogSource.length u N : ℂ)*
        ((u : ℂ)^(N+1)*∑ n∈E,prefixSlope N n*zetaPrimeLogKernel (N+1) (3/2+Complex.I*y) n)+
      (u : ℂ)^(N+1)*∑ n∈S,r n*zetaPrimeLogKernel N (3/2+Complex.I*y) n := by
    rw [hliteral]
    dsimp only [finitePrefixPairDefect]
    rw [hsplit] at hsum
    rw [←hsum]
    dsimp only [S]
    ring
  have hmB : ‖((N+1 : ℕ) : ℂ)/(SquarefreeVaughanLogSource.length u N : ℂ)*
      ((u : ℂ)^(N+1)*∑ n∈E,prefixSlope N n*zetaPrimeLogKernel (N+1) (3/2+Complex.I*y) n)‖≤
      ZetaRieszLargeOrderCore.rate^N*D := by
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) hratio).trans hs
  rw [hdiff]
  apply (norm_add_le _ _).trans
  apply (add_le_add (norm_add_le _ _) (le_refl _)).trans
  calc
    _ ≤ ZetaRieszLargeOrderCore.rate^N*(2*C)+ZetaRieszLargeOrderCore.rate^N*D+
        ZetaRieszLargeOrderCore.rate^N*C :=
      add_le_add (add_le_add hi2 hmB) hr
    _ = _ := by ring

/-- The chosen finite constant of the independent whole-boundary theorem.
No numerical smallness of this constant is assumed. -/
def wholeCompletionConstant : ℝ := Classical.choose exists_whole_pair_completion_bound

theorem wholeCompletionConstant_nonneg : 0≤wholeCompletionConstant :=
  (Classical.choose_spec exists_whole_pair_completion_bound).1

/-- The exact geometric cost of removing all literal pair boundaries. -/
def wholeCompletionBudget (N : ℕ) : ℝ :=
  ZetaRieszLargeOrderCore.rate^N*wholeCompletionConstant

theorem wholeCompletionBudget_nonneg (N : ℕ) : 0≤wholeCompletionBudget N :=
  mul_nonneg (pow_nonneg ZetaRieszLargeOrderCore.rate_bounds.1.le N)
    wholeCompletionConstant_nonneg

/-- The whole-boundary cost tends to zero, without a zero hypothesis. -/
theorem wholeCompletionBudget_tendsto : Tendsto wholeCompletionBudget atTop (𝓝 0) := by
  change Tendsto (fun N : ℕ => ZetaRieszLargeOrderCore.rate^N*wholeCompletionConstant)
    atTop (𝓝 0)
  simpa only [zero_mul] using
    (tendsto_pow_atTop_nhds_zero_of_lt_one ZetaRieszLargeOrderCore.rate_bounds.1.le
      ZetaRieszLargeOrderCore.rate_bounds.2).mul_const wholeCompletionConstant

/-- Uniform source-scale completion error; neither the retained main nor
its selected resonance is estimated by this norm. -/
theorem eventually_norm_whole_completion_le {u : ℝ} (hu : 1/2≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54≤|y|)
    {N : ℕ} (hN : 65536≤N) :
    ∀ᶠ P : ℕ in atTop,
      ‖finitePrefixPairDefect u y N P-prefixPairDefect u y N‖≤wholeCompletionBudget N :=
  (Classical.choose_spec exists_whole_pair_completion_bound).2 u y hu hU hy N hN

/-- The boundary payment licenses the COMPLETE factorial convolution.
Order-zero cancellation, both incidences and the whole square diagonal
are exactly those of the earlier finite theorem. Selberg stays signed. -/
theorem finitePrefixPairDefect_eq_joined (u y : ℝ) (N P : ℕ) :
    finitePrefixPairDefect u y N P=
      (u : ℂ)^(N+1)*(
        (N+1 : ℂ)/2*(∑ k∈ZetaRieszPairPrefixConvolution.centralOrders (N+1) (13*N/32),
          finiteMoment (primePrefix P) k (3/2+Complex.I*y)*
            finiteMoment (primePrefix P) (N+1-k) (3/2+Complex.I*y))-
        (N+1 : ℂ)*(N+2)/(2*(SquarefreeVaughanLogSource.length u N : ℂ))*
          (∑ k∈ZetaRieszPairPrefixConvolution.centralOrders (N+2) (13*N/32),
            finiteMoment (primePrefix P) k (3/2+Complex.I*y)*
              finiteMoment (primePrefix P) (N+2-k) (3/2+Complex.I*y))-
        (N+1 : ℂ)/(SquarefreeVaughanLogSource.length u N : ℂ)*
          (∑ k∈(Finset.range (13*N/32+1)).filter (fun k => 0<k),
            (k : ℂ)*finiteMoment (primePrefix P) k (3/2+Complex.I*y)*
              finiteMoment (primePrefix P) (N+2-k) (3/2+Complex.I*y))-
        (1/2 : ℂ)*(∑ p∈primePrefix P,
          (prefixLogCoefficient N (SquarefreeVaughanLogSource.length u N) (log p) (log p) : ℂ)*
            zetaPrimeLogKernel N (3/2+Complex.I*y) (p^2))-
        ∑ n∈ZetaRieszRemainingPrefix.pairedLabels (primePrefix P),
          selbergCoefficient n*zetaPrimeLogKernel N (3/2+Complex.I*y) n) := by
  unfold finitePrefixPairDefect
  simp only [sub_mul,Finset.sum_sub_distrib]
  rw [ZetaRieszPairPrefixConvolution.unordered_prefix_eq_central_sub_diagonal (primePrefix P)
    (fun p hp => (Finset.mem_filter.mp hp).2) N (SquarefreeVaughanLogSource.length u N)
      (SquarefreeVaughanLogSource.length_pos u N).ne' (3/2+Complex.I*y)]

/-- Spend the new whole-boundary cost ONCE in the original native-order
floor. The complete signed pair expression is still the unpaid main. -/
theorem eventually_native_whole_pair_floor {u C : ℝ} (hu : 1/2<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54≤|y|)
    (hC : 1≤C)
    (ha : ∀ k,‖(u : ℂ)^(k+1)*zetaOrdinaryPrimeLogMoment k (3/2+Complex.I*y)‖≤C) :
    ∀ᶠ j in atTop,∀ᶠ P : ℕ in atTop,
      -(finitePrefixPairDefect u y (dyadicMomentOrder j) P).re-
        (nativeSelbergBudget u y C j+prefixBudget (dyadicMomentOrder j)+
          wholeCompletionBudget (dyadicMomentOrder j))≤
      ((u : ℂ)^(dyadicMomentOrder j+1)*ZetaRieszParityPacket.coreResponse u y
        (dyadicMomentOrder j) (ZetaRieszNearCriticalCountPayment.countCeiling j)).re := by
  filter_upwards [eventually_native_prefix_floor hu hU hy hC ha,
    tendsto_dyadicMomentOrder.eventually (eventually_ge_atTop 65536)] with j hfloor hN
  filter_upwards [eventually_norm_whole_completion_le hu.le hU hy hN] with P hP
  have he := Complex.re_le_norm (prefixPairDefect u y (dyadicMomentOrder j)-
    finitePrefixPairDefect u y (dyadicMomentOrder j) P)
  rw [Complex.sub_re,norm_sub_rev] at he
  linarith only [hfloor,he,hP]

/-- Under the simple exposed-zero hypotheses, all three old/new budgets
vanish. No independent upper bound for the complete quadratic is supplied. -/
theorem exists_native_whole_pair_payment_simple (rho : NontrivialZetaZero)
    (hrho : 1/2<rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero,tau≠rho→
      ‖(3/2:ℂ)+Complex.I*rho.1.im-tau.1‖>3/2-rho.1.re)
    (hm : analyticZetaZeroMultiplicity rho=1)
    (hU : 3/2-rho.1.re≤ZetaRieszWideOwnerAudit.radiusCeiling)
    (hy : 54≤|rho.1.im|) :
    ∃ C : ℝ,1≤C ∧
      Tendsto (fun j => nativeSelbergBudget (3/2-rho.1.re) rho.1.im C j+
        prefixBudget (dyadicMomentOrder j)+wholeCompletionBudget (dyadicMomentOrder j))
        atTop (𝓝 0) ∧
      ∀ᶠ j in atTop,∀ᶠ P : ℕ in atTop,
        -(finitePrefixPairDefect (3/2-rho.1.re) rho.1.im (dyadicMomentOrder j) P).re-
          (nativeSelbergBudget (3/2-rho.1.re) rho.1.im C j+
            prefixBudget (dyadicMomentOrder j)+wholeCompletionBudget (dyadicMomentOrder j))≤
        (((3/2-rho.1.re : ℝ) : ℂ)^(dyadicMomentOrder j+1)*ZetaRieszParityPacket.coreResponse
          (3/2-rho.1.re) rho.1.im (dyadicMomentOrder j)
            (ZetaRieszNearCriticalCountPayment.countCeiling j)).re := by
  obtain ⟨C,hC,hcost,hfloor⟩ := exists_native_prefix_payment_simple rho hrho hexposed hm hU hy
  have hu : 1/2≤3/2-rho.1.re := by linarith only [NontrivialZetaZero.re_lt_one rho]
  refine ⟨C,hC,?_,?_⟩
  · simpa only [add_zero,Function.comp_def] using
      hcost.add (wholeCompletionBudget_tendsto.comp tendsto_dyadicMomentOrder)
  · filter_upwards [hfloor,tendsto_dyadicMomentOrder.eventually (eventually_ge_atTop 65536)]
      with j hf hN
    filter_upwards [eventually_norm_whole_completion_le hu hU hy hN] with P hP
    have he := Complex.re_le_norm (prefixPairDefect (3/2-rho.1.re) rho.1.im (dyadicMomentOrder j)-
      finitePrefixPairDefect (3/2-rho.1.re) rho.1.im (dyadicMomentOrder j) P)
    rw [Complex.sub_re,norm_sub_rev] at he
    linarith only [hf,he,hP]

end RiemannGaussian.ZetaRieszPairWholeCompletion
