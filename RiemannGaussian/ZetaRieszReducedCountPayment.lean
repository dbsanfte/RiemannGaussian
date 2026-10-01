/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszPolynomialOwnerPayment

/-!
# A global geometric payment starting below the original count ceiling

The count moment pays every retained original label with `256*omega(n) >= K`.
This is one independent geometric estimate over all share geometries, radial
periods, original phases and partial divisor selections. It does not assert
cancellation or a floor on the surviving lower-count signed aggregate.
-/

noncomputable section
open Filter Topology Real
open scoped BigOperators Classical ArithmeticFunction.Moebius
namespace RiemannGaussian.ZetaRieszReducedCountPayment
open ZetaRieszPrimeCountMass ZetaRieszPrimeCountFrequency ZetaRieszSmoothHead
open ZetaRieszSignedConvolution ZetaRieszUnsignedDivisorError
open ZetaRieszPrimeEndpoint ZetaRieszParityPacket ZetaRieszShortDivisorOrbits
open ZetaRieszHingeAllocationPayment

/-- The exact count saving extracted from the original dyadic power
inequality, without changing the moment schedule. -/
def countRoot : ℝ := exp (log (17/16 : ℝ)/256)

/-- The saving has a strictly positive base and its exact 256th power. -/
theorem countRoot_pow : 0<countRoot ∧ countRoot^256=(17/16 : ℝ) := by
  refine ⟨exp_pos _,?_⟩
  unfold countRoot
  rw [← exp_nat_mul]
  rw [show ((256 : ℕ) : ℝ)*(log (17/16 : ℝ)/256)=log (17/16 : ℝ) by norm_num; ring]
  rw [exp_log (by norm_num : (0 : ℝ)<17/16)]

/-- The original arithmetic count inequality applies at one 256th of
the former count threshold, on every original label. -/
theorem reduced_count_power_saving (j k : ℕ)
    (hk : dyadicPrimeCount j ≤ 256*k) :
    countRoot^dyadicMomentOrder j ≤ (dyadicPrimeCount j : ℝ)^k := by
  apply (pow_le_pow_iff_left₀ (pow_nonneg countRoot_pow.1.le _)
    (by positivity) (by norm_num : (256 : ℕ)≠0)).mp
  rw [← pow_mul,show dyadicMomentOrder j*256=256*dyadicMomentOrder j by omega,
    pow_mul,countRoot_pow.2,← pow_mul]
  apply (dyadic_count_power_saving j).trans
  apply pow_le_pow_right₀
  · exact_mod_cast (show 1 ≤ dyadicPrimeCount j by have := four_le_dyadicPrimeCount j; omega)
  · omega

/-- The count saving beats the FULL source growth on the current
restricted radius, even with a genuinely summable tilted Euler mass. -/
def reducedCountRate : ℝ := (10001/20000 : ℝ)/(499999/1000000)/countRoot

/-- A strict geometric rate; no prime cancellation or zero hypothesis
is hidden in the choice of tilt. -/
theorem reducedCountRate_bounds : 0<reducedCountRate ∧ reducedCountRate<1 := by
  have hroot := countRoot_pow.1
  have hpow : ((10001/20000 : ℝ)/(499999/1000000))^256 < (17/16 : ℝ) := by norm_num
  have hlt : (10001/20000 : ℝ)/(499999/1000000)<countRoot := by
    apply (pow_lt_pow_iff_left₀ (by norm_num) hroot.le (by norm_num : (256 : ℕ)≠0)).mp
    rw [countRoot_pow.2]
    exact hpow
  exact ⟨div_pos (by norm_num) hroot,(div_lt_one hroot).mpr hlt⟩

/-- All selected counts are summed inside one Euler moment before its
positive bound is used for this independently decaying population. -/
theorem reduced_count_mass_bound (S : Finset ℕ) (j : ℕ)
    (hS : ∀ n ∈ S, Squarefree n)
    (hcount : ∀ n ∈ S, dyadicPrimeCount j ≤ 256*n.primeFactors.card)
    {sigma : ℝ} (hsigma : 1<sigma) :
    (∑ n ∈ S, (2 : ℝ)^n.primeFactors.card*exp (-sigma*log n)) ≤
      exp (2*(dyadicPrimeCount j : ℝ)*countMass sigma)/countRoot^dyadicMomentOrder j := by
  apply (le_div_iff₀ (pow_pos countRoot_pow.1 _)).mpr
  calc
    _ = ∑ n ∈ S, (countRoot^dyadicMomentOrder j*(2 : ℝ)^n.primeFactors.card)*
        exp (-sigma*log n) := by rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro n _; ring
    _ ≤ ∑ n ∈ S, ((dyadicPrimeCount j : ℝ)^n.primeFactors.card*
        (2 : ℝ)^n.primeFactors.card)*exp (-sigma*log n) := by
      apply Finset.sum_le_sum
      intro n hn
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (reduced_count_power_saving j _ (hcount n hn))
          (by positivity)) (exp_pos _).le
    _ = ∑ n ∈ S, (2*(dyadicPrimeCount j : ℝ))^n.primeFactors.card*
        exp (-sigma*log n) := by
      apply Finset.sum_congr rfl
      intro n _
      rw [mul_pow]
      ring
    _ ≤ _ := squarefree_count_mass_le_exp S hS hsigma (by positivity)

/-- A tilted arithmetic bound for the exact factor-two partial-incidence
coefficients on the unchanged central log window. -/
theorem norm_partial_sum_mass_bound (S : Finset ℕ) (a : ℕ → ℂ) (N : ℕ) (y : ℝ)
    (ha : ∀ n ∈ S, ‖a n‖ ≤ 2*zetaMoebiusLogMajorant n)
    (hS : ∀ n ∈ S, Squarefree n)
    (hlog : ∀ n ∈ S, log n ≤ (203/100 : ℝ)*N) {q : ℝ} (hq : 0<q) :
    ‖∑ n ∈ S, a n*zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ ≤
      ((203/50 : ℝ)*(N : ℝ)*q⁻¹^N)*
        ∑ n ∈ S, (2 : ℝ)^n.primeFactors.card*exp (-(3/2-q)*log n) := by
  calc
    _ ≤ ∑ n ∈ S, ‖a n*zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ S, ((203/50 : ℝ)*(N : ℝ)*q⁻¹^N)*
        ((2 : ℝ)^n.primeFactors.card*exp (-(3/2-q)*log n)) := by
      apply Finset.sum_le_sum
      intro n hn
      have hn1 : (1 : ℝ)≤n := by exact_mod_cast Nat.pos_of_ne_zero (hS n hn).ne_zero
      have hsupp : (1 : Polynomial ℂ).support={0} := Polynomial.support_C (one_ne_zero : (1 : ℂ)≠0)
      have hk := norm_zetaPrimeFilterKernel_le_tilt (1 : Polynomial ℂ) N (3/2+Complex.I*y) hn1 hq
      simp only [ZetaRieszJointAllocation.filter_one_eq,hsupp,Finset.sum_singleton] at hk
      norm_num at hk
      have hc := (ha n hn).trans (mul_le_mul_of_nonneg_left
        ((logMajorant_le_prime_count (hS n hn)).trans
          (mul_le_mul_of_nonneg_right (hlog n hn) (by positivity))) (by norm_num : (0 : ℝ)≤2))
      rw [norm_mul]
      convert mul_le_mul hc hk (norm_nonneg _) (by positivity) using 1; ring
    _ = _ := (Finset.mul_sum ..).symm

/-- A global source-scale bound for the complete selected high-count
population, including all its original phases and correlated coefficients. -/
theorem norm_reduced_count_sum_bound (S : Finset ℕ) (a : ℕ → ℂ) (j : ℕ) (y : ℝ)
    (ha : ∀ n ∈ S, ‖a n‖ ≤ 2*zetaMoebiusLogMajorant n)
    (hS : ∀ n ∈ S, Squarefree n)
    (hlog : ∀ n ∈ S, log n ≤ (203/100 : ℝ)*dyadicMomentOrder j)
    (hcount : ∀ n ∈ S, dyadicPrimeCount j ≤ 256*n.primeFactors.card)
    {u : ℝ} (hu : 0≤u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) :
    ‖(u : ℂ)^(dyadicMomentOrder j+1)*∑ n ∈ S,
      a n*zetaPrimeLogKernel (dyadicMomentOrder j) (3/2+Complex.I*y) n‖ ≤
      ((203/50 : ℝ)*(10001/20000))*(dyadicMomentOrder j : ℝ)*reducedCountRate^dyadicMomentOrder j*
        exp (2*(dyadicPrimeCount j : ℝ)*countMass (1000001/1000000)) := by
  have hk := norm_partial_sum_mass_bound S a (dyadicMomentOrder j) y ha hS hlog
    (by norm_num : (0 : ℝ)<499999/1000000)
  have hm := reduced_count_mass_bound S j hS hcount (by norm_num : (1 : ℝ)<1000001/1000000)
  have hsigma : (3/2 : ℝ)-499999/1000000=1000001/1000000 := by norm_num
  rw [hsigma] at hk
  have hmain := hk.trans (mul_le_mul_of_nonneg_left hm (by positivity))
  have hroot := countRoot_pow.1
  rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg hu]
  apply (mul_le_mul_of_nonneg_left hmain (pow_nonneg hu _)).trans
  calc
    _ ≤ (10001/20000 : ℝ)^(dyadicMomentOrder j+1)*
        (((203/50 : ℝ)*(dyadicMomentOrder j : ℝ)*(499999/1000000 : ℝ)⁻¹^dyadicMomentOrder j)*
          (exp (2*(dyadicPrimeCount j : ℝ)*countMass (1000001/1000000))/countRoot^dyadicMomentOrder j)) := by
      apply mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hu hU _) (by positivity)
    _ = _ := by
      unfold reducedCountRate
      simp only [div_eq_mul_inv,mul_pow,pow_succ]
      ring

/-- The one global rate after absorbing the sublinear count cost; it
remains strict even though `2*u > 1`. -/
def paidCountRate : ℝ := (1+reducedCountRate)/2

/-- A strict geometric rate for the all-geometry count payment. -/
theorem paidCountRate_bounds : 0<paidCountRate ∧ paidCountRate<1 := by
  unfold paidCountRate
  constructor <;> linarith [reducedCountRate_bounds.1,reducedCountRate_bounds.2]

/-- All counts from `ceil(K/256)` upward have ONE eventual geometric
budget, uniform over every original label, radial period, height and mask. -/
theorem eventually_reduced_count_sum_bound :
    ∀ᶠ j : ℕ in atTop, ∀ (S : Finset ℕ) (a : ℕ → ℂ) (y u : ℝ),
      0≤u → u ≤ ZetaRieszWideOwnerAudit.radiusCeiling →
      (∀ n ∈ S, ‖a n‖ ≤ 2*zetaMoebiusLogMajorant n) →
      (∀ n ∈ S, Squarefree n) →
      (∀ n ∈ S, log n ≤ (203/100 : ℝ)*dyadicMomentOrder j) →
      (∀ n ∈ S, dyadicPrimeCount j ≤ 256*n.primeFactors.card) →
      ‖(u : ℂ)^(dyadicMomentOrder j+1)*∑ n ∈ S,
        a n*zetaPrimeLogKernel (dyadicMomentOrder j) (3/2+Complex.I*y) n‖ ≤
        ((203/50 : ℝ)*(10001/20000))*
          ((dyadicMomentOrder j : ℝ)+1)*paidCountRate^dyadicMomentOrder j := by
  let s : ℝ := (1+reducedCountRate)/(2*reducedCountRate)
  have hR := reducedCountRate_bounds.1
  have hPaid := paidCountRate_bounds.1
  have hs : 1<s := by
    apply (lt_div_iff₀ (mul_pos (by norm_num : (0 : ℝ)<2) hR)).mpr
    linarith [reducedCountRate_bounds.2]
  have hRs : reducedCountRate*s=paidCountRate := by
    dsimp [s,paidCountRate]
    field_simp [hR.ne']
  filter_upwards [eventually_exp_count_le_geometric (2*countMass (1000001/1000000)) hs]
    with j hj S a y u hu hU ha hS hlog hcount
  have hb := norm_reduced_count_sum_bound S a j y ha hS hlog hcount hu hU
  have he : exp (2*(dyadicPrimeCount j : ℝ)*countMass (1000001/1000000)) ≤
      s^dyadicMomentOrder j := by simpa only [mul_assoc,mul_left_comm,mul_comm] using hj
  apply hb.trans
  calc
    _ ≤ ((203/50 : ℝ)*(10001/20000))*(dyadicMomentOrder j : ℝ)*
        reducedCountRate^dyadicMomentOrder j*s^dyadicMomentOrder j := by
      apply mul_le_mul_of_nonneg_left he (by positivity)
    _ = ((203/50 : ℝ)*(10001/20000))*(dyadicMomentOrder j : ℝ)*
        paidCountRate^dyadicMomentOrder j := by rw [← hRs,mul_pow]; ring
    _ ≤ _ := by gcongr; linarith

/-- The complete reduced-count budget vanishes on the original source
schedule, independently of all arithmetic and hypothetical-zero phases. -/
theorem tendsto_reducedCountBudget :
    Tendsto (fun j : ℕ => ((203/50 : ℝ)*(10001/20000))*
      ((dyadicMomentOrder j : ℝ)+1)*paidCountRate^dyadicMomentOrder j) atTop (𝓝 0) := by
  have ht := (ZetaRieszEulerPrimeHeadDensity.tendsto_successor_pow_mul_geometric 1
    paidCountRate_bounds.1 paidCountRate_bounds.2).comp tendsto_dyadicMomentOrder
  simpa only [Function.comp_def,pow_one,mul_zero,mul_assoc] using
    ht.const_mul ((203/50 : ℝ)*(10001/20000))

/-- The paid part of the actual central core, retaining every literal
physical and count-ceiling mask. No completed labels are added. -/
def reducedCountLabels (u : ℝ) (N K : ℕ) : Finset ℕ :=
  (((coreBand u N K).filter (fun n : ℕ => (197/100 : ℝ)*N<log n)).filter Squarefree).filter
    (fun n => K ≤ 256*n.primeFactors.card)

/-- The independent count payment controls arbitrary retained ORIGINAL
partial divisor incidences, allocation masks and full complex phases. -/
theorem eventually_literal_reducedCount_bound :
    ∀ᶠ j : ℕ in atTop, ∀ (S : Finset ℕ) (A : ℕ → Finset ℕ)
      (D : ℕ → Finset (ℕ×ℕ)) (y u : ℝ),
      0≤u → u ≤ ZetaRieszWideOwnerAudit.radiusCeiling →
      (11/8 : ℝ)*dyadicMomentOrder j ≤ SquarefreeVaughanLogSource.length u (dyadicMomentOrder j) →
      S ⊆ reducedCountLabels u (dyadicMomentOrder j) (dyadicPrimeCount j) →
      (∀ n ∈ S, D n ⊆ (n/largestPrime n).divisorsAntidiagonal) →
      ‖(u : ℂ)^(dyadicMomentOrder j+1)*∑ n ∈ S,
        partialCoefficient (A n) (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j))
          (dyadicMomentOrder j) (largestPrime n) (n/largestPrime n) (D n)*
        zetaPrimeLogKernel (dyadicMomentOrder j) (3/2+Complex.I*y) n‖ ≤
        ((203/50 : ℝ)*(10001/20000))*
          ((dyadicMomentOrder j : ℝ)+1)*paidCountRate^dyadicMomentOrder j := by
  filter_upwards [eventually_reduced_count_sum_bound] with j hJ S A D y u hu hU hL hS hD
  have hNr : (1 : ℝ) ≤ dyadicMomentOrder j := by
    have hc : (1 : ℝ) ≤ dyadicPrimeCount j := by exact_mod_cast (four_le_dyadicPrimeCount j).trans' (by norm_num)
    simp only [dyadicMomentOrder,Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat]
    nlinarith [Nat.cast_nonneg (α := ℝ) j]
  have hLs : 0<SquarefreeVaughanLogSource.length u (dyadicMomentOrder j) := by linarith only [hL,hNr]
  have hs n (hn : n ∈ S) : Squarefree n := (Finset.mem_filter.mp (Finset.mem_filter.mp (hS hn)).1).2
  have hc n (hn : n ∈ S) := (Finset.mem_filter.mp (Finset.mem_filter.mp (hS hn)).1).1
  have hlog n (hn : n ∈ S) := (ZetaRieszLowerRadialPayment.central_log_bounds (hc n hn)).2
  have hp n (hn : n ∈ S) := core_data (Finset.mem_filter.mp (hc n hn)).1 (hs n hn)
  have hprod n (hn : n ∈ S) : largestPrime n*(n/largestPrime n)=n :=
    Nat.mul_div_cancel' (Nat.dvd_of_mem_primeFactors
      (ZetaRieszOwnedCells.largestPrime_mem_of_two
        (by have := ZetaRieszJointPrimeEnergy.core_count (Finset.mem_filter.mp (hc n hn)).1; omega)))
  apply hJ S (fun n => partialCoefficient (A n)
    (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) (dyadicMomentOrder j)
      (largestPrime n) (n/largestPrime n) (D n)) y u hu hU
  · intro n hn
    have ht : log n ≤ 2*SquarefreeVaughanLogSource.length u (dyadicMomentOrder j) :=
      by nlinarith only [hL,hlog n hn,Nat.cast_nonneg (α := ℝ) (dyadicMomentOrder j)]
    have hb := partialCoefficient_bound (A n) (dyadicMomentOrder j) (hp n hn).1.pos
      (Nat.pos_of_ne_zero (hp n hn).2.1.ne_zero) (D n) (hD n hn) hLs
        (by simpa only [hprod n hn] using ht)
    rwa [hprod n hn] at hb
  · exact hs
  · exact hlog
  · exact fun n hn => (Finset.mem_filter.mp (hS hn)).2

/-- Crop the complete paid count population inside the current signed
central main after both exact affine cancellations. No count-by-count debit
or additional phase allowance is introduced. -/
theorem eventually_central_reducedCount_crop_bound :
    ∀ᶠ j : ℕ in atTop, ∀ (y u : ℝ) (A : ℕ → Finset ℕ),
      0≤u → u ≤ ZetaRieszWideOwnerAudit.radiusCeiling →
      (11/8 : ℝ)*dyadicMomentOrder j ≤ SquarefreeVaughanLogSource.length u (dyadicMomentOrder j) →
      let N := dyadicMomentOrder j
      let K := dyadicPrimeCount j
      let C := ((coreBand u N K).filter (fun n : ℕ => (197/100 : ℝ)*N<log n)).filter Squarefree
      let D := fun n => (n/largestPrime n).divisorsAntidiagonal \
        (cancelledOrbitDivisors u N n ∪ ZetaRieszCrossingOrbitCancellation.affineDivisors u N n)
      let f := fun n => ∑ db ∈ D n,
        phaseWeight (A n) (SquarefreeVaughanLogSource.length u N) N y
          (n/largestPrime n) (largestPrime n)*(μ db.2 : ℂ)*
            (pairHinge (SquarefreeVaughanLogSource.length u N) (largestPrime n) db.2 : ℂ)
      ‖(u : ℂ)^(N+1)*((∑ n ∈ C, f n)-
        ∑ n ∈ C \ reducedCountLabels u N K, f n)‖ ≤
        ((203/50 : ℝ)*(10001/20000))*((N : ℝ)+1)*paidCountRate^N := by
  filter_upwards [eventually_literal_reducedCount_bound] with j hJ y u A hu hU hL
  dsimp only
  have hsub : reducedCountLabels u (dyadicMomentOrder j) (dyadicPrimeCount j) ⊆
      ((coreBand u (dyadicMomentOrder j) (dyadicPrimeCount j)).filter
        (fun n : ℕ => (197/100 : ℝ)*dyadicMomentOrder j<log n)).filter Squarefree :=
    Finset.filter_subset _ _
  let D := fun n => (n/largestPrime n).divisorsAntidiagonal \
    (cancelledOrbitDivisors u (dyadicMomentOrder j) n ∪
      ZetaRieszCrossingOrbitCancellation.affineDivisors u (dyadicMomentOrder j) n)
  have hb := hJ (reducedCountLabels u (dyadicMomentOrder j) (dyadicPrimeCount j)) A D y u hu hU hL
    (Finset.Subset.refl _) (fun _ _ => Finset.sdiff_subset)
  have he : (∑ n ∈ reducedCountLabels u (dyadicMomentOrder j) (dyadicPrimeCount j),
      partialCoefficient (A n) (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j))
        (dyadicMomentOrder j) (largestPrime n) (n/largestPrime n) (D n)*
          zetaPrimeLogKernel (dyadicMomentOrder j) (3/2+Complex.I*y) n)=
      ∑ n ∈ reducedCountLabels u (dyadicMomentOrder j) (dyadicPrimeCount j), ∑ db ∈ D n,
        phaseWeight (A n) (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j))
          (dyadicMomentOrder j) y (n/largestPrime n) (largestPrime n)*(μ db.2 : ℂ)*
            (pairHinge (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) (largestPrime n) db.2 : ℂ) := by
    apply Finset.sum_congr rfl
    intro n hn
    have hc := (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).1
    have hp := ZetaRieszOwnedCells.largestPrime_mem_of_two
      (show 2 ≤ n.primeFactors.card from by
        have := ZetaRieszJointPrimeEnergy.core_count (Finset.mem_filter.mp hc).1
        omega)
    have hprod := Nat.mul_div_cancel' (Nat.dvd_of_mem_primeFactors hp)
    have ha := partial_atom_eq_original_incidences (A n)
      (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) (dyadicMomentOrder j)
        (largestPrime n) (n/largestPrime n) (D n) y
    rw [hprod] at ha
    exact ha
  rw [he] at hb
  have hsum := Finset.sum_sdiff hsub (f := fun n => ∑ db ∈ D n,
    phaseWeight (A n) (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j))
      (dyadicMomentOrder j) y (n/largestPrime n) (largestPrime n)*(μ db.2 : ℂ)*
        (pairHinge (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) (largestPrime n) db.2 : ℂ))
  rw [← hsum,add_sub_cancel_left]
  exact hb

/-- Direct two-sided global floor-ledger bounds after lowering the paid
count threshold by 256. All previous credits are unchanged and subtracted
once; the remaining main retains both hinges and every original phase. -/
theorem eventually_remaining_reducedCount_bounds {u : ℝ} (hu : 1/2<u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (y : ℝ) :
    ∀ᶠ j : ℕ in atTop,
    let N := dyadicMomentOrder j
    let K := dyadicPrimeCount j
    let C := ((coreBand u N K).filter (fun n : ℕ => (197/100 : ℝ)*N<log n)).filter Squarefree
    let D := fun n => (n/largestPrime n).divisorsAntidiagonal \
      (cancelledOrbitDivisors u N n ∪ ZetaRieszCrossingOrbitCancellation.affineDivisors u N n)
    let U := (∑ n ∈ C \ reducedCountLabels u N K, ∑ db ∈ D n,
      phaseWeight (if n ∈ hingeLabels u N K then ∅ else
        ZetaRieszAnnulusJoint.intermediatePrimes u N ∩ {largestPrime n})
        (SquarefreeVaughanLogSource.length u N) N y (n/largestPrime n) (largestPrime n)*
          (μ db.2 : ℂ)*(pairHinge (SquarefreeVaughanLogSource.length u N) (largestPrime n) db.2 : ℂ)).re-
      (ZetaRieszUnifiedSignedRows.largeOwnerIncidences u y N K).re-
      (ZetaRieszOwnerGapRows.ownerGapLiteralRows u y j+ZetaRieszOwnerGapRows.ownerGapEndpointRows u y j)-
      ZetaRieszPolynomialCutoffRows.literalCutoffPacket u y j
    let E := (503/500 : ℝ)*zetaMoebiusLogMajorantMass (2049/2048)*hingeAllocationRate^N+
      ((203/50 : ℝ)*(10001/20000))*((N : ℝ)+1)*paidCountRate^N;
    u^(N+1)*U-E ≤ u^(N+1)*ZetaRieszPolynomialCutoffRows.polynomialCentralRemaining u y j ∧
      u^(N+1)*ZetaRieszPolynomialCutoffRows.polynomialCentralRemaining u y j ≤ u^(N+1)*U+E := by
  have hlen := ZetaRieszLowerDegreeBounds.eventually_length_ge_exponent
    (by linarith : 0<u) (by norm_num : (0 : ℝ)≤11/16)
    (hU.trans_lt ZetaRieszWideOwnerAudit.radius_lt_source)
  filter_upwards [eventually_central_reducedCount_crop_bound,
    tendsto_dyadicMomentOrder.eventually hlen] with j hJ hLN
  dsimp only
  have hL : (11/8 : ℝ)*dyadicMomentOrder j ≤ SquarefreeVaughanLogSource.length u (dyadicMomentOrder j) :=
    by nlinarith only [hLN]
  have hp := polynomial_remaining_hinge_allocation_bounds j y (by linarith : 0≤u) hU hL
  have hb := hJ y u (fun n => if n ∈ hingeLabels u (dyadicMomentOrder j) (dyadicPrimeCount j)
      then ∅ else ZetaRieszAnnulusJoint.intermediatePrimes u (dyadicMomentOrder j) ∩ {largestPrime n})
    (by linarith : 0≤u) hU hL
  dsimp only at hp hb
  have hr := abs_le.mp ((Complex.abs_re_le_norm _).trans hb)
  rw [← Complex.ofReal_pow] at hr
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,Complex.sub_re] at hr
  constructor <;> nlinarith only [hp.1,hp.2,hr.1,hr.2]

/-- The remaining literal main has a strictly lower count ceiling. This
is an exact support statement, not a claim about the fraction of signed mass. -/
theorem count_lt_after_crop {u : ℝ} {N K n : ℕ}
    (hn : n ∈ (((coreBand u N K).filter (fun n : ℕ => (197/100 : ℝ)*N<log n)).filter Squarefree) \
      reducedCountLabels u N K) :
    256*n.primeFactors.card<K := by
  have hmem := Finset.mem_sdiff.mp hn
  apply lt_of_not_ge
  intro hcount
  exact hmem.2 (Finset.mem_filter.mpr ⟨hmem.1,hcount⟩)

/-- On genuine retained hinges the unpaid counts now lie between seven
and the reduced ceiling. No old low-count credit is counted again. -/
theorem retained_hinge_count_bounds {u : ℝ} {N K n : ℕ}
    (hn : n ∈ (((coreBand u N K).filter (fun n : ℕ => (197/100 : ℝ)*N<log n)).filter Squarefree) \
      reducedCountLabels u N K)
    (hh : n ∈ hingeLabels u N K)
    (hL : (11/8 : ℝ)*N ≤ SquarefreeVaughanLogSource.length u N) :
    7 ≤ n.primeFactors.card ∧ 256*n.primeFactors.card<K :=
  ⟨(hingeLabels_geometry hh hL).2.2.2.2.2,count_lt_after_crop hn⟩

/-- Both independent global savings in the final displayed ledger have
source-scale error tending to zero on the original cofinal schedule. -/
theorem tendsto_combined_reducedCount_error :
    Tendsto (fun j : ℕ => (503/500 : ℝ)*zetaMoebiusLogMajorantMass (2049/2048)*
      hingeAllocationRate^dyadicMomentOrder j+
      ((203/50 : ℝ)*(10001/20000))*((dyadicMomentOrder j : ℝ)+1)*
        paidCountRate^dyadicMomentOrder j) atTop (𝓝 0) := by
  have ht := (tendsto_hingeAllocationBudget.comp tendsto_dyadicMomentOrder).add
    tendsto_reducedCountBudget
  simpa only [Function.comp_def,zero_add] using ht

end RiemannGaussian.ZetaRieszReducedCountPayment
