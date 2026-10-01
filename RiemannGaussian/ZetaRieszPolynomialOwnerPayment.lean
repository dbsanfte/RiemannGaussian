/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszHingeAllocationPayment

/-!
# Pay complete polynomial-owner populations in the current signed floor

All original labels whose largest prime is at most `(N+1)^32` have an
independent geometric payment. The estimate is uniform in every selected
divisor incidence, allocation and complex phase. It does not norm-pay the
remaining signed prime rows. The original floor ledger and its credits are
retained; no count or prime interval is completed.
-/

noncomputable section
open Filter Topology Real
open scoped BigOperators Classical ArithmeticFunction.Moebius
namespace RiemannGaussian.ZetaRieszPolynomialOwnerPayment
open ZetaRieszPrimeCountMass ZetaRieszSmoothHead ZetaRieszEulerPrimeHeadDensity
open ZetaRieszSignedConvolution ZetaRieszUnsignedDivisorError
open ZetaRieszPrimeEndpoint ZetaRieszParityPacket ZetaRieszShortDivisorOrbits
open ZetaRieszHingeAllocationPayment

/-- The fixed arithmetic rate includes the sublinear finite Euler cost.
It is independent of phase height, count, labels and incidence masks. -/
def polynomialOwnerRate : ℝ := (10001/20000 : ℝ)*(64/33)*exp (1/256)

/-- A rational strict geometric margin for the whole polynomial-owner
population, rather than a polynomial improvement to the whole core. -/
theorem polynomialOwnerRate_bounds :
    0 < polynomialOwnerRate ∧ polynomialOwnerRate < 39/40 := by
  constructor
  · unfold polynomialOwnerRate; positivity
  · have he := add_one_le_exp (-(1/256 : ℝ))
    have hm := mul_le_mul_of_nonneg_left he (exp_pos (1/256 : ℝ)).le
    rw [← exp_add] at hm
    norm_num at hm
    unfold polynomialOwnerRate
    nlinarith

/-- On this actual prime support the Rankin comparison costs only
`(N+1)^(3/4)`, while its comparison mass is genuinely summable. -/
theorem polynomial_prime_mass_bound (S : Finset ℕ) (N : ℕ)
    (hS : ∀ p ∈ S, p.Prime ∧ p ≤ (N+1)^32) :
    (∑ p ∈ S, exp (-(63/64 : ℝ)*log p)) ≤
      exp ((3/4 : ℝ)*log ((N : ℝ)+1))*countMass (129/128) := by
  have hlog p (hp : p ∈ S) : log p ≤ 32*log ((N : ℝ)+1) := by
    have hn : (p : ℝ) ≤ ((N : ℝ)+1)^32 := by exact_mod_cast (hS p hp).2
    have hl := log_le_log (by exact_mod_cast (hS p hp).1.pos) hn
    rw [log_pow] at hl
    exact hl
  calc
    _ ≤ ∑ p ∈ S, exp ((3/4 : ℝ)*log ((N : ℝ)+1))*
        exp (-(129/128 : ℝ)*log p) := by
      apply Finset.sum_le_sum
      intro p hp
      rw [← exp_add]
      apply exp_le_exp.mpr
      linarith [hlog p hp]
    _ = exp ((3/4 : ℝ)*log ((N : ℝ)+1))*
        ∑ p ∈ S, exp (-(129/128 : ℝ)*log p) := (Finset.mul_sum ..).symm
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (exp_pos _).le
      exact (summable_zetaPrimeExpWeight (by norm_num : (1 : ℝ)<129/128)).sum_le_tsum
        S (fun _ _ => (exp_pos _).le)

/-- The entire original divisor-choice Euler product, not one count
class, has an explicit sublinear exponent on polynomial-owner labels. -/
theorem polynomial_head_product_bound (S : Finset ℕ) (N : ℕ)
    (hS : ∀ p ∈ S, p.Prime ∧ p ≤ (N+1)^32) :
    (∏ p ∈ S, (1+2*exp (-(63/64 : ℝ)*log p))) ≤
      exp (2*countMass (129/128)*exp ((3/4 : ℝ)*log ((N : ℝ)+1))) := by
  apply (head_product_le_exp_mass S (63/64)).trans
  apply exp_le_exp.mpr
  have hm := mul_le_mul_of_nonneg_left (polynomial_prime_mass_bound S N hS)
    (by norm_num : (0 : ℝ) ≤ 2)
  nlinarith only [hm]

/-- The sublinear Euler exponent is absorbed uniformly over all
polynomial prime subsets, at every sufficiently large original order. -/
theorem eventually_polynomial_head_product_bound :
    ∀ᶠ N : ℕ in atTop, ∀ S : Finset ℕ,
      (∀ p ∈ S, p.Prime ∧ p ≤ (N+1)^32) →
      (∏ p ∈ S, (1+2*exp (-(63/64 : ℝ)*log p))) ≤ exp ((N : ℝ)/256) := by
  have ht : Tendsto (fun N : ℕ => 2*countMass (129/128)*
      ((N : ℝ)+1)^(-(1/4 : ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero,Function.comp_def] using ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ)<1/4)).comp
    ((tendsto_natCast_atTop_atTop (R := ℝ)).atTop_add
      (tendsto_const_nhds (x := (1 : ℝ))))).const_mul (2*countMass (129/128))
  have hb : ∀ᶠ N : ℕ in atTop,
      2*countMass (129/128)*exp ((3/4 : ℝ)*log ((N : ℝ)+1)) ≤ (N : ℝ)/256 := by
    filter_upwards [ht.eventually (gt_mem_nhds (by norm_num : (0 : ℝ)<1/512)),
      eventually_ge_atTop (1 : ℕ)] with N hsmall hN
    have hn : (0 : ℝ)<(N : ℝ)+1 := by positivity
    have hid : ((N : ℝ)+1)^(-(1/4 : ℝ))*((N : ℝ)+1)=
        exp ((3/4 : ℝ)*log ((N : ℝ)+1)) := by
      calc
        _ = ((N : ℝ)+1)^(-(1/4 : ℝ))*((N : ℝ)+1)^(1 : ℝ) := by rw [rpow_one]
        _ = ((N : ℝ)+1)^(-(1/4 : ℝ)+1) := (rpow_add hn _ _).symm
        _ = _ := by norm_num; rw [rpow_def_of_pos hn]; ring_nf
    have hh := mul_le_mul_of_nonneg_right hsmall.le hn.le
    rw [mul_assoc,hid] at hh
    have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  filter_upwards [hb] with N hN S hS
  exact (polynomial_head_product_bound S N hS).trans (exp_le_exp.mpr hN)

/-- Arbitrary original coefficients with the established factor-two
partial-incidence majorant inherit one finite Euler bound. -/
theorem norm_partial_head_sum_bound (D S : Finset ℕ) (a : ℕ → ℂ)
    (N : ℕ) (y : ℝ)
    (ha : ∀ n ∈ D, ‖a n‖ ≤ 2*zetaMoebiusLogMajorant n)
    (hD : ∀ n ∈ D, Squarefree n)
    (hlog : ∀ n ∈ D, log n ≤ (203/100 : ℝ)*N)
    (hS : ∀ n ∈ D, n.primeFactors ⊆ S) :
    ‖∑ n ∈ D, a n*zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ ≤
      ((203/50 : ℝ)*(N : ℝ)*(64/33 : ℝ)^N)*
        ∏ p ∈ S, (1+2*exp (-(63/64 : ℝ)*log p)) := by
  have hb : ‖∑ n ∈ D, a n*zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ ≤
      ((203/50 : ℝ)*(N : ℝ)*(64/33 : ℝ)^N)*
        ∑ n ∈ D, (2 : ℝ)^n.primeFactors.card*exp (-(63/64 : ℝ)*log n) := by
    calc
      _ ≤ ∑ n ∈ D, ‖a n*zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ D, ((203/50 : ℝ)*(N : ℝ)*(64/33 : ℝ)^N)*
          ((2 : ℝ)^n.primeFactors.card*exp (-(63/64 : ℝ)*log n)) := by
        apply Finset.sum_le_sum
        intro n hn
        have hn1 : (1 : ℝ)≤n := by
          exact_mod_cast Nat.pos_of_ne_zero (hD n hn).ne_zero
        have hsupp : (1 : Polynomial ℂ).support={0} :=
          Polynomial.support_C (one_ne_zero : (1 : ℂ) ≠ 0)
        have hk := norm_zetaPrimeFilterKernel_le_tilt (1 : Polynomial ℂ) N
          (3/2+Complex.I*y) hn1 (by norm_num : (0 : ℝ)<33/64)
        simp only [ZetaRieszJointAllocation.filter_one_eq,hsupp,Finset.sum_singleton] at hk
        norm_num at hk
        have hc := (ha n hn).trans (mul_le_mul_of_nonneg_left
          ((logMajorant_le_prime_count (hD n hn)).trans
            (mul_le_mul_of_nonneg_right (hlog n hn) (by positivity)))
          (by norm_num : (0 : ℝ)≤2))
        rw [norm_mul]
        convert mul_le_mul hc hk (norm_nonneg _) (by positivity) using 1; ring
      _ = _ := (Finset.mul_sum ..).symm
  have hm := squarefree_head_mass_le D S hD hS (63/64)
  simp only [neg_mul] at hm hb ⊢
  exact hb.trans (mul_le_mul_of_nonneg_left hm (by positivity))

/-- One global geometric allowance for arbitrary dominated signed
coefficients on polynomial-owner labels. Heights and masks may vary freely. -/
theorem eventually_norm_polynomial_head_bound :
    ∀ᶠ N : ℕ in atTop, ∀ (D S : Finset ℕ) (a : ℕ → ℂ) (y u : ℝ),
      0 ≤ u → u ≤ ZetaRieszWideOwnerAudit.radiusCeiling →
      (∀ n ∈ D, ‖a n‖ ≤ 2*zetaMoebiusLogMajorant n) →
      (∀ n ∈ D, Squarefree n) → (∀ n ∈ D, log n ≤ (203/100 : ℝ)*N) →
      (∀ n ∈ D, n.primeFactors ⊆ S) →
      (∀ p ∈ S, p.Prime ∧ p ≤ (N+1)^32) →
      ‖(u : ℂ)^(N+1)*∑ n ∈ D, a n*zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ ≤
        ((203/50 : ℝ)*(10001/20000))*(N : ℝ)*polynomialOwnerRate^N := by
  filter_upwards [eventually_polynomial_head_product_bound] with N hN D S a y u
    hu hU ha hs hb hS hp
  have hcap : u ≤ (10001/20000 : ℝ) := hU
  have ht := (norm_partial_head_sum_bound D S a N y ha hs hb hS).trans
    (mul_le_mul_of_nonneg_left (hN S hp)
      (show 0 ≤ (203/50 : ℝ)*(N : ℝ)*(64/33 : ℝ)^N by positivity))
  rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg hu]
  apply (mul_le_mul_of_nonneg_left ht (pow_nonneg hu _)).trans
  calc
    _ ≤ (10001/20000 : ℝ)^(N+1)*
        (((203/50 : ℝ)*(N : ℝ)*(64/33 : ℝ)^N)*exp ((N : ℝ)/256)) := by gcongr
    _ = _ := by
      rw [show (N : ℝ)/256=(N : ℝ)*(1/256 : ℝ) by ring,exp_nat_mul]
      unfold polynomialOwnerRate
      rw [mul_pow,mul_pow,pow_succ]
      ring

/-- The fixed whole-population budget vanishes, with an explicit
geometric factor and no zero or cancellation hypothesis. -/
theorem tendsto_polynomialOwnerBudget :
    Tendsto (fun N : ℕ => ((203/50 : ℝ)*(10001/20000))*
      (N : ℝ)*polynomialOwnerRate^N) atTop (𝓝 0) := by
  have ht := tendsto_pow_const_mul_const_pow_of_lt_one 1
    polynomialOwnerRate_bounds.1.le
    (polynomialOwnerRate_bounds.2.trans (by norm_num : (39/40 : ℝ)<1))
  simpa only [pow_one,mul_zero,mul_assoc] using
    ht.const_mul ((203/50 : ℝ)*(10001/20000))

/-- Absorb the displayed linear prefactor into a fixed rational
geometric rate. The starting order is existential, not a numerical certificate. -/
theorem eventually_norm_polynomial_head_le_geometric :
    ∀ᶠ N : ℕ in atTop, ∀ (D S : Finset ℕ) (a : ℕ → ℂ) (y u : ℝ),
      0 ≤ u → u ≤ ZetaRieszWideOwnerAudit.radiusCeiling →
      (∀ n ∈ D, ‖a n‖ ≤ 2*zetaMoebiusLogMajorant n) →
      (∀ n ∈ D, Squarefree n) → (∀ n ∈ D, log n ≤ (203/100 : ℝ)*N) →
      (∀ n ∈ D, n.primeFactors ⊆ S) →
      (∀ p ∈ S, p.Prime ∧ p ≤ (N+1)^32) →
      ‖(u : ℂ)^(N+1)*∑ n ∈ D, a n*zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ ≤
        (39/40 : ℝ)^N := by
  have hr : 0 ≤ polynomialOwnerRate/(39/40 : ℝ) :=
    div_nonneg polynomialOwnerRate_bounds.1.le (by norm_num)
  have hr1 : polynomialOwnerRate/(39/40 : ℝ)<1 := by
    exact (div_lt_one (by norm_num : (0 : ℝ)<39/40)).mpr polynomialOwnerRate_bounds.2
  have ht : Tendsto (fun N : ℕ => ((203/50 : ℝ)*(10001/20000))*
      ((N : ℝ)*(polynomialOwnerRate/(39/40 : ℝ))^N)) atTop (𝓝 0) := by
    simpa only [pow_one,mul_zero] using
      (tendsto_pow_const_mul_const_pow_of_lt_one 1 hr hr1).const_mul
        ((203/50 : ℝ)*(10001/20000))
  filter_upwards [eventually_norm_polynomial_head_bound,
    ht.eventually (gt_mem_nhds (by norm_num : (0 : ℝ)<1))] with N hN hsmall
    D S a y u hu hU ha hs hb hS hp
  apply (hN D S a y u hu hU ha hs hb hS hp).trans
  have hh := mul_le_mul_of_nonneg_right hsmall.le
    (pow_nonneg (by norm_num : (0 : ℝ)≤39/40) N)
  rw [div_pow] at hh
  have hn : (39/40 : ℝ)^N ≠ 0 := (pow_pos (by norm_num : (0 : ℝ)<39/40) N).ne'
  field_simp at hh
  nlinarith only [hh]

/-- Every original prime is bounded by its canonical owner, including
at the integer level needed for the finite Euler support. -/
theorem prime_le_largestPrime {n p : ℕ} (hp : p ∈ n.primeFactors) :
    p ≤ largestPrime n := by
  have hne : n.primeFactors.Nonempty := ⟨p,hp⟩
  rw [largestPrime,dif_pos hne]
  exact Finset.le_max' _ p hp

/-- The paid population is a literal subset of the current central
core. It adds no new scalar carrier or completion. -/
def smallOwnerLabels (u : ℝ) (N K : ℕ) : Finset ℕ :=
  ((coreBand u N K).filter (fun n : ℕ => (197/100 : ℝ)*N<log n)).filter
    (fun n => Squarefree n ∧ largestPrime n ≤ (N+1)^32)

/-- All primes in every paid label obey the same polynomial threshold;
the complete original squarefree support is retained. -/
theorem smallOwnerLabels_prime_support {u : ℝ} {N K n p : ℕ}
    (hn : n ∈ smallOwnerLabels u N K) (hp : p ∈ n.primeFactors) :
    p.Prime ∧ p ≤ (N+1)^32 := by
  exact ⟨Nat.prime_of_mem_primeFactors hp,
    (prime_le_largestPrime hp).trans (Finset.mem_filter.mp hn).2.2⟩

private theorem smallOwnerLabels_geometry {u : ℝ} {N K n : ℕ}
    (hN : 1 ≤ N) (hn : n ∈ smallOwnerLabels u N K)
    (hL : (11/8 : ℝ)*N ≤ SquarefreeVaughanLogSource.length u N) :
    Squarefree n ∧ log n ≤ (203/100 : ℝ)*N ∧
      0 < largestPrime n ∧ 0 < n/largestPrime n ∧
      largestPrime n*(n/largestPrime n)=n ∧
      0 < SquarefreeVaughanLogSource.length u N ∧
      log n ≤ 2*SquarefreeVaughanLogSource.length u N := by
  obtain ⟨hc,hs,_⟩ := Finset.mem_filter.mp hn
  have hcore := (Finset.mem_filter.mp hc).1
  have hp := ZetaRieszOwnedCells.largestPrime_mem_of_two
    (by have := ZetaRieszJointPrimeEnergy.core_count hcore; omega : 2 ≤ n.primeFactors.card)
  have hd := core_data hcore hs
  have ht := (ZetaRieszLowerRadialPayment.central_log_bounds hc).2
  have hNr : (1 : ℝ)≤N := by exact_mod_cast hN
  refine ⟨hs,ht,(Nat.prime_of_mem_primeFactors hp).pos,
    Nat.pos_of_ne_zero hd.2.1.ne_zero,Nat.mul_div_cancel' (Nat.dvd_of_mem_primeFactors hp),?_,?_⟩
  · linarith only [hL,hNr]
  · nlinarith only [ht,hL,Nat.cast_nonneg (α := ℝ) N]

/-- Pay any selected ORIGINAL partial-incidence sum over the complete
small-owner population. Allocation, full phase, count and radial masks remain. -/
theorem eventually_literal_smallOwner_bound :
    ∀ᶠ N : ℕ in atTop, ∀ (K : ℕ) (y u : ℝ) (S : Finset ℕ)
      (A : ℕ → Finset ℕ) (D : ℕ → Finset (ℕ×ℕ)) (w : ℕ → ℂ),
      0 ≤ u → u ≤ ZetaRieszWideOwnerAudit.radiusCeiling →
      (11/8 : ℝ)*N ≤ SquarefreeVaughanLogSource.length u N →
      S ⊆ smallOwnerLabels u N K →
      (∀ n ∈ S, D n ⊆ (n/largestPrime n).divisorsAntidiagonal) →
      (∀ n ∈ S, ‖w n‖ ≤ 1) →
      ‖(u : ℂ)^(N+1)*∑ n ∈ S, w n*
        partialCoefficient (A n) (SquarefreeVaughanLogSource.length u N) N
          (largestPrime n) (n/largestPrime n) (D n)*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ ≤ (39/40 : ℝ)^N := by
  filter_upwards [eventually_norm_polynomial_head_le_geometric,
    eventually_ge_atTop (1 : ℕ)] with N hN hpos K y u S A D w hu hU hL hS hD hw
  let Q := S.biUnion Nat.primeFactors
  have hgeom n (hn : n ∈ S) := smallOwnerLabels_geometry hpos (hS hn) hL
  have hQ p (hp : p ∈ Q) : p.Prime ∧ p ≤ (N+1)^32 := by
    obtain ⟨n,hn,hp⟩ := Finset.mem_biUnion.mp hp
    exact smallOwnerLabels_prime_support (hS hn) hp
  apply hN S Q (fun n => w n*partialCoefficient (A n)
    (SquarefreeVaughanLogSource.length u N) N (largestPrime n) (n/largestPrime n) (D n))
    y u hu hU
  · intro n hn
    have hg := hgeom n hn
    have hb := partialCoefficient_bound (A n) N hg.2.2.1 hg.2.2.2.1 (D n)
      (hD n hn) hg.2.2.2.2.2.1 (by simpa only [hg.2.2.2.2.1] using hg.2.2.2.2.2.2)
    rw [hg.2.2.2.2.1] at hb
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hw n hn)).trans hb
  · exact fun n hn => (hgeom n hn).1
  · exact fun n hn => (hgeom n hn).2.1
  · intro n hn p hp
    exact Finset.mem_biUnion.mpr ⟨n,hn,hp⟩
  · exact hQ

/-- The paid coefficient is exactly the current literal signed incidence
sum, with the same original label on its factorial kernel. -/
theorem eventually_smallOwner_incidences_bound :
    ∀ᶠ N : ℕ in atTop, ∀ (K : ℕ) (y u : ℝ) (S : Finset ℕ)
      (A : ℕ → Finset ℕ) (D : ℕ → Finset (ℕ×ℕ)),
      0 ≤ u → u ≤ ZetaRieszWideOwnerAudit.radiusCeiling →
      (11/8 : ℝ)*N ≤ SquarefreeVaughanLogSource.length u N →
      S ⊆ smallOwnerLabels u N K →
      (∀ n ∈ S, D n ⊆ (n/largestPrime n).divisorsAntidiagonal) →
      ‖(u : ℂ)^(N+1)*∑ n ∈ S, ∑ db ∈ D n,
        phaseWeight (A n) (SquarefreeVaughanLogSource.length u N) N y
          (n/largestPrime n) (largestPrime n)*(μ db.2 : ℂ)*
            (pairHinge (SquarefreeVaughanLogSource.length u N) (largestPrime n) db.2 : ℂ)‖ ≤
        (39/40 : ℝ)^N := by
  filter_upwards [eventually_literal_smallOwner_bound,eventually_ge_atTop (1 : ℕ)] with
    N hN hpos K y u S A D hu hU hL hS hD
  have hb := hN K y u S A D (fun _ => (1 : ℂ)) hu hU hL hS hD
    (fun _ _ => by norm_num)
  simp only [one_mul] at hb
  have he : (∑ n ∈ S, partialCoefficient (A n)
        (SquarefreeVaughanLogSource.length u N) N (largestPrime n) (n/largestPrime n) (D n)*
          zetaPrimeLogKernel N (3/2+Complex.I*y) n)=
      ∑ n ∈ S, ∑ db ∈ D n,
        phaseWeight (A n) (SquarefreeVaughanLogSource.length u N) N y
          (n/largestPrime n) (largestPrime n)*(μ db.2 : ℂ)*
            (pairHinge (SquarefreeVaughanLogSource.length u N) (largestPrime n) db.2 : ℂ) := by
    apply Finset.sum_congr rfl
    intro n hn
    have hg := smallOwnerLabels_geometry hpos (hS hn) hL
    have ha := partial_atom_eq_original_incidences (A n)
      (SquarefreeVaughanLogSource.length u N) N (largestPrime n) (n/largestPrime n) (D n) y
    rw [hg.2.2.2.2.1] at ha
    exact ha
  rw [he] at hb
  exact hb

/-- Remove the complete polynomial-owner population from the current
central signed main. Both affine zero selectors, original allocation,
all count/radial/physical masks and original phases are unchanged. -/
theorem eventually_central_smallOwner_crop_bound :
    ∀ᶠ N : ℕ in atTop, ∀ (K : ℕ) (y u : ℝ) (A : ℕ → Finset ℕ),
      0 ≤ u → u ≤ ZetaRieszWideOwnerAudit.radiusCeiling →
      (11/8 : ℝ)*N ≤ SquarefreeVaughanLogSource.length u N →
      let C := ((coreBand u N K).filter (fun n : ℕ => (197/100 : ℝ)*N<log n)).filter Squarefree
      let D := fun n => (n/largestPrime n).divisorsAntidiagonal \
        (cancelledOrbitDivisors u N n ∪ ZetaRieszCrossingOrbitCancellation.affineDivisors u N n)
      let f := fun n => ∑ db ∈ D n,
        phaseWeight (A n) (SquarefreeVaughanLogSource.length u N) N y
          (n/largestPrime n) (largestPrime n)*(μ db.2 : ℂ)*
            (pairHinge (SquarefreeVaughanLogSource.length u N) (largestPrime n) db.2 : ℂ)
      ‖(u : ℂ)^(N+1)*((∑ n ∈ C, f n)-
        ∑ n ∈ C \ smallOwnerLabels u N K, f n)‖ ≤ (39/40 : ℝ)^N := by
  filter_upwards [eventually_smallOwner_incidences_bound] with N hN K y u A hu hU hL
  dsimp only
  have hsub : smallOwnerLabels u N K ⊆
      ((coreBand u N K).filter (fun n : ℕ => (197/100 : ℝ)*N<log n)).filter Squarefree := by
    intro n hn
    obtain ⟨hc,hs,_⟩ := Finset.mem_filter.mp hn
    exact Finset.mem_filter.mpr ⟨hc,hs⟩
  have hsum := Finset.sum_sdiff hsub (f := fun n =>
    ∑ db ∈ (n/largestPrime n).divisorsAntidiagonal \
        (cancelledOrbitDivisors u N n ∪ ZetaRieszCrossingOrbitCancellation.affineDivisors u N n),
      phaseWeight (A n) (SquarefreeVaughanLogSource.length u N) N y
        (n/largestPrime n) (largestPrime n)*(μ db.2 : ℂ)*
          (pairHinge (SquarefreeVaughanLogSource.length u N) (largestPrime n) db.2 : ℂ))
  rw [← hsum,add_sub_cancel_left]
  exact hN K y u (smallOwnerLabels u N K) A
    (fun n => (n/largestPrime n).divisorsAntidiagonal \
      (cancelledOrbitDivisors u N n ∪ ZetaRieszCrossingOrbitCancellation.affineDivisors u N n))
    hu hU hL (Finset.Subset.refl _) (fun _ _ => Finset.sdiff_subset)

/-- DIRECT bounds for the authoritative floor ledger after both proved
global savings: remove the selected hinge allocation and the complete
polynomial-owner label population. Earlier credits are unchanged and spent
once. The surviving signed prime rows, rather than their positive majorant,
are the remaining floor target. -/
theorem eventually_polynomial_remaining_crop_bounds {u : ℝ} (hu : 1/2<u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (y : ℝ) :
    ∀ᶠ j : ℕ in atTop,
    let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
    let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
    let C := ((coreBand u N K).filter (fun n : ℕ => (197/100 : ℝ)*N<log n)).filter Squarefree
    let D := fun n => (n/largestPrime n).divisorsAntidiagonal \
      (cancelledOrbitDivisors u N n ∪ ZetaRieszCrossingOrbitCancellation.affineDivisors u N n)
    let U := (∑ n ∈ C \ smallOwnerLabels u N K, ∑ db ∈ D n,
      phaseWeight (if n ∈ hingeLabels u N K then ∅ else
        ZetaRieszAnnulusJoint.intermediatePrimes u N ∩ {largestPrime n})
        (SquarefreeVaughanLogSource.length u N) N y (n/largestPrime n) (largestPrime n)*
          (μ db.2 : ℂ)*(pairHinge (SquarefreeVaughanLogSource.length u N) (largestPrime n) db.2 : ℂ)).re-
      (ZetaRieszUnifiedSignedRows.largeOwnerIncidences u y N K).re-
      (ZetaRieszOwnerGapRows.ownerGapLiteralRows u y j+ZetaRieszOwnerGapRows.ownerGapEndpointRows u y j)-
      ZetaRieszPolynomialCutoffRows.literalCutoffPacket u y j
    let E := (503/500 : ℝ)*zetaMoebiusLogMajorantMass (2049/2048)*hingeAllocationRate^N+
      (39/40 : ℝ)^N;
    u^(N+1)*U-E ≤ u^(N+1)*ZetaRieszPolynomialCutoffRows.polynomialCentralRemaining u y j ∧
      u^(N+1)*ZetaRieszPolynomialCutoffRows.polynomialCentralRemaining u y j ≤ u^(N+1)*U+E := by
  have hlen := ZetaRieszLowerDegreeBounds.eventually_length_ge_exponent
    (by linarith : 0<u) (by norm_num : (0 : ℝ)≤11/16)
    (hU.trans_lt ZetaRieszWideOwnerAudit.radius_lt_source)
  filter_upwards [ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
      eventually_central_smallOwner_crop_bound,
    ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually hlen] with j hN hLN
  dsimp only
  have hL : (11/8 : ℝ)*ZetaRieszPrimeCountFrequency.dyadicMomentOrder j ≤
      SquarefreeVaughanLogSource.length u (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j) :=
    by nlinarith only [hLN]
  have hp := polynomial_remaining_hinge_allocation_bounds j y (by linarith : 0≤u) hU hL
  have hb := hN (ZetaRieszPrimeCountFrequency.dyadicPrimeCount j) y u
    (fun n => if n ∈ hingeLabels u (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)
        (ZetaRieszPrimeCountFrequency.dyadicPrimeCount j) then ∅ else
      ZetaRieszAnnulusJoint.intermediatePrimes u (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j) ∩
        {largestPrime n}) (by linarith : 0≤u) hU hL
  dsimp only at hp hb
  have hr := abs_le.mp ((Complex.abs_re_le_norm _).trans hb)
  rw [← Complex.ofReal_pow] at hr
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,Complex.sub_re] at hr
  constructor <;> nlinarith only [hp.1,hp.2,hr.1,hr.2]

/-- The literal paid population vanishes for arbitrary moving phase
heights, prime-count ceilings, allocation masks and original divisor
selections. No exposed-zero or prime-cancellation hypothesis is used. -/
theorem tendsto_literal_smallOwner_sum (K : ℕ → ℕ) (S : ℕ → Finset ℕ)
    (A : ℕ → ℕ → Finset ℕ) (D : ℕ → ℕ → Finset (ℕ×ℕ))
    (w : ℕ → ℕ → ℂ) (y : ℕ → ℝ) {u : ℝ} (hu : 0<u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hS : ∀ N, S N ⊆ smallOwnerLabels u N (K N))
    (hD : ∀ N n, n ∈ S N → D N n ⊆ (n/largestPrime n).divisorsAntidiagonal)
    (hw : ∀ N n, n ∈ S N → ‖w N n‖ ≤ 1) :
    Tendsto (fun N : ℕ => (u : ℂ)^(N+1)*∑ n ∈ S N, w N n*
      partialCoefficient (A N n) (SquarefreeVaughanLogSource.length u N) N
        (largestPrime n) (n/largestPrime n) (D N n)*
      zetaPrimeLogKernel N (3/2+Complex.I*y N) n) atTop (𝓝 0) := by
  apply squeeze_zero_norm' (a := fun N : ℕ => (39/40 : ℝ)^N) ?_
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))
  filter_upwards [eventually_literal_smallOwner_bound,
    ZetaRieszLowerDegreeBounds.eventually_length_ge_exponent hu
      (by norm_num : (0 : ℝ)≤11/16)
      (hU.trans_lt ZetaRieszWideOwnerAudit.radius_lt_source)] with N hN hLN
  exact hN (K N) (y N) u (S N) (A N) (D N) (w N) hu.le hU
    (by nlinarith only [hLN]) (hS N) (hD N) (hw N)

/-- The combined ledger error tends to zero on the original dyadic
schedule, so neither new payment spends a positive fixed floor margin. -/
theorem tendsto_combined_crop_error :
    Tendsto (fun j : ℕ =>
      (503/500 : ℝ)*zetaMoebiusLogMajorantMass (2049/2048)*
        hingeAllocationRate^ZetaRieszPrimeCountFrequency.dyadicMomentOrder j+
      (39/40 : ℝ)^ZetaRieszPrimeCountFrequency.dyadicMomentOrder j) atTop (𝓝 0) := by
  have ht := (tendsto_hingeAllocationBudget.comp
    ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder).add
    ((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ)≤39/40)
      (by norm_num : (39/40 : ℝ)<1)).comp
        ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder)
  simpa only [Function.comp_def,zero_add] using ht

end RiemannGaussian.ZetaRieszPolynomialOwnerPayment
