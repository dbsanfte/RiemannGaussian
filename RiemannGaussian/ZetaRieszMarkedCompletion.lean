/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszMarkedEuler

/-!
# Arithmetic boundary estimates for the ordered marked completion

Completion means all squarefree subsets of the same finite physical prime
set. Whole-label masks are compared explicitly; no Euler-product identity
is used to assume that their difference is small.
-/

namespace RiemannGaussian.ZetaRieszMarkedCompletion
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszJointAllocation ZetaRieszJointBoundary ZetaRieszJointOwnerTransfer
open ZetaRieszLeastBoundary ZetaRieszAnnulusJoint ZetaRieszPrimeEndpoint
open ZetaRieszPrimeCountFrequency ZetaRieszWideOwnerAudit ZetaRieszParityPacket

/-- Every subset of a finite set of genuine primes is squarefree. -/
theorem squarefree_prime_product (A : Finset ℕ) (hA : ∀ p ∈ A, p.Prime) :
    Squarefree (∏ p ∈ A, p) := by
  refine Finset.squarefree_prod_of_pairwise_isCoprime (fun p hp q hq hpq => ?_)
    (fun p hp => (hA p hp).squarefree)
  change IsRelPrime p q
  rw [← Nat.coprime_iff_isRelPrime]
  exact (Nat.coprime_primes (hA p hp) (hA q hq)).mpr hpq

/-- The complete finite subset universe has no total-log, ownership or
prime-count ceiling. The two-mark rectangle kills its lower count cases. -/
def completeBand (A : Finset ℕ) : Finset ℕ :=
  (∏ p ∈ A, p).divisors.filter (fun n => 3 ≤ n.primeFactors.card)

theorem mem_completeBand (A : Finset ℕ) (hA : ∀ p ∈ A, p.Prime) (n : ℕ) :
    n ∈ completeBand A ↔ Squarefree n ∧ 3 ≤ n.primeFactors.card ∧
      ∀ p ∈ n.primeFactors, p ∈ A := by
  have hprod := squarefree_prime_product A hA
  have hpf := Nat.primeFactors_prod hA
  constructor
  · intro hn
    obtain ⟨hd,hc⟩ := Finset.mem_filter.mp hn
    have hdiv := Nat.dvd_of_mem_divisors hd
    refine ⟨hprod.squarefree_of_dvd hdiv,hc,?_⟩
    intro p hp
    have hh := Nat.primeFactors_mono hdiv hprod.ne_zero hp
    simpa only [hpf] using hh
  · rintro ⟨hn,hc,hs⟩
    change n ∈ (∏ p ∈ A, p).divisors.filter (fun n => 3 ≤ n.primeFactors.card)
    refine Finset.mem_filter.mpr ?_
    refine ⟨?_,hc⟩
    apply Nat.mem_divisors.mpr ⟨?_,hprod.ne_zero⟩
    rw [← Nat.prod_primeFactors_of_squarefree hn]
    exact Finset.prod_dvd_prod_of_subset _ _ (fun p : ℕ => p) hs

/-- The complete sum of original marked factorial incidence weights. -/
def markedMass (N n : ℕ) : ℝ := ∑ p ∈ n.primeFactors, markedWeight N n p

/-- The original signed arithmetic kernel on all physical squarefree
subsets, with its exact marked factorial mass. -/
def completePacket (u y : ℝ) (N : ℕ) : ℂ :=
  ∑ n ∈ completeBand (intermediatePrimes u N), (markedMass N n : ℂ)*
    (SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n*
      zetaPrimeLogKernel N (3/2+Complex.I*y) n)

/-- The completed subset universe restricted only to the original
core total-log window. -/
def coreBand (u : ℝ) (N : ℕ) : Finset ℕ :=
  LogarithmicDeviation.deviationBand (completeBand (intermediatePrimes u N)) (39/20) (203/100) N

/-- The exact completed response inside the core total-log window. -/
def corePacket (u y : ℝ) (N : ℕ) : ℂ :=
  ∑ n ∈ coreBand u N, (markedMass N n : ℂ)*
    (SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n*
      zetaPrimeLogKernel N (3/2+Complex.I*y) n)

/-- The retained share interior of the completed core response. -/
def interiorPacket (u y : ℝ) (N : ℕ) : ℂ :=
  ∑ n ∈ (coreBand u N).filter ZetaRieszLeastBoundary.interior, (markedMass N n : ℂ)*
    (SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n*
      zetaPrimeLogKernel N (3/2+Complex.I*y) n)

/-- The complementary share exterior, kept explicitly until its
source-normalized bound is proved. -/
def exteriorPacket (u y : ℝ) (N : ℕ) : ℂ :=
  ∑ n ∈ (coreBand u N).filter (fun n => ¬ZetaRieszLeastBoundary.interior n),
    (markedMass N n : ℂ)*
      (SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n)

theorem core_ledger (u y : ℝ) (N : ℕ) :
    corePacket u y N = interiorPacket u y N+exteriorPacket u y N := by
  exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm

theorem completeBand_data {u : ℝ} {N n : ℕ}
    (hn : n ∈ completeBand (intermediatePrimes u N)) :
    Squarefree n ∧ 1 < n ∧ 3 ≤ n.primeFactors.card ∧
      ∀ p ∈ n.primeFactors, p ∈ intermediatePrimes u N := by
  obtain ⟨hs,hc,hA⟩ := (mem_completeBand _
    (fun p hp => ((mem_intermediatePrimes u N p).mp hp).1) n).mp hn
  refine ⟨hs,?_,hc,hA⟩
  have h0 := hs.ne_zero
  have h1 : n ≠ 1 := by rintro rfl; norm_num at hc
  omega

/-- Complete radial tails are paid with the unchanged rectangle mass,
which is at most one even on the enlarged subset universe. -/
theorem exists_complete_radial_error :
    ∃ r C : ℝ, 0 ≤ r ∧ r < 1 ∧ 0 ≤ C ∧
      ∀ N : ℕ, 21 ≤ N → ∀ y u : ℝ, 0 ≤ u → u ≤ radiusCeiling →
        ‖(u : ℂ)^(N+1)*(completePacket u y N-corePacket u y N)‖ ≤ r^N*C := by
  obtain ⟨r,C,hr0,hr1,hC,h⟩ := ZetaArithmeticDeviationBounds.exists_uniform_deviation_bound
    (1 : Polynomial ℂ) (by norm_num [radiusCeiling])
    (by norm_num : (0 : ℝ) < 39/20) (by norm_num) (by norm_num : (2 : ℝ) < 203/100)
    core_window_costs.1 core_window_costs.2
  refine ⟨r,C,hr0,hr1,hC,?_⟩
  intro N hN y u hu hU
  have ha (n : ℕ) (hn : n ∈ completeBand (intermediatePrimes u N)) :
      ‖(markedMass N n : ℂ)*SquarefreeVaughanLogSource.coefficient
        (SquarefreeVaughanLogSource.length u N) n‖ ≤ zetaMoebiusLogMajorant n := by
    obtain ⟨hs,h1,_hc,_hA⟩ := completeBand_data hn
    have hw : 0 ≤ markedMass N n :=
      Finset.sum_nonneg (fun p _ => markedWeight_nonneg N n p)
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hw]
    exact (mul_le_of_le_one_left (norm_nonneg _) (marked_mass_le_one hs h1 N hN)).trans
      (SquarefreeVaughanLogSource.norm_coefficient_le (SquarefreeVaughanLogSource.length_pos u N) n)
  simpa only [completePacket, corePacket, coreBand, mul_assoc,
    SquarefreeEulerQuadratic.primeFilterKernel_one, zetaPrimeLogKernel] using
    h N (completeBand (intermediatePrimes u N)) (fun n =>
      (markedMass N n : ℂ)*SquarefreeVaughanLogSource.coefficient
        (SquarefreeVaughanLogSource.length u N) n) ha y u hu hU

/-- A wrong owner is paid with the actual factor count; a completed
universe must not reuse the obsolete fixed count ceiling. -/
theorem wrongWeight_le_card {n : ℕ} (hn : Squarefree n) (hn1 : 1 < n)
    (hp : largestPrime n ∈ n.primeFactors) (N : ℕ) :
    wrongWeight N n ≤ (n.primeFactors.card : ℝ)*2*Real.exp (-(N : ℝ)/1600) := by
  unfold wrongWeight
  calc
    _ ≤ ∑ _p ∈ n.primeFactors.erase (largestPrime n), 2*Real.exp (-(N : ℝ)/1600) := by
      apply Finset.sum_le_sum
      intro p hq
      obtain ⟨hne,hq⟩ := Finset.mem_erase.mp hq
      exact markedWeight_small_share hn hn1 hq N (wrong_owner_share hn hn1 hp hq hne)
    _ ≤ _ := by
      rw [Finset.sum_const, nsmul_eq_mul]
      have hc : ((n.primeFactors.erase (largestPrime n)).card : ℝ) ≤ n.primeFactors.card :=
        Nat.cast_le.mpr Finset.card_erase_le
      nlinarith [Real.exp_pos (-(N : ℝ)/1600)]

/-- The factor count costs only a logarithm, uniformly over the complete
physical subset universe. -/
theorem card_le_two_log {n : ℕ} (hn : Squarefree n) :
    (n.primeFactors.card : ℝ) ≤ 2*Real.log n := by
  have hh : (∑ _p ∈ n.primeFactors, (1/2 : ℝ)) ≤
      ∑ p ∈ n.primeFactors, Real.log p := by
    apply Finset.sum_le_sum
    intro p hp
    have hlog : Real.log (2 : ℝ) ≤ Real.log p :=
      Real.log_le_log (by norm_num) (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le)
    linarith [Real.log_two_gt_d9]
  rw [Finset.sum_const, nsmul_eq_mul,
    ← CoprimeEulerPhase.squarefree_log_eq_prime_sum hn] at hh
  linarith

/-- The whole marked mass outside the old share interior is exponentially
small with only one extra logarithmic factor. Counts remain unrestricted. -/
theorem markedMass_exterior {n : ℕ} (hn : Squarefree n) (hn1 : 1 < n)
    (hc : 3 ≤ n.primeFactors.card) (N : ℕ) (hN : 1 ≤ N)
    (he : ¬ZetaRieszLeastBoundary.interior n) :
    0 ≤ markedMass N n ∧
      markedMass N n ≤ 6*Real.log n*Real.exp (-(N : ℝ)/1600) := by
  have hp := ZetaRieszOwnedCells.largestPrime_mem_of_two (by omega : 2 ≤ n.primeFactors.card)
  have hw := weight_joint_exterior hn hn1 hp N hN he
  have hwrong := wrongWeight_le_card hn hn1 hp N
  have hcR : (3 : ℝ) ≤ n.primeFactors.card := by exact_mod_cast hc
  have hcLog := card_le_two_log hn
  refine ⟨Finset.sum_nonneg (fun p _ => markedWeight_nonneg N n p),?_⟩
  rw [markedMass, incidence_weight_ledger hp]
  nlinarith [Real.exp_pos (-(N : ℝ)/1600),
    mul_le_mul_of_nonneg_right hcLog (Real.exp_pos (-(N : ℝ)/1600)).le]

/-- The old count ceiling follows from the literal least-share interior,
without any assumption that the label already satisfies the old masks. -/
theorem interior_card_le {n : ℕ} (hn : Squarefree n) (hn1 : 1 < n)
    (hi : ZetaRieszLeastBoundary.interior n) : n.primeFactors.card ≤ 200 := by
  have hl : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn1)
  have hr : (1/200 : ℝ)*Real.log n ≤ Real.log n.minFac :=
    ((lt_div_iff₀ hl).mp hi.2.1).le
  have hs : (∑ _p ∈ n.primeFactors, (1/200 : ℝ)*Real.log n) ≤
      ∑ p ∈ n.primeFactors, Real.log p := by
    apply Finset.sum_le_sum
    intro p hp
    have hmin : n.minFac ≤ p := Nat.minFac_le_of_dvd
      (Nat.prime_of_mem_primeFactors hp).two_le (Nat.dvd_of_mem_primeFactors hp)
    exact hr.trans (Real.log_le_log
      (by exact_mod_cast (Nat.minFac_prime hn1.ne').pos)
      (by exact_mod_cast hmin))
  rw [Finset.sum_const, nsmul_eq_mul,
    ← CoprimeEulerPhase.squarefree_log_eq_prime_sum hn] at hs
  by_contra hc
  have hcR : (201 : ℝ) ≤ n.primeFactors.card := by exact_mod_cast (by omega : 201 ≤ n.primeFactors.card)
  nlinarith

/-- On the core and share interior, all original whole-label masks follow
arithmetically. Neither the cancelling nor dominant sector is reintroduced. -/
theorem core_interior_mem_fullBand (j : ℕ) (hj : 32 ≤ j) {u : ℝ}
    (hu : 1/2 < u) (hU : u ≤ radiusCeiling)
    (hL : (5/4 : ℝ)*dyadicMomentOrder j ≤ SquarefreeVaughanLogSource.length u (dyadicMomentOrder j))
    {n : ℕ} (hn : n ∈ completeBand (intermediatePrimes u (dyadicMomentOrder j)))
    (hi : ZetaRieszLeastBoundary.interior n)
    (hwindow : (39/20 : ℝ)*dyadicMomentOrder j < Real.log n ∧
      Real.log n ≤ (203/100 : ℝ)*dyadicMomentOrder j) :
    n ∈ fullBand u (dyadicMomentOrder j) (dyadicPrimeCount j) := by
  let N := dyadicMomentOrder j
  let K := dyadicPrimeCount j
  obtain ⟨hs,hc,hA⟩ := (mem_completeBand _
    (fun p hp => ((mem_intermediatePrimes u N p).mp hp).1) n).mp hn
  have hln : 0 < Real.log n := by nlinarith [hwindow.1,Nat.cast_nonneg (α := ℝ) N]
  have hn1 : 1 < n := by
    have hn0 := hs.ne_zero
    have hne : n ≠ 1 := by rintro rfl; norm_num at hln
    omega
  have hcU := interior_card_le hs hn1 hi
  have hK : 200 < K := by
    have hh := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) (show 8 ≤ j+3 by omega)
    norm_num [K,dyadicPrimeCount] at hh ⊢
    omega
  have hmax := ZetaRieszOwnedCells.largestPrime_mem_of_two (by omega : 2 ≤ n.primeFactors.card)
  have hdom (p : ℕ) (hp : p ∈ n.primeFactors) :
      Real.log p < (13/20 : ℝ)*Real.log n := by
    have hne : n.primeFactors.Nonempty := ⟨p,hp⟩
    have hple : p ≤ largestPrime n := by
      rw [largestPrime, dif_pos hne]
      exact Finset.le_max' _ _ hp
    have hlog : Real.log p ≤ Real.log (largestPrime n) :=
      Real.log_le_log (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos)
      (by exact_mod_cast hple)
    have hhi := (div_lt_iff₀ hln).mp hi.1.2
    linarith
  have hmem := ZetaRieszMaskSupport.window_mem_originalMask j hj hu
    (hU.trans radius_lt_source.le) hL
    ((mem_literalWindow N n).mpr (by constructor <;> nlinarith [hwindow.1,hwindow.2]))
    hs hc (by omega)
    (fun p hp => ((mem_intermediatePrimes u N p).mp (hA p hp)).2.2)
  have hcancel : n ∉ cancellingSector u N K := by
    intro hh
    obtain ⟨_,_,_,_,_,p,hp,_,_,_,hhi⟩ := Finset.mem_filter.mp hh
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hlog : Real.log (n/p : ℕ) = Real.log n-Real.log p := by
      rw [Nat.cast_div (Nat.dvd_of_mem_primeFactors hp) (by exact_mod_cast hpp.ne_zero),
        Real.log_div (by exact_mod_cast hs.ne_zero) (by exact_mod_cast hpp.ne_zero)]
    have hh' := (div_le_iff₀ hln).mp hhi
    rw [hlog] at hh'
    nlinarith [hdom p hp]
  have hret : n ∈ ZetaRieszMaskSupport.retainedBand u N K :=
    Finset.mem_sdiff.mpr ⟨hmem,hcancel⟩
  have hnd : n ∈ ZetaRieszDominantAllocation.nondominantBand u N K := by
    refine Finset.mem_sdiff.mpr ⟨hret,?_⟩
    intro hh
    obtain ⟨_,_,_,_,p,hp,_,_,hlarge⟩ := Finset.mem_filter.mp hh
    exact (hdom p hp).not_ge hlarge
  have hcore : n ∈ ZetaRieszParityPacket.coreBand u N K := Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
    ⟨hnd,by constructor <;> nlinarith [hwindow.1,hwindow.2]⟩,hwindow⟩
  exact Finset.mem_filter.mpr ⟨hcore,hs,hn1,hc,hmax,hA⟩

/-- Exact agreement of the completed interior with the original support,
after every count, physical and previous-deletion mask has been checked. -/
theorem core_interior_eq (j : ℕ) (hj : 32 ≤ j) {u : ℝ}
    (hu : 1/2 < u) (hU : u ≤ radiusCeiling)
    (hL : (5/4 : ℝ)*dyadicMomentOrder j ≤ SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) :
    (coreBand u (dyadicMomentOrder j)).filter ZetaRieszLeastBoundary.interior =
      (fullBand u (dyadicMomentOrder j) (dyadicPrimeCount j)).filter ZetaRieszLeastBoundary.interior := by
  ext n
  constructor
  · intro hn
    obtain ⟨hb,hi⟩ := Finset.mem_filter.mp hn
    obtain ⟨hc,hw⟩ := Finset.mem_filter.mp hb
    exact Finset.mem_filter.mpr ⟨core_interior_mem_fullBand j hj hu hU hL hc hi hw,hi⟩
  · intro hn
    obtain ⟨hb,hi⟩ := Finset.mem_filter.mp hn
    obtain ⟨hcore,hs,h1,hc,_hp,hA⟩ := Finset.mem_filter.mp hb
    apply Finset.mem_filter.mpr ⟨?_,hi⟩
    change n ∈ (completeBand (intermediatePrimes u (dyadicMomentOrder j))).filter _
    refine Finset.mem_filter.mpr ?_
    refine ⟨?_,(Finset.mem_filter.mp hcore).2⟩
    exact (mem_completeBand _
      (fun p hp => ((mem_intermediatePrimes u (dyadicMomentOrder j) p).mp hp).1) n).mpr
        ⟨hs,hc,hA⟩

theorem interiorPacket_eq_raw (j : ℕ) (hj : 32 ≤ j) {u : ℝ}
    (hu : 1/2 < u) (hU : u ≤ radiusCeiling)
    (hL : (5/4 : ℝ)*dyadicMomentOrder j ≤ SquarefreeVaughanLogSource.length u (dyadicMomentOrder j))
    (y : ℝ) :
    interiorPacket u y (dyadicMomentOrder j) =
      rawInteriorPacket u y (dyadicMomentOrder j) (dyadicPrimeCount j) := by
  rw [interiorPacket, core_interior_eq j hj hu hU hL]
  rfl

/-- The logarithm from the unrestricted incidence count costs one
factorial shift, not a new exponential rate. -/
theorem log_norm_kernel (N n : ℕ) (s : ℂ) :
    Real.log n*‖zetaPrimeLogKernel N s n‖ =
      (N+1 : ℝ)*‖zetaPrimeLogKernel (N+1) s n‖ := by
  have h := congrArg (fun z : ℂ => ‖z‖) (ZetaRieszHeadOrders.log_mul_kernel N n s)
  have hc : ‖((N+1 : ℕ) : ℂ)‖ = ((N+1 : ℕ) : ℝ) := norm_natCast _
  rw [norm_mul,norm_mul,Complex.norm_real,
    Real.norm_of_nonneg (Real.log_natCast_nonneg n),hc] at h
  simpa only [Nat.cast_add,Nat.cast_one] using h

/-- Source-scale completion of both share boundaries, with the entire
prime-count range paid. The polynomial factor is explicit. -/
theorem exteriorPacket_bound {u : ℝ} (hu : 0 ≤ u) (hU : u ≤ radiusCeiling)
    (N : ℕ) (hN : 1 ≤ N) (y : ℝ) :
    ‖(u : ℂ)^(N+1)*exteriorPacket u y N‖ ≤
      (6*radiusCeiling*(131071/262144 : ℝ)⁻¹)*
        ((N+1 : ℝ)*exteriorRate^N)*zetaMoebiusLogMajorantMass (1+1/262144) := by
  have ha (n : ℕ) (hn : n ∈ (coreBand u N).filter (fun n => ¬ZetaRieszLeastBoundary.interior n)) :
      ‖(u : ℂ)^(N+1)*((markedMass N n : ℂ)*
        (SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n*
          zetaPrimeLogKernel N (3/2+Complex.I*y) n))‖ ≤
      (6*radiusCeiling*(131071/262144 : ℝ)⁻¹)*((N+1 : ℝ)*exteriorRate^N)*
        (zetaMoebiusLogMajorant n*zetaPrimeExpWeight (1+1/262144) n) := by
    obtain ⟨hs,h1,hc,_hA⟩ := completeBand_data
      (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).1
    have hw := markedMass_exterior hs h1 hc N hN (Finset.mem_filter.mp hn).2
    have hcoef := SquarefreeVaughanLogSource.norm_coefficient_le
      (SquarefreeVaughanLogSource.length_pos u N) n
    have hmajorant : 0 ≤ zetaMoebiusLogMajorant n := zetaMoebiusLogMajorant_nonneg n
    have hk : ‖zetaPrimeLogKernel (N+1) (3/2+Complex.I*y) n‖ ≤
        (131071/262144 : ℝ)⁻¹^(N+1)*zetaPrimeExpWeight (1+1/262144) n := by
      convert norm_zetaPrimeLogKernel_le (N+1) (3/2+Complex.I*y) n
        (by norm_num : (0 : ℝ) < 131071/262144) using 1
      norm_num
    have he : Real.exp (-(N : ℝ)/1600) = Real.exp (-(1/1600 : ℝ))^N := by
      rw [← Real.exp_nat_mul]; congr 1; ring
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hu,
      norm_mul, Complex.norm_real, Real.norm_of_nonneg hw.1, norm_mul]
    calc
      _ ≤ radiusCeiling^(N+1)*((6*Real.log n*Real.exp (-(N : ℝ)/1600))*
          (zetaMoebiusLogMajorant n*‖zetaPrimeLogKernel N (3/2+Complex.I*y) n‖)) := by
        gcongr
        · exact mul_nonneg hw.1 (mul_nonneg (norm_nonneg _) (norm_nonneg _))
        · unfold radiusCeiling; positivity
        · exact hw.2
      _ = 6*radiusCeiling^(N+1)*Real.exp (-(N : ℝ)/1600)*zetaMoebiusLogMajorant n*
          ((N+1 : ℝ)*‖zetaPrimeLogKernel (N+1) (3/2+Complex.I*y) n‖) := by
        rw [← log_norm_kernel]; ring
      _ ≤ 6*radiusCeiling^(N+1)*Real.exp (-(N : ℝ)/1600)*zetaMoebiusLogMajorant n*
          ((N+1 : ℝ)*((131071/262144 : ℝ)⁻¹^(N+1)*zetaPrimeExpWeight (1+1/262144) n)) := by
        gcongr
        all_goals first | exact hk | exact zetaMoebiusLogMajorant_nonneg n |
          (unfold radiusCeiling; positivity)
      _ = _ := by rw [he,exteriorRate,mul_pow,mul_pow,pow_succ,pow_succ]; ring
  rw [exteriorPacket, Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ n ∈ (coreBand u N).filter (fun n => ¬ZetaRieszLeastBoundary.interior n),
        (6*radiusCeiling*(131071/262144 : ℝ)⁻¹)*((N+1 : ℝ)*exteriorRate^N)*
          (zetaMoebiusLogMajorant n*zetaPrimeExpWeight (1+1/262144) n) := Finset.sum_le_sum ha
    _ ≤ _ := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left
        (Summable.sum_le_tsum _ (fun n _ => mul_nonneg (zetaMoebiusLogMajorant_nonneg n)
          (Real.exp_pos _).le) (summable_zetaMoebiusLogMajorant (by norm_num)))
        (by apply mul_nonneg <;> first | (unfold radiusCeiling; positivity) |
          exact mul_nonneg (by positivity) (pow_nonneg exteriorRate_bounds.1 _))

theorem tendsto_complete_sub_core {u : ℝ} (hu : 0 ≤ u) (hU : u ≤ radiusCeiling)
    (heights : ℕ → ℝ) :
    Tendsto (fun N => (u : ℂ)^(N+1)*(completePacket u (heights N) N-corePacket u (heights N) N))
      atTop (𝓝 0) := by
  obtain ⟨r,C,hr0,hr1,_hC,h⟩ := exists_complete_radial_error
  have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).mul_const C
  simp only [zero_mul] at ht
  apply squeeze_zero_norm' _ ht
  filter_upwards [eventually_ge_atTop 21] with N hN
  exact h N hN _ _ hu hU

theorem tendsto_core_sub_interior {u : ℝ} (hu : 0 ≤ u) (hU : u ≤ radiusCeiling)
    (heights : ℕ → ℝ) :
    Tendsto (fun N => (u : ℂ)^(N+1)*(corePacket u (heights N) N-interiorPacket u (heights N) N))
      atTop (𝓝 0) := by
  have hr : 0 < exteriorRate := by unfold exteriorRate radiusCeiling; positivity
  have ht := ((ZetaRieszEulerPrimeHeadDensity.tendsto_successor_pow_mul_geometric
    1 hr exteriorRate_bounds.2).const_mul (6*radiusCeiling*(131071/262144 : ℝ)⁻¹)).mul_const
      (zetaMoebiusLogMajorantMass (1+1/262144))
  simp only [pow_one, mul_zero, zero_mul] at ht
  apply squeeze_zero_norm' _ ht
  filter_upwards [eventually_ge_atTop 1] with N hN
  rw [core_ledger,add_sub_cancel_left]
  exact exteriorPacket_bound hu hU N hN _

/-- The CURRENT signed counts 3..55 minus upper-overflow counts 3..13
are source-equivalent to the all-count finite physical completion.
The comparison is independent of zeros and assumes no signed estimate. -/
theorem tendsto_complete_sub_current {u : ℝ} (hu : 1/2 < u)
    (hU : u ≤ radiusCeiling) (y : ℝ) :
    Tendsto (fun j => (u : ℂ)^(dyadicMomentOrder j+1)*
      (completePacket u y (dyadicMomentOrder j)-
        (ZetaRieszLeastOrderOverflow.lowerThresholdPacket u y (dyadicMomentOrder j) (dyadicPrimeCount j)-
          ZetaRieszLeastOrderOverflow.shortOverflowPacket u y (dyadicMomentOrder j) (dyadicPrimeCount j))))
      atTop (𝓝 0) := by
  have hu0 : 0 ≤ u := by linarith
  have hrad := (tendsto_complete_sub_core hu0 hU (fun _ => y)).comp tendsto_dyadicMomentOrder
  have hshare := (tendsto_core_sub_interior hu0 hU (fun _ => y)).comp tendsto_dyadicMomentOrder
  have hraw := ZetaRieszLeastBoundary.tendsto_raw_sub_full hu0 hU (fun _ => y)
    dyadicMomentOrder dyadicPrimeCount tendsto_dyadicMomentOrder
  have htarget := ZetaRieszLeastOrderOverflow.tendsto_full_sub_joint_boundary hu0 hU (fun _ => y)
    dyadicMomentOrder dyadicPrimeCount tendsto_dyadicMomentOrder
  have h := ((hrad.add hshare).add hraw).add htarget
  simp only [zero_add] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 32,
    tendsto_dyadicMomentOrder.eventually (ZetaRieszMaskSupport.eventually_length_lower
      (by linarith : 0 < u) (hU.trans radius_lt_source.le))] with j hj hL
  simp only [Function.comp_def]
  rw [interiorPacket_eq_raw j hj hu hU hL y]
  ring


end
end RiemannGaussian.ZetaRieszMarkedCompletion
