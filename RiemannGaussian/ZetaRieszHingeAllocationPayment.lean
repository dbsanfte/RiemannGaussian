/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszHingePairCancellation
import RiemannGaussian.ZetaRieszNonownerAllocation

/-!
# Pay the owner allocation on the surviving hinge population

A genuine cofactor hinge with failed based-owner gap forces the ORIGINAL
largest prime below 131N/400. On the retained central window every original
prime carries at most one sixth of the original logarithm. Its unique-owner
allocation costs exp(-N/8); the WHOLE source-scale sum has rate below 9/10,
even for arbitrary selected original divisor incidences.

Only the allocation difference is norm-paid. The unallocated signed hinge,
its original label, phase, count and physical masks remain in the main sum.
-/

noncomputable section
open Filter Topology Real
open scoped BigOperators Classical ArithmeticFunction.Moebius
namespace RiemannGaussian.ZetaRieszHingeAllocationPayment
open ZetaRieszPrimeEndpoint ZetaRieszParityPacket ZetaRieszJointAllocation
open ZetaRieszShortDivisorOrbits ZetaRieszUnsignedDivisorError
open ZetaRieszBalancedCompanion ZetaRieszNonownerAllocation
open ZetaRieszSignedConvolution

/-- A cofactor hinge and failure of the based-owner gap force a small
ORIGINAL owner. No replacement of the factorial label by its based quotient
is made here. -/
theorem hinge_owner_log_le {u : ℝ} {N K n e : ℕ}
    (hn : n ∈ coreBand u N K) (hs : Squarefree n)
    (he : e ∣ n/largestPrime n)
    (hhinge : SquarefreeVaughanLogSource.length u N ≤
      log ((n/largestPrime n)/e : ℕ))
    (hgap : log n-log e+log (largestPrime n) ≤ (203/100 : ℝ)*N)
    (hL : (11/8 : ℝ)*N ≤ SquarefreeVaughanLogSource.length u N) :
    log (largestPrime n) ≤ (131/400 : ℝ)*N := by
  have hd := core_data hn hs
  have hl := base_log hd.2.1 hd.1 he
  have hp := ZetaRieszOwnedCells.largestPrime_mem_of_two
    (by have := ZetaRieszJointPrimeEnergy.core_count hn; omega : 2 ≤ n.primeFactors.card)
  have hnprod : largestPrime n*(n/largestPrime n)=n :=
    Nat.mul_div_cancel' (Nat.dvd_of_mem_primeFactors hp)
  have hb0 : 0 < (n/largestPrime n)/e := Nat.div_pos
    (Nat.le_of_dvd (Nat.pos_of_ne_zero hd.2.1.ne_zero) he)
    (Nat.pos_of_dvd_of_pos he (Nat.pos_of_ne_zero hd.2.1.ne_zero))
  have hprod : log (largestPrime n*((n/largestPrime n)/e) : ℕ)=
      log (largestPrime n)+log ((n/largestPrime n)/e : ℕ) := by
    rw [Nat.cast_mul,log_mul (by exact_mod_cast hd.1.ne_zero)
      (by exact_mod_cast hb0.ne')]
  rw [hnprod,hprod] at hl
  linarith

/-- All original prime factors, including the unique owner, carry at most
ONE SIXTH of the original total logarithm
on a genuine failed-gap hinge in the current central radial window. -/
theorem hinge_all_primes_log_le_sixth {u : ℝ} {N K n e : ℕ}
    (hn : n ∈ (coreBand u N K).filter
      (fun n : ℕ => (197/100 : ℝ)*N < log n))
    (hs : Squarefree n) (he : e ∣ n/largestPrime n)
    (hhinge : SquarefreeVaughanLogSource.length u N ≤
      log ((n/largestPrime n)/e : ℕ))
    (hgap : log n-log e+log (largestPrime n) ≤ (203/100 : ℝ)*N)
    (hL : (11/8 : ℝ)*N ≤ SquarefreeVaughanLogSource.length u N)
    {q : ℕ} (hq : q ∈ n.primeFactors) : log q ≤ log n/6 := by
  have hcore := (Finset.mem_filter.mp hn).1
  have hP := hinge_owner_log_le hcore hs he hhinge hgap hL
  have hne : n.primeFactors.Nonempty := ⟨q,hq⟩
  have hm : n.primeFactors.max' hne=largestPrime n := by
    simp only [largestPrime,dif_pos hne]
  have hqP : log q ≤ log (largestPrime n) :=
    log_le_log (by exact_mod_cast (Nat.prime_of_mem_primeFactors hq).pos)
      (by exact_mod_cast (Finset.le_max' _ q hq).trans_eq hm)
  have hT := (ZetaRieszLowerRadialPayment.central_log_bounds hn).1
  nlinarith [Nat.cast_nonneg (α := ℝ) N]

/-- Such a hinge has at least SEVEN original prime factors. This excludes
the previously paid low-count populations rather than reusing their credits. -/
theorem hinge_count_ge_seven {u : ℝ} {N K n e : ℕ}
    (hn : n ∈ (coreBand u N K).filter
      (fun n : ℕ => (197/100 : ℝ)*N < log n))
    (hs : Squarefree n) (he : e ∣ n/largestPrime n)
    (hhinge : SquarefreeVaughanLogSource.length u N ≤
      log ((n/largestPrime n)/e : ℕ))
    (hgap : log n-log e+log (largestPrime n) ≤ (203/100 : ℝ)*N)
    (hL : (11/8 : ℝ)*N ≤ SquarefreeVaughanLogSource.length u N) :
    7 ≤ n.primeFactors.card := by
  have hP := hinge_owner_log_le (Finset.mem_filter.mp hn).1 hs he hhinge hgap hL
  have hc := ZetaRieszJointPrimeEnergy.core_count (Finset.mem_filter.mp hn).1
  have hne : n.primeFactors.Nonempty := Finset.card_pos.mp (by omega)
  have hm : n.primeFactors.max' hne=largestPrime n := by
    simp only [largestPrime,dif_pos hne]
  have hlog : log n ≤ (n.primeFactors.card : ℝ)*log (largestPrime n) := by
    calc
      _ = ∑ q ∈ n.primeFactors, log q := CoprimeEulerPhase.squarefree_log_eq_prime_sum hs
      _ ≤ ∑ _q ∈ n.primeFactors, log (largestPrime n) := by
        apply Finset.sum_le_sum
        intro q hq
        exact log_le_log (by exact_mod_cast (Nat.prime_of_mem_primeFactors hq).pos)
          (by exact_mod_cast (Finset.le_max' _ q hq).trans_eq hm)
      _ = _ := by simp
  by_contra hcount
  have hc6 : (n.primeFactors.card : ℝ) ≤ 6 := by exact_mod_cast (by omega : n.primeFactors.card ≤ 6)
  have hT := (ZetaRieszLowerRadialPayment.central_log_bounds hn).1
  have hupper := hlog.trans (mul_le_mul_of_nonneg_right hc6
    (log_natCast_nonneg (largestPrime n)))
  nlinarith [Nat.cast_nonneg (α := ℝ) N]

private theorem boundedShare_empty (N n : ℕ) : boundedShare ∅ N n=0 := by
  simp [boundedShare,allocationShare,assignedAmplitude]

/-- The actual five-sixths cofactor share certifies a much stronger tilt
than mere balancedness. The original unpaid order endpoint is unchanged. -/
theorem sixth_log_rate : log (7/12 : ℝ)+(13/32 : ℝ)*log 2 ≤ -(1/8 : ℝ) := by
  have hlog := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 7/12)
  linarith [log_two_lt_d9]

/-- Every original unpaid factorial order is retained, but its complete
mass costs at most exp(-N/8) when the cofactor share is at least five sixths. -/
theorem unpaid_mass_five_sixths_le (N : ℕ) {x : ℝ}
    (hx : (5/6 : ℝ) ≤ x) (hx1 : x ≤ 1) :
    (∑ k ∈ ZetaRieszWingHighOrders.unpaidOrders N, mass (N+1) k x) ≤
      exp (-(N : ℝ)/8) := by
  have hx0 : 0 ≤ x := by linarith
  have ht : 0 ≤ log (2 : ℝ) := log_nonneg (by norm_num)
  have hUS : ZetaRieszWingHighOrders.unpaidOrders N ⊆ Finset.range (N+1+1) := by
    intro k hk
    have h := unpaid_orders_submajority N k hk
    simp only [Finset.mem_range]
    omega
  have hh := selected_tilt_bound (N+1) _ hUS hx0 hx1
    (by norm_num : (0 : ℝ) ≤ 1/2) (exp_pos ((13/32 : ℝ)*N*log 2)).le ?_
  · have hb : ((1/2 : ℝ)*x+(1-x))^(N+1) ≤ (7/12 : ℝ)^(N+1) :=
      pow_le_pow_left₀ (by linarith) (by linarith) _
    have he : exp ((13/32 : ℝ)*N*log 2)*(7/12 : ℝ)^(N+1)=
        (7/12 : ℝ)*exp ((N : ℝ)*(log (7/12 : ℝ)+(13/32 : ℝ)*log 2)) := by
      rw [pow_succ]
      have hp : (7/12 : ℝ)^N=exp ((N : ℝ)*log (7/12 : ℝ)) := by
        rw [exp_nat_mul,exp_log (by norm_num : (0 : ℝ) < 7/12)]
      rw [hp]
      rw [show (N : ℝ)*(log (7/12 : ℝ)+(13/32 : ℝ)*log 2)=
        (13/32 : ℝ)*N*log 2+(N : ℝ)*log (7/12 : ℝ) by ring,exp_add]
      ring
    have hrate : exp ((N : ℝ)*(log (7/12 : ℝ)+(13/32 : ℝ)*log 2)) ≤ exp (-(N : ℝ)/8) :=
      exp_le_exp.mpr (by
        nlinarith [mul_le_mul_of_nonneg_left sixth_log_rate (Nat.cast_nonneg (α := ℝ) N)])
    have hprod := mul_le_mul_of_nonneg_left hb (exp_pos ((13/32 : ℝ)*N*log 2)).le
    rw [he] at hprod
    nlinarith [exp_pos (-(N : ℝ)/8)]
  · intro k hk
    have hkcut := (ZetaRieszWingHighOrders.unpaidOrders_support hk).2.1
    have hc : (k : ℝ) ≤ (13/32 : ℝ)*N := by
      have hn : 32*k ≤ 13*N := by omega
      have hnR : (32 : ℝ)*k ≤ 13*N := by exact_mod_cast hn
      linarith
    have he : (1/2 : ℝ)=exp (-log (2 : ℝ)) := by
      rw [exp_neg,exp_log (by norm_num : (0 : ℝ) < 2)]
      norm_num
    rw [he,← exp_nat_mul,← exp_add]
    apply one_le_exp_iff.mpr
    nlinarith [mul_le_mul_of_nonneg_right hc ht]

/-- The SINGLE selected balanced prime has an exponential allocation bound
without a prime-count multiplier. Eligibility and every factorial order are
still exactly those of the original allocation. -/
theorem owner_share_le (A : Finset ℕ) (N : ℕ) {n p : ℕ}
    (hp : p ∈ n.primeFactors) (hbal : log p ≤ log n/6) :
    boundedShare (A ∩ {p}) N n ≤ exp (-(N : ℝ)/8) := by
  by_cases hs : Squarefree n ∧ 1<n ∧ ¬n.Prime
  · rw [boundedShare,if_pos hs,share_eq_binomial_sum _ N hs.1 hs.2.1]
    rw [Finset.sum_eq_single p]
    · by_cases hel : p ∈ A ∩ {p} ∧ eligibleCofactor p (n/p)
      · rw [if_pos hel]
        have hpp := Nat.prime_of_mem_primeFactors hp
        have hlog : log (n/p : ℕ)=log n-log p := by
          rw [Nat.cast_div (Nat.dvd_of_mem_primeFactors hp)
            (by exact_mod_cast hpp.ne_zero),log_div
            (by exact_mod_cast hs.1.ne_zero) (by exact_mod_cast hpp.ne_zero)]
        have hln : 0 < log n := log_pos (by exact_mod_cast hs.2.1)
        apply unpaid_mass_five_sixths_le
        · apply (le_div_iff₀ hln).mpr
          rw [hlog]
          linarith
        · apply (div_le_one hln).mpr
          rw [hlog]
          linarith [log_natCast_nonneg p]
      · rw [if_neg hel]
        exact (exp_pos _).le
    · intro q _ hqp
      simp [Finset.mem_inter,Finset.mem_singleton,hqp]
    · intro hnot
      exact (hnot hp).elim
  · rw [boundedShare,if_neg hs]
    exact (exp_pos _).le

/-- The exact allocation correction of an arbitrary original incidence
selection has the balanced exponential saving. The unallocated SIGNED sum
is not norm-paid, and the majorant is on the original product p*a. -/
theorem partial_owner_difference_bound (A : Finset ℕ) (N : ℕ) {p a : ℕ}
    (hp : p ∈ (p*a).primeFactors) (ha : 0 < a)
    (hbal : log p ≤ log (p*a : ℕ)/6)
    (D : Finset (ℕ×ℕ)) (hD : D ⊆ a.divisorsAntidiagonal)
    {L : ℝ} (hL : 0 < L) (hT : log (p*a : ℕ) ≤ 2*L) :
    ‖partialCoefficient (A ∩ {p}) L N p a D-partialCoefficient ∅ L N p a D‖ ≤
      2*exp (-(N : ℝ)/8)*zetaMoebiusLogMajorant (p*a) := by
  have htheta := owner_share_le A N hp hbal
  have ht0 := (boundedShare_bounds (A ∩ {p}) N (p*a)).1
  have hscale0 : 0 ≤ log (p*a : ℕ)/L := div_nonneg (log_natCast_nonneg _) hL.le
  have hscale2 : log (p*a : ℕ)/L ≤ 2 := (div_le_iff₀ hL).mpr hT
  have heq : partialCoefficient (A ∩ {p}) L N p a D-partialCoefficient ∅ L N p a D=
      -((boundedShare (A ∩ {p}) N (p*a) : ℝ) : ℂ)*
        (((log (p*a : ℕ)/L)*∑ db ∈ D, (μ db.2 : ℝ)*pairHinge L p db.2 : ℝ) : ℂ) := by
    simp only [partialCoefficient,boundedShare_empty]
    push_cast
    ring
  rw [heq,norm_mul,norm_neg,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ht0,
    Complex.norm_real,Real.norm_eq_abs,abs_mul,abs_of_nonneg hscale0]
  have hb := partial_hinge_majorant (Nat.prime_of_mem_primeFactors hp).pos ha D hD L
  calc
    _ ≤ exp (-(N : ℝ)/8)*(2*zetaMoebiusLogMajorant (p*a)) :=
      mul_le_mul htheta (mul_le_mul hscale2 hb (abs_nonneg _) (by norm_num))
        (mul_nonneg hscale0 (abs_nonneg _)) (exp_pos _).le
    _ = _ := by ring

/-- The stronger hinge allocation rate still includes the WHOLE summable
arithmetic moment. It does not hide a bound on the unpaid signed main. -/
def hingeAllocationRate : ℝ := (503/1000 : ℝ)*(2048/1023 : ℝ)*exp (-(1/8 : ℝ))

theorem hingeAllocationRate_bounds : 0 ≤ hingeAllocationRate ∧ hingeAllocationRate < 9/10 := by
  constructor
  · unfold hingeAllocationRate; positivity
  · rw [hingeAllocationRate,exp_neg,mul_inv_lt_iff₀ (exp_pos _)]
    have h := add_one_le_exp (1/8 : ℝ)
    linarith

/-- One source-scale payment for arbitrary original incidence selections,
moving prime masks, and bounded complex masks. There is NO count factor or
sum of separate radial-period allowances. -/
theorem partial_owner_sum_bound (S : Finset ℕ) (A : ℕ → Finset ℕ)
    (p a : ℕ → ℕ) (D : ℕ → Finset (ℕ×ℕ)) (w : ℕ → ℂ)
    (N : ℕ) {L : ℝ} (hL : 0 < L)
    (hp : ∀ n ∈ S, p n ∈ n.primeFactors) (ha : ∀ n ∈ S, 0 < a n)
    (he : ∀ n ∈ S, p n*a n=n)
    (hbal : ∀ n ∈ S, log (p n) ≤ log n/6)
    (hD : ∀ n ∈ S, D n ⊆ (a n).divisorsAntidiagonal)
    (hT : ∀ n ∈ S, log n ≤ 2*L) (hw : ∀ n ∈ S, ‖w n‖ ≤ 1)
    (y : ℝ) {u : ℝ} (hu : 0 ≤ u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) :
    ‖(u : ℂ)^(N+1)*∑ n ∈ S, w n*
      (partialCoefficient (A n ∩ {p n}) L N (p n) (a n) (D n)-
        partialCoefficient ∅ L N (p n) (a n) (D n))*
          zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ ≤
      (503/500 : ℝ)*zetaMoebiusLogMajorantMass (2049/2048)*hingeAllocationRate^N := by
  let C : ℝ := 2*exp (-(N : ℝ)/8)
  have hC : 0 < C := by dsimp [C]; positivity
  let c : ℕ → ℂ := fun n => w n*
    (partialCoefficient (A n ∩ {p n}) L N (p n) (a n) (D n)-
      partialCoefficient ∅ L N (p n) (a n) (D n))/(C : ℂ)
  have hc : ∀ n ∈ S, ‖c n‖ ≤ zetaMoebiusLogMajorant n := by
    intro n hn
    have hb := partial_owner_difference_bound (p := p n) (a := a n) (A n) N
      (by simpa only [he n hn] using hp n hn) (ha n hn)
      (by simpa only [he n hn] using hbal n hn) (D n) (hD n hn) hL
      (by simpa only [he n hn] using hT n hn)
    rw [he n hn] at hb
    have hwc : ‖w n*(partialCoefficient (A n ∩ {p n}) L N (p n) (a n) (D n)-
        partialCoefficient ∅ L N (p n) (a n) (D n))‖ ≤
        ‖partialCoefficient (A n ∩ {p n}) L N (p n) (a n) (D n)-
          partialCoefficient ∅ L N (p n) (a n) (D n)‖ := by
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (hw n hn)
    dsimp only [c]
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hC]
    apply (div_le_iff₀ hC).mpr
    exact (hwc.trans hb).trans_eq (by dsimp [C]; ring)
  have hb := ZetaArithmeticLogWindow.norm_sum_moment_of_log_bound S c hc N 0 y
    (2049/2048) (1023/2048) 0 (by norm_num) (by norm_num) (fun n _ => by norm_num)
  norm_num only [Nat.add_zero,exp_zero,mul_one,pow_zero,inv_div] at hb
  have hu503 : u ≤ (503/1000 : ℝ) := hU.trans (by norm_num [ZetaRieszWideOwnerAudit.radiusCeiling])
  have hbu : ‖(u : ℂ)^(N+1)*∑ n ∈ S, c n*zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ ≤
      (503/1000 : ℝ)^(N+1)*(2048/1023 : ℝ)^N*zetaMoebiusLogMajorantMass (2049/2048) := by
    rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hu]
    exact (mul_le_mul (pow_le_pow_left₀ hu hu503 _) hb (norm_nonneg _)
      (by positivity)).trans_eq (by ring)
  have hsum : (u : ℂ)^(N+1)*(∑ n ∈ S, w n*
      (partialCoefficient (A n ∩ {p n}) L N (p n) (a n) (D n)-
        partialCoefficient ∅ L N (p n) (a n) (D n))*zetaPrimeLogKernel N (3/2+Complex.I*y) n)=
      (C : ℂ)*((u : ℂ)^(N+1)*∑ n ∈ S, c n*zetaPrimeLogKernel N (3/2+Complex.I*y) n) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    dsimp only [c]
    have hCc : (C : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hC.ne'
    field_simp
  rw [hsum,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hC]
  apply (mul_le_mul_of_nonneg_left hbu hC.le).trans_eq
  have hexp : exp (-(N : ℝ)/8)=exp (-(1/8 : ℝ))^N := by
    rw [← exp_nat_mul]
    congr 1
    ring
  dsimp only [C,hingeAllocationRate]
  rw [hexp,mul_pow,mul_pow,pow_succ]
  ring

/-- This independent geometric error tends to zero; no effective starting
order or numerical value of the fixed full majorant mass is asserted. -/
theorem tendsto_hingeAllocationBudget :
    Tendsto (fun N : ℕ => (503/500 : ℝ)*zetaMoebiusLogMajorantMass (2049/2048)*
      hingeAllocationRate^N) atTop (𝓝 0) := by
  have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one hingeAllocationRate_bounds.1
    (hingeAllocationRate_bounds.2.trans (by norm_num))).const_mul
      ((503/500 : ℝ)*zetaMoebiusLogMajorantMass (2049/2048))
  simpa only [mul_zero] using ht

/-- A literal subset of the already retained central physical labels.
The witness is an ORIGINAL based cofactor, not a completed cofactor label. -/
def hingeLabels (u : ℝ) (N K : ℕ) : Finset ℕ :=
  ((coreBand u N K).filter (fun n : ℕ => (197/100 : ℝ)*N < log n)).filter
    (fun n => Squarefree n ∧ ∃ e : ℕ, e ∣ n/largestPrime n ∧
      SquarefreeVaughanLogSource.length u N ≤ log ((n/largestPrime n)/e : ℕ) ∧
      log n-log e+log (largestPrime n) ≤ (203/100 : ℝ)*N)

/-- Every selected literal hinge label supplies the small-owner geometry
and the original product identity used in the independent payment. -/
theorem hingeLabels_geometry {u : ℝ} {N K n : ℕ} (hn : n ∈ hingeLabels u N K)
    (hL : (11/8 : ℝ)*N ≤ SquarefreeVaughanLogSource.length u N) :
    largestPrime n ∈ n.primeFactors ∧ 0 < n/largestPrime n ∧
      largestPrime n*(n/largestPrime n)=n ∧ log (largestPrime n) ≤ log n/6 ∧
      log n ≤ 2*SquarefreeVaughanLogSource.length u N ∧ 7 ≤ n.primeFactors.card := by
  obtain ⟨hcentral,hs,e,he,hhinge,hgap⟩ := Finset.mem_filter.mp hn
  have hcore := (Finset.mem_filter.mp hcentral).1
  have hd := core_data hcore hs
  have hp := ZetaRieszOwnedCells.largestPrime_mem_of_two
    (by have := ZetaRieszJointPrimeEnergy.core_count hcore; omega : 2 ≤ n.primeFactors.card)
  refine ⟨hp,Nat.pos_of_ne_zero hd.2.1.ne_zero,Nat.mul_div_cancel'
    (Nat.dvd_of_mem_primeFactors hp),hinge_all_primes_log_le_sixth hcentral hs he hhinge hgap hL hp,?_,
    hinge_count_ge_seven hcentral hs he hhinge hgap hL⟩
  have hT := (ZetaRieszLowerRadialPayment.central_log_bounds hcentral).2
  nlinarith [Nat.cast_nonneg (α := ℝ) N]

/-- The whole selected hinge population has one global allocation payment.
Every original divisor mask can vary with its label, and the actual phase
height is retained. Only the owner allocation is removed from the signed main. -/
theorem literal_hinge_owner_sum_bound (S : Finset ℕ) (A : ℕ → Finset ℕ)
    (D : ℕ → Finset (ℕ×ℕ)) (w : ℕ → ℂ) (N K : ℕ) {u : ℝ}
    (hu : 0 ≤ u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hS : S ⊆ hingeLabels u N K)
    (hL : (11/8 : ℝ)*N ≤ SquarefreeVaughanLogSource.length u N)
    (hD : ∀ n ∈ S, D n ⊆ (n/largestPrime n).divisorsAntidiagonal)
    (hw : ∀ n ∈ S, ‖w n‖ ≤ 1) (y : ℝ) :
    ‖(u : ℂ)^(N+1)*∑ n ∈ S, w n*
      (partialCoefficient (A n ∩ {largestPrime n}) (SquarefreeVaughanLogSource.length u N)
        N (largestPrime n) (n/largestPrime n) (D n)-
      partialCoefficient ∅ (SquarefreeVaughanLogSource.length u N)
        N (largestPrime n) (n/largestPrime n) (D n))*
          zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ ≤
      (503/500 : ℝ)*zetaMoebiusLogMajorantMass (2049/2048)*hingeAllocationRate^N := by
  apply partial_owner_sum_bound S A largestPrime (fun n => n/largestPrime n) D w N
    (SquarefreeVaughanLogSource.length_pos u N)
    (fun n hn => (hingeLabels_geometry (hS hn) hL).1)
    (fun n hn => (hingeLabels_geometry (hS hn) hL).2.1)
    (fun n hn => (hingeLabels_geometry (hS hn) hL).2.2.1)
    (fun n hn => (hingeLabels_geometry (hS hn) hL).2.2.2.1) hD
    (fun n hn => (hingeLabels_geometry (hS hn) hL).2.2.2.2.1) hw y hu hU

/-- BOTH signed sides transfer to the unallocated original hinge sum with
the one independently paid geometric error. No floor for that sum is assumed
or concluded here. -/
theorem literal_hinge_signed_bounds (S : Finset ℕ) (A : ℕ → Finset ℕ)
    (D : ℕ → Finset (ℕ×ℕ)) (w : ℕ → ℂ) (N K : ℕ) {u : ℝ}
    (hu : 0 ≤ u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hS : S ⊆ hingeLabels u N K)
    (hL : (11/8 : ℝ)*N ≤ SquarefreeVaughanLogSource.length u N)
    (hD : ∀ n ∈ S, D n ⊆ (n/largestPrime n).divisorsAntidiagonal)
    (hw : ∀ n ∈ S, ‖w n‖ ≤ 1) (y : ℝ) :
    let O := (u : ℂ)^(N+1)*∑ n ∈ S, w n*
      partialCoefficient (A n ∩ {largestPrime n}) (SquarefreeVaughanLogSource.length u N)
        N (largestPrime n) (n/largestPrime n) (D n)*zetaPrimeLogKernel N (3/2+Complex.I*y) n
    let U := (u : ℂ)^(N+1)*∑ n ∈ S, w n*
      partialCoefficient ∅ (SquarefreeVaughanLogSource.length u N)
        N (largestPrime n) (n/largestPrime n) (D n)*zetaPrimeLogKernel N (3/2+Complex.I*y) n
    let E := (503/500 : ℝ)*zetaMoebiusLogMajorantMass (2049/2048)*hingeAllocationRate^N;
    U.re-E ≤ O.re ∧ O.re ≤ U.re+E := by
  dsimp only
  have hb := literal_hinge_owner_sum_bound S A D w N K hu hU hS hL hD hw y
  simp only [mul_sub,sub_mul,Finset.sum_sub_distrib] at hb
  have hr := abs_le.mp ((Complex.abs_re_le_norm _).trans hb)
  simp only [Complex.sub_re] at hr
  constructor <;> linarith

/-- Arbitrarily moving literal incidence masks, counts and heights preserve
decay of this allocation difference on the ENTIRE selected hinge population.
The actual moving Riesz length supplies the needed lower bound eventually. -/
theorem tendsto_literal_hinge_owner_difference (K : ℕ → ℕ) (S : ℕ → Finset ℕ)
    (A : ℕ → ℕ → Finset ℕ) (D : ℕ → ℕ → Finset (ℕ×ℕ))
    (w : ℕ → ℕ → ℂ) (y : ℕ → ℝ) {u : ℝ} (hu : 0 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hS : ∀ N, S N ⊆ hingeLabels u N (K N))
    (hD : ∀ N n, n ∈ S N → D N n ⊆ (n/largestPrime n).divisorsAntidiagonal)
    (hw : ∀ N n, n ∈ S N → ‖w N n‖ ≤ 1) :
    Tendsto (fun N => (u : ℂ)^(N+1)*∑ n ∈ S N, w N n*
      (partialCoefficient (A N n ∩ {largestPrime n}) (SquarefreeVaughanLogSource.length u N)
        N (largestPrime n) (n/largestPrime n) (D N n)-
      partialCoefficient ∅ (SquarefreeVaughanLogSource.length u N)
        N (largestPrime n) (n/largestPrime n) (D N n))*
          zetaPrimeLogKernel N (3/2+Complex.I*y N) n) atTop (𝓝 0) := by
  apply squeeze_zero_norm' (a := fun N : ℕ =>
    (503/500 : ℝ)*zetaMoebiusLogMajorantMass (2049/2048)*hingeAllocationRate^N) ?_
    tendsto_hingeAllocationBudget
  filter_upwards [ZetaRieszLowerDegreeBounds.eventually_length_ge_exponent
    hu (by norm_num : (0 : ℝ) ≤ 11/16)
    (hU.trans_lt ZetaRieszWideOwnerAudit.radius_lt_source)] with N hLN
  have hL : (11/8 : ℝ)*N ≤ SquarefreeVaughanLogSource.length u N := by nlinarith only [hLN]
  exact literal_hinge_owner_sum_bound (S N) (A N) (D N) (w N) N (K N) hu.le hU
    (hS N) hL (hD N) (hw N) (y N)

/-- The partial-coefficient API is EXACTLY the previously retained original
incidence sum. No completed label or altered Fourier observation is used. -/
theorem partial_atom_eq_original_incidences (A : Finset ℕ) (L : ℝ) (N : ℕ)
    (p a : ℕ) (D : Finset (ℕ×ℕ)) (y : ℝ) :
    partialCoefficient A L N p a D*zetaPrimeLogKernel N (3/2+Complex.I*y) (p*a)=
      ∑ db ∈ D, phaseWeight A L N y a p*(μ db.2 : ℂ)*(pairHinge L p db.2 : ℂ) := by
  simp only [partialCoefficient,phaseWeight]
  push_cast
  simp only [Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro db _
  ring

/-- The paid allocation leaves the SAME full factorial kernel with a
smooth total-log prefactor and the original complex prime phase. -/
theorem unallocated_phaseWeight_eq (L : ℝ) (N : ℕ) (y : ℝ) (a p : ℕ) :
    phaseWeight ∅ L N y a p=
      (((log (p*a : ℕ)/L : ℝ) : ℂ))*zetaPrimeLogKernel N (3/2+Complex.I*y) (p*a) := by
  simp only [phaseWeight,boundedShare_empty,sub_zero,one_mul]

/-- Direct geometric payment on the CURRENT retained original incidences,
after the previously proved zero-cost affine deletions. Their unallocated
signed prime sum, all counts, radial periods and physical holes remain. -/
theorem retained_hinge_allocation_bound (N K : ℕ) (y : ℝ) {u : ℝ}
    (hu : 0 ≤ u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hL : (11/8 : ℝ)*N ≤ SquarefreeVaughanLogSource.length u N) :
    let D := fun n => (n/largestPrime n).divisorsAntidiagonal \
      (cancelledOrbitDivisors u N n ∪ ZetaRieszCrossingOrbitCancellation.affineDivisors u N n)
    ‖(u : ℂ)^(N+1)*∑ n ∈ hingeLabels u N K, ∑ db ∈ D n,
      (phaseWeight (ZetaRieszAnnulusJoint.intermediatePrimes u N ∩ {largestPrime n})
        (SquarefreeVaughanLogSource.length u N) N y (n/largestPrime n) (largestPrime n)-
       phaseWeight ∅ (SquarefreeVaughanLogSource.length u N) N y (n/largestPrime n) (largestPrime n))*
          (μ db.2 : ℂ)*(pairHinge (SquarefreeVaughanLogSource.length u N) (largestPrime n) db.2 : ℂ)‖ ≤
      (503/500 : ℝ)*zetaMoebiusLogMajorantMass (2049/2048)*hingeAllocationRate^N := by
  dsimp only
  have hb := literal_hinge_owner_sum_bound (hingeLabels u N K)
    (fun _ => ZetaRieszAnnulusJoint.intermediatePrimes u N)
    (fun n => (n/largestPrime n).divisorsAntidiagonal \
      (cancelledOrbitDivisors u N n ∪ ZetaRieszCrossingOrbitCancellation.affineDivisors u N n))
    (fun _ => 1) N K hu hU (Finset.Subset.refl _) hL
    (by intro n _; exact Finset.sdiff_subset) (by intros; simp) y
  simp only [one_mul,sub_mul] at hb
  have hp n (hn : n ∈ hingeLabels u N K) : largestPrime n*(n/largestPrime n)=n :=
    (hingeLabels_geometry hn hL).2.2.1
  convert hb using 1
  congr 2
  apply Finset.sum_congr rfl
  intro n hn
  have hO := partial_atom_eq_original_incidences
    (ZetaRieszAnnulusJoint.intermediatePrimes u N ∩ {largestPrime n})
    (SquarefreeVaughanLogSource.length u N) N (largestPrime n) (n/largestPrime n)
    ((n/largestPrime n).divisorsAntidiagonal \
      (cancelledOrbitDivisors u N n ∪ ZetaRieszCrossingOrbitCancellation.affineDivisors u N n)) y
  have hE := partial_atom_eq_original_incidences ∅ (SquarefreeVaughanLogSource.length u N)
    N (largestPrime n) (n/largestPrime n)
    ((n/largestPrime n).divisorsAntidiagonal \
      (cancelledOrbitDivisors u N n ∪ ZetaRieszCrossingOrbitCancellation.affineDivisors u N n)) y
  rw [hp n hn] at hO hE
  rw [hO,hE,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro db _
  ring

/-- Apply the new payment INSIDE the whole current central main. Outside
the selected genuine hinge population the original owner weight is unchanged.
Every original antidiagonal, phase and previous zero selector is retained. -/
theorem central_hinge_allocation_bound (N K : ℕ) (y : ℝ) {u : ℝ}
    (hu : 0 ≤ u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hL : (11/8 : ℝ)*N ≤ SquarefreeVaughanLogSource.length u N) :
    let C := ((coreBand u N K).filter (fun n : ℕ => (197/100 : ℝ)*N < log n)).filter Squarefree
    let D := fun n => (n/largestPrime n).divisorsAntidiagonal \
      (cancelledOrbitDivisors u N n ∪ ZetaRieszCrossingOrbitCancellation.affineDivisors u N n)
    ‖(u : ℂ)^(N+1)*∑ n ∈ C, ∑ db ∈ D n,
      (phaseWeight (ZetaRieszAnnulusJoint.intermediatePrimes u N ∩ {largestPrime n})
        (SquarefreeVaughanLogSource.length u N) N y (n/largestPrime n) (largestPrime n)-
       phaseWeight (if n ∈ hingeLabels u N K then ∅ else
          ZetaRieszAnnulusJoint.intermediatePrimes u N ∩ {largestPrime n})
        (SquarefreeVaughanLogSource.length u N) N y (n/largestPrime n) (largestPrime n))*
          (μ db.2 : ℂ)*(pairHinge (SquarefreeVaughanLogSource.length u N) (largestPrime n) db.2 : ℂ)‖ ≤
      (503/500 : ℝ)*zetaMoebiusLogMajorantMass (2049/2048)*hingeAllocationRate^N := by
  dsimp only
  have hsub : hingeLabels u N K ⊆
      ((coreBand u N K).filter (fun n : ℕ => (197/100 : ℝ)*N < log n)).filter Squarefree := by
    intro n hn
    obtain ⟨hcentral,hs,_⟩ := Finset.mem_filter.mp hn
    exact Finset.mem_filter.mpr ⟨hcentral,hs⟩
  have heq := Finset.sum_subset hsub (f := fun n =>
    ∑ db ∈ (n/largestPrime n).divisorsAntidiagonal \
        (cancelledOrbitDivisors u N n ∪ ZetaRieszCrossingOrbitCancellation.affineDivisors u N n),
      (phaseWeight (ZetaRieszAnnulusJoint.intermediatePrimes u N ∩ {largestPrime n})
        (SquarefreeVaughanLogSource.length u N) N y (n/largestPrime n) (largestPrime n)-
       phaseWeight (if n ∈ hingeLabels u N K then ∅ else
          ZetaRieszAnnulusJoint.intermediatePrimes u N ∩ {largestPrime n})
        (SquarefreeVaughanLogSource.length u N) N y (n/largestPrime n) (largestPrime n))*
          (μ db.2 : ℂ)*(pairHinge (SquarefreeVaughanLogSource.length u N) (largestPrime n) db.2 : ℂ))
    (by intro n _ hnot; simp only [if_neg hnot,sub_self,zero_mul,Finset.sum_const_zero])
  rw [← heq]
  calc
    _ = ‖(u : ℂ)^(N+1)*∑ n ∈ hingeLabels u N K,
        ∑ db ∈ (n/largestPrime n).divisorsAntidiagonal \
          (cancelledOrbitDivisors u N n ∪ ZetaRieszCrossingOrbitCancellation.affineDivisors u N n),
          (phaseWeight (ZetaRieszAnnulusJoint.intermediatePrimes u N ∩ {largestPrime n})
            (SquarefreeVaughanLogSource.length u N) N y (n/largestPrime n) (largestPrime n)-
           phaseWeight ∅ (SquarefreeVaughanLogSource.length u N) N y (n/largestPrime n) (largestPrime n))*
            (μ db.2 : ℂ)*(pairHinge (SquarefreeVaughanLogSource.length u N) (largestPrime n) db.2 : ℂ)‖ := by
      apply congrArg (fun z : ℂ => ‖(u : ℂ)^(N+1)*z‖)
      apply Finset.sum_congr rfl
      intro n hn
      rw [if_pos hn]
    _ ≤ _ := retained_hinge_allocation_bound N K y hu hU hL

/-- A DIRECT two-sided inequality for the authoritative remaining floor
ledger. The selected hinge allocation is paid once; all earlier large-owner,
owner-gap and polynomial-row credits are subtracted exactly as before.
The displayed unallocated signed central main is still unbounded. -/
theorem polynomial_remaining_hinge_allocation_bounds (j : ℕ) (y : ℝ) {u : ℝ}
    (hu : 0 ≤ u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hL : (11/8 : ℝ)*ZetaRieszPrimeCountFrequency.dyadicMomentOrder j ≤
      SquarefreeVaughanLogSource.length u (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)) :
    let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
    let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
    let C := ((coreBand u N K).filter (fun n : ℕ => (197/100 : ℝ)*N < log n)).filter Squarefree
    let D := fun n => (n/largestPrime n).divisorsAntidiagonal \
      (cancelledOrbitDivisors u N n ∪ ZetaRieszCrossingOrbitCancellation.affineDivisors u N n)
    let U := (∑ n ∈ C, ∑ db ∈ D n,
      phaseWeight (if n ∈ hingeLabels u N K then ∅ else
        ZetaRieszAnnulusJoint.intermediatePrimes u N ∩ {largestPrime n})
        (SquarefreeVaughanLogSource.length u N) N y (n/largestPrime n) (largestPrime n)*
          (μ db.2 : ℂ)*(pairHinge (SquarefreeVaughanLogSource.length u N) (largestPrime n) db.2 : ℂ)).re-
      (ZetaRieszUnifiedSignedRows.largeOwnerIncidences u y N K).re-
      (ZetaRieszOwnerGapRows.ownerGapLiteralRows u y j+ZetaRieszOwnerGapRows.ownerGapEndpointRows u y j)-
      ZetaRieszPolynomialCutoffRows.literalCutoffPacket u y j
    let E := (503/500 : ℝ)*zetaMoebiusLogMajorantMass (2049/2048)*hingeAllocationRate^N;
    u^(N+1)*U-E ≤ u^(N+1)*ZetaRieszPolynomialCutoffRows.polynomialCentralRemaining u y j ∧
      u^(N+1)*ZetaRieszPolynomialCutoffRows.polynomialCentralRemaining u y j ≤ u^(N+1)*U+E := by
  dsimp only
  have hb := central_hinge_allocation_bound
    (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)
    (ZetaRieszPrimeCountFrequency.dyadicPrimeCount j) y hu hU hL
  dsimp only at hb
  simp only [sub_mul,Finset.sum_sub_distrib] at hb
  have hr := abs_le.mp ((Complex.abs_re_le_norm _).trans hb)
  rw [← Complex.ofReal_pow] at hr
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,Complex.sub_re] at hr
  have hpoly := ZetaRieszCrossingOrbitCancellation.polynomialCentralRemaining_eq_affine_sdiff u y j
  dsimp only at hpoly
  rw [hpoly]
  constructor <;> nlinarith only [hr.1,hr.2]

end RiemannGaussian.ZetaRieszHingeAllocationPayment
