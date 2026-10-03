/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszBalancedRadialPayment
import RiemannGaussian.ZetaRieszPostHingeEnergy

/-!
# A common signed prime-critical response at every cofactor count

Pair the two least primes before measuring the divisor response. On a
least-prime gap, only one critical divisor shell remains. The literal core
budget excludes two disjoint critical divisors. In particular, one prime
in that shell excludes EVERY other critical divisor, not only other primes.
The exact Riesz response is then minus the least-prime logarithm at any
total prime count. The actual phase stays in the downstream inequality.
Neither a count-parity rule nor a cofinal floor is assumed.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open Real Filter Topology
open scoped BigOperators Classical ArithmeticFunction.Moebius
namespace RiemannGaussian.ZetaRieszCriticalPrimeFloor
open ZetaSquarefreeRieszWindows ZetaRieszPrimeCountFrequency
open ZetaRieszBalancedOwnerFloor LogarithmicDeviation
open ZetaRieszPrimeEndpoint

/-- The full cofactor spectrum misses the least-prime translation strip.
The empty divisor and both exact endpoints are retained. -/
def Gap (L : ℝ) (r a : ℕ) : Prop :=
  ∀ d∈a.divisors, L≤log d ∨ log d+log r≤L

/-- The remaining integer Mobius prefix after BOTH least-prime pairings.
The lower endpoint is strict; the upper endpoint is closed. -/
def criticalDivisors (L : ℝ) (r q b : ℕ) : Finset ℕ :=
  b.divisors.filter (fun d => L-log r-log q<log d ∧ log d+log r≤L)

private theorem log_mul_nat {a b : ℕ} (ha : a≠0) (hb : b≠0) :
    log (a*b : ℕ)=log a+log b := by
  rw [Nat.cast_mul,log_mul (by exact_mod_cast ha) (by exact_mod_cast hb)]

private theorem log_divisor_le {a b : ℕ} (ha : 0<a) (hb : b≠0) (hd : a∣b) :
    log a≤log b := by
  exact log_le_log (by exact_mod_cast ha)
    (by exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hb) hd)

private theorem divisor_ge_minimum {q b d : ℕ} (hb : b≠0)
    (hmin : ∀ p∈b.primeFactors,q≤p) (hd : d∣b) (hd1 : d≠1) : q≤d := by
  have hd0 : d≠0 := (Nat.pos_of_dvd_of_pos hd (Nat.pos_of_ne_zero hb)).ne'
  have hprime := Nat.minFac_prime hd1
  have hmem : d.minFac∈b.primeFactors :=
    Nat.primeFactors_mono hd hb
      (hprime.mem_primeFactors (Nat.minFac_dvd d) hd0)
  exact (hmin _ hmem).trans
    (Nat.minFac_le_of_dvd (by omega : 2≤d) (dvd_refl d))

private theorem tent_eq_plateau_of_gap {a b D L : ℝ}
    (ha : 0≤a) (hab : a≤b)
    (hg : L≤D ∨ D+a≤L) (hgb : L≤D+b ∨ D+b+a≤L) :
    primePairTent a b (L-D)=if L-a-b<D ∧ D+a≤L then a else 0 := by
  by_cases h : L-a-b<D ∧ D+a≤L
  · rw [if_pos h]
    have hx : a≤L-D := by linarith only [h.2]
    have hxb : L-D≤b := by
      rcases hgb with hgb | hgb
      · linarith only [hgb]
      · linarith only [h.1,hgb]
    unfold primePairTent
    rw [max_eq_right (by linarith : 0≤L-D),
      max_eq_right (by linarith : 0≤L-D-a),
      max_eq_left (by linarith : L-D-b≤0),
      max_eq_left (by linarith : L-D-a-b≤0)]
    ring
  · rw [if_neg h]
    apply primePairTent_eq_zero_of_outside ha (ha.trans hab)
    rcases hg with hg | hg
    · exact Or.inl (by linarith)
    · right
      have hd : D≤L-a-b := by
        by_contra hd
        exact h ⟨lt_of_not_ge hd,hg⟩
      linarith only [hd]

/-- This joins ALL subset ranks before evaluating the response. There is
no density, prime completion, phase or fixed-count hypothesis. -/
theorem riesz_eq_signed_critical_shell {r q b : ℕ} (hr : r.Prime)
    (hq : q.Prime) (hrq : r<q) (hs : Squarefree (r*(q*b)))
    {L : ℝ} (hg : Gap L r (q*b)) :
    VaughanLogAverage.riesz L (r*(q*b))=
      log r*∑ d∈criticalDivisors L r q b,(μ d : ℝ) := by
  have hb0 := hs.of_mul_right.of_mul_right.ne_zero
  have hqb0 := hs.of_mul_right.ne_zero
  have hrb : ¬r∣b := hr.coprime_iff_not_dvd.mp
    ((Nat.coprime_of_squarefree_mul hs).of_dvd_right (dvd_mul_left b q))
  have hqbd : ¬q∣b := hq.coprime_iff_not_dvd.mp
    (Nat.coprime_of_squarefree_mul hs.of_mul_right)
  rw [riesz_two_primes_eq_tent L hr hq hrq.ne hrb hqbd]
  have hlogrq : log r≤log q := log_le_log
    (by exact_mod_cast hr.pos) (by exact_mod_cast hrq.le)
  have he d (hd : d∈b.divisors) :
      primePairTent (log r) (log q) (L-log d)=
        if L-log r-log q<log d ∧ log d+log r≤L then log r else 0 := by
    have hdB := Nat.dvd_of_mem_divisors hd
    have hda : d∈(q*b).divisors := Nat.mem_divisors.mpr
      ⟨hdB.trans (dvd_mul_left b q),hqb0⟩
    have hqda : q*d∈(q*b).divisors := Nat.mem_divisors.mpr
      ⟨Nat.mul_dvd_mul_left q hdB,hqb0⟩
    have hqd := hg (q*d) hqda
    rw [log_mul_nat hq.ne_zero (Nat.pos_of_mem_divisors hd).ne'] at hqd
    exact tent_eq_plateau_of_gap (log_natCast_nonneg r) hlogrq (hg d hda)
      (by rcases hqd with h | h <;> [left; right] <;> linarith only [h])
  simp_rw [Finset.mul_sum]
  rw [criticalDivisors,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d hd
  rw [he d hd]
  split_ifs <;> ring

/-- The common core budget allows at most ONE prime-critical divisor.
It also rules out every composite divisor in the same shell. The proof
uses disjoint divisor geometry, not an assumed homology cancellation. -/
theorem criticalDivisors_eq_singleton {r q b p : ℕ} (hr : r.Prime)
    (hq : q.Prime) (hrq : r<q) (hs : Squarefree (r*(q*b)))
    (hmin : ∀ t∈b.primeFactors,q≤t) (hp : p∈b.primeFactors)
    {L : ℝ} (hg : Gap L r (q*b))
    (hbudget : 2*log (r*(q*b) : ℕ)<3*L)
    (hpc : p∈criticalDivisors L r q b) :
    criticalDivisors L r q b={p} := by
  have hb0 := hs.of_mul_right.of_mul_right.ne_zero
  have hqb0 := hs.of_mul_right.ne_zero
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hpB := Nat.dvd_of_mem_primeFactors hp
  have hpr : 0<log r := log_pos (by exact_mod_cast hr.one_lt)
  have hqr : log r≤log q := log_le_log
    (by exact_mod_cast hr.pos) (by exact_mod_cast hrq.le)
  have hpq : log q≤log p := log_le_log
    (by exact_mod_cast hq.pos) (by exact_mod_cast hmin p hp)
  have hpb := log_divisor_le hpp.pos hb0 hpB
  have hnlog : log (r*(q*b) : ℕ)=log r+log q+log b := by
    rw [log_mul_nat hr.ne_zero hqb0,log_mul_nat hq.ne_zero hb0]
    ring
  have hlo : log r+log q<L := by nlinarith only [hbudget,hnlog,hqr,hpq,hpb]
  have hc := (Finset.mem_filter.mp hpc).2
  have hqp : L≤log q+log p := by
    have h := hg (q*p) (Nat.mem_divisors.mpr ⟨Nat.mul_dvd_mul_left q hpB,hqb0⟩)
    rw [log_mul_nat hq.ne_zero hpp.ne_zero] at h
    rcases h with h | h
    · exact h
    · linarith only [hc.1,h]
  have unique d (hd : d∈criticalDivisors L r q b) : d=p := by
    obtain ⟨hdB,hdc⟩ := Finset.mem_filter.mp hd
    have hd0 := (Nat.pos_of_mem_divisors hdB).ne'
    have hdBd := Nat.dvd_of_mem_divisors hdB
    have hd1 : d≠1 := by
      intro he
      rw [he,Nat.cast_one,log_one] at hdc
      linarith only [hlo,hdc.1]
    have hqd : log q≤log d := log_le_log
      (by exact_mod_cast hq.pos)
      (by exact_mod_cast divisor_ge_minimum hb0 hmin hdBd hd1)
    by_contra hdp
    have hnotpd : ¬p∣d := by
      intro hpd
      have he : p*(d/p)=d := Nat.mul_div_cancel' hpd
      have heB : d/p∣b := (Nat.div_dvd_of_dvd hpd).trans hdBd
      have he1 : d/p≠1 := by
        intro he1
        rw [he1,mul_one] at he
        exact hdp he.symm
      have he0 : d/p≠0 := by
        intro he0
        rw [he0,mul_zero] at he
        exact hd0 he.symm
      have hqe : log q≤log (d/p : ℕ) := log_le_log
        (by exact_mod_cast hq.pos)
        (by exact_mod_cast divisor_ge_minimum hb0 hmin heB he1)
      have hde : log d=log p+log (d/p : ℕ) := by
        calc
          _ = log (p*(d/p) : ℕ) := congrArg (fun n : ℕ => log n) he.symm
          _ = _ := log_mul_nat hpp.ne_zero he0
      linarith only [hde,hqe,hqp,hdc.2,hpr]
    have hpdB : p*d∣b := (hpp.coprime_iff_not_dvd.mpr hnotpd).mul_dvd_of_dvd_of_dvd hpB hdBd
    have hpd : log p+log d≤log b := by
      have h := log_divisor_le (Nat.mul_pos hpp.pos (Nat.pos_of_mem_divisors hdB)) hb0 hpdB
      rwa [log_mul_nat hpp.ne_zero hd0] at h
    have hqdc : L≤log q+log d := by
      have h := hg (q*d) (Nat.mem_divisors.mpr ⟨Nat.mul_dvd_mul_left q hdBd,hqb0⟩)
      rw [log_mul_nat hq.ne_zero hd0] at h
      rcases h with h | h
      · exact h
      · linarith only [hdc.1,h]
    by_cases hhalf : 2*log q≤L
    · nlinarith only [hbudget,hnlog,hpd,hqp,hqdc,hhalf,hpr]
    · nlinarith only [hbudget,hnlog,hpd,hpq,hqd,hhalf,hpr]
  ext d
  simp only [Finset.mem_singleton]
  exact ⟨unique d,fun he => he ▸ hpc⟩

/-- Exact arithmetic sign across EVERY total prime count. Adding an
inactive cofactor prime need not reverse this sign. -/
theorem riesz_eq_neg_least_log {r q b p : ℕ} (hr : r.Prime)
    (hq : q.Prime) (hrq : r<q) (hs : Squarefree (r*(q*b)))
    (hmin : ∀ t∈b.primeFactors,q≤t) (hp : p∈b.primeFactors)
    {L : ℝ} (hg : Gap L r (q*b))
    (hbudget : 2*log (r*(q*b) : ℕ)<3*L)
    (hpc : p∈criticalDivisors L r q b) :
    VaughanLogAverage.riesz L (r*(q*b))= -log r := by
  rw [riesz_eq_signed_critical_shell hr hq hrq hs hg,
    criticalDivisors_eq_singleton hr hq hrq hs hmin hp hg hbudget hpc,
    Finset.sum_singleton,ArithmeticFunction.moebius_apply_prime
      (Nat.prime_of_mem_primeFactors hp)]
  norm_num

/-- A prime-critical shell has a positive ORIGINAL arithmetic coefficient.
This does not impose a sign on its complex phase. -/
theorem coefficient_eq_least_log {r q b p : ℕ} (hr : r.Prime)
    (hq : q.Prime) (hrq : r<q) (hs : Squarefree (r*(q*b)))
    (hmin : ∀ t∈b.primeFactors,q≤t) (hp : p∈b.primeFactors)
    {L : ℝ} (hg : Gap L r (q*b))
    (hbudget : 2*log (r*(q*b) : ℕ)<3*L)
    (hpc : p∈criticalDivisors L r q b) :
    SquarefreeVaughanLogSource.coefficient L (r*(q*b))=
      ((log (r*(q*b) : ℕ)*log r/L : ℝ) : ℂ) := by
  have hqb1 : q*b≠1 := fun he => hq.ne_one (mul_eq_one.mp he).1
  have hnp : ¬(r*(q*b)).Prime := Nat.not_prime_mul hr.ne_one hqb1
  rw [SquarefreeVaughanLogSource.coefficient,if_pos ⟨hs,hnp⟩,
    riesz_eq_neg_least_log hr hq hrq hs hmin hp hg hbudget hpc]
  congr 1
  ring

/-- A native label certificate, with the exact least-prime pair and the
full uncompleted cofactor. Its arithmetic test has no count cutoff. -/
def PrimeCritical (L : ℝ) (n : ℕ) : Prop :=
  ∃ r q b p : ℕ, n=r*(q*b) ∧ r.Prime ∧ q.Prime ∧ r<q ∧
    (∀ t∈b.primeFactors,q≤t) ∧ Gap L r (q*b) ∧
    p∈b.primeFactors ∧ p∈criticalDivisors L r q b

/-- The existing physical-length lower bound discharges the strict
three-halves budget on EVERY central native label, without a zero. -/
theorem native_budget {u : ℝ} (hu : 0<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {j n : ℕ}
    (hN : 65536≤dyadicMomentOrder j)
    (hn : n∈ZetaRieszBalancedRadialPayment.centralLabels u j) :
    2*log n<3*SquarefreeVaughanLogSource.length u (dyadicMomentOrder j) := by
  have hl := ZetaRieszPostHingeEnergy.length_ge_rational hN hu hU
  have ht := (ZetaRieszBalancedRadialPayment.mem_centralLabels.mp hn).2.2
  have hNp : (0 : ℝ)<dyadicMomentOrder j := by exact_mod_cast (by omega : 0<dyadicMomentOrder j)
  nlinarith only [hl,ht,hNp]

/-- The native owner and length budgets limit the prime-critical gap to
counts three and four. The generic signed-shell identity is not a payment
of the higher-count active or composite-critical populations. -/
theorem native_primeCritical_count_le_four {u : ℝ} (hu : 0<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {j n : ℕ}
    (hN : 65536≤dyadicMomentOrder j)
    (hn : n∈ZetaRieszBalancedRadialPayment.centralLabels u j)
    (hcrit : PrimeCritical
      (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) n) :
    n.primeFactors.card≤4 := by
  obtain ⟨r,q,b,p,he,hr,hq,hrq,hmin,hg,hp,hpc⟩ := hcrit
  have hrest := (ZetaRieszBalancedRadialPayment.mem_centralLabels.mp hn).1
  have hs : Squarefree n := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hrest).1).2
  rw [he] at hs
  have hb0 := hs.of_mul_right.of_mul_right.ne_zero
  have hqb0 := hs.of_mul_right.ne_zero
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hpB := Nat.dvd_of_mem_primeFactors hp
  have hqp : SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)≤log q+log p := by
    have hh := hg (q*p) (Nat.mem_divisors.mpr ⟨Nat.mul_dvd_mul_left q hpB,hqb0⟩)
    rw [log_mul_nat hq.ne_zero hpp.ne_zero] at hh
    rcases hh with hh | hh
    · exact hh
    · have hc := (Finset.mem_filter.mp hpc).2.1
      linarith only [hc,hh]
  have hpN : p∈n.primeFactors := by
    rw [he]
    exact Nat.primeFactors_mono
      (show b∣r*(q*b) from ⟨r*q,by ring⟩) hs.ne_zero hp
  have hpmax : p≤largestPrime n := by
    rw [largestPrime,dif_pos (show n.primeFactors.Nonempty from ⟨p,hpN⟩)]
    exact Finset.le_max' _ _ hpN
  have hplog : log p<(51/50 : ℝ)*dyadicMomentOrder j :=
    (log_le_log (by exact_mod_cast hpp.pos)
      (by exact_mod_cast hpmax)).trans_lt (mem_restLabels.mp hrest).2
  have hl := ZetaRieszPostHingeEnergy.length_ge_rational hN hu hU
  have ht := (ZetaRieszBalancedRadialPayment.mem_centralLabels.mp hn).2.2
  have hNp : (0 : ℝ)<dyadicMomentOrder j := by
    exact_mod_cast (by omega : 0<dyadicMomentOrder j)
  by_contra hc
  have hPF : (r*(q*b)).primeFactors={r}∪({q}∪b.primeFactors) := by
    rw [Nat.primeFactors_mul hr.ne_zero hqb0,Nat.primeFactors_mul hq.ne_zero hb0,
      hr.primeFactors,hq.primeFactors]
  have hcard : n.primeFactors.card≤2+b.primeFactors.card := by
    rw [he,hPF]
    have h1 := Finset.card_union_le ({r} : Finset ℕ) ({q}∪b.primeFactors)
    have h2 := Finset.card_union_le ({q} : Finset ℕ) b.primeFactors
    simp only [Finset.card_singleton] at h1 h2
    omega
  have hecard : 2≤(b.primeFactors.erase p).card := by
    rw [Finset.card_erase_of_mem hp]
    omega
  have hqlog : 0≤log q := log_natCast_nonneg q
  have hcardR : (2 : ℝ)≤(b.primeFactors.erase p).card := by exact_mod_cast hecard
  have hsum : (b.primeFactors.erase p).card*log q≤
      ∑ t∈b.primeFactors.erase p,log t := by
    have hh : (∑ _t∈b.primeFactors.erase p,log q)≤
        ∑ t∈b.primeFactors.erase p,log t := Finset.sum_le_sum (fun t ht =>
      log_le_log (by exact_mod_cast hq.pos)
        (by exact_mod_cast hmin t (Finset.mem_erase.mp ht).2))
    simpa only [Finset.sum_const,nsmul_eq_mul] using hh
  have hbmass : log p+2*log q≤log b := by
    have hsplit := Finset.sum_erase_add b.primeFactors (fun t : ℕ => log t) hp
    have heq := CoprimeEulerPhase.squarefree_log_eq_prime_sum hs.of_mul_right.of_mul_right
    have hh := mul_le_mul_of_nonneg_right hcardR hqlog
    linarith only [hsplit,heq,hsum,hh]
  have hlog : log n=log r+log q+log b := by
    rw [he,log_mul_nat hr.ne_zero hqb0,log_mul_nat hq.ne_zero hb0]
    ring
  nlinarith only [hl,hqp,hplog,hbmass,hlog,ht,hNp,log_natCast_nonneg r]

/-- A new favorable PHASE test on the original central population. No
label is completed, no phase is frozen, and the ordinary-prime head is
not included in or deleted by this filter. -/
def favorableLabels (u y : ℝ) (j : ℕ) : Finset ℕ :=
  (ZetaRieszBalancedRadialPayment.centralLabels u j).filter (fun n =>
    PrimeCritical (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) n ∧
      0≤(zetaPrimeLogKernel (dyadicMomentOrder j) (3/2+Complex.I*y) n).re)

theorem favorableLabels_subset (u y : ℝ) (j : ℕ) :
    favorableLabels u y j⊆ZetaRieszBalancedRadialPayment.centralLabels u j :=
  Finset.filter_subset _ _

/-- The arithmetic coefficient, not a fitted population allowance, pays
the whole favorable prime-critical response at source scale. -/
theorem favorable_atom_nonneg {u : ℝ} (hu : 0<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} {j n : ℕ}
    (hN : 65536≤dyadicMomentOrder j) (hn : n∈favorableLabels u y j) :
    0≤((u : ℂ)^(dyadicMomentOrder j+1)*
      (SquarefreeVaughanLogSource.coefficient
        (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) n*
        zetaPrimeLogKernel (dyadicMomentOrder j) (3/2+Complex.I*y) n)).re := by
  obtain ⟨hn,hcrit,hphase⟩ := Finset.mem_filter.mp hn
  have hns := (ZetaRieszBalancedRadialPayment.centralLabels_subset_rest u j hn)
  have hs : Squarefree n := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hns).1).2
  obtain ⟨r,q,b,p,he,hr,hq,hrq,hmin,hg,hp,hpc⟩ := hcrit
  have hb := native_budget hu hU hN hn
  rw [he] at hs hb
  have hcoef := coefficient_eq_least_log hr hq hrq hs hmin hp hg hb hpc
  rw [← he] at hcoef
  rw [hcoef,← Complex.ofReal_pow]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,sub_zero,
    zero_mul]
  exact mul_nonneg (pow_nonneg hu.le _) (mul_nonneg
    (div_nonneg (mul_nonneg (log_natCast_nonneg _) (log_natCast_nonneg _))
      (SquarefreeVaughanLogSource.length_pos u _).le) hphase)

/-- Counts are joined before this nonnegative signed credit is spent.
The theorem concerns the literal finite arithmetic sum at the native
order, not a numerical or continuum prediction. -/
theorem favorable_sum_nonneg {u : ℝ} (hu : 0<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) (y : ℝ) {j : ℕ}
    (hN : 65536≤dyadicMomentOrder j) :
    0≤((u : ℂ)^(dyadicMomentOrder j+1)*∑ n∈favorableLabels u y j,
      SquarefreeVaughanLogSource.coefficient
        (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) n*
        zetaPrimeLogKernel (dyadicMomentOrder j) (3/2+Complex.I*y) n).re := by
  rw [Finset.mul_sum,Complex.re_sum]
  exact Finset.sum_nonneg (fun n hn => favorable_atom_nonneg hu hU hN hn)

/-- Spend this common signed payment in the WHOLE central floor, retaining
the SAME head. No clipping monotonicity or double-spent credit is used.
The adverse complement is an explicit original subpopulation and its
cofinal numerical floor is still open. -/
theorem central_joint_floor_of_favorable {u : ℝ} (hu : 0<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) (y : ℝ) {j : ℕ}
    (hN : 65536≤dyadicMomentOrder j) :
    ((u : ℂ)^(dyadicMomentOrder j+1)*
      ∑ n∈ZetaRieszBalancedRadialPayment.centralLabels u j\favorableLabels u y j,
        SquarefreeVaughanLogSource.coefficient
          (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) n*
          zetaPrimeLogKernel (dyadicMomentOrder j) (3/2+Complex.I*y) n).re-
            ZetaRieszRoughPrimePairCancellation.nativeHead u y (dyadicMomentOrder j)≤
      (ZetaRieszBalancedRadialPayment.centralRest u y j).re-
        ZetaRieszRoughPrimePairCancellation.nativeHead u y (dyadicMomentOrder j) := by
  have he := Finset.sum_sdiff_eq_sub (f:=fun n =>
    SquarefreeVaughanLogSource.coefficient
      (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) n*
      zetaPrimeLogKernel (dyadicMomentOrder j) (3/2+Complex.I*y) n)
    (favorableLabels_subset u y j)
  have hp := favorable_sum_nonneg hu hU y hN
  rw [he,mul_sub,Complex.sub_re]
  change _≤_ at hp
  change _≤(_ : ℂ).re-_ at ⊢
  unfold ZetaRieszBalancedRadialPayment.centralRest
  linarith only [hp]

end RiemannGaussian.ZetaRieszCriticalPrimeFloor
