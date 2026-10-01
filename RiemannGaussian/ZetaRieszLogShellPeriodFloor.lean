/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszSymmetricPeriodPayment
import RiemannGaussian.ZetaRieszHigherRankHingeFloor
import RiemannGaussian.ZetaRieszOwnerTieFloor

/-!
# Count-uniform signed prime periods with comparable cofactor logarithms

The single-layer based-block geometry forces every cofactor prime into
one logarithmic shell. Retaining that restriction removes the growing
count cost: squarefree reciprocal masses are bounded by `M^k/k!` with a
constant `M` independent of both shell height and count. The already
proved signed complete-prime-period estimate can therefore be summed
over every selected count, with no count ceiling.

Only complete original fibres are paid. Literal clipped endpoints and
owner holes remain outside these theorems, and the supply comparison is
explicit. No whole floor or source-scale decay is claimed.
-/

noncomputable section
open Filter Topology Real
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszLogShellPeriodFloor
open ZetaRieszSymmetricPeriodPayment ZetaRieszStaggeredFloor
open ZetaRieszSignedPeriodFloor ZetaRieszFixedCountPeriod
open ZetaRieszAllowancePrimeBoxes ZetaRieszQuantitativePrimePeriod
open ZetaRieszShortDivisorCancellation ZetaRieszHingePairCancellation

/-- A fixed ratio in prime logarithms, retaining every selected prime. -/
def shellPrimes (H : ℝ) : Finset ℕ :=
  (Nat.primesLE ⌊exp (4*H)⌋₊).filter (fun p => H ≤ log p)

theorem shellPrimes_data {H : ℝ} {p : ℕ} (hp : p ∈ shellPrimes H) :
    p.Prime ∧ H ≤ log p ∧ log p ≤ 4*H := by
  obtain ⟨hp,hlo⟩ := Finset.mem_filter.mp hp
  obtain ⟨hupper,hprime⟩ := Nat.mem_primesLE.mp hp
  have hle : (p : ℝ) ≤ exp (4*H) :=
    (by exact_mod_cast hupper : (p : ℝ) ≤ ⌊exp (4*H)⌋₊).trans
      (Nat.floor_le (exp_nonneg _))
  exact ⟨hprime,hlo,by simpa using (log_le_log
    (by exact_mod_cast hprime.pos : (0 : ℝ) < p) hle)⟩

theorem mem_shellPrimes {H : ℝ} {p : ℕ} (hp : p.Prime)
    (hlo : H ≤ log p) (hhi : log p ≤ 4*H) : p ∈ shellPrimes H := by
  apply Finset.mem_filter.mpr
  refine ⟨Nat.mem_primesLE.mpr ⟨?_,hp⟩,hlo⟩
  apply Nat.le_floor
  simpa only [exp_log (by exact_mod_cast hp.pos : (0 : ℝ) < p)] using
    exp_le_exp.mpr hhi

/-- The shell cost is fixed as its height tends to infinity. -/
def shellMass : ℝ := 5*log 4

theorem shellMass_pos : 0 < shellMass := by
  unfold shellMass
  positivity

/-- This is an actual prime reciprocal-mass bound, not a prime-density
replacement or an error estimate for the signed carrier. -/
theorem prime_shell_mass_le (P : Finset ℕ) {H : ℝ} (hH : 1 ≤ H)
    (hP : ∀ p ∈ P, p.Prime ∧ H ≤ log p ∧ log p ≤ 4*H) :
    (∑ p ∈ P, (p : ℝ)⁻¹) ≤ shellMass := by
  have hH0 : 0 < H := by linarith
  have hmass := ZetaRieszCoreExtensions.prime_log_mass_le P
    (by linarith : 0 ≤ 4*H) (fun p hp => ⟨(hP p hp).1,(hP p hp).2.2⟩)
  have hfirst : H*(∑ p ∈ P, (p : ℝ)⁻¹) ≤
      ∑ p ∈ P, log p*exp (-log p) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p hp
    rw [exp_neg,exp_log (by exact_mod_cast (hP p hp).1.pos)]
    exact mul_le_mul_of_nonneg_right (hP p hp).2.1 (by positivity)
  have hlog : 0 ≤ log 4 := log_nonneg (by norm_num)
  have hh : log 4*(1+4*H) ≤ H*shellMass := by
    unfold shellMass
    nlinarith only [mul_nonneg hlog (show 0 ≤ H-1 by linarith)]
  exact (mul_le_mul_iff_right₀ hH0).mp (by
    simpa only [mul_comm H] using hfirst.trans (hmass.trans hh))

/-- The shell restriction and squarefreeness keep the true factorial
symmetry at every count, including a moving count set. -/
theorem shell_cofactor_mass_le (D : Finset ℕ) (k : ℕ) {H : ℝ} (hH : 1 ≤ H)
    (hD : ∀ a ∈ D, Squarefree a ∧ a.primeFactors.card=k ∧
      a.primeFactors ⊆ shellPrimes H) :
    (∑ a ∈ D, (a : ℝ)⁻¹) ≤ shellMass^k/(k.factorial : ℝ) := by
  have hprod (a : ℕ) (ha : a ∈ D) :
      (∏ p ∈ a.primeFactors, (p : ℝ)⁻¹) = (a : ℝ)⁻¹ := by
    rw [Finset.prod_inv_distrib,← Nat.cast_prod,
      Nat.prod_primeFactors_of_squarefree (hD a ha).1]
  have hh := factorial_product_mass D (shellPrimes H) k
    (fun p => (p : ℝ)⁻¹) (by intro p _; positivity) hD
  have hm := prime_shell_mass_le (shellPrimes H) hH
    (fun _ hp => shellPrimes_data hp)
  have hpow := pow_le_pow_left₀ (Finset.sum_nonneg (by intro p _; positivity)) hm k
  have hfact : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  apply (le_div_iff₀ hfact).mpr
  rw [mul_comm]
  simpa only [Finset.sum_congr rfl hprod] using hh.trans hpow

private theorem successor_le_two_pow (k : ℕ) : ((k : ℝ)+1) ≤ (2 : ℝ)^k := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    rw [Nat.cast_succ,pow_succ]
    have ht : (1 : ℝ) ≤ (2 : ℝ)^k := one_le_pow₀ (by norm_num)
    nlinarith only [ih,ht]

private theorem responseConstant_le (k : ℕ) : responseConstant k ≤ 6*(2 : ℝ)^k := by
  have hp (b : ℕ) : (ZetaRieszSignedSperner.parityCapacity (k-2) b : ℝ) ≤ (2 : ℝ)^k := by
    have hh := (ZetaRieszSignedSperner.parityCapacity_le_middle (k-2) b).trans
      (Nat.choose_le_two_pow (k-2) ((k-2)/2))
    have ht : (2 : ℕ)^(k-2) ≤ 2^k := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact_mod_cast hh.trans ht
  have h0 := hp 0
  have h1 := hp 1
  have hpow : (1 : ℝ) ≤ (2 : ℝ)^k := one_le_pow₀ (by norm_num)
  unfold responseConstant
  nlinarith only [h0,h1,hpow]

/-- Joint count cost after summing each original signed prime fibre. -/
def shellCountCost (k : ℕ) : ℝ :=
  (200000*responseConstant k+1200*((k : ℝ)+1)*responseConstant k+
    400*(2 : ℝ)^k)*shellMass^k/(k.factorial : ℝ)

theorem shellCountCost_nonneg (k : ℕ) : 0 ≤ shellCountCost k := by
  unfold shellCountCost
  positivity [responseConstant_pos k,shellMass_pos]

theorem shellCountCost_le (k : ℕ) :
    shellCountCost k ≤ 1207600*(4*shellMass)^k/(k.factorial : ℝ) := by
  have hr := responseConstant_le k
  have hk := successor_le_two_pow k
  have hpow : (1 : ℝ) ≤ (2 : ℝ)^k := one_le_pow₀ (by norm_num)
  have hstep : 200000*responseConstant k+1200*((k : ℝ)+1)*responseConstant k+
      400*(2 : ℝ)^k ≤ 1207600*(4 : ℝ)^k := by
    rw [show (4 : ℝ)^k=(2 : ℝ)^k*(2 : ℝ)^k by rw [← mul_pow]; norm_num]
    have hkr := mul_le_mul hk hr (responseConstant_pos k).le (by positivity)
    nlinarith only [hr,hkr,mul_le_mul_of_nonneg_left hpow (by positivity : 0 ≤ (2 : ℝ)^k)]
  unfold shellCountCost
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hh := mul_le_mul_of_nonneg_right hstep (pow_nonneg shellMass_pos.le k)
  simpa only [mul_pow,mul_assoc] using hh

/-- One finite constant pays ALL selected cofactor counts. -/
def allCountCost : ℝ := 1207600*exp (4*shellMass)

theorem allCountCost_pos : 0 < allCountCost := by unfold allCountCost; positivity

theorem sum_shellCountCost_le (I : Finset ℕ) :
    (∑ k ∈ I, shellCountCost k) ≤ allCountCost := by
  have he := NormedSpace.expSeries_div_hasSum_exp (4*shellMass)
  have hh := he.summable.sum_le_tsum I
    (by intro k _; positivity [shellMass_pos])
  rw [he.tsum_eq] at hh
  rw [← Real.exp_eq_exp_ℝ] at hh
  have hb := Finset.sum_le_sum (fun k (_hk : k ∈ I) => shellCountCost_le k)
  have hscale := mul_le_mul_of_nonneg_left hh (by norm_num : (0 : ℝ) ≤ 1207600)
  unfold allCountCost
  exact hb.trans (by simpa only [← Finset.mul_sum,mul_div_assoc] using hscale)

/-- Retaining the cofactor shell improves the already proved literal
signed period estimate. No countwise phase absolute value is used. -/
theorem shell_population_floor {k N : ℕ} (hk : 2 ≤ k) {e : ℝ} (he : |e|=1)
    (A S : Finset ℕ) {v y L H : ℝ} (hv : 500000 ≤ v)
    (hNv : (N : ℝ)+2 ≤ v) (hy : 54 ≤ y) (hL : (67/100 : ℝ)*v ≤ L)
    (hH : 1 ≤ H) (hS : S ⊆ ZetaRieszTransitionFiveFloor.cofactors k v)
    (hshell : ∀ a ∈ S, a.primeFactors ⊆ shellPrimes H)
    (hA : ∀ a ∈ S, ∀ p ∈ logPrimes (v-Real.pi/y-log a) (2*Real.pi/y), p ∈ A)
    (hpeak : sin (y*v)=0) (hsign : e*cos (y*v) ≤ 0) :
    -(shellCountCost k*v^(-(1/2 : ℝ)))*(amplitude N v/v) ≤
      ∑ a ∈ S, ∑ p ∈ logPrimes (v-Real.pi/y-log a) (2*Real.pi/y),
        signedPart e A L y N (p*a) := by
  have hv0 : 0 < v := by linarith
  have hSF (a : ℕ) (ha : a ∈ S) : Squarefree a ∧ a.primeFactors.card=k ∧
      a.primeFactors ⊆ shellPrimes H := by
    have hd := ZetaRieszTransitionFiveFloor.cofactor_data (hS ha)
    exact ⟨hd.1,hd.2.1,hshell a ha⟩
  have hrec := shell_cofactor_mass_le S k hH hSF
  have hlog : (∑ a ∈ S, log a.minFac*(a : ℝ)⁻¹) ≤
      v*(shellMass^k/(k.factorial : ℝ)) := by
    have hh := Finset.sum_le_sum (fun a (ha : a ∈ S) =>
      mul_le_mul_of_nonneg_right
        (ZetaRieszTransitionFiveFloor.cofactor_data (hS ha)).2.2.1
        (by positivity : 0 ≤ (a : ℝ)⁻¹))
    rw [← Finset.mul_sum] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left hrec hv0.le)
  let F := 200000*responseConstant k/v^2+
    1200*((k : ℝ)+1)*responseConstant k*sqrt (N+1)/v^2
  let G := 400*(2 : ℝ)^k/v
  have hF : 0 ≤ F := by dsimp [F]; positivity [responseConstant_pos k]
  have hG : 0 ≤ G := by dsimp [G]; positivity
  have hmass : (∑ a ∈ S, (F*(log a.minFac*(a : ℝ)⁻¹)+G*(a : ℝ)⁻¹)) ≤
      (F*v+G)*(shellMass^k/(k.factorial : ℝ)) := by
    rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum]
    have hl := mul_le_mul_of_nonneg_left hlog hF
    have hr := mul_le_mul_of_nonneg_left hrec hG
    nlinarith only [hl,hr]
  have hrat : v^(1/2 : ℝ)/v=v^(-(1/2 : ℝ)) := by
    have hh := rpow_sub hv0 (1/2 : ℝ) 1
    norm_num at hh
    exact hh.symm
  have hsqrt : sqrt (N+1)/v ≤ v^(-(1/2 : ℝ)) := by
    have hh := div_le_div_of_nonneg_right
      (sqrt_le_sqrt (show (N : ℝ)+1 ≤ v by linarith)) hv0.le
    rwa [sqrt_eq_rpow v,hrat] at hh
  have hinv : 1/v ≤ v^(-(1/2 : ℝ)) := by
    have hh := rpow_le_rpow_of_exponent_le (show 1 ≤ v by linarith)
      (show (-1 : ℝ) ≤ -(1/2 : ℝ) by norm_num)
    simpa only [rpow_neg_one,one_div] using hh
  have hcosteq : F*v+G =
      (200000*responseConstant k+400*(2 : ℝ)^k)*(1/v)+
        1200*((k : ℝ)+1)*responseConstant k*(sqrt (N+1)/v) := by
    dsimp [F,G]
    field_simp
    ring
  have hprice : F*v+G ≤
      (200000*responseConstant k+1200*((k : ℝ)+1)*responseConstant k+
        400*(2 : ℝ)^k)*v^(-(1/2 : ℝ)) := by
    rw [hcosteq]
    have h₁ := mul_le_mul_of_nonneg_left hinv
      (by positivity [responseConstant_pos k] :
        0 ≤ 200000*responseConstant k+400*(2 : ℝ)^k)
    have h₂ := mul_le_mul_of_nonneg_left hsqrt
      (by positivity [responseConstant_pos k] :
        0 ≤ 1200*((k : ℝ)+1)*responseConstant k)
    nlinarith only [h₁,h₂]
  have hcost : (∑ a ∈ S, (F*(log a.minFac*(a : ℝ)⁻¹)+G*(a : ℝ)⁻¹)) ≤
      shellCountCost k*v^(-(1/2 : ℝ)) := by
    have hh := mul_le_mul_of_nonneg_right hprice
      (by positivity [shellMass_pos] : 0 ≤ shellMass^k/(k.factorial : ℝ))
    exact hmass.trans (by simpa only [shellCountCost,div_eq_mul_inv,mul_assoc,
      mul_left_comm,mul_comm] using hh)
  have hrow := Finset.sum_le_sum (fun a (ha : a ∈ S) =>
    ZetaRieszTransitionFiveFloor.signedPart_fibre_radial hk he A hv hNv hy hL
      (hS ha) (hA a ha) hpeak hsign)
  rw [← Finset.mul_sum] at hrow
  have hbase : 0 ≤ amplitude N v/v := div_nonneg (amplitude_nonneg N hv0.le) hv0.le
  have hh := mul_le_mul_of_nonpos_left hcost (neg_nonpos.mpr hbase)
  calc
    _ = -(amplitude N v/v)*(shellCountCost k*v^(-(1/2 : ℝ))) := by ring
    _ ≤ _ := hh.trans hrow

/-- Every selected count is joined before pricing. There is NO upper
count restriction and no fixed-count eventual threshold. -/
theorem all_counts_floor (I : Finset ℕ) (N : ℕ) (e : ℝ) (A : Finset ℕ)
    (S : ℕ → Finset ℕ) {v y L H : ℝ} (hI : ∀ k ∈ I, 2 ≤ k) (he : |e|=1)
    (hv : 500000 ≤ v) (hNv : (N : ℝ)+2 ≤ v) (hy : 54 ≤ y)
    (hL : (67/100 : ℝ)*v ≤ L) (hH : 1 ≤ H)
    (hS : ∀ k ∈ I, S k ⊆ ZetaRieszTransitionFiveFloor.cofactors k v)
    (hshell : ∀ k ∈ I, ∀ a ∈ S k, a.primeFactors ⊆ shellPrimes H)
    (hA : ∀ k ∈ I, ∀ a ∈ S k,
      ∀ p ∈ logPrimes (v-Real.pi/y-log a) (2*Real.pi/y), p ∈ A)
    (hpeak : sin (y*v)=0) (hsign : e*cos (y*v) ≤ 0) :
    -(allCountCost*v^(-(1/2 : ℝ)))*(amplitude N v/v) ≤
      ∑ k ∈ I, ∑ a ∈ S k, ∑ p ∈ logPrimes (v-Real.pi/y-log a) (2*Real.pi/y),
        signedPart e A L y N (p*a) := by
  have hh := Finset.sum_le_sum (fun k hk => shell_population_floor (hI k hk)
    he A (S k) hv hNv hy hL hH (hS k hk) (hshell k hk) (hA k hk) hpeak hsign)
  have hbase : 0 ≤ amplitude N v/v := by
    exact div_nonneg (amplitude_nonneg N (by linarith)) (by linarith)
  have hcost := mul_le_mul_of_nonneg_right (sum_shellCountCost_le I)
    (by positivity : 0 ≤ v^(-(1/2 : ℝ)))
  have hpaid := mul_le_mul_of_nonneg_right (neg_le_neg hcost) hbase
  exact hpaid.trans (by
    simpa only [← Finset.sum_mul,Finset.sum_neg_distrib] using hh)

/-- The total-logarithmic cancellation centre is common to all prime
geometries with the same based rank. Both original hinges are retained. -/
theorem single_layer_radial_eq {a e : ℕ} (ha : 0 < a) (he : e ∣ a)
    {k : ℕ} (hk : 2 ≤ k) (P L : ℝ) :
    log (a/e : ℕ)-((k : ℝ)-1)*P-(k : ℝ)*(log (a/e : ℕ)-L) =
      ((k : ℝ)-1)*(log e+(k : ℝ)*L/((k : ℝ)-1)-(P+log a)) := by
  have he0 := Nat.pos_of_dvd_of_pos he ha
  have hq0 := Nat.div_pos (Nat.le_of_dvd ha he) he0
  have hloga : log a=log e+log (a/e : ℕ) := by
    calc
      _ = log (e*(a/e) : ℕ) := by rw [Nat.mul_div_cancel' he]
      _ = _ := by rw [Nat.cast_mul,log_mul (by exact_mod_cast he0.ne')
        (by exact_mod_cast hq0.ne')]
  have hk0 : (k : ℝ)-1 ≠ 0 := by
    have hh : (2 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  rw [hloga]
  field_simp
  ring

/-- Because the based block contains the canonical least pair, its
single-layer condition restricts ALL cofactor primes, including the base.
This is the support information lost by the older fractional-moment cost. -/
theorem single_layer_all_cofactor_logs {a p e : ℕ} (ha : Squarefree a)
    (hc : 2 ≤ a.primeFactors.card) (he : e ∣ a/leastPairBlock a) {L : ℝ}
    (hD : 0 ≤ log (a/e : ℕ)-L)
    (hprime : ∀ q ∈ (a/e).primeFactors,
      (log p+(log (a/e : ℕ)-L))/2 ≤ log q)
    (howner : ∀ q ∈ a.primeFactors, log q ≤ log p) :
    ∀ q ∈ a.primeFactors, log p/2 ≤ log q ∧ log q ≤ log p := by
  have hQ := (leastPairBlock_data ha hc).1
  have hQR := ZetaRieszShortDivisorOrbits.block_dvd_quotient hQ he
  have hmin : a.minFac ∣ a/e :=
    (show a.minFac ∣ leastPairBlock a from dvd_mul_right _ _).trans hQR
  have ha1 : a ≠ 1 := by intro hh; simp [hh] at hc
  have hmprime := Nat.minFac_prime ha1
  have hR := ha.squarefree_of_dvd (Nat.div_dvd_of_dvd
    (ZetaRieszShortDivisorOrbits.base_dvd hQ he))
  have hm := hprime a.minFac (hmprime.mem_primeFactors hmin hR.ne_zero)
  intro q hq
  have hminq : log a.minFac ≤ log q := log_le_log
    (by exact_mod_cast Nat.minFac_pos a)
    (by exact_mod_cast (Nat.minFac_le_of_dvd (Nat.prime_of_mem_primeFactors hq).two_le
      (Nat.dvd_of_mem_primeFactors hq)))
  exact ⟨by linarith,howner q hq⟩

/-- The comparable-log restriction follows from the CURRENT retained
based geometry, rather than an extra arithmetic cancellation hypothesis. -/
theorem retained_single_layer_logs {u : ℝ} {N K n e : ℕ}
    (hn : n ∈ ZetaRieszParityPacket.coreBand u N K) (hs : Squarefree n)
    (hdata : ZetaRieszHigherRankHingeFloor.HigherRankData u N n e) :
    ∀ q ∈ (n/ZetaRieszPrimeEndpoint.largestPrime n).primeFactors,
      log (ZetaRieszPrimeEndpoint.largestPrime n)/2 ≤ log q ∧
        log q ≤ log (ZetaRieszPrimeEndpoint.largestPrime n) := by
  have hd := ZetaRieszShortDivisorOrbits.core_data hn hs
  have hc := ZetaRieszJointPrimeEnergy.core_count hn
  have hp := ZetaRieszOwnedCells.largestPrime_mem_of_two (by omega : 2 ≤ n.primeFactors.card)
  have hdiv := Nat.div_dvd_of_dvd (Nat.dvd_of_mem_primeFactors hp)
  apply single_layer_all_cofactor_logs hd.2.1 hd.2.2 hdata.base_dvd
    hdata.offset_nonneg (fun q hq => (hdata.single_layer q hq).1)
  intro q hq
  have hqn := Nat.primeFactors_mono hdiv hs.ne_zero hq
  have hne : n.primeFactors.Nonempty := ⟨q,hqn⟩
  have hm : n.primeFactors.max' hne=ZetaRieszPrimeEndpoint.largestPrime n := by
    simp only [ZetaRieszPrimeEndpoint.largestPrime,dif_pos hne]
  exact log_le_log (by exact_mod_cast (Nat.prime_of_mem_primeFactors hq).pos)
    (by exact_mod_cast (Finset.le_max' _ q hqn).trans_eq hm)

/-- The close-owner cover needs no count ceiling when its remaining
prime logarithms are retained in the shell. -/
theorem close_owner_shell_cover {k n p q : ℕ} {v H : ℝ}
    (hn : Squarefree n) (hc : n.primeFactors.card=k+2)
    (hp : p ∈ n.primeFactors) (hq : q ∈ n.primeFactors) (hpq : p ≠ q)
    (howner : ∀ r ∈ n.primeFactors, r ≤ p) (hgap : log p-1/8 < log q)
    (hT : v-1/16 < log n ∧ log n ≤ v+1/16)
    (hshell : n.primeFactors ⊆ shellPrimes H) :
    ∃ b : ℕ, n=p*(q*b) ∧ Squarefree b ∧ b.primeFactors.card=k ∧
      b.primeFactors ⊆ shellPrimes H ∧ log b ≤ v-2*H+1/16 ∧
      p ∈ ZetaRieszOwnerTieFloor.pairWindow v b ∧
      q ∈ ZetaRieszOwnerTieFloor.pairWindow v b := by
  obtain ⟨b,he,hs,hbc⟩ := ZetaRieszOwnerTieFloor.two_prime_factorization hn hc hp hq hpq
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hqp := Nat.prime_of_mem_primeFactors hq
  have hlog : log n=log p+log q+log b := by
    rw [he,Nat.cast_mul,log_mul (by exact_mod_cast hpp.ne_zero)
      (by exact_mod_cast Nat.mul_ne_zero hqp.ne_zero hs.ne_zero),Nat.cast_mul,
      log_mul (by exact_mod_cast hqp.ne_zero) (by exact_mod_cast hs.ne_zero)]
    ring
  have hqpLog : log q ≤ log p := log_le_log
    (by exact_mod_cast hqp.pos) (by exact_mod_cast howner q hq)
  have hbd : b ∣ n := by rw [he]; exact dvd_mul_of_dvd_right (dvd_mul_left b q) p
  have hbsub : b.primeFactors ⊆ shellPrimes H :=
    (Nat.primeFactors_mono hbd hn.ne_zero).trans hshell
  have hpH := (shellPrimes_data (hshell hp)).2.1
  have hqH := (shellPrimes_data (hshell hq)).2.1
  refine ⟨b,he,hs,hbc,hbsub,by linarith [hT.2],?_,?_⟩
  · apply (ZetaRieszMacroPrimeWindows.mem_logPrimes_iff _ _ _).mpr
    exact ⟨hpp,by linarith [hT.1],by linarith [hT.2]⟩
  · apply (ZetaRieszMacroPrimeWindows.mem_logPrimes_iff _ _ _).mpr
    exact ⟨hqp,by linarith [hT.1],by linarith [hT.2]⟩

/-- The original close-owner window gains TWO small prime masses, with
their exact short endpoints. This is used only for the clipped boundary. -/
theorem shell_pairWindow_mass {v H : ℝ} (hH : 10000 ≤ H) {b : ℕ}
    (hb : log b ≤ v-2*H+1/16) :
    (∑ p ∈ ZetaRieszOwnerTieFloor.pairWindow v b, (p : ℝ)⁻¹) ≤ 2/H := by
  have hH0 : 0 < H := by linarith
  have hlo : H/2 ≤ (v-log b)/2-1/8 := by linarith
  have ha : 5000 ≤ (v-log b)/2-1/8 := by linarith
  exact (ZetaRieszOwnerTieFloor.short_prime_mass ha (by norm_num) (by norm_num)).trans
    ((div_le_div_of_nonneg_left (by norm_num) (by positivity : 0 < H/2) hlo).trans_eq (by ring))

/-- A count-uniform boundary price, applied only after the two close
prime incidences have been counted jointly. -/
def shellTieCost (k : ℕ) : ℝ :=
  512*((k : ℝ)+2)*responseConstant (k+2)*shellMass^k/(k.factorial : ℝ)

theorem shellTieCost_le (k : ℕ) :
    shellTieCost k ≤ 24576*(4*shellMass)^k/(k.factorial : ℝ) := by
  have hr := responseConstant_le (k+2)
  have hk : (k : ℝ)+2 ≤ 2*(2 : ℝ)^k := by
    have hs := successor_le_two_pow k
    have hp : (1 : ℝ) ≤ (2 : ℝ)^k := one_le_pow₀ (by norm_num)
    linarith
  have hr' : responseConstant (k+2) ≤ 24*(2 : ℝ)^k := by
    norm_num [pow_add] at hr
    convert hr using 1
    ring
  have hprod := mul_le_mul hk hr' (responseConstant_pos (k+2)).le (by positivity)
  unfold shellTieCost
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hstep : 512*((k : ℝ)+2)*responseConstant (k+2) ≤ 24576*(4 : ℝ)^k := by
    rw [show (4 : ℝ)^k=(2 : ℝ)^k*(2 : ℝ)^k by rw [← mul_pow]; norm_num]
    nlinarith only [hprod]
  have hh := mul_le_mul_of_nonneg_right hstep (pow_nonneg shellMass_pos.le k)
  simpa only [mul_pow,mul_assoc] using hh

/-- An actual selected boundary population at ANY count. Original
allocation, physical masks and full complex phase remain on the left. -/
theorem close_owner_shell_norm_bound {k N : ℕ} (hk : 0 < k)
    (A D : Finset ℕ) (y : ℝ) {v L H : ℝ} (hH : 10000 ≤ H)
    (hv : 0 < v) (hNv : (N : ℝ)+1 ≤ v) (hL : v/2 ≤ L)
    (hD : ∀ n ∈ D, Squarefree n ∧ n.primeFactors.card=k+2 ∧
      (v-1/16 < log n ∧ log n ≤ v+1/16) ∧
      ZetaRieszOwnerTieFloor.CloseOwners n ∧ n.primeFactors ⊆ shellPrimes H) :
    (∑ n ∈ D, ‖ZetaRieszJointAllocation.residualCoefficient A L N n*
      zetaPrimeLogKernel N (3/2+Complex.I*y) n‖) ≤
      (shellTieCost k/v)*(amplitude N v/v) := by
  by_cases hne : D.Nonempty
  · obtain ⟨n0,hn0⟩ := hne
    have hn := hD n0 hn0
    have hlogs : log n0 ≤ (k+2 : ℕ)*(4*H) := by
      rw [CoprimeEulerPhase.squarefree_log_eq_prime_sum hn.1]
      have hh := Finset.sum_le_sum (fun p hp => (shellPrimes_data (hn.2.2.2.2 hp)).2.2)
      simpa only [Finset.sum_const,nsmul_eq_mul,hn.2.1] using hh
    have hkR : (0 : ℝ) < k+2 := by positivity
    have hH0 : 0 < H := by linarith
    have hwidth : v ≤ 8*H*((k : ℝ)+2) := by
      push_cast at hlogs
      nlinarith only [hlogs,hn.2.2.1.1,mul_le_mul_of_nonneg_left
        (show (1 : ℝ) ≤ k+2 by linarith [Nat.cast_nonneg (α := ℝ) k]) hH0.le,hH]
    let R := (ZetaRieszCofactorMass.products k (4*H)).filter (fun b : ℕ =>
      Squarefree b ∧ b.primeFactors.card=k ∧ b.primeFactors ⊆ shellPrimes H ∧
        log b ≤ v-2*H+1/16)
    let V := R.sigma (fun b => (ZetaRieszOwnerTieFloor.pairWindow v b).product
      (ZetaRieszOwnerTieFloor.pairWindow v b))
    let label := fun x : Σ _ : ℕ, ℕ×ℕ => x.2.1*(x.2.2*x.1)
    let f := fun n => if n ∈ D then
      ‖ZetaRieszJointAllocation.residualCoefficient A L N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ else 0
    let B := 2*amplitude N v*responseConstant (k+2)/L
    have hL0 : 0 < L := by linarith
    have hB : 0 ≤ B := by dsimp [B]; positivity [amplitude_nonneg N hv.le,responseConstant_pos (k+2)]
    have hf (n : ℕ) : 0 ≤ f n := by dsimp [f]; split_ifs <;> positivity
    have hcover : D ⊆ V.image label := by
      intro n hn
      obtain ⟨hs,hc,hT,⟨p,hp,q,hq,hpq,howner,hgap⟩,hshell⟩ := hD n hn
      obtain ⟨b,he,hb,hbc,hbsub,hcap,hpw,hqw⟩ :=
        close_owner_shell_cover hs hc hp hq hpq howner hgap hT hshell
      have hbm : b ∈ ZetaRieszCofactorMass.products k (4*H) :=
        ZetaRieszCofactorMass.mem_products_of_squarefree hb hbc
          (fun r hr => (shellPrimes_data (hbsub hr)).2.2)
      exact Finset.mem_image.mpr ⟨⟨b,(p,q)⟩,Finset.mem_sigma.mpr
        ⟨Finset.mem_filter.mpr ⟨hbm,hb,hbc,hbsub,hcap⟩,
          Finset.mem_product.mpr ⟨hpw,hqw⟩⟩,he.symm⟩
    have hfirst : (∑ n ∈ D, ‖ZetaRieszJointAllocation.residualCoefficient A L N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n‖) ≤ ∑ x ∈ V, f (label x) := by
      have hh := (Finset.sum_le_sum_of_subset_of_nonneg hcover (fun n _ _ => hf n)).trans
        (Finset.sum_image_le_of_nonneg (fun n _ => hf n))
      simpa only [f,ite_true,Finset.sum_congr rfl (fun n hn => if_pos hn)] using hh
    have hpoint (b : ℕ) (hb : b ∈ R) (p q : ℕ) :
        f (p*(q*b)) ≤ B*(4*H*(b : ℝ)⁻¹)*(p : ℝ)⁻¹*(q : ℝ)⁻¹ := by
      obtain ⟨_,hbs,hbc,hbsub,_⟩ := Finset.mem_filter.mp hb
      have hb1 : b ≠ 1 := by intro hh; simp [hh] at hbc; omega
      have hm : log b.minFac ≤ 4*H := (shellPrimes_data
        (hbsub ((Nat.minFac_prime hb1).mem_primeFactors (Nat.minFac_dvd b) hbs.ne_zero))).2.2
      by_cases hn : p*(q*b) ∈ D
      · have hd := hD _ hn
        have hT : |log (p*(q*b) : ℕ)-v| ≤ 1 :=
          abs_le.mpr ⟨by linarith [hd.2.2.1.1],by linarith [hd.2.2.1.2]⟩
        have hh := ZetaRieszOwnerTieFloor.boundary_atom_norm A y hv hNv hL0 hd.1 hd.2.1
          hb1 (dvd_mul_of_dvd_right (dvd_mul_left b q) p) hT
        dsimp only [f]
        rw [if_pos hn]
        have hle := mul_le_mul_of_nonneg_left hm (by positivity :
          0 ≤ B*(b : ℝ)⁻¹*(p : ℝ)⁻¹*(q : ℝ)⁻¹)
        have heq : B*(log b.minFac/(p*(q*b) : ℕ)) =
            (B*(b : ℝ)⁻¹*(p : ℝ)⁻¹*(q : ℝ)⁻¹)*log b.minFac := by
          simp only [Nat.cast_mul,div_eq_mul_inv,mul_inv_rev]
          ring
        change _ ≤ B*(log b.minFac/(p*(q*b) : ℕ)) at hh
        rw [heq] at hh
        exact hh.trans (by convert hle using 1; ring)
      · dsimp only [f]
        rw [if_neg hn]
        positivity
    have hrec := shell_cofactor_mass_le R k (by linarith : 1 ≤ H) (by
      intro b hb
      have hh := (Finset.mem_filter.mp hb).2
      exact ⟨hh.1,hh.2.1,hh.2.2.1⟩)
    have hsum : (∑ x ∈ V, f (label x)) ≤
        B*(4*H)*(4/H^2)*(shellMass^k/(k.factorial : ℝ)) := by
      change (∑ x ∈ R.sigma _, f (label x)) ≤ _
      rw [Finset.sum_sigma]
      have hrow (b : ℕ) (hb : b ∈ R) :
          (∑ pq ∈ (ZetaRieszOwnerTieFloor.pairWindow v b).product
            (ZetaRieszOwnerTieFloor.pairWindow v b), f (pq.1*(pq.2*b))) ≤
          B*(4*H)*(4/H^2)*(b : ℝ)⁻¹ := by
        rw [Finset.product_eq_sprod,Finset.sum_product]
        have hh := Finset.sum_le_sum (s := ZetaRieszOwnerTieFloor.pairWindow v b)
          (fun p _ => Finset.sum_le_sum (s := ZetaRieszOwnerTieFloor.pairWindow v b)
            (fun q _ => hpoint b hb p q))
        have hm := shell_pairWindow_mass hH (Finset.mem_filter.mp hb).2.2.2.2
        have hsq := pow_le_pow_left₀ (by positivity) hm 2
        have heq : (∑ p ∈ ZetaRieszOwnerTieFloor.pairWindow v b,
            ∑ q ∈ ZetaRieszOwnerTieFloor.pairWindow v b,
              B*(4*H*(b : ℝ)⁻¹)*(p : ℝ)⁻¹*(q : ℝ)⁻¹) =
            (B*(4*H*(b : ℝ)⁻¹))*(∑ p ∈ ZetaRieszOwnerTieFloor.pairWindow v b,(p : ℝ)⁻¹)^2 := by
          simp_rw [← Finset.mul_sum]
          rw [← Finset.sum_mul,← Finset.mul_sum,pow_two]
          ring
        rw [heq] at hh
        have hpay := mul_le_mul_of_nonneg_left hsq
          (by positivity : 0 ≤ B*(4*H*(b : ℝ)⁻¹))
        exact hh.trans (by convert hpay using 1; field_simp; ring)
      have hh := Finset.sum_le_sum hrow
      rw [← Finset.mul_sum] at hh
      exact hh.trans (mul_le_mul_of_nonneg_left hrec (by positivity))
    have hpre : B ≤ 4*(amplitude N v/v)*responseConstant (k+2) := by
      have hh := div_le_div_of_nonneg_left
        (by positivity [amplitude_nonneg N hv.le,responseConstant_pos (k+2)] :
          0 ≤ 2*amplitude N v*responseConstant (k+2))
        (by positivity : 0 < v/2) hL
      convert hh using 1
      all_goals first | rfl | ring
    have hcost := mul_le_mul_of_nonneg_right hpre
      (by positivity [shellMass_pos] : 0 ≤ (4*H)*(4/H^2)*(shellMass^k/(k.factorial : ℝ)))
    have hHinv : 1/H ≤ 8*((k : ℝ)+2)/v :=
      (div_le_div_iff₀ hH0 hv).mpr (by nlinarith only [hwidth])
    have hpay := mul_le_mul_of_nonneg_left hHinv (by positivity [shellMass_pos,responseConstant_pos (k+2),amplitude_nonneg N hv.le] :
      0 ≤ 64*(amplitude N v/v)*responseConstant (k+2)*(shellMass^k/(k.factorial : ℝ)))
    have heq : (4*(amplitude N v/v)*responseConstant (k+2))*
        ((4*H)*(4/H^2)*(shellMass^k/(k.factorial : ℝ))) =
        (64*(amplitude N v/v)*responseConstant (k+2)*(shellMass^k/(k.factorial : ℝ)))*(1/H) := by
      field_simp
      ring
    rw [heq] at hcost
    exact hfirst.trans (hsum.trans (by
      have hh := hcost.trans hpay
      unfold shellTieCost
      convert hh using 1 <;> ring))
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne,Finset.sum_empty]
    unfold shellTieCost
    positivity [responseConstant_pos (k+2),amplitude_nonneg N hv.le,shellMass_pos]

/-- One constant pays every count of the literal close-owner boundary. -/
def allTieCost : ℝ := 24576*exp (4*shellMass)

theorem allTieCost_pos : 0 < allTieCost := by unfold allTieCost; positivity

theorem sum_shellTieCost_le (I : Finset ℕ) :
    (∑ k ∈ I, shellTieCost k) ≤ allTieCost := by
  have he := NormedSpace.expSeries_div_hasSum_exp (4*shellMass)
  have hh := he.summable.sum_le_tsum I (by intro k _; positivity [shellMass_pos])
  rw [he.tsum_eq,← Real.exp_eq_exp_ℝ] at hh
  have hb := Finset.sum_le_sum (fun k (_hk : k ∈ I) => shellTieCost_le k)
  have hscale := mul_le_mul_of_nonneg_left hh (by norm_num : (0 : ℝ) ≤ 24576)
  unfold allTieCost
  exact hb.trans (by simpa only [← Finset.mul_sum,mul_div_assoc] using hscale)

/-- No count restriction or count-dependent eventual threshold remains
in this ORIGINAL clipped-owner population estimate. -/
theorem all_count_close_owner_norm_bound (A D : Finset ℕ) (y : ℝ) (N : ℕ)
    {v L H : ℝ} (hH : 10000 ≤ H) (hv : 0 < v)
    (hNv : (N : ℝ)+1 ≤ v) (hL : v/2 ≤ L)
    (hD : ∀ n ∈ D, Squarefree n ∧ 3 ≤ n.primeFactors.card ∧
      (v-1/16 < log n ∧ log n ≤ v+1/16) ∧
      ZetaRieszOwnerTieFloor.CloseOwners n ∧ n.primeFactors ⊆ shellPrimes H) :
    (∑ n ∈ D, ‖ZetaRieszJointAllocation.residualCoefficient A L N n*
      zetaPrimeLogKernel N (3/2+Complex.I*y) n‖) ≤
      (allTieCost/v)*(amplitude N v/v) := by
  let I := D.image (fun n => n.primeFactors.card-2)
  let S := fun k => D.filter (fun n => n.primeFactors.card-2=k)
  let f := fun n => ‖ZetaRieszJointAllocation.residualCoefficient A L N n*
    zetaPrimeLogKernel N (3/2+Complex.I*y) n‖
  have hI : ∀ k ∈ I, 0 < k := by
    intro k hk
    obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hk
    have hh := (hD n hn).2.1
    omega
  have hrow (k : ℕ) (hk : k ∈ I) :
      (∑ n ∈ S k, f n) ≤ (shellTieCost k/v)*(amplitude N v/v) := by
    apply close_owner_shell_norm_bound (hI k hk) A (S k) y hH hv hNv hL
    intro n hn
    obtain ⟨hn,hcount⟩ := Finset.mem_filter.mp hn
    have hh := hD n hn
    exact ⟨hh.1,by omega,hh.2.2⟩
  have heq : (∑ k ∈ I, ∑ n ∈ S k, f n)=∑ n ∈ D, f n :=
    Finset.sum_fiberwise_of_maps_to (f := f) (fun n hn =>
      Finset.mem_image_of_mem (fun n => n.primeFactors.card-2) hn)
  have hh := Finset.sum_le_sum hrow
  rw [heq,← Finset.sum_mul,← Finset.sum_div] at hh
  have hcost := mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right (sum_shellTieCost_le I) hv.le)
    (div_nonneg (amplitude_nonneg N hv.le) hv.le)
  exact hh.trans hcost

/-- An actual signed floor for complete original prime fibres AND their
selected close-owner boundary, with all counts already summed. Other
clippings and owner holes are not silently supplied by this theorem. -/
theorem signed_period_with_boundary_floor (I : Finset ℕ) (N : ℕ) (e : ℝ)
    (A D : Finset ℕ) (S : ℕ → Finset ℕ) {v y L H : ℝ}
    (hI : ∀ k ∈ I, 2 ≤ k) (he : |e|=1) (hv : 500000 ≤ v)
    (hNv : (N : ℝ)+2 ≤ v) (hy : 54 ≤ y) (hL : (67/100 : ℝ)*v ≤ L)
    (hH : 10000 ≤ H)
    (hS : ∀ k ∈ I, S k ⊆ ZetaRieszTransitionFiveFloor.cofactors k v)
    (hshell : ∀ k ∈ I, ∀ a ∈ S k, a.primeFactors ⊆ shellPrimes H)
    (hA : ∀ k ∈ I, ∀ a ∈ S k,
      ∀ p ∈ logPrimes (v-Real.pi/y-log a) (2*Real.pi/y), p ∈ A)
    (hpeak : sin (y*v)=0) (hsign : e*cos (y*v) ≤ 0)
    (hD : ∀ n ∈ D, Squarefree n ∧ 3 ≤ n.primeFactors.card ∧
      (v-1/16 < log n ∧ log n ≤ v+1/16) ∧
      ZetaRieszOwnerTieFloor.CloseOwners n ∧ n.primeFactors ⊆ shellPrimes H) :
    -((allCountCost+allTieCost)*v^(-(1/2 : ℝ)))*(amplitude N v/v) ≤
      (∑ k ∈ I, ∑ a ∈ S k, ∑ p ∈ logPrimes (v-Real.pi/y-log a) (2*Real.pi/y),
        signedPart e A L y N (p*a))+
      (∑ n ∈ D, ZetaRieszJointAllocation.residualCoefficient A L N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n).re := by
  have hv0 : 0 < v := by linarith
  have hp := all_counts_floor I N e A S hI he hv hNv hy hL
    (by linarith : 1 ≤ H) hS hshell hA hpeak hsign
  have hb := all_count_close_owner_norm_bound A D y N hH hv0
    (show (N : ℝ)+1 ≤ v by linarith) (show v/2 ≤ L by linarith) hD
  have hsigns := Finset.sum_le_sum (s := D) (fun n _ =>
    (abs_le.mp (Complex.abs_re_le_norm
      (ZetaRieszJointAllocation.residualCoefficient A L N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n))).1)
  simp only [Finset.sum_neg_distrib,← Complex.re_sum] at hsigns
  have hinv : 1/v ≤ v^(-(1/2 : ℝ)) := by
    have hh := rpow_le_rpow_of_exponent_le (show 1 ≤ v by linarith)
      (show (-1 : ℝ) ≤ -(1/2 : ℝ) by norm_num)
    simpa only [rpow_neg_one,one_div] using hh
  have hbase : 0 ≤ amplitude N v/v := div_nonneg (amplitude_nonneg N hv0.le) hv0.le
  have hcost := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hinv allTieCost_pos.le) hbase
  have hcost' : (allTieCost/v)*(amplitude N v/v) ≤
      (allTieCost*v^(-(1/2 : ℝ)))*(amplitude N v/v) := by
    simpa only [div_eq_mul_inv,one_div,one_mul] using hcost
  calc
    _ = -(allCountCost*v^(-(1/2 : ℝ)))*(amplitude N v/v)-
        (allTieCost*v^(-(1/2 : ℝ)))*(amplitude N v/v) := by ring
    _ ≤ _ := add_le_add hp ((neg_le_neg (hb.trans hcost')).trans hsigns)

/-- The all-count price tends to zero relative to the SAME radial units;
it is not asserted to tend to zero at source scale by itself. -/
theorem tendsto_all_count_relative_cost :
    Tendsto (fun N : ℕ => (allCountCost+allTieCost)*
      ((N : ℝ)+1)^(-(1/2 : ℝ))) atTop (𝓝 0) := by
  have hlim := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1/2)).const_mul
    (allCountCost+allTieCost)
  have ht : Tendsto (fun N : ℕ => (N : ℝ)+1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 (tendsto_natCast_atTop_atTop (R := ℝ))
  simpa only [mul_zero,Function.comp_def] using hlim.comp ht

/-- Counts, shell heights, literal owner boundaries and radial periods
may all vary with the order. Their entire signed debit is joined before
charging the SAME radial units. No count ceiling remains in the price. -/
theorem radial_periods_with_boundary_floor (J : Finset ℕ) (N : ℕ) (A : Finset ℕ)
    (I : ℕ → Finset ℕ) (S : ℕ → ℕ → Finset ℕ) (D : ℕ → Finset ℕ)
    (v e H : ℕ → ℝ) (L y : ℝ) (hy : 54 ≤ y)
    (hI : ∀ i ∈ J, ∀ k ∈ I i, 2 ≤ k) (he : ∀ i ∈ J, |e i|=1)
    (hv : ∀ i ∈ J, 500000 ≤ v i ∧ (N : ℝ)+2 ≤ v i)
    (hL : ∀ i ∈ J, (67/100 : ℝ)*v i ≤ L) (hH : ∀ i ∈ J, 10000 ≤ H i)
    (hS : ∀ i ∈ J, ∀ k ∈ I i, S i k ⊆ ZetaRieszTransitionFiveFloor.cofactors k (v i))
    (hshell : ∀ i ∈ J, ∀ k ∈ I i, ∀ a ∈ S i k, a.primeFactors ⊆ shellPrimes (H i))
    (hA : ∀ i ∈ J, ∀ k ∈ I i, ∀ a ∈ S i k,
      ∀ p ∈ logPrimes (v i-Real.pi/y-log a) (2*Real.pi/y), p ∈ A)
    (hpeak : ∀ i ∈ J, sin (y*v i)=0) (hsign : ∀ i ∈ J, e i*cos (y*v i) ≤ 0)
    (hD : ∀ i ∈ J, ∀ n ∈ D i, Squarefree n ∧ 3 ≤ n.primeFactors.card ∧
      (v i-1/16 < log n ∧ log n ≤ v i+1/16) ∧
      ZetaRieszOwnerTieFloor.CloseOwners n ∧ n.primeFactors ⊆ shellPrimes (H i)) :
    -((allCountCost+allTieCost)*((N : ℝ)+1)^(-(1/2 : ℝ)))*
      (∑ i ∈ J, exp (-v i/2)*(v i)^N/N.factorial) ≤
      ∑ i ∈ J, ((∑ k ∈ I i, ∑ a ∈ S i k,
        ∑ p ∈ logPrimes (v i-Real.pi/y-log a) (2*Real.pi/y),
          signedPart (e i) A L y N (p*a))+
        (∑ n ∈ D i, ZetaRieszJointAllocation.residualCoefficient A L N n*
          zetaPrimeLogKernel N (3/2+Complex.I*y) n).re) := by
  have hrow (i : ℕ) (hi : i ∈ J) :
      -((allCountCost+allTieCost)*((N : ℝ)+1)^(-(1/2 : ℝ)))*
        (exp (-v i/2)*(v i)^N/N.factorial) ≤
        (∑ k ∈ I i, ∑ a ∈ S i k,
          ∑ p ∈ logPrimes (v i-Real.pi/y-log a) (2*Real.pi/y),
            signedPart (e i) A L y N (p*a))+
          (∑ n ∈ D i, ZetaRieszJointAllocation.residualCoefficient A L N n*
            zetaPrimeLogKernel N (3/2+Complex.I*y) n).re := by
    have hb := signed_period_with_boundary_floor (I i) N (e i) A (D i) (S i)
      (hI i hi) (he i hi) (hv i hi).1 (hv i hi).2 hy (hL i hi) (hH i hi)
      (hS i hi) (hshell i hi) (hA i hi) (hpeak i hi) (hsign i hi) (hD i hi)
    have hcost := mul_le_mul_of_nonneg_left
      (rpow_le_rpow_of_nonpos (by positivity : (0 : ℝ) < (N : ℝ)+1)
        (show (N : ℝ)+1 ≤ v i by linarith only [(hv i hi).2])
        (by norm_num : -(1/2 : ℝ) ≤ 0))
      (by linarith only [allCountCost_pos,allTieCost_pos] : 0 ≤ allCountCost+allTieCost)
    have hv0 : 0 < v i := by linarith only [(hv i hi).1]
    have hbase : 0 ≤ amplitude N (v i)/v i := div_nonneg (amplitude_nonneg N hv0.le) hv0.le
    have heq : amplitude N (v i)/v i=exp (-v i/2)*(v i)^N/N.factorial := by
      unfold amplitude
      rw [pow_succ]
      field_simp
    rw [← heq]
    exact (mul_le_mul_of_nonneg_right (neg_le_neg hcost) hbase).trans hb
  simpa only [← Finset.mul_sum] using Finset.sum_le_sum hrow

end RiemannGaussian.ZetaRieszLogShellPeriodFloor
