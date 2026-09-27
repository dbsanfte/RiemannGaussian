/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszCoreExtensions
import RiemannGaussian.ZetaRieszFivePrimeReserve

/-!
# Paying the small-prime triple sector from actual four-prime credit

Chebyshev bounds are applied only to positive counting costs. The resulting
debit is compared with the already proved signed four-prime supply at the
same radial location and original moment order.
-/

namespace RiemannGaussian.ZetaRieszSmallPrimeCompensation
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszAllowancePrimeBoxes ZetaRieszJointAllocation
open ZetaRieszOneSidedArithmetic ZetaRieszRadialCompensation
open ZetaRieszBandCompensation ZetaRieszTriplePrime ZetaSquarefreeRieszWindows

/-- The original labels with a small prime, in one radial slab. The upper
prime-log mask follows from the original physical cutoff. -/
def smallTriples (S : Finset ℕ) (M Q : ℕ) : Finset ℕ :=
  S.filter (fun n => Squarefree n ∧ n.primeFactors.card = 3 ∧
    2*(M : ℝ) ≤ Real.log n ∧ Real.log n < 2*(M : ℝ)+2 ∧
    (∀ p ∈ n.primeFactors, Real.log p ≤ (3/2 : ℝ)*M) ∧
    ∃ r ∈ n.primeFactors, r ≤ Q)

private def firstPrimes (M r : ℕ) : Finset ℕ :=
  logPrimes ((M : ℝ)/4) (2*M+2-Real.log r-(M : ℝ)/2)

private def secondPrimes (M r p : ℕ) : Finset ℕ :=
  logPrimes ((M : ℝ)/4) (2*M+2-Real.log r-Real.log p-(M : ℝ)/4)

private theorem logPrimes_mem {p : ℕ} (hp : p.Prime) {a h : ℝ}
    (hlo : a < Real.log p) (hhi : Real.log p ≤ a+h) : p ∈ logPrimes a h := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_Ioc.mpr ⟨?_,?_⟩,hp⟩
  · apply (Nat.floor_lt (Real.exp_nonneg a)).mpr
    simpa only [Real.exp_log hpR] using Real.exp_lt_exp.mpr hlo
  · apply (Nat.le_floor_iff (mul_nonneg (Real.exp_nonneg h) (Real.exp_nonneg a))).mpr
    simpa only [Real.exp_add,Real.exp_log hpR,mul_comm] using Real.exp_le_exp.mpr hhi

/-- The third finite difference costs the logarithm of ANY marked prime. -/
theorem abs_riesz_triple_le_marked_log (L : ℝ) {r p q : ℕ}
    (hr : r.Prime) (hp : p.Prime) (hq : q.Prime)
    (hrp : r ≠ p) (hrq : r ≠ q) (hpq : p ≠ q) :
    |VaughanLogAverage.riesz L (r*(p*q))| ≤ Real.log r := by
  rw [riesz_three_primes_eq_difference L hr hp hq hrp hrq hpq]
  have h₀ := primePairTent_bounds (Real.log_natCast_nonneg r) (Real.log_natCast_nonneg p) L
  have h₁ := primePairTent_bounds (Real.log_natCast_nonneg r) (Real.log_natCast_nonneg p)
    (L-Real.log q)
  apply abs_le.mpr
  unfold tripleDifference
  constructor <;> linarith [min_le_left (Real.log r) (Real.log p)]

private theorem factorization {S : Finset ℕ} {M Q n : ℕ}
    (hM : 1 ≤ M) (hQ : Real.log Q ≤ (M : ℝ)/8)
    (hn : n ∈ smallTriples S M Q) :
    ∃ r ∈ Nat.primesLE Q, ∃ p ∈ firstPrimes M r, ∃ q ∈ secondPrimes M r p,
      n = r*(p*q) ∧ r ≠ p ∧ r ≠ q ∧ p ≠ q := by
  obtain ⟨_,hs,hc,hlo,hhi,hphysical,r,hr,hrQ⟩ := Finset.mem_filter.mp hn
  have hrp := Nat.prime_of_mem_primeFactors hr
  have hrlog : Real.log r ≤ (M : ℝ)/8 :=
    (Real.log_le_log (by exact_mod_cast hrp.pos) (by exact_mod_cast hrQ)).trans hQ
  have hec : (n.primeFactors.erase r).card = 2 := by rw [Finset.card_erase_of_mem hr,hc]
  obtain ⟨p,q,hpq,he⟩ := Finset.card_eq_two.mp hec
  have hpE : p ∈ n.primeFactors.erase r := by simp [he]
  have hqE : q ∈ n.primeFactors.erase r := by simp [he]
  have hp := Finset.mem_of_mem_erase hpE
  have hq := Finset.mem_of_mem_erase hqE
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hqp := Nat.prime_of_mem_primeFactors hq
  have hnprod : n = r*(p*q) := by
    rw [← Nat.prod_primeFactors_of_squarefree hs,← Finset.mul_prod_erase _ _ hr,he]
    simp [hpq]
  have hlog : Real.log n = Real.log r+Real.log p+Real.log q := by
    rw [hnprod,Nat.cast_mul,Real.log_mul (by exact_mod_cast hrp.ne_zero)
      (by exact_mod_cast Nat.mul_ne_zero hpp.ne_zero hqp.ne_zero),Nat.cast_mul,
      Real.log_mul (by exact_mod_cast hpp.ne_zero) (by exact_mod_cast hqp.ne_zero)]
    ring
  have hm : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hpl : (M : ℝ)/4 < Real.log p := by linarith [hphysical q hq]
  have hql : (M : ℝ)/4 < Real.log q := by linarith [hphysical p hp]
  refine ⟨r,Nat.mem_primesLE.mpr ⟨hrQ,hrp⟩,p,?_,q,?_,hnprod,
    (Finset.ne_of_mem_erase hpE).symm,(Finset.ne_of_mem_erase hqE).symm,hpq⟩
  · apply logPrimes_mem hpp hpl
    linarith
  · apply logPrimes_mem hqp hql
    linarith

private theorem second_card_upper {M r p : ℕ} (hM : 1 ≤ M)
    (hp : p ∈ firstPrimes M r) :
    ((secondPrimes M r p).card : ℝ) ≤
      8*Real.log 4*Real.exp (2*(M : ℝ)+2)*Real.exp (-Real.log r)*
        Real.exp (-Real.log p)/((M : ℝ)+1) := by
  have hm : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hpU := (logPrimes_bounds hp).2.2
  have hwidth : 0 ≤ 2*(M : ℝ)+2-Real.log r-Real.log p-(M : ℝ)/4 := by
    change Real.log p ≤ (M : ℝ)/4+(2*M+2-Real.log r-(M : ℝ)/2) at hpU
    linarith
  have hb := ZetaRieszQuadrupleCompensation.interval_card_upper
    (show 0 < (M : ℝ)/4 by positivity) hwidth
  change ((secondPrimes M r p).card : ℝ) ≤ _ at hb
  have hden : ((M : ℝ)+1)/8 ≤ (M : ℝ)/4 := by linarith
  apply hb.trans
  calc
    _ ≤ Real.log 4*Real.exp ((M : ℝ)/4+(2*M+2-Real.log r-Real.log p-(M : ℝ)/4))/
        (((M : ℝ)+1)/8) := div_le_div_of_nonneg_left (by positivity) (by positivity) hden
    _ = _ := by
      rw [show (M : ℝ)/4+(2*M+2-Real.log r-Real.log p-(M : ℝ)/4) =
        (2*M+2)+(-Real.log r)+(-Real.log p) by ring,Real.exp_add,Real.exp_add]
      field_simp

private theorem first_reciprocal_upper {M r : ℕ} (hM : 1 ≤ M) :
    (∑ p ∈ firstPrimes M r, Real.exp (-Real.log p)) ≤ 24*Real.log 4 := by
  have hm : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hp (p : ℕ) (hp : p ∈ firstPrimes M r) :
      p.Prime ∧ Real.log p ≤ 2*(M : ℝ)+2 := by
    have hb := logPrimes_bounds hp
    refine ⟨hb.1,?_⟩
    have hupper := hb.2.2
    change Real.log p ≤ (M : ℝ)/4+(2*M+2-Real.log r-(M : ℝ)/2) at hupper
    linarith [Real.log_natCast_nonneg r]
  have hmass := ZetaRieszCoreExtensions.prime_log_mass_le (firstPrimes M r)
    (show 0 ≤ 2*(M : ℝ)+2 by positivity) hp
  have hlow : (((M : ℝ)+1)/8)*(∑ p ∈ firstPrimes M r, Real.exp (-Real.log p)) ≤
      ∑ p ∈ firstPrimes M r, Real.log p*Real.exp (-Real.log p) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p hp
    apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
    have h := (logPrimes_bounds hp).2.1
    change (M : ℝ)/4 < Real.log p at h
    linarith
  have hlog : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hmain := hlow.trans hmass
  nlinarith

/-- A uniform cost for the original atoms, with every allocation and
complex phase retained. This is not a signed prime-density approximation. -/
theorem atom_norm_le_marked_log (A : Finset ℕ) {N M n r p q : ℕ}
    (hM : 1 ≤ M) (hNM : N ≤ 2*M) {L : ℝ} (hL0 : 0 < L) (hL : (M : ℝ) ≤ L)
    (hr : r.Prime) (hp : p.Prime) (hq : q.Prime)
    (hrp : r ≠ p) (hrq : r ≠ q) (hpq : p ≠ q)
    (he : n = r*(p*q)) (hlo : 2*(M : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ 2*(M : ℝ)+2) (y : ℝ) :
    ‖residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ ≤
      4*Real.log r*Real.exp 2*radialEnvelope N M := by
  have hm : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hratio : Real.log n/L ≤ 4 := (div_le_iff₀ hL0).mpr (by linarith)
  have hc : ‖SquarefreeVaughanLogSource.coefficient L n‖ ≤ 4*Real.log r := by
    have hriesz : |VaughanLogAverage.riesz L n| ≤ Real.log r := by
      rw [he]
      exact abs_riesz_triple_le_marked_log L hr hp hq hrp hrq hpq
    unfold SquarefreeVaughanLogSource.coefficient
    split_ifs
    · rw [Complex.norm_real,Real.norm_eq_abs,abs_div,abs_mul,abs_neg,
        abs_of_nonneg (Real.log_natCast_nonneg n),abs_of_pos hL0]
      calc
        _ = (Real.log n/L)*|VaughanLogAverage.riesz L n| := by ring
        _ ≤ 4*Real.log r := mul_le_mul hratio hriesz (abs_nonneg _ ) (by norm_num)
    · simp only [norm_zero]
      positivity
  have hker : ‖zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ = amplitude N n := by
    rw [norm_zetaPrimeLogKernel]
    norm_num [zetaPrimeExpWeight,amplitude]
    ring
  rw [norm_mul,hker]
  exact (mul_le_mul ((ZetaRieszJointCountFloor.norm_residual_le A L N n).trans hc)
    (amplitude_le_radial (by omega) hNM hlo hhi)
    (by unfold amplitude; positivity) (by positivity)).trans_eq (by ring)

private theorem pair_count_upper {M r : ℕ} (hM : 1 ≤ M) :
    (∑ p ∈ firstPrimes M r, ((secondPrimes M r p).card : ℝ)) ≤
      192*(Real.log 4)^2*Real.exp (2*(M : ℝ)+2)*Real.exp (-Real.log r)/((M : ℝ)+1) := by
  have hs := Finset.sum_le_sum (s := firstPrimes M r) (fun p hp => second_card_upper hM hp)
  have he : (∑ p ∈ firstPrimes M r,
      8*Real.log 4*Real.exp (2*(M : ℝ)+2)*Real.exp (-Real.log r)*
        Real.exp (-Real.log p)/((M : ℝ)+1)) =
      (8*Real.log 4*Real.exp (2*(M : ℝ)+2)*Real.exp (-Real.log r)/((M : ℝ)+1))*
        (∑ p ∈ firstPrimes M r, Real.exp (-Real.log p)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    ring
  rw [he] at hs
  exact hs.trans ((mul_le_mul_of_nonneg_left (first_reciprocal_upper hM)
    (by positivity)).trans_eq (by ring))

/-- The complete small-prime triple debit in a slab has only a logarithmic
head cost. All actual primes below Q are summed, rather than bounding one
fixed small-prime fibre and losing its reciprocal weight. -/
theorem small_triples_norm_upper (S A : Finset ℕ) {N M Q : ℕ}
    (hM : 1 ≤ M) (hNM : N ≤ 2*M) (hQ : Real.log Q ≤ (M : ℝ)/8)
    {L : ℝ} (hL0 : 0 < L) (hL : (M : ℝ) ≤ L) (y : ℝ) :
    ‖∑ n ∈ smallTriples S M Q, residualCoefficient A L N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ ≤
      (768*(Real.log 4)^3*Real.exp 4)*(1+Real.log Q)*
        Real.exp (2*(M : ℝ))/((M : ℝ)+1)*radialEnvelope N M := by
  let f := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
  let V := smallTriples S M Q
  let D := (Nat.primesLE Q).sigma (fun r => (firstPrimes M r).sigma (secondPrimes M r))
  let product := fun x : Σ _r : ℕ, Σ _p : ℕ, ℕ => x.1*(x.2.1*x.2.2)
  let g := fun n => if n ∈ V then ‖f n‖ else 0
  let H := 4*Real.exp 2*radialEnvelope N M
  have hH : 0 ≤ H := by dsimp [H]; positivity [radialEnvelope_nonneg N M]
  have hsub : V ⊆ D.image product := by
    intro n hn
    obtain ⟨r,hr,p,hp,q,hq,he,_⟩ := factorization hM hQ hn
    exact Finset.mem_image.mpr ⟨⟨r,p,q⟩,Finset.mem_sigma.mpr
      ⟨hr,Finset.mem_sigma.mpr ⟨hp,hq⟩⟩,he.symm⟩
  have hpoint (x : Σ _r : ℕ, Σ _p : ℕ, ℕ) (hx : x ∈ D) :
      g (product x) ≤ H*Real.log x.1 := by
    obtain ⟨hr,hpq⟩ := Finset.mem_sigma.mp hx
    obtain ⟨hp,hq⟩ := Finset.mem_sigma.mp hpq
    have hr' := (Nat.mem_primesLE.mp hr).2
    have hp' := (logPrimes_bounds hp).1
    have hq' := (logPrimes_bounds hq).1
    dsimp only [g]
    split_ifs with hn
    · obtain ⟨_,hs,_,hlo,hhi,_⟩ := Finset.mem_filter.mp hn
      change Squarefree (x.1*(x.2.1*x.2.2)) at hs
      have hrnd := hr'.coprime_iff_not_dvd.mp (Nat.coprime_of_squarefree_mul hs)
      have hpnd := hp'.coprime_iff_not_dvd.mp (Nat.coprime_of_squarefree_mul hs.of_mul_right)
      have hrp : x.1 ≠ x.2.1 := by
        intro he
        exact hrnd (he ▸ dvd_mul_right _ _)
      have hrq : x.1 ≠ x.2.2 := by
        intro he
        exact hrnd (he ▸ dvd_mul_left _ _)
      have hpq : x.2.1 ≠ x.2.2 := by intro he; exact hpnd (he ▸ dvd_refl _)
      exact (atom_norm_le_marked_log A hM hNM hL0 hL hr' hp' hq' hrp hrq hpq
        rfl hlo hhi.le y).trans_eq (by dsimp [H]; ring)
    · positivity
  have hb : ‖∑ n ∈ V, f n‖ ≤ ∑ x ∈ D, H*Real.log x.1 := by
    calc
      _ ≤ ∑ n ∈ V, ‖f n‖ := norm_sum_le _ _
      _ = ∑ n ∈ V, g n := Finset.sum_congr rfl (fun n hn => by simp only [g,if_pos hn])
      _ ≤ ∑ n ∈ D.image product, g n :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (by intro n _ _; exact ite_nonneg (norm_nonneg _) le_rfl)
      _ ≤ ∑ x ∈ D, g (product x) :=
        Finset.sum_image_le_of_nonneg (by intro n _; exact ite_nonneg (norm_nonneg _) le_rfl)
      _ ≤ _ := Finset.sum_le_sum hpoint
  have he : (∑ x ∈ D, H*Real.log x.1) =
      ∑ r ∈ Nat.primesLE Q, H*Real.log r*(∑ p ∈ firstPrimes M r, ((secondPrimes M r p).card : ℝ)) := by
    simp only [D,Finset.sum_sigma,Finset.sum_const,nsmul_eq_mul]
    apply Finset.sum_congr rfl
    intro r _
    rw [Finset.card_sigma,Nat.cast_sum,Finset.sum_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    ring
  rw [he] at hb
  have hpair := Finset.sum_le_sum (s := Nat.primesLE Q) (fun r _ =>
    mul_le_mul_of_nonneg_left (pair_count_upper (r := r) hM)
      (mul_nonneg hH (Real.log_natCast_nonneg r)))
  have hmass := ZetaRieszCoreExtensions.prime_log_mass_le (Nat.primesLE Q)
    (Real.log_natCast_nonneg Q) (fun r hr => ⟨(Nat.mem_primesLE.mp hr).2,
      Real.log_le_log (by exact_mod_cast (Nat.mem_primesLE.mp hr).2.pos)
        (by exact_mod_cast (Nat.mem_primesLE.mp hr).1)⟩)
  have he' : (∑ r ∈ Nat.primesLE Q, H*Real.log r*
      (192*(Real.log 4)^2*Real.exp (2*(M : ℝ)+2)*Real.exp (-Real.log r)/((M : ℝ)+1))) =
      (H*192*(Real.log 4)^2*Real.exp (2*(M : ℝ)+2)/((M : ℝ)+1))*
        (∑ r ∈ Nat.primesLE Q, Real.log r*Real.exp (-Real.log r)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    ring
  rw [he'] at hpair
  refine (hb.trans hpair).trans ((mul_le_mul_of_nonneg_left hmass (by positivity)).trans_eq ?_)
  dsimp [H]
  rw [Real.exp_add]
  have he4 : Real.exp (2 : ℝ)*Real.exp 2 = Real.exp 4 := by rw [← Real.exp_add]; norm_num
  calc
    _ = (768*(Real.log 4)^3*(Real.exp 2*Real.exp 2))*(1+Real.log Q)*
        Real.exp (2*(M : ℝ))/((M : ℝ)+1)*radialEnvelope N M := by ring
    _ = _ := by rw [he4]

private theorem tendsto_small_prime_rate :
    Tendsto (fun N : ℕ => (1+2*Real.log N)/(N : ℝ)) atTop (𝓝 0) := by
  have h₀ := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 0 one_ne_zero).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have h₁ := ((Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul 2
  convert h₀.add h₁ using 1 <;> simp [add_div,mul_div_assoc]

/-- A polynomial small-prime threshold consumes an arbitrarily small
fraction of the positive supply's radial scale, uniformly over all slabs.
The conclusion is a relative cost estimate, not source-normalized decay. -/
theorem eventually_small_slabs_cost {b : ℝ} (hb : 0 < b) :
    ∀ᶠ N : ℕ in atTop, ∀ (M : ℕ) (S A : Finset ℕ) (L y : ℝ),
      N ≤ 2*M → 0 < L → (M : ℝ) ≤ L →
      ‖∑ n ∈ smallTriples S M (N^2), residualCoefficient A L N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ ≤
      b*(M : ℝ)*Real.exp (2*(M : ℝ))/((M : ℝ)+1)*radialEnvelope N M := by
  let B : ℝ := 768*(Real.log 4)^3*Real.exp 4
  have hB : 0 < B := by dsimp [B]; positivity
  filter_upwards [eventually_ge_atTop (2 : ℕ),
    tendsto_small_prime_rate.eventually_lt_const (show 0 < b/(2*B) by positivity),
    tendsto_small_prime_rate.eventually_lt_const (by norm_num : (0 : ℝ) < 1/16)]
    with N hN hcost hsmall M S A L y hNM hL0 hL
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hnm : (N : ℝ) ≤ 2*M := by exact_mod_cast hNM
  have hlog : Real.log (N^2 : ℕ) = 2*Real.log N := by rw [Nat.cast_pow,Real.log_pow]; norm_num
  have hQ : Real.log (N^2 : ℕ) ≤ (M : ℝ)/8 := by
    rw [hlog]
    have ht := (div_lt_iff₀ hn).mp hsmall
    linarith
  have hbudget : B*(1+Real.log (N^2 : ℕ)) ≤ b*M := by
    rw [hlog]
    have ht := (div_lt_iff₀ hn).mp hcost
    have ht' := mul_lt_mul_of_pos_left ht hB
    have he : B*(b/(2*B)*N) = b/2*N := by field_simp
    rw [he] at ht'
    nlinarith
  have hbound := small_triples_norm_upper S A (by omega : 1 ≤ M) hNM hQ hL0 hL y
  change ‖_‖ ≤ B*(1+Real.log (N^2 : ℕ))*_/_*_ at hbound
  apply hbound.trans
  have ht := mul_le_mul_of_nonneg_right hbudget
    (show 0 ≤ Real.exp (2*(M : ℝ))/((M : ℝ)+1)*radialEnvelope N M by
      positivity [radialEnvelope_nonneg N M])
  convert ht using 1 <;> ring

/-- The SAME signed four-prime supply pays both a balanced share band
and every small-prime triple. Half plus one quarter is spent, never two
independent copies of the supply. -/
theorem eventually_joint_slabs_spending {y : ℝ} (hy : 16 ≤ |y|) :
    ∃ η h : ℝ, 0 < η ∧ η ≤ 1/1000 ∧ 0 < h ∧ h ≤ 1/20 ∧
      ∀ᶠ N : ℕ in atTop, ∀ (M : ℕ) (S D A : Finset ℕ) (L : ℝ),
        N ≤ 2*M → 0 < L → (271/200 : ℝ)*M ≤ L → L ≤ (143/100 : ℝ)*M →
        ∃ v : ℝ, 0 ≤ v ∧ v ≤ 1/2 ∧
          let f := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
          0 < (∑ n ∈ supply M h v, f n).re ∧
            ‖∑ n ∈ slabTriples S M η, f n‖ ≤ (1/2 : ℝ)*(∑ n ∈ supply M h v, f n).re ∧
            ‖∑ n ∈ smallTriples D M (N^2), f n‖ ≤ (1/4 : ℝ)*(∑ n ∈ supply M h v, f n).re := by
  obtain ⟨h,hh,hhhi,hphase⟩ := exists_short_negative_window hy
  obtain ⟨c,hc,hsupply⟩ := eventually_supply_lower hh hhhi
  let B : ℝ := 27*(6*Real.log 4)^3*Real.exp 8
  have hB : 0 < B := by dsimp [B]; positivity
  let η := min (1/1000 : ℝ) (Real.sqrt (c/(2*B)))
  have hη : 0 < η := lt_min (by norm_num) (Real.sqrt_pos.mpr (by positivity))
  have hηu : η ≤ 1/1000 := min_le_left _ _
  have hηcost : B*η^2 ≤ c/2 := by
    have hs := pow_le_pow_left₀ hη.le (min_le_right (1/1000 : ℝ) (Real.sqrt (c/(2*B)))) 2
    rw [Real.sq_sqrt (by positivity)] at hs
    have ht := (le_div_iff₀ (by positivity : 0 < 2*B)).mp hs
    nlinarith
  refine ⟨η,h,hη,hηu,hh,hhhi,?_⟩
  filter_upwards [hsupply,eventually_small_slabs_cost (show 0 < c/4 by positivity),
    eventually_ge_atTop (40 : ℕ),
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (2/η)]
    with N hs hsmall hN hsize M S D A L hNM hL0 hL hLu
  have hM : 20 ≤ M := by omega
  have hηM : 1 ≤ η*M := by
    have ht := (div_le_iff₀ hη).mp hsize
    have hnr : (N : ℝ) ≤ 2*M := by exact_mod_cast hNM
    nlinarith
  obtain ⟨v,hv,hvhi,hcos⟩ := hphase (2*(M : ℝ))
  have hpos := hs M A v L y hNM hv hvhi hL0 hL hLu hcos
  have hLM : (M : ℝ) ≤ L := by nlinarith [Nat.cast_nonneg (α := ℝ) M]
  have hneg := slab_norm_upper S A hη hηu hM hηM hNM hL0 hLM y
  have hsm := hsmall M D A L y hNM hL0 hLM
  refine ⟨v,hv,hvhi,?_⟩
  dsimp only
  refine ⟨lt_of_lt_of_le (by positivity [radialEnvelope_pos N (show 0 < M by omega)]) hpos,?_,?_⟩
  · have hbudget := mul_le_mul_of_nonneg_right hηcost
      (show 0 ≤ (M : ℝ)*Real.exp (2*(M : ℝ))/((M : ℝ)+1)*radialEnvelope N M by
        positivity [radialEnvelope_nonneg N M])
    change ‖_‖ ≤ B*η^2*_*_/_*_ at hneg
    calc
      _ ≤ B*η^2*(M : ℝ)*Real.exp (2*(M : ℝ))/((M : ℝ)+1)*radialEnvelope N M := hneg
      _ ≤ (c/2)*((M : ℝ)*Real.exp (2*(M : ℝ))/((M : ℝ)+1)*radialEnvelope N M) := by
        calc
          _ = B*η^2*((M : ℝ)*Real.exp (2*(M : ℝ))/((M : ℝ)+1)*radialEnvelope N M) := by ring
          _ ≤ _ := hbudget
      _ = (1/2 : ℝ)*(c*(M : ℝ)*Real.exp (2*(M : ℝ))/((M : ℝ)+1)*radialEnvelope N M) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hpos (by norm_num)
  · calc
      _ ≤ (c/4)*(M : ℝ)*Real.exp (2*(M : ℝ))/((M : ℝ)+1)*radialEnvelope N M := hsm
      _ = (1/4 : ℝ)*(c*(M : ℝ)*Real.exp (2*(M : ℝ))/((M : ℝ)+1)*radialEnvelope N M) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hpos (by norm_num)

open ZetaRieszPrimeCountFrequency ZetaRieszParityPacket ZetaRieszMaskSupport

/-- All selected small-prime slabs, with disjoint radial endpoints. -/
def radialSmallTriples (S : Finset ℕ) (N : ℕ) : Finset ℕ :=
  (radialIndices N).biUnion (fun M => smallTriples S M (N^2))

/-- The entire three-prime head in the original support. -/
def smallHead (S : Finset ℕ) (N : ℕ) : Finset ℕ :=
  S.filter (fun n => Squarefree n ∧ n.primeFactors.card = 3 ∧
    ∃ r ∈ n.primeFactors, r ≤ N^2)

theorem smallTriples_disjoint (S : Finset ℕ) (Q : ℕ) :
    Pairwise (fun M M' : ℕ => Disjoint (smallTriples S M Q) (smallTriples S M' Q)) := by
  intro M M' hne
  apply Finset.disjoint_left.mpr
  intro n hn hn'
  have hb := (Finset.mem_filter.mp hn).2
  have hb' := (Finset.mem_filter.mp hn').2
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have hr : (M : ℝ)+1 ≤ M' := by exact_mod_cast hlt
    linarith [hb.2.2.2.1,hb'.2.2.1]
  · have hr : (M' : ℝ)+1 ≤ M := by exact_mod_cast hlt
    linarith [hb'.2.2.2.1,hb.2.2.1]

theorem small_union_spending {N : ℕ} {S : Finset ℕ} {f : ℕ → ℂ} {h : ℝ} {v : ℕ → ℝ}
    (hh : h ≤ 1/20) (hv : ∀ M ∈ radialIndices N, 0 ≤ v M ∧ v M ≤ 1/2)
    (hpay : ∀ M ∈ radialIndices N,
      ‖∑ n ∈ smallTriples S M (N^2), f n‖ ≤ (1/4 : ℝ)*(∑ n ∈ supply M h (v M), f n).re) :
    ‖∑ n ∈ radialSmallTriples S N, f n‖ ≤ (1/4 : ℝ)*(∑ n ∈ radialSupply N h v, f n).re := by
  have ht : (radialIndices N : Set ℕ).PairwiseDisjoint (fun M => smallTriples S M (N^2)) :=
    fun _ _ _ _ hne => smallTriples_disjoint S (N^2) hne
  rw [radialSmallTriples,Finset.sum_biUnion ht,radialSupply,Finset.sum_biUnion (supply_disjoint hh hv)]
  calc
    _ ≤ ∑ M ∈ radialIndices N, ‖∑ n ∈ smallTriples S M (N^2), f n‖ := norm_sum_le _ _
    _ ≤ ∑ M ∈ radialIndices N, (1/4 : ℝ)*(∑ n ∈ supply M h (v M), f n).re := Finset.sum_le_sum hpay
    _ = _ := by rw [← Finset.mul_sum,Complex.re_sum]

private theorem triple_supply_disjoint {N : ℕ} (D : Finset ℕ) {h : ℝ} {v : ℕ → ℝ}
    (hD : ∀ n ∈ D, n.primeFactors.card = 3)
    (hN : 2000 ≤ N) (hh : 0 < h) (hhhi : h ≤ 1/20)
    (hv : ∀ M ∈ radialIndices N, 0 ≤ v M ∧ v M ≤ 1/2) :
    Disjoint D (radialSupply N h v) := by
  apply Finset.disjoint_left.mpr
  intro n hn hn'
  have hthree := hD n hn
  obtain ⟨M,hM,hn'⟩ := Finset.mem_biUnion.mp hn'
  have hbounds := (Finset.mem_filter.mp hM).2
  have hNR : (2000 : ℝ) ≤ N := by exact_mod_cast hN
  have hw : h+v M ≤ (M : ℝ)/1000 := by linarith [(hv M hM).2]
  obtain ⟨ijk,hijk,hn'⟩ := Finset.mem_biUnion.mp hn'
  obtain ⟨hi,hjk⟩ := Finset.mem_product.mp hijk
  obtain ⟨hj,hk⟩ := Finset.mem_product.mp hjk
  obtain ⟨p,hp,hpn⟩ := Finset.mem_image.mp hn'
  have hfour := tuple_count hh hi hj hk (hv M hM).1 hw hp
  rw [hpn] at hfour
  omega

/-- Both triple populations are paid in one literal core inequality.
The small-prime selection explicitly excludes the already paid balanced
slabs; the positive parts and a quarter of the one actual supply remain. -/
theorem eventually_core_joint_floor {u y : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (hy : 16 ≤ |y|) :
    ∃ η h : ℝ, 0 < η ∧ η ≤ 1/1000 ∧ 0 < h ∧ h ≤ 1/20 ∧
      ∀ᶠ j : ℕ in atTop, ∃ v : ℕ → ℝ,
        (∀ M ∈ radialIndices (dyadicMomentOrder j), 0 ≤ v M ∧ v M ≤ 1/2) ∧
        let N := dyadicMomentOrder j
        let S := coreBand u N (dyadicPrimeCount j)
        let f := fun n => residualCoefficient (ZetaRieszAnnulusJoint.intermediatePrimes u N)
          (SquarefreeVaughanLogSource.length u N) N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
        let X := ∑ n ∈ radialTriples S N η, f n
        let Z := ∑ n ∈ radialSmallTriples (S\radialTriples S N η) N, f n
        let Y := ∑ n ∈ radialSupply N h v, f n
        let W := ∑ n ∈ S\(radialTriples S N η ∪ radialSmallTriples (S\radialTriples S N η) N ∪
          radialSupply N h v), f n
        0 < Y.re ∧
          u^(N+1)*(W.re+max X.re 0+max Z.re 0+Y.re/4) ≤
            ((u : ℂ)^(N+1)*coreResponse u y N (dyadicPrimeCount j)).re := by
  obtain ⟨η,h,hη,hηu,hh,hhhi,hpay⟩ := eventually_joint_slabs_spending hy
  refine ⟨η,h,hη,hηu,hh,hhhi,?_⟩
  filter_upwards [tendsto_dyadicMomentOrder.eventually hpay,
    tendsto_dyadicMomentOrder.eventually (eventually_length_on_slabs hu hU),
    eventually_radial_supply_in_core hu hU hh hhhi,
    tendsto_dyadicMomentOrder.eventually (eventually_ge_atTop (2000 : ℕ))]
    with j hpay hL hsub hN
  let N := dyadicMomentOrder j
  let L := SquarefreeVaughanLogSource.length u N
  let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
  let S := coreBand u N (dyadicPrimeCount j)
  let Xs := radialTriples S N η
  let Zs := radialSmallTriples (S\Xs) N
  let f := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
  have hex : ∀ M : ℕ, ∃ v : ℝ, M ∈ radialIndices N →
      0 ≤ v ∧ v ≤ 1/2 ∧ 0 < (∑ n ∈ supply M h v, f n).re ∧
      ‖∑ n ∈ slabTriples S M η, f n‖ ≤ (1/2 : ℝ)*(∑ n ∈ supply M h v, f n).re ∧
      ‖∑ n ∈ smallTriples (S\Xs) M (N^2), f n‖ ≤ (1/4 : ℝ)*(∑ n ∈ supply M h v, f n).re := by
    intro M
    by_cases hM : M ∈ radialIndices N
    · obtain ⟨v,hv,hvhi,hY,hX,hZ⟩ := hpay M S (S\Xs) A L (hL M hM).1
        (SquarefreeVaughanLogSource.length_pos _ _) (hL M hM).2.1 (hL M hM).2.2
      exact ⟨v,fun _ => ⟨hv,hvhi,hY,hX,hZ⟩⟩
    · exact ⟨0,fun h => False.elim (hM h)⟩
  choose v hv using hex
  have hvbounds : ∀ M ∈ radialIndices N, 0 ≤ v M ∧ v M ≤ 1/2 :=
    fun M hM => ⟨(hv M hM).1,(hv M hM).2.1⟩
  have hY : 0 < (∑ n ∈ radialSupply N h v, f n).re := by
    rw [radialSupply,Finset.sum_biUnion (supply_disjoint hhhi hvbounds),Complex.re_sum]
    apply Finset.sum_pos'
    · intro M hM
      exact (hv M hM).2.2.1.le
    · exact ⟨N,self_mem_radialIndices (by omega),(hv N (self_mem_radialIndices (by omega))).2.2.1⟩
  have hXpay := union_spending hhhi hvbounds (fun M hM => (hv M hM).2.2.2.1)
  have hZpay := small_union_spending hhhi hvbounds (fun M hM => (hv M hM).2.2.2.2)
  have hXsub : Xs ⊆ S := by
    intro n hn
    obtain ⟨M,_,hn⟩ := Finset.mem_biUnion.mp hn
    exact (Finset.mem_filter.mp hn).1
  have hZsub : Zs ⊆ S\Xs := by
    intro n hn
    obtain ⟨M,_,hn⟩ := Finset.mem_biUnion.mp hn
    exact (Finset.mem_filter.mp hn).1
  have hXZ : Disjoint Xs Zs := Finset.disjoint_left.mpr (fun _ hx hz => (Finset.mem_sdiff.mp (hZsub hz)).2 hx)
  have hZ3 : ∀ n ∈ Zs, n.primeFactors.card = 3 := by
    intro n hn
    obtain ⟨M,_,hn⟩ := Finset.mem_biUnion.mp hn
    exact (Finset.mem_filter.mp hn).2.2.1
  have hXY := unions_disjoint S η hN hh hhhi hvbounds
  have hZY := triple_supply_disjoint Zs hZ3 hN hh hhhi hvbounds
  have hsuball : Xs ∪ Zs ∪ radialSupply N h v ⊆ S := by
    apply Finset.union_subset
    · exact Finset.union_subset hXsub (fun _ hn => (Finset.mem_sdiff.mp (hZsub hn)).1)
    · intro n hn
      obtain ⟨M,hM,hn⟩ := Finset.mem_biUnion.mp hn
      exact hsub M hM (v M) (hvbounds M hM).1 (hvbounds M hM).2 hn
  have hledger := Finset.sum_sdiff (f := f) hsuball
  rw [Finset.sum_union (Finset.disjoint_union_left.mpr ⟨hXY,hZY⟩),Finset.sum_union hXZ] at hledger
  have hre := congrArg Complex.re hledger
  simp only [Complex.add_re] at hre
  have hXneg := (abs_le.mp ((Complex.abs_re_le_norm _).trans hXpay)).1
  have hZneg := (abs_le.mp ((Complex.abs_re_le_norm _).trans hZpay)).1
  have hmain : (∑ n ∈ S\(Xs ∪ Zs ∪ radialSupply N h v), f n).re+
      max (∑ n ∈ Xs, f n).re 0+max (∑ n ∈ Zs, f n).re 0+
      (∑ n ∈ radialSupply N h v, f n).re/4 ≤ (∑ n ∈ S, f n).re := by
    change -(1/2*(∑ n ∈ radialSupply N h v, f n).re) ≤ (∑ n ∈ Xs, f n).re at hXneg
    change -(1/4*(∑ n ∈ radialSupply N h v, f n).re) ≤ (∑ n ∈ Zs, f n).re at hZneg
    rcases le_total (∑ n ∈ Xs, f n).re 0 with hx | hx <;>
      rcases le_total (∑ n ∈ Zs, f n).re 0 with hz | hz
    all_goals simp only [max_eq_left hx,max_eq_right hx,max_eq_left hz,max_eq_right hz]
    all_goals linarith
  refine ⟨v,hvbounds,hY,?_⟩
  have ht := mul_le_mul_of_nonneg_left hmain (pow_nonneg (by linarith : 0 ≤ u) (N+1))
  change _ ≤ ((u : ℂ)^(N+1)*(∑ n ∈ S, f n)).re
  rw [← Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  exact ht

private theorem core_prime_log_le_length {u : ℝ} {N K n p : ℕ}
    (hn : n ∈ coreBand u N K) (hp : p ∈ n.primeFactors) :
    Real.log p ≤ SquarefreeVaughanLogSource.length u N := by
  have hnon := (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).1
  have hret := (Finset.mem_sdiff.mp hnon).1
  have horig := (Finset.mem_sdiff.mp hret).1
  have hfew := (Finset.mem_filter.mp horig).1
  have hunpaired := (Finset.mem_filter.mp hfew).1
  have hphys := (Finset.mem_filter.mp (Finset.mem_sdiff.mp (Finset.mem_filter.mp hunpaired).1).1).2
  have hpx := hphys p hp
  have ht := Real.log_le_log (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos)
    (show (p : ℝ) ≤ ((ZetaVaughanCutoffBudget.linearDampedCutoff u N+2)^2 : ℕ) by exact_mod_cast hpx.le)
  simpa only [SquarefreeVaughanLogSource.length,Nat.cast_pow,Nat.cast_add,Nat.cast_ofNat] using ht

/-- Every small-prime triple in the interior radial window enters the
paid union. There is no restriction on the ratio of its two large primes. -/
theorem smallHead_mem_radialSmallTriples {S : Finset ℕ} {N n : ℕ} {L : ℝ}
    (hN : 4000 ≤ N)
    (hL : ∀ M ∈ radialIndices N, L ≤ (143/100 : ℝ)*M)
    (hphys : ∀ p ∈ n.primeFactors, Real.log p ≤ L)
    (hn : n ∈ smallHead S N)
    (hlo : (244/125 : ℝ)*N < Real.log n) (hhi : Real.log n ≤ (2029/1000 : ℝ)*N) :
    n ∈ radialSmallTriples S N := by
  obtain ⟨hnS,hs,hc,hsmall⟩ := Finset.mem_filter.mp hn
  let M := ⌊Real.log n/2⌋₊
  have hNR : (4000 : ℝ) ≤ N := by exact_mod_cast hN
  have hfloor : (M : ℝ) ≤ Real.log n/2 := Nat.floor_le (by positivity [Real.log_natCast_nonneg n])
  have hceil : Real.log n/2 < (M : ℝ)+1 := Nat.lt_floor_add_one _
  have hMR : (M : ℝ) ≤ 2*N := by linarith
  have hM : M ∈ radialIndices N := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr ?_,?_⟩
    · have h : M ≤ 2*N := by exact_mod_cast hMR
      omega
    constructor <;> linarith
  apply Finset.mem_biUnion.mpr
  refine ⟨M,hM,Finset.mem_filter.mpr ⟨hnS,hs,hc,by linarith,by linarith,?_,hsmall⟩⟩
  intro p hp
  have h := (hphys p hp).trans (hL M hM)
  nlinarith [Nat.cast_nonneg (α := ℝ) M]

open LogarithmicDeviation ZetaArithmeticDeviationBounds

/-- The two paid populations can miss only the already controlled radial
edges. This one allowance covers their union, including overlaps. -/
theorem exists_joint_missed_bound :
    ∃ r C : ℝ, 0 ≤ r ∧ r < 1 ∧ 0 ≤ C ∧
      ∀ (N : ℕ) (S A : Finset ℕ) (η y u : ℝ),
        4000 ≤ N → 0 < η → 4 ≤ η*N → 0 ≤ u → u ≤ ZetaRieszWideOwnerAudit.radiusCeiling →
        (∀ M ∈ radialIndices N, SquarefreeVaughanLogSource.length u N ≤ (143/100 : ℝ)*M) →
        (∀ n ∈ S, ∀ p ∈ n.primeFactors, Real.log p ≤ SquarefreeVaughanLogSource.length u N) →
        let X := radialTriples S N η
        let Z := radialSmallTriples (S\X) N
        ‖(u : ℂ)^(N+1)*∑ n ∈ (balancedTriples S N η ∪ smallHead S N)\(X ∪ Z),
          residualCoefficient A (SquarefreeVaughanLogSource.length u N) N n*
            zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ ≤ r^N*C := by
  obtain ⟨r,C,hr,hr1,hC,h⟩ := exists_uniform_deviation_bound (1 : Polynomial ℂ)
    (by norm_num [ZetaRieszWideOwnerAudit.radiusCeiling])
    (by norm_num : (0 : ℝ) < 244/125) (by norm_num) (by norm_num : (2 : ℝ) < 2029/1000)
    radial_edge_costs.1 radial_edge_costs.2
  refine ⟨r,C,hr,hr1,hC,?_⟩
  intro N S A η y u hN hη hηN hu hU hL hphys
  let X := radialTriples S N η
  let Z := radialSmallTriples (S\X) N
  let D := (balancedTriples S N η ∪ smallHead S N)\(X ∪ Z)
  have he : deviationBand D (244/125) (2029/1000) N = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro n hn
    obtain ⟨hnD,hlo,hhi⟩ := Finset.mem_filter.mp hn
    obtain ⟨hnB,hnXZ⟩ := Finset.mem_sdiff.mp hnD
    rcases Finset.mem_union.mp hnB with hbal | hsmall
    · exact hnXZ (Finset.mem_union_left _ (balanced_mem_radialTriples hN hη hηN hbal hlo hhi))
    · obtain ⟨hnS,hs,hc,hhead⟩ := Finset.mem_filter.mp hsmall
      have hnX : n ∉ X := fun h => hnXZ (Finset.mem_union_left _ h)
      have hin : n ∈ smallHead (S\X) N :=
        Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hnS,hnX⟩,hs,hc,hhead⟩
      exact hnXZ (Finset.mem_union_right _ (smallHead_mem_radialSmallTriples hN hL
        (hphys n hnS) hin hlo hhi))
  have hb := h N D (residualCoefficient A (SquarefreeVaughanLogSource.length u N) N)
    (fun n _ => norm_residualCoefficient_le A (SquarefreeVaughanLogSource.length_pos u N) N n)
    y u hu hU
  simpa only [he,Finset.sum_empty,sub_zero,zetaPrimeLogKernel,
    SquarefreeEulerQuadratic.primeFilterKernel_one] using hb

/-- The ENTIRE original small-prime triple head and a fixed balanced
share band are paid together, up to a geometric edge error. Only one
positive four-prime supply is used; the signed complement, both positive
triple credits and a quarter of that supply remain in the joint floor. -/
theorem eventually_core_small_balanced_floor {u y : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (hy : 16 ≤ |y|) :
    ∃ η h r C : ℝ, 0 < η ∧ η ≤ 1/1000 ∧ 0 < h ∧ h ≤ 1/20 ∧
      0 ≤ r ∧ r < 1 ∧ 0 ≤ C ∧
      ∀ᶠ j : ℕ in atTop, ∃ v : ℕ → ℝ,
        (∀ M ∈ radialIndices (dyadicMomentOrder j), 0 ≤ v M ∧ v M ≤ 1/2) ∧
        let N := dyadicMomentOrder j
        let S := coreBand u N (dyadicPrimeCount j)
        let f := fun n => residualCoefficient (ZetaRieszAnnulusJoint.intermediatePrimes u N)
          (SquarefreeVaughanLogSource.length u N) N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
        let Xs := radialTriples S N η
        let Zs := radialSmallTriples (S\Xs) N
        let X := ∑ n ∈ Xs, f n
        let Z := ∑ n ∈ Zs, f n
        let Y := ∑ n ∈ radialSupply N h v, f n
        let W := ∑ n ∈ S\(Xs ∪ Zs ∪ radialSupply N h v ∪ balancedTriples S N η ∪ smallHead S N), f n
        0 < Y.re ∧
          u^(N+1)*(W.re+max X.re 0+max Z.re 0+Y.re/4)-r^N*C ≤
            ((u : ℂ)^(N+1)*coreResponse u y N (dyadicPrimeCount j)).re := by
  obtain ⟨η,h,hη,hηu,hh,hhhi,hspend⟩ := eventually_core_joint_floor hu hU hy
  obtain ⟨r,C,hr,hr1,hC,hmissed⟩ := exists_joint_missed_bound
  refine ⟨η,h,r,C,hη,hηu,hh,hhhi,hr,hr1,hC,?_⟩
  have hord : Tendsto (fun j => (dyadicMomentOrder j : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp tendsto_dyadicMomentOrder
  filter_upwards [hspend,tendsto_dyadicMomentOrder.eventually (eventually_ge_atTop (4000 : ℕ)),
    hord.eventually_ge_atTop (4/η),
    tendsto_dyadicMomentOrder.eventually (eventually_length_on_slabs hu hU)] with j hj hN hsize hL
  obtain ⟨v,hvb,hY,hfloor⟩ := hj
  let N := dyadicMomentOrder j
  let L := SquarefreeVaughanLogSource.length u N
  let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
  let S := coreBand u N (dyadicPrimeCount j)
  let f := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
  let Xs := radialTriples S N η
  let Zs := radialSmallTriples (S\Xs) N
  let B := balancedTriples S N η ∪ smallHead S N
  let D := B\(Xs ∪ Zs)
  have hηN : 4 ≤ η*N := by
    have ht := (div_le_iff₀ hη).mp hsize
    dsimp [N]
    nlinarith
  have hnorm := hmissed N S A η y u hN hη hηN (by linarith) hU
    (fun M hM => (hL M hM).2.2) (fun _ hn _ hp => core_prime_log_le_length hn hp)
  change ‖(u : ℂ)^(N+1)*∑ n ∈ D, f n‖ ≤ r^N*C at hnorm
  have hreal : -(r^N*C) ≤ u^(N+1)*(∑ n ∈ D, f n).re := by
    have ht := (abs_le.mp ((Complex.abs_re_le_norm _).trans hnorm)).1
    simpa only [← Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,
      Complex.ofReal_im,zero_mul,sub_zero] using ht
  have hB3 : ∀ n ∈ B, n.primeFactors.card = 3 := by
    intro n hn
    rcases Finset.mem_union.mp hn with hn | hn <;> exact (Finset.mem_filter.mp hn).2.2.1
  have hBY := triple_supply_disjoint B hB3 (by omega : 2000 ≤ N) hh hhhi hvb
  have hDsub : D ⊆ S\(Xs ∪ Zs ∪ radialSupply N h v) := by
    intro n hn
    obtain ⟨hnB,hnXZ⟩ := Finset.mem_sdiff.mp hn
    have hnS : n ∈ S := by
      rcases Finset.mem_union.mp hnB with hn | hn <;> exact (Finset.mem_filter.mp hn).1
    apply Finset.mem_sdiff.mpr
    refine ⟨hnS,?_⟩
    intro hn'
    rcases Finset.mem_union.mp hn' with hn' | hn'
    · exact hnXZ hn'
    · exact Finset.disjoint_left.mp hBY hnB hn'
  have hset : (S\(Xs ∪ Zs ∪ radialSupply N h v))\D =
      S\(Xs ∪ Zs ∪ radialSupply N h v ∪ balancedTriples S N η ∪ smallHead S N) := by
    ext n
    simp only [D,B,Finset.mem_sdiff,Finset.mem_union]
    constructor
    · rintro ⟨⟨hn,hpaid⟩,hnot⟩
      refine ⟨hn,?_⟩
      rintro ((hpaid' | hbal) | hsmall)
      · exact hpaid hpaid'
      · exact hnot ⟨Or.inl hbal,fun hxz => hpaid (Or.inl hxz)⟩
      · exact hnot ⟨Or.inr hsmall,fun hxz => hpaid (Or.inl hxz)⟩
    · rintro ⟨hn,hall⟩
      refine ⟨⟨hn,fun hpaid => hall (Or.inl (Or.inl hpaid))⟩,?_⟩
      rintro ⟨hbal | hsmall,_⟩
      · exact hall (Or.inl (Or.inr hbal))
      · exact hall (Or.inr hsmall)
  have hsum := Finset.sum_sdiff (f := f) hDsub
  rw [hset] at hsum
  have hre := congrArg Complex.re hsum
  rw [Complex.add_re] at hre
  refine ⟨v,hvb,hY,?_⟩
  change u^(N+1)*((∑ n ∈ S\(Xs ∪ Zs ∪ radialSupply N h v ∪ balancedTriples S N η ∪ smallHead S N), f n).re+
    max (∑ n ∈ Xs, f n).re 0+max (∑ n ∈ Zs, f n).re 0+
    (∑ n ∈ radialSupply N h v, f n).re/4)-r^N*C ≤ _
  change u^(N+1)*((∑ n ∈ S\(Xs ∪ Zs ∪ radialSupply N h v), f n).re+
    max (∑ n ∈ Xs, f n).re 0+max (∑ n ∈ Zs, f n).re 0+
    (∑ n ∈ radialSupply N h v, f n).re/4) ≤ _ at hfloor
  rw [← hre] at hfloor
  nlinarith

/-- The exact four- and five-prime debit applies only to the untouched
complement after BOTH triple populations have been paid. All other
prime-count classes stay signed, with the original literal weights. -/
theorem eventually_compensated_core_floor {u y : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (hy : 16 ≤ |y|) :
    ∃ η h r C : ℝ, 0 < η ∧ η ≤ 1/1000 ∧ 0 < h ∧ h ≤ 1/20 ∧
      0 ≤ r ∧ r < 1 ∧ 0 ≤ C ∧
      ∀ᶠ j : ℕ in atTop, ∃ v : ℕ → ℝ,
        (∀ M ∈ radialIndices (dyadicMomentOrder j), 0 ≤ v M ∧ v M ≤ 1/2) ∧
        let N := dyadicMomentOrder j
        let L := SquarefreeVaughanLogSource.length u N
        let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
        let S := coreBand u N (dyadicPrimeCount j)
        let f := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
        let Xs := radialTriples S N η
        let Zs := radialSmallTriples (S\Xs) N
        let X := ∑ n ∈ Xs, f n
        let Z := ∑ n ∈ Zs, f n
        let Y := ∑ n ∈ radialSupply N h v, f n
        let W := S\(Xs ∪ Zs ∪ radialSupply N h v ∪ balancedTriples S N η ∪ smallHead S N)
        let B := ∑ n ∈ W, if n.primeFactors.card = 4 then
          max (f n).re 0-weight A N n*ZetaRieszFourPrimeReserve.fourDebit L y n
          else if n.primeFactors.card = 5 ∧ Real.cos (y*Real.log n) ≤ 0 then
            max (f n).re 0-weight A N n*ZetaRieszFivePrimeReserve.positiveAllowance L n*(-Real.cos (y*Real.log n))
          else (f n).re
        0 < Y.re ∧
          u^(N+1)*(B+max X.re 0+max Z.re 0+Y.re/4)-r^N*C ≤
            ((u : ℂ)^(N+1)*coreResponse u y N (dyadicPrimeCount j)).re := by
  obtain ⟨η,h,r,C,hη,hηu,hh,hhu,hr,hr1,hC,hfloor⟩ := eventually_core_small_balanced_floor hu hU hy
  refine ⟨η,h,r,C,hη,hηu,hh,hhu,hr,hr1,hC,?_⟩
  have hsource := hU.trans_lt ZetaRieszWideOwnerAudit.radius_lt_source
  have hL := ZetaRieszLowerDegreeBounds.eventually_length_ge_exponent
    (by linarith : 0 < u) (by norm_num : (0 : ℝ) ≤ 137/200)
    (hsource.trans (Real.exp_lt_exp.mpr (by norm_num : -(11/16 : ℝ) < -(137/200 : ℝ))))
  filter_upwards [hfloor,tendsto_dyadicMomentOrder.eventually hL,
    tendsto_dyadicMomentOrder.eventually (eventually_ge_atTop (2 : ℕ))] with j hj hlow hN
  obtain ⟨v,hv,hY,hfloor⟩ := hj
  let N := dyadicMomentOrder j
  let L := SquarefreeVaughanLogSource.length u N
  let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
  let S := coreBand u N (dyadicPrimeCount j)
  let Xs := radialTriples S N η
  let Zs := radialSmallTriples (S\Xs) N
  let W := S\(Xs ∪ Zs ∪ radialSupply N h v ∪ balancedTriples S N η ∪ smallHead S N)
  have hupp : L ≤ (7/5 : ℝ)*N := by
    have hl := ZetaRieszHeadOrders.length_le_two_log_two hu.le hN
    dsimp [L,N]
    nlinarith [Real.log_two_lt_d9,Nat.cast_nonneg (α := ℝ) (dyadicMomentOrder j)]
  have hwindow (n : ℕ) (hn : n ∈ W)
      (_hc : n.primeFactors.card = 4 ∨ n.primeFactors.card = 5) :
      L ≤ Real.log n ∧ 2*Real.log n ≤ 3*L ∧ 4*L ≤ 3*Real.log n := by
    have hnS : n ∈ S := (Finset.mem_sdiff.mp hn).1
    have hw := (Finset.mem_filter.mp hnS).2
    change 2*(137/200 : ℝ)*N ≤ L at hlow
    constructor
    · nlinarith [hw.1,hw.2,Nat.cast_nonneg (α := ℝ) N]
    constructor <;> nlinarith [hw.1,hw.2,Nat.cast_nonneg (α := ℝ) N]
  have hb := ZetaRieszFivePrimeReserve.re_sum_ge_four_five_credit W A N
    (SquarefreeVaughanLogSource.length_pos u N) y hwindow
  refine ⟨v,hv,hY,?_⟩
  apply le_trans _ hfloor
  apply sub_le_sub_right
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg (by linarith : 0 ≤ u) (N+1))
  exact add_le_add (add_le_add (add_le_add hb le_rfl) le_rfl) le_rfl

end
end RiemannGaussian.ZetaRieszSmallPrimeCompensation
