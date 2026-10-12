/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ArithmeticOperatorKummerPolynomialAudit
import RiemannGaussian.ArithmeticOperatorTwistedBulkAudit
import RiemannGaussian.ZetaRieszPrimeCompletionPhase

/-!
# Different Kummer rows at one prime conserve a common-divisor source

For any fixed finite family of literal binomial rows, the product of their
prime valuations equals the indicator that the prime divides their common
GCD, except for an explicitly bounded square-root/polylogarithmic correction.
Every carry order and the complete moving bounded phase are retained. The
GCD-weighted prime sum is UNPAID. This is not a distinct-prime-column estimate.

Unrestricted row selection already contains the entire ordinary-prime moment:
choose(q,1)=q gives an exact prime selector. Its exposed source is the old
nonzero source, not a new arithmetic constraint. Twisted selector diagonals
remain negative beyond every head at each fixed nonzero height.
-/

namespace RiemannGaussian.ArithmeticOperatorKummerGcdAudit
noncomputable section
open ArithmeticOperatorKummerPolynomialAudit Filter
open scoped BigOperators Classical Topology

variable {ι : Type*}

/-- All different binomial rows are kept before multiplying at one prime. -/
def valuationProduct (S : Finset ι) (a b : ι → ℕ) (p : ℕ) : ℕ :=
  ∏ i ∈ S, valuation p (a i) (b i)

/-- The actual integer common divisor; no prime density replaces it. -/
def commonDivisor (S : Finset ι) (a b : ι → ℕ) : ℕ :=
  S.gcd (fun i => (a i+b i).choose (b i))

/-- The surviving Boolean row product, including the empty-family convention. -/
def commonPrime (S : Finset ι) (a b : ι → ℕ) (p : ℕ) : ℕ :=
  if p ∣ commonDivisor S a b then 1 else 0

theorem commonPrime_le_product {p : ℕ} (hp : p.Prime)
    (S : Finset ι) (a b : ι → ℕ) :
    commonPrime S a b p ≤ valuationProduct S a b p := by
  let : Fact p.Prime := ⟨hp⟩
  unfold commonPrime valuationProduct
  split_ifs with hg
  · apply Finset.one_le_prod₀
    intro i hi
    apply one_le_padicValNat_of_dvd
    · exact (Nat.choose_pos (by omega : b i ≤ a i+b i)).ne'
    · exact Finset.dvd_gcd_iff.mp hg i hi
  · exact Nat.zero_le _

theorem valuationProduct_le {p J : ℕ} (hp : p.Prime)
    (S : Finset ι) (a b : ι → ℕ) (hab : ∀ i ∈ S, a i+b i≤2^(2*J)) :
    valuationProduct S a b p ≤ (2*J)^S.card := by
  unfold valuationProduct
  calc
    _ ≤ ∏ _i ∈ S, 2*J := Finset.prod_le_prod₀ (fun _i _hi => Nat.zero_le _)
      (fun i hi => valuation_le_orders hp (hab i hi))
    _ = _ := by simp

/-- Large-prime valuations are binary on every row, so their joined
product is EXACTLY common divisibility, not a statistical approximation. -/
theorem valuationProduct_large_prime {p J : ℕ} (hp : p.Prime)
    (S : Finset ι) (a b : ι → ℕ) (hab : ∀ i ∈ S, a i+b i≤2^(2*J))
    (hlarge : 2^J<p) : valuationProduct S a b p = commonPrime S a b p := by
  by_cases hg : p ∣ commonDivisor S a b
  · have he (i : ι) (hi : i ∈ S) : valuation p (a i) (b i)=1 := by
      have hlow : 1 ≤ valuation p (a i) (b i) := by
        let : Fact p.Prime := ⟨hp⟩
        apply one_le_padicValNat_of_dvd
        · exact (Nat.choose_pos (by omega : b i≤a i+b i)).ne'
        · exact Finset.dvd_gcd_iff.mp hg i hi
      have hhigh := valuation_large_prime_le_one hp (hab i hi) hlarge
      omega
    simp only [commonPrime, hg, ite_true, valuationProduct]
    exact Finset.prod_eq_one he
  · have hn : ∃ i ∈ S, ¬p ∣ (a i+b i).choose (b i) := by
      by_contra hh
      push Not at hh
      exact hg (Finset.dvd_gcd_iff.mpr hh)
    obtain ⟨i,hi,hn⟩ := hn
    have hz : valuation p (a i) (b i)=0 :=
      padicValNat.eq_zero_of_not_dvd hn
    simp only [commonPrime, hg, ite_false, valuationProduct]
    exact Finset.prod_eq_zero hi hz

/-- The actual higher-order increment is nonnegative. -/
def excess (S : Finset ι) (a b : ι → ℕ) (p : ℕ) : ℕ :=
  valuationProduct S a b p-commonPrime S a b p

theorem valuationProduct_eq_common_add_excess {p : ℕ} (hp : p.Prime)
    (S : Finset ι) (a b : ι → ℕ) :
    valuationProduct S a b p=commonPrime S a b p+excess S a b p := by
  have hh := commonPrime_le_product hp S a b
  unfold excess
  omega

theorem excess_large_prime_zero {p J : ℕ} (hp : p.Prime)
    (S : Finset ι) (a b : ι → ℕ) (hab : ∀ i ∈ S, a i+b i≤2^(2*J))
    (hlarge : 2^J<p) : excess S a b p=0 := by
  simp only [excess, valuationProduct_large_prime hp S a b hab hlarge, Nat.sub_self]

/-- Full finite row product, with arbitrary correlated phase/cutoff code. -/
def productPacket (P : Finset ℕ) (S : Finset ι) (a b : ι → ℕ)
    (phase : ℕ → ℂ) : ℂ :=
  ∑ p ∈ P, (Real.log p : ℂ)*phase p*(valuationProduct S a b p : ℂ)

/-- This common-divisor weighted prime sum is retained, not paid. -/
def commonPacket (P : Finset ℕ) (S : Finset ι) (a b : ι → ℕ)
    (phase : ℕ → ℂ) : ℂ :=
  ∑ p ∈ P, (Real.log p : ℂ)*phase p*(commonPrime S a b p : ℂ)

/-- Only the nonlinear excess; the full signed common-divisor term stays. -/
def correction (P : Finset ℕ) (S : Finset ι) (a b : ι → ℕ)
    (phase : ℕ → ℂ) : ℂ :=
  ∑ p ∈ P, (Real.log p : ℂ)*phase p*(excess S a b p : ℂ)

theorem productPacket_eq_common_add_correction (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (S : Finset ι) (a b : ι → ℕ) (phase : ℕ → ℂ) :
    productPacket P S a b phase=commonPacket P S a b phase+correction P S a b phase := by
  unfold productPacket commonPacket correction
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  have he : (valuationProduct S a b p : ℂ)=
      (commonPrime S a b p : ℂ)+(excess S a b p : ℂ) := by
    exact_mod_cast valuationProduct_eq_common_add_excess (hP p hp) S a b
  rw [he]
  ring

theorem correction_eq_small {J : ℕ} (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (S : Finset ι) (a b : ι → ℕ)
    (hab : ∀ i ∈ S, a i+b i≤2^(2*J)) (phase : ℕ → ℂ) :
    correction P S a b phase=correction (P.filter (fun p => p≤2^J)) S a b phase := by
  unfold correction
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro p hp hpnot
  have hlarge : 2^J<p := by
    by_contra hh
    exact hpnot (Finset.mem_filter.mpr ⟨hp,by omega⟩)
  rw [excess_large_prime_zero (hP p hp) S a b hab hlarge,Nat.cast_zero,mul_zero]

/-- The entire higher-power interaction is square-root/polylogarithmic,
uniformly in moving row geometry, prime masks and unit-bounded phases. -/
theorem norm_correction_le {J : ℕ} (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (S : Finset ι) (a b : ι → ℕ)
    (hab : ∀ i ∈ S, a i+b i≤2^(2*J)) (phase : ℕ → ℂ)
    (hphase : ∀ p ∈ P, ‖phase p‖≤1) :
    ‖correction P S a b phase‖≤
      (2 : ℝ)^J*((2*J : ℕ) : ℝ)^(S.card+1)*Real.log 2 := by
  rw [correction_eq_small P hP S a b hab]
  let Q := P.filter (fun p => p≤2^J)
  have hcard : (Q.card : ℝ)≤(2 : ℝ)^J := by
    have hs : Q ⊆ Finset.Icc 1 (2^J) := by
      intro p hp
      obtain ⟨hp,hpb⟩ := Finset.mem_filter.mp hp
      exact Finset.mem_Icc.mpr ⟨(hP p hp).pos,hpb⟩
    exact_mod_cast (by simpa using Finset.card_le_card hs : Q.card≤2^J)
  have hterm (p : ℕ) (hp : p ∈ Q) :
      ‖(Real.log p : ℂ)*phase p*(excess S a b p : ℂ)‖≤
        ((2*J : ℕ) : ℝ)^(S.card+1)*Real.log 2 := by
    have hpP := (Finset.mem_filter.mp hp).1
    have hpS := (Finset.mem_filter.mp hp).2
    have hlog : ‖(Real.log p : ℂ)‖≤((2*J : ℕ) : ℝ)*Real.log 2 := by
      rw [Complex.norm_real,Real.norm_of_nonneg (Real.log_natCast_nonneg p)]
      have hpX : p≤2^(2*J) := hpS.trans (by
        apply Nat.pow_le_pow_right (by omega : 0<(2 : ℕ)); omega)
      have hh := Real.log_le_log (by exact_mod_cast (hP p hpP).pos : (0 : ℝ)<p)
        (by exact_mod_cast hpX : (p : ℝ)≤(2 : ℝ)^(2*J))
      simpa only [Real.log_pow] using hh
    have hd : ‖(excess S a b p : ℂ)‖≤((2*J : ℕ) : ℝ)^S.card := by
      rw [Complex.norm_natCast]
      exact_mod_cast (Nat.sub_le (valuationProduct S a b p) (commonPrime S a b p)).trans
        (valuationProduct_le (hP p hpP) S a b hab)
    rw [norm_mul,norm_mul]
    calc
      _ ≤ (((2*J : ℕ) : ℝ)*Real.log 2)*1*((2*J : ℕ) : ℝ)^S.card :=
        mul_le_mul (mul_le_mul hlog (hphase p hpP) (norm_nonneg _) (by positivity))
          hd (norm_nonneg _) (by positivity)
      _ = _ := by rw [pow_succ]; ring
  unfold correction
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _p ∈ Q, ((2*J : ℕ) : ℝ)^(S.card+1)*Real.log 2 := Finset.sum_le_sum hterm
    _ = (Q.card : ℝ)*(((2*J : ℕ) : ℝ)^(S.card+1)*Real.log 2) := by simp
    _ ≤ _ := by
      calc
        _ ≤ (2 : ℝ)^J*(((2*J : ℕ) : ℝ)^(S.card+1)*Real.log 2) :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
        _ = _ := by ring

/-- The nonlinear excess cannot contribute any nonzero campaign source. -/
theorem tendsto_scaled_correction (P : ℕ → Finset ℕ) (S : Finset ι)
    (a b : ℕ → ι → ℕ) (phase : ℕ → ℕ → ℂ)
    (hP : ∀ J p, p ∈ P J → p.Prime) (hab : ∀ J i, i ∈ S → a J i+b J i≤2^(2*J))
    (hphase : ∀ J p, p ∈ P J → ‖phase J p‖≤1)
    {beta : ℝ} (hbeta : 1/2<beta) :
    Tendsto (fun J : ℕ => (Real.exp (-2*beta*Real.log 2)^J : ℂ)*
      correction (P J) S (a J) (b J) (phase J)) atTop (𝓝 0) := by
  let r := Real.exp ((1-2*beta)*Real.log 2)
  have hr0 : 0≤r := (Real.exp_pos _).le
  have hr1 : r<1 := Real.exp_lt_one_iff.mpr
    (mul_neg_of_neg_of_pos (by linarith) (Real.log_pos (by norm_num)))
  have he : Real.exp (-2*beta*Real.log 2)*2=r := by
    calc
      _ = Real.exp (-2*beta*Real.log 2)*Real.exp (Real.log 2) := by
        rw [Real.exp_log (by norm_num : (0 : ℝ)<2)]
      _ = _ := by dsimp [r]; rw [←Real.exp_add]; congr 1; ring
  have ht := (tendsto_pow_const_mul_const_pow_of_lt_one (S.card+1) hr0 hr1).const_mul
    ((2 : ℝ)^(S.card+1)*Real.log 2)
  simp only [mul_zero] at ht
  apply squeeze_zero_norm (a := fun J : ℕ =>
    ((2 : ℝ)^(S.card+1)*Real.log 2)*((J : ℝ)^(S.card+1)*r^J)) _ ht
  intro J
  rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg (Real.exp_pos _).le]
  apply (mul_le_mul_of_nonneg_left
    (norm_correction_le (P J) (hP J) S (a J) (b J) (hab J) (phase J) (hphase J))
    (by positivity)).trans_eq
  rw [←he,mul_pow]
  push_cast
  rw [mul_pow]
  ring

/-- The extra valuation multiplicity fails the nonzero-source gate. -/
theorem no_nonzero_correction_source (P : ℕ → Finset ℕ) (S : Finset ι)
    (a b : ℕ → ι → ℕ) (phase : ℕ → ℕ → ℂ)
    (hP : ∀ J p, p ∈ P J → p.Prime) (hab : ∀ J i, i ∈ S → a J i+b J i≤2^(2*J))
    (hphase : ∀ J p, p ∈ P J → ‖phase J p‖≤1)
    {beta : ℝ} (hbeta : 1/2<beta) {v : ℂ} (hv : v≠0) :
    ¬Tendsto (fun J : ℕ => (Real.exp (-2*beta*Real.log 2)^J : ℂ)*
      correction (P J) S (a J) (b J) (phase J)) atTop (𝓝 v) := by
  intro hh
  exact hv (tendsto_nhds_unique hh
    (tendsto_scaled_correction P S a b phase hP hab hphase hbeta))

/-- Any source survives wholly in the common-GCD packet, in both directions.
This does NOT estimate that signed packet or infer its source from a zero. -/
theorem tendsto_scaled_product_iff_common (P : ℕ → Finset ℕ) (S : Finset ι)
    (a b : ℕ → ι → ℕ) (phase : ℕ → ℕ → ℂ)
    (hP : ∀ J p, p ∈ P J → p.Prime) (hab : ∀ J i, i ∈ S → a J i+b J i≤2^(2*J))
    (hphase : ∀ J p, p ∈ P J → ‖phase J p‖≤1)
    {beta : ℝ} (hbeta : 1/2<beta) (v : ℂ) :
    Tendsto (fun J => (Real.exp (-2*beta*Real.log 2)^J : ℂ)*
      productPacket (P J) S (a J) (b J) (phase J)) atTop (𝓝 v) ↔
    Tendsto (fun J => (Real.exp (-2*beta*Real.log 2)^J : ℂ)*
      commonPacket (P J) S (a J) (b J) (phase J)) atTop (𝓝 v) := by
  have hc := tendsto_scaled_correction P S a b phase hP hab hphase hbeta
  constructor
  · intro hp
    have hh := hp.sub hc
    simp only [sub_zero] at hh
    apply hh.congr'
    filter_upwards [] with J
    rw [productPacket_eq_common_add_correction (P J) (hP J) S (a J) (b J) (phase J)]
    ring
  · intro hp
    have hh := hp.add hc
    simp only [add_zero] at hh
    apply hh.congr'
    filter_upwards [] with J
    rw [productPacket_eq_common_add_correction (P J) (hP J) S (a J) (b J) (phase J)]
    ring

/-- A literal binomial selector, not a smooth or generalized-prime model. -/
theorem selector_valuation {p q : ℕ} (hp : p.Prime) (hq : q.Prime) :
    valuation p (q-1) 1=if p=q then 1 else 0 := by
  unfold valuation
  rw [Nat.sub_add_cancel hq.one_le,Nat.choose_one_right]
  by_cases hpq : p=q
  · subst p
    let : Fact q.Prime := ⟨hq⟩
    simp only [ite_true,padicValNat_self]
  · rw [ite_eq_right hpq]
    apply padicValNat.eq_zero_of_not_dvd
    intro hd
    rcases (Nat.dvd_prime hq).mp hd with h | h
    · exact hp.ne_one h
    · exact hpq h

/-- Two genuinely different binomial rows can still select one ordinary
prime. The exceptional prime two is excluded EXPLICITLY in this identity. -/
theorem distinct_selector_product {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hq2 : 2<q) :
    valuation p (q-1) 1*valuation p (2*q-1) 1=if p=q then 1 else 0 := by
  rw [selector_valuation hp hq]
  by_cases hpq : p=q
  · subst p
    let : Fact q.Prime := ⟨hq⟩
    have hn : 1≤2*q := by omega
    have hn2 : ¬q ∣ 2 := by
      intro hd
      have hh := Nat.le_of_dvd (by norm_num : 0<(2 : ℕ)) hd
      omega
    simp only [ite_true,one_mul,valuation,Nat.sub_add_cancel hn,Nat.choose_one_right]
    rw [padicValNat.mul (by norm_num : (2 : ℕ)≠0) hq.ne_zero,
      padicValNat.eq_zero_of_not_dvd hn2,padicValNat_self,zero_add]
  · simp only [ite_eq_right hpq,zero_mul]

/-- Joining arbitrary weighted selector rows restores exactly the original
prime profile. This equality supplies no constraint on those weights. -/
def selectorGram (P : Finset ℕ) (w : ℕ → ℂ) (m n : ℕ) : ℂ :=
  ∑ p ∈ P, w p*(valuation p (m-1) 1 : ℂ)*(valuation p (n-1) 1 : ℂ)

theorem selectorGram_diagonal (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (w : ℕ → ℂ) {q : ℕ} (hq : q ∈ P) : selectorGram P w q q=w q := by
  unfold selectorGram
  rw [Finset.sum_eq_single q]
  · rw [selector_valuation (hP q hq) (hP q hq)]
    simp
  · intro p hp hpq
    rw [selector_valuation (hP p hp) (hP q hq)]
    simp only [ite_eq_right hpq,Nat.cast_zero,mul_zero]
  · exact fun hh => (hh hq).elim

/-- The whole joined selector trace is the same arbitrary-weight prime sum,
including its complex height and any external modular/Gaussian code. -/
theorem selector_trace_eq (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (w alpha : ℕ → ℂ) :
    (∑ q ∈ P, alpha q*selectorGram P w q q)=∑ q ∈ P, alpha q*w q := by
  exact Finset.sum_congr rfl (fun q hq => by rw [selectorGram_diagonal P hP w hq])

/-- Genuine prime factorial moments encoded by a binomial-row quadratic. -/
def selectorMoment (k : ℕ) (s : ℂ) : ℂ :=
  ∑' p, if p.Prime then (ArithmeticFunction.vonMangoldt p : ℂ)*zetaPrimeLogKernel k s p*
    (valuation p (p-1) 1 : ℂ)^2 else 0

theorem selectorMoment_eq_ordinary (k : ℕ) (s : ℂ) :
    selectorMoment k s=zetaOrdinaryPrimeLogMoment k s := by
  unfold selectorMoment zetaOrdinaryPrimeLogMoment
  apply tsum_congr
  intro p
  by_cases hp : p.Prime
  · rw [ite_eq_left hp,ite_eq_left hp,selector_valuation hp hp]
    simp
  · simp only [ite_eq_right hp]

/-- Actual exposed zeros retain their NONZERO full multiplicity source.
This is the old ordinary-prime source, not a fresh nonlinear source proof. -/
theorem tendsto_selectorMoment_source (rho : NontrivialZetaZero)
    (hrho : 1/2<rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau≠rho →
      3/2-rho.1.re<‖(3/2+Complex.I*(rho.1.im : ℂ))-tau.1‖) :
    Tendsto (fun k : ℕ => ((3/2-rho.1.re : ℝ) : ℂ)^(k+1)*
      selectorMoment k (3/2+Complex.I*(rho.1.im : ℂ))) atTop
      (𝓝 (-(analyticZetaZeroMultiplicity rho : ℂ))) := by
  simpa only [selectorMoment_eq_ordinary] using
    ZetaRieszPrimeCompletionPhase.tendsto_ordinary_prime_source rho hrho hexposed

/-- No unrestricted PSD rescue: the same literal binomial selector has a
negative phased prime diagonal beyond every fixed head at every y!=0. -/
theorem exists_negative_selector_diagonal {y : ℝ} (hy : y≠0) (H : ℕ) :
    ∃ p : ℕ, H<p ∧ p.Prime ∧
      (selectorGram {p} (fun q => (ArithmeticFunction.vonMangoldt q : ℂ)*
        SuzukiCarryCorrelation.primePhase y q) p p).re<0 := by
  obtain ⟨p,hH,hp,hneg⟩ :=
    ArithmeticOperatorTwistedBulkAudit.exists_negative_prime_diagonal_above hy H
  refine ⟨p,hH,hp,?_⟩
  rw [selectorGram_diagonal {p} (by simpa) _ (Finset.mem_singleton_self p)]
  simpa only [ArithmeticOperatorGcdAudit.gcdKernel,Nat.gcd_self,hp.divisors,
    Finset.sum_pair hp.ne_one.symm,ArithmeticFunction.vonMangoldt_apply_one,
    Complex.ofReal_zero,zero_mul,zero_add] using hneg

end
end RiemannGaussian.ArithmeticOperatorKummerGcdAudit
