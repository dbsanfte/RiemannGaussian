/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ArithmeticOperatorKummerGcdAudit
import Mathlib.Data.Nat.ModEq

/-!
# Consecutive balanced Kummer rows select a single quotient interval

Products of first-order carries for choose((k+1)N,N), 1<=k<=r, are EXACTLY
the indicator (r+1)(N mod d)>=r*d. This retains all quotient endpoints and
uses no primality, coefficient, density or phase assumption. Large-prime
actual valuations coincide with these carries; their other orders remain
in the existing square-root correction, not silently discarded here.
-/

namespace RiemannGaussian.ArithmeticOperatorKummerThresholdAudit
noncomputable section
open ArithmeticOperatorKummerCutoff
open Filter
open scoped BigOperators Classical Topology

/-- First carry in the k-th literal balanced binomial row. -/
def rowCarry (k N d : ℕ) : ℕ := binomialCarry (k*N) N d

/-- Every row from choose(2N,N) through choose((r+1)N,N). -/
def intersection (r N d : ℕ) : ℕ := ∏ k ∈ Finset.range r, rowCarry (k+1) N d

theorem rowCarry_le_one (k N d : ℕ) : rowCarry k N d≤1 := by
  have h := Nat.add_div_le_div_add_div_add_one (k*N) N d
  unfold rowCarry binomialCarry
  omega

/-- Exact telescoping identity before collapsing the binary intersection. -/
theorem sum_rowCarry (r N d : ℕ) :
    (∑ k ∈ Finset.range r, (rowCarry (k+1) N d : ℤ))=
      (((r+1)*N/d : ℕ) : ℤ)-(r+1)*(N/d : ℕ) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Finset.sum_range_succ,ih,rowCarry,binomialCarry_eq_sub]
    rw [show (r+1)*N+N=(r+1+1)*N by ring]
    push_cast
    ring

private theorem sum_eq_card_iff (S : Finset ℕ) (f : ℕ → ℕ)
    (hf : ∀ i ∈ S, f i≤1) :
    (∑ i ∈ S, f i)=S.card ↔ ∀ i ∈ S, f i=1 := by
  constructor
  · intro hs i hi
    by_contra hbad
    have hlt : f i<1 := by have := hf i hi;omega
    have hh := Finset.sum_lt_sum hf ⟨i,hi,hlt⟩
    simp only [Finset.sum_const,smul_eq_mul,mul_one] at hh
    omega
  · intro hh
    simp only [Finset.sum_congr rfl hh,Finset.sum_const,smul_eq_mul,mul_one]

private theorem mul_div_decompose (a N d : ℕ) (hd : 0<d) :
    a*N/d=a*(N/d)+(a*(N%d))/d := by
  have hn := Nat.mod_add_div N d
  conv_lhs => rw [←hn]
  rw [Nat.mul_add,show a*(d*(N/d))=(a*(N/d))*d by ring,
    Nat.add_mul_div_right _ _ hd]
  omega

/-- The maximum total carry forces all the individual rows, and conversely. -/
theorem intersection_eq_one_iff {d : ℕ} (hd : 0<d) (r N : ℕ) :
    intersection r N d=1 ↔ r*d≤(r+1)*(N%d) := by
  have hs := sum_rowCarry r N d
  rw [mul_div_decompose (r+1) N d hd] at hs
  have hsum : (∑ k ∈ Finset.range r, rowCarry (k+1) N d)=
      (r+1)*(N%d)/d := by
    exact_mod_cast (by
      simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_one] at hs
      linear_combination hs :
      (∑ k ∈ Finset.range r, (rowCarry (k+1) N d : ℤ))=
        (((r+1)*(N%d)/d : ℕ) : ℤ))
  have hcap : (r+1)*(N%d)/d≤r := by
    have hm := Nat.mod_lt N hd
    have hh : (r+1)*(N%d)<(r+1)*d := by nlinarith
    have hv := (Nat.div_lt_iff_lt_mul hd).mpr hh
    omega
  have hp : intersection r N d=1 ↔
      ∀ k ∈ Finset.range r, rowCarry (k+1) N d=1 := by
    unfold intersection
    exact Finset.prod_eq_one_iff_of_le_one (fun k _ => rowCarry_le_one (k+1) N d)
  rw [hp,←sum_eq_card_iff _ _ (fun k _ => rowCarry_le_one (k+1) N d),
    Finset.card_range,hsum]
  have hge : r≤(r+1)*(N%d)/d ↔ r*d≤(r+1)*(N%d) :=
    Nat.le_div_iff_mul_le hd
  omega

/-- Literal endpoint-preserving quotient mask. No carry order is inferred
from a limiting fractional-part picture. -/
theorem intersection_eq_threshold {d : ℕ} (hd : 0<d) (r N : ℕ) :
    intersection r N d=if r*d≤(r+1)*(N%d) then 1 else 0 := by
  have hi : intersection r N d≤1 := by
    unfold intersection
    calc
      _ ≤ ∏ _k ∈ Finset.range r, (1 : ℕ) :=
        Finset.prod_le_prod₀ (fun _ _ => Nat.zero_le _) (fun k _ => rowCarry_le_one (k+1) N d)
      _ = 1 := by simp
  split_ifs with ht
  · exact (intersection_eq_one_iff hd r N).mpr ht
  · have hh : intersection r N d≠1 := fun h => ht ((intersection_eq_one_iff hd r N).mp h)
    omega

/-- Exact scalar join for EVERY array, including every original height,
modular or Gaussian phase put into w. No arithmetic estimate is supplied. -/
theorem weighted_intersection_eq (D : Finset ℕ) (hD : ∀ d ∈ D, 0<d)
    (r N : ℕ) (w : ℕ → ℂ) :
    (∑ d ∈ D, w d*(intersection r N d : ℂ))=
      ∑ d ∈ D, if r*d≤(r+1)*(N%d) then w d else 0 := by
  apply Finset.sum_congr rfl
  intro d hd
  rw [intersection_eq_threshold (hD d hd)]
  split_ifs <;> simp

/-- In the top quotient cell this is just an ordinary short prime band.
The identity is exact for every integer denominator, not a density model. -/
theorem intersection_above_cutoff {N d : ℕ} (hN : N<d) (r : ℕ) :
    intersection r N d=if r*d≤(r+1)*N then 1 else 0 := by
  rw [intersection_eq_threshold (by omega),Nat.mod_eq_of_lt hN]

/-- ALL actual Kummer orders are kept in the valuation. Their exact support
reduces to the first carry when p squared exceeds the row's literal top. -/
theorem valuation_eq_firstCarry {p a b : ℕ} (hp : p.Prime)
    (hab : a+b<p^2) :
    ArithmeticOperatorKummerPolynomialAudit.valuation p a b=binomialCarry a b p := by
  let : Fact p.Prime := ⟨hp⟩
  by_cases hzero : a+b=0
  · have ha : a=0 := by omega
    have hb : b=0 := by omega
    simp [ha,hb,ArithmeticOperatorKummerPolynomialAudit.valuation,binomialCarry]
  have hlog : Nat.log p (a+b)<2 := (Nat.log_lt_iff_lt_pow hp.one_lt hzero).mpr hab
  have hc : binomialCarry a b p=if p≤b%p+a%p then 1 else 0 := by
    unfold binomialCarry
    rw [Nat.add_div hp.pos]
    split_ifs <;> omega
  rw [ArithmeticOperatorKummerPolynomialAudit.valuation,valuation_eq_carry_count hlog]
  have hi : Finset.Ico (1 : ℕ) 2={1} := by
    ext i
    simp only [Finset.mem_Ico,Finset.mem_singleton]
    omega
  simp only [hi,pow_one,Finset.filter_singleton]
  rw [hc]
  split_ifs <;> simp_all

/-- Literal differently balanced binomial valuations, without a limiting
carry approximation, have the same single threshold on the large primes. -/
theorem valuationProduct_eq_threshold {p : ℕ} (hp : p.Prime) (r N : ℕ)
    (hlarge : (r+1)*N<p^2) :
    ArithmeticOperatorKummerGcdAudit.valuationProduct (Finset.range r)
      (fun k => (k+1)*N) (fun _ => N) p=
      if r*p≤(r+1)*(N%p) then 1 else 0 := by
  have he : ArithmeticOperatorKummerGcdAudit.valuationProduct (Finset.range r)
      (fun k => (k+1)*N) (fun _ => N) p=intersection r N p := by
    unfold ArithmeticOperatorKummerGcdAudit.valuationProduct intersection
    apply Finset.prod_congr rfl
    intro k hk
    rw [valuation_eq_firstCarry hp]
    · rfl
    · have hh := Finset.mem_range.mp hk
      exact (by nlinarith : (k+1)*N+N≤(r+1)*N).trans_lt hlarge
  rw [he,intersection_eq_threshold hp.pos]

private theorem balanced_top_le {r N J : ℕ} (hX : (r+1)*N≤2^(2*J)) :
    ∀ k ∈ Finset.range r, (k+1)*N+N≤2^(2*J) := by
  intro k hk
  have hh := Finset.mem_range.mp hk
  exact (by nlinarith : (k+1)*N+N≤(r+1)*N).trans hX

/-- All higher-order actual common-divisor data agree with the threshold
above the square-root cutoff. None are approximated on the small primes. -/
theorem commonPrime_large_eq_intersection {p r N J : ℕ} (hp : p.Prime)
    (hX : (r+1)*N≤2^(2*J)) (hlarge : 2^J<p) :
    ArithmeticOperatorKummerGcdAudit.commonPrime (Finset.range r)
      (fun k => (k+1)*N) (fun _ => N) p=intersection r N p := by
  rw [←ArithmeticOperatorKummerGcdAudit.valuationProduct_large_prime hp
    (Finset.range r) (fun k => (k+1)*N) (fun _ => N) (balanced_top_le hX) hlarge,
    valuationProduct_eq_threshold hp,intersection_eq_threshold hp.pos]
  apply hX.trans_lt
  rw [show 2*J=J*2 by omega,pow_mul]
  exact Nat.pow_lt_pow_left hlarge (by omega)

/-- The common-GCD/threshold difference is genuinely paid at square-root
scale, with every actual valuation and the original BASE-PRIME phase kept.
The full threshold packet remains UNPAID. -/
theorem norm_common_sub_threshold_le {r N J : ℕ} (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hX : (r+1)*N≤2^(2*J)) (phase : ℕ → ℂ)
    (hphase : ∀ p ∈ P, ‖phase p‖≤1) :
    ‖ArithmeticOperatorKummerGcdAudit.commonPacket P (Finset.range r)
      (fun k => (k+1)*N) (fun _ => N) phase-
        ∑ p ∈ P, (Real.log p : ℂ)*phase p*(intersection r N p : ℂ)‖≤
          (2 : ℝ)^J*((2*J : ℕ) : ℝ)*Real.log 2 := by
  let f (p : ℕ) : ℂ := (Real.log p : ℂ)*phase p*
    ((ArithmeticOperatorKummerGcdAudit.commonPrime (Finset.range r)
      (fun k => (k+1)*N) (fun _ => N) p : ℂ)-(intersection r N p : ℂ))
  have he : ArithmeticOperatorKummerGcdAudit.commonPacket P (Finset.range r)
      (fun k => (k+1)*N) (fun _ => N) phase-
        ∑ p ∈ P, (Real.log p : ℂ)*phase p*(intersection r N p : ℂ)=∑ p ∈ P, f p := by
    unfold ArithmeticOperatorKummerGcdAudit.commonPacket f
    rw [←Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun _ _ => by ring)
  rw [he]
  have hs : (∑ p ∈ P, f p)=∑ p ∈ P.filter (fun p => p≤2^J), f p := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro p hp hpn
    have hh : 2^J<p := by
      by_contra hn
      exact hpn (Finset.mem_filter.mpr ⟨hp,by omega⟩)
    simp only [f,commonPrime_large_eq_intersection (hP p hp) hX hh,sub_self,mul_zero]
  rw [hs]
  let Q := P.filter (fun p => p≤2^J)
  have hc : (Q.card : ℝ)≤(2 : ℝ)^J := by
    have hh : Q ⊆ Finset.Icc 1 (2^J) := by
      intro p hp
      obtain ⟨hp,hh⟩ := Finset.mem_filter.mp hp
      exact Finset.mem_Icc.mpr ⟨(hP p hp).pos,hh⟩
    exact_mod_cast (by simpa using Finset.card_le_card hh : Q.card≤2^J)
  have hf (p : ℕ) (hp : p ∈ Q) : ‖f p‖≤((2*J : ℕ) : ℝ)*Real.log 2 := by
    obtain ⟨hpP,hps⟩ := Finset.mem_filter.mp hp
    have hlog : ‖(Real.log p : ℂ)‖≤((2*J : ℕ) : ℝ)*Real.log 2 := by
      rw [Complex.norm_real,Real.norm_of_nonneg (Real.log_natCast_nonneg p)]
      have hpX : p≤2^(2*J) := hps.trans (Nat.pow_le_pow_right (by omega) (by omega))
      have hh := Real.log_le_log (by exact_mod_cast (hP p hpP).pos : (0 : ℝ)<p)
        (by exact_mod_cast hpX : (p : ℝ)≤(2 : ℝ)^(2*J))
      simpa only [Real.log_pow] using hh
    have hd : ‖(ArithmeticOperatorKummerGcdAudit.commonPrime (Finset.range r)
        (fun k => (k+1)*N) (fun _ => N) p : ℂ)-(intersection r N p : ℂ)‖≤1 := by
      rw [intersection_eq_threshold (hP p hpP).pos]
      unfold ArithmeticOperatorKummerGcdAudit.commonPrime
      split_ifs <;> norm_num
    dsimp only [f]
    rw [norm_mul,norm_mul]
    calc
      _ ≤ (((2*J : ℕ) : ℝ)*Real.log 2)*1*1 :=
        mul_le_mul (mul_le_mul hlog (hphase p hpP) (norm_nonneg _) (by positivity))
          hd (norm_nonneg _) (by positivity)
      _ = _ := by ring
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _p ∈ Q, ((2*J : ℕ) : ℝ)*Real.log 2 := Finset.sum_le_sum hf
    _ = (Q.card : ℝ)*(((2*J : ℕ) : ℝ)*Real.log 2) := by simp
    _ ≤ _ := (mul_le_mul_of_nonneg_right hc (by positivity)).trans_eq (by ring)

/-- The exact unpaid common-divisor packet and threshold packet have the
same source at every exponent beta>1/2. This is not a prime-sum estimate. -/
theorem tendsto_scaled_common_sub_threshold (P : ℕ → Finset ℕ) (r : ℕ)
    (N : ℕ → ℕ) (phase : ℕ → ℕ → ℂ)
    (hP : ∀ J p, p ∈ P J → p.Prime) (hX : ∀ J, (r+1)*N J≤2^(2*J))
    (hphase : ∀ J p, p ∈ P J → ‖phase J p‖≤1)
    {beta : ℝ} (hb : 1/2<beta) :
    Tendsto (fun J : ℕ => (Real.exp (-2*beta*Real.log 2)^J : ℂ)*
      (ArithmeticOperatorKummerGcdAudit.commonPacket (P J) (Finset.range r)
        (fun k => (k+1)*N J) (fun _ => N J) (phase J)-
          ∑ p ∈ P J, (Real.log p : ℂ)*phase J p*(intersection r (N J) p : ℂ))) atTop (𝓝 0) := by
  let q := Real.exp ((1-2*beta)*Real.log 2)
  have hq0 : 0≤q := (Real.exp_pos _).le
  have hq1 : q<1 := Real.exp_lt_one_iff.mpr
    (mul_neg_of_neg_of_pos (by linarith) (Real.log_pos (by norm_num)))
  have he : Real.exp (-2*beta*Real.log 2)*2=q := by
    calc
      _ = Real.exp (-2*beta*Real.log 2)*Real.exp (Real.log 2) := by
        rw [Real.exp_log (by norm_num : (0 : ℝ)<2)]
      _ = _ := by dsimp [q];rw [←Real.exp_add];congr 1;ring
  have ht := (tendsto_pow_const_mul_const_pow_of_lt_one 1 hq0 hq1).const_mul
    (2*Real.log 2)
  simp only [mul_zero,pow_one] at ht
  apply squeeze_zero_norm (a := fun J : ℕ => (2*Real.log 2)*((J : ℝ)*q^J)) _ ht
  intro J
  rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg (Real.exp_pos _).le]
  apply (mul_le_mul_of_nonneg_left
    (norm_common_sub_threshold_le (P J) (hP J) (hX J) (phase J) (hphase J))
    (by positivity)).trans_eq
  rw [←he,mul_pow]
  push_cast
  ring

/-- Complete actual binomial valuations, including ALL positive carry
orders, are source-equivalent to the threshold packet. Higher orders and
small-prime Boolean corrections have both been paid explicitly. -/
theorem tendsto_scaled_product_sub_threshold (P : ℕ → Finset ℕ) (r : ℕ)
    (N : ℕ → ℕ) (phase : ℕ → ℕ → ℂ)
    (hP : ∀ J p, p ∈ P J → p.Prime) (hX : ∀ J, (r+1)*N J≤2^(2*J))
    (hphase : ∀ J p, p ∈ P J → ‖phase J p‖≤1)
    {beta : ℝ} (hb : 1/2<beta) :
    Tendsto (fun J : ℕ => (Real.exp (-2*beta*Real.log 2)^J : ℂ)*
      (ArithmeticOperatorKummerGcdAudit.productPacket (P J) (Finset.range r)
        (fun k => (k+1)*N J) (fun _ => N J) (phase J)-
          ∑ p ∈ P J, (Real.log p : ℂ)*phase J p*(intersection r (N J) p : ℂ))) atTop (𝓝 0) := by
  have hc := ArithmeticOperatorKummerGcdAudit.tendsto_scaled_correction P (Finset.range r)
    (fun J k => (k+1)*N J) (fun J _ => N J) phase hP
    (fun J => balanced_top_le (hX J)) hphase hb
  have ht := tendsto_scaled_common_sub_threshold P r N phase hP hX hphase hb
  have hh := hc.add ht
  simp only [zero_add] at hh
  apply hh.congr'
  filter_upwards [] with J
  rw [ArithmeticOperatorKummerGcdAudit.productPacket_eq_common_add_correction
    (P J) (hP J) (Finset.range r) (fun k => (k+1)*N J) (fun _ => N J)]
  ring

/-- The collapsed kernel imposes no all-weight allowance: any active
column makes every finite bound fail. Actual Gamma data are not free data. -/
theorem intersection_bound_forall_weights_iff (D : Finset ℕ) (r N : ℕ) (B : ℝ) :
    (∀ w : ℕ → ℂ, ‖∑ d ∈ D, w d*(intersection r N d : ℂ)‖≤B) ↔
      0≤B ∧ ∀ d ∈ D, intersection r N d=0 := by
  simpa only [Nat.cast_eq_zero] using
    ArithmeticOperatorGramAudit.scalar_bound_forall_weights_iff D
      (fun d => (intersection r N d : ℂ)) B

end
end RiemannGaussian.ArithmeticOperatorKummerThresholdAudit
