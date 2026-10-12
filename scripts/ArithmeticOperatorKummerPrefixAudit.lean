/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import scripts.ArithmeticOperatorKummerMinimumAudit
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Tactic.Linter
import Lean.Util.CollectAxioms

/-!
# Literal constrained binomial prefixes: cutoff/source collapse audit

The minimum is taken BEFORE the prime join, over precisely the splits
1 <= k <= H. No endpoint, power or moving cutoff is approximated.
The resulting exact integer identity is audited for arithmetic content.
-/

set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
open scoped BigOperators Classical Topology
namespace RiemannGaussian.ArithmeticOperatorKummerPrefixAudit
open Complex Filter

/-- Literal nonempty prefix of nonunit splits; H=n retains the unit end. -/
def prefixGcd (n H : ℕ) : ℕ := (Finset.Icc 1 H).gcd n.choose

private theorem mul_sub_one {p t : ℕ} (hp : 0<p) (ht : 0<t) :
    p*t-1=p*(t-1)+(p-1) := by
  have he : p*(t-1)+(p-1)+1=p*t := by
    calc
      _ = p*(t-1)+p := by omega
      _ = p*(t-1+1) := by ring
      _ = p*t := by rw [Nat.sub_add_cancel (by omega : 1≤t)]
  omega

/-- Every p-power witness has a p-unit complementary binomial factor. -/
theorem unit_choose_power {p : ℕ} (hp : p.Prime) (s a : ℕ) (ha : 0<a) :
    (((p^s*a-1).choose (p^s-1) : ℕ) : ZMod p)=1 := by
  let : Fact p.Prime := ⟨hp⟩
  induction s with
  | zero => simp
  | succ s ih =>
    have hv : 0<p^s*a := Nat.mul_pos (Nat.pow_pos hp.pos) ha
    have hmod : p-1<p := by have := hp.pos; omega
    have hn : p^(s+1)*a-1=p*(p^s*a-1)+(p-1) := by
      rw [pow_succ',mul_assoc]
      exact mul_sub_one hp.pos hv
    have hk : p^(s+1)-1=p*(p^s-1)+(p-1) := by
      rw [pow_succ']
      exact mul_sub_one hp.pos (Nat.pow_pos hp.pos)
    have he := Choose.choose_modEq_choose_mod_mul_choose_div (p := p)
      (n := p^(s+1)*a-1) (k := p^(s+1)-1)
    rw [← ZMod.intCast_eq_intCast_iff] at he
    norm_cast at he
    simp only [hn,hk,Nat.mul_add_mod,Nat.mod_eq_of_lt hmod,
      Nat.mul_add_div hp.pos,Nat.div_eq_of_lt hmod,
      add_zero,Nat.choose_self,one_mul] at he
    rw [hn,hk]
    exact he.trans ih

/-- Exact binomial recurrence before taking a valuation. -/
theorem choose_order_identity {n k : ℕ} (hn : 0<n) (hk : 0<k) :
    n*(n-1).choose (k-1)=n.choose k*k := by
  have he := Nat.add_one_mul_choose_eq (n-1) (k-1)
  simpa only [Nat.sub_add_cancel (by omega : 1≤n),
    Nat.sub_add_cancel (by omega : 1≤k)] using he

/-- Every prefix member has the required lower valuation; this bound
retains the complementary factor rather than assuming it is a unit. -/
theorem choose_factorization_lower {p n k : ℕ}
    (hk : 0<k) (hkn : k≤n) :
    n.factorization p-k.factorization p≤(n.choose k).factorization p := by
  have hn : 0<n := lt_of_lt_of_le hk hkn
  have hc : (n-1).choose (k-1)≠0 := Nat.choose_ne_zero (by omega)
  have he := congrArg (fun a : ℕ => a.factorization p) (choose_order_identity hn hk)
  rw [Nat.factorization_mul hn.ne' hc,
    Nat.factorization_mul (Nat.choose_ne_zero hkn) hk.ne',Finsupp.add_apply,
    Finsupp.add_apply] at he
  omega

/-- The power witness attains the lower bound at EVERY valuation order. -/
theorem choose_power_factorization {p n s : ℕ} (hp : p.Prime)
    (hn : 0<n) (hdiv : p^s∣n) :
    (n.choose (p^s)).factorization p=n.factorization p-s := by
  have hk : 0<p^s := Nat.pow_pos hp.pos
  obtain ⟨a,ha⟩ := hdiv
  have hap : 0<a := by nlinarith
  have hu : ¬p∣(n-1).choose (p^s-1) := by
    intro hd
    have hz : (((n-1).choose (p^s-1) : ℕ) : ZMod p)=0 :=
      (ZMod.natCast_eq_zero_iff _ _).mpr hd
    rw [ha,unit_choose_power hp s a hap] at hz
    exact hp.ne_one (ZMod.one_eq_zero_iff.mp hz)
  have hkn : p^s≤n := Nat.le_of_dvd hn ⟨a,ha⟩
  have he := congrArg (fun a : ℕ => a.factorization p) (choose_order_identity hn hk)
  rw [Nat.factorization_mul hn.ne' (Nat.choose_ne_zero (by omega)),
    Nat.factorization_mul (Nat.choose_ne_zero hkn) hk.ne',Finsupp.add_apply,
    Finsupp.add_apply,Nat.factorization_eq_zero_of_not_dvd hu,Nat.factorization_pow_self hp] at he
  omega

theorem prefixGcd_ne_zero {n H : ℕ} (hn : 0<n) (hH : 0<H) :
    prefixGcd n H≠0 := by
  exact Finset.gcd_ne_zero_iff.mpr ⟨1,Finset.mem_Icc.mpr ⟨le_rfl,by omega⟩,
    by simpa using hn.ne'⟩

/-- The sharp prefix minimum has a single p-power witness for each prime.
This is not a simultaneous witness for distinct primes or for other masks. -/
theorem prefixGcd_factorization {p n H : ℕ} (hp : p.Prime)
    (hH : 0<H) (hHn : H≤n) :
    (prefixGcd n H).factorization p=n.factorization p-Nat.log p H := by
  have hn : 0<n := lt_of_lt_of_le hH hHn
  have hg : prefixGcd n H≠0 := prefixGcd_ne_zero hn hH
  apply Nat.le_antisymm
  · let s := min (n.factorization p) (Nat.log p H)
    have hsH : p^s≤H := (Nat.pow_le_pow_right hp.pos (min_le_right _ _)).trans
      (Nat.pow_log_le_self p hH.ne')
    have hdiv : p^s∣n := (hp.pow_dvd_iff_le_factorization hn.ne').mpr (min_le_left _ _)
    have hmem : p^s∈Finset.Icc 1 H :=
      Finset.mem_Icc.mpr ⟨by have := Nat.pow_pos hp.pos (n := s); omega,hsH⟩
    have hd : prefixGcd n H∣n.choose (p^s) := Finset.gcd_dvd hmem
    have hl := (Nat.factorization_le_iff_dvd hg (Nat.choose_ne_zero (hsH.trans hHn))).mpr hd p
    rw [choose_power_factorization hp hn hdiv] at hl
    dsimp only [s] at hl
    omega
  · apply (hp.pow_dvd_iff_le_factorization hg).mp
    apply Finset.dvd_gcd
    intro k hk
    obtain ⟨hk1,hkH⟩ := Finset.mem_Icc.mp hk
    have hl : k.factorization p≤Nat.log p H := by
      rw [Nat.factorization_def k hp]
      exact (padicValNat_le_nat_log k).trans (Nat.log_mono_right hkH)
    apply (hp.pow_dvd_iff_le_factorization (Nat.choose_ne_zero (hkH.trans hHn))).mpr
    have := choose_factorization_lower (p := p) (by omega : 0<k) (hkH.trans hHn)
    omega

/-- Exact classical constrained-prefix identity, with the literal LCM
cutoff. No Gamma approximation, prime-head deletion or density input. -/
theorem prefixGcd_eq_quotient {n H : ℕ} (hH : 0<H) (hHn : H≤n) :
    prefixGcd n H=n/Nat.gcd n (Nat.lcmUpto H) := by
  have hn : 0<n := lt_of_lt_of_le hH hHn
  have hd := Nat.gcd_dvd_left n (Nat.lcmUpto H)
  have hc : 0<Nat.gcd n (Nat.lcmUpto H) := Nat.gcd_pos_of_pos_left _ hn
  have hq : n/Nat.gcd n (Nat.lcmUpto H)≠0 :=
    (Nat.div_pos (Nat.le_of_dvd hn hd) hc).ne'
  apply Nat.eq_of_factorization_eq (prefixGcd_ne_zero hn hH) hq
  intro p
  by_cases hp : p.Prime
  · rw [prefixGcd_factorization hp hH hHn,Nat.factorization_div hd,
      Finsupp.tsub_apply,Nat.factorization_gcd hn.ne' (Nat.lcmUpto_ne_zero H),
      Finsupp.inf_apply,Nat.factorization_lcmUpto H hp]
    omega
  · simp only [Nat.factorization_eq_zero_of_not_prime _ hp]

/-- Including the literal endpoint n makes the constrained source vanish. -/
theorem prefixGcd_eq_one_of_ge {n H : ℕ} (hH : n≤H) (hn : 0<n) :
    prefixGcd n H=1 := by
  have hd : prefixGcd n H∣1 := by
    simpa only [prefixGcd,Nat.choose_self] using
      (Finset.gcd_dvd (f := n.choose) (Finset.mem_Icc.mpr ⟨by omega,hH⟩))
  exact Nat.dvd_one.mp hd

/-- The empty prefix is not silently substituted for a complete observation. -/
theorem prefixGcd_zero (n : ℕ) : prefixGcd n 0=0 := by simp [prefixGcd]

/-- At a prime-power divisor the LCM cutoff is EXACTLY an integer cutoff. -/
theorem pow_dvd_gcd_lcmUpto_iff {p n H r : ℕ} (hp : p.Prime) (hH : 0<H) :
    p^r∣Nat.gcd n (Nat.lcmUpto H) ↔ p^r∣n ∧ p^r≤H := by
  rw [Nat.dvd_gcd_iff,hp.pow_dvd_iff_le_factorization (Nat.lcmUpto_ne_zero H),
    Nat.factorization_lcmUpto H hp,Nat.le_log_iff_pow_le hp.one_lt hH.ne']

/-- The lower prefix LCM removes exactly the small prime-power divisors;
mixed divisors are retained with their true zero Mangoldt coefficients. -/
theorem log_gcd_lcmUpto_eq_small {n H : ℕ} (hn : 0<n) (hH : 0<H) :
    Real.log (Nat.gcd n (Nat.lcmUpto H))=
      ∑ d∈n.divisors,if d≤H then ArithmeticFunction.vonMangoldt d else 0 := by
  rw [←ArithmeticFunction.vonMangoldt_sum]
  let g := Nat.gcd n (Nat.lcmUpto H)
  have hg : g≠0 := (Nat.gcd_pos_of_pos_left _ hn).ne'
  have hsub : g.divisors⊆n.divisors := Nat.divisors_subset_of_dvd hn.ne' (Nat.gcd_dvd_left _ _)
  rw [←Finset.sum_subset hsub]
  · apply Finset.sum_congr rfl
    intro d hd
    by_cases hdH : d≤H
    · simp only [ite_eq_left hdH]
    · have hz : ArithmeticFunction.vonMangoldt d=0 := by
        by_cases hpow : IsPrimePow d
        · obtain ⟨p,r,hp,hr,he⟩ := (isPrimePow_nat_iff d).mp hpow
          have hdv : p^r∣g := he ▸ Nat.dvd_of_mem_divisors hd
          have hb := (pow_dvd_gcd_lcmUpto_iff hp hH).mp hdv
          exact False.elim (hdH (he ▸ hb.2))
        · exact ite_eq_right hpow
      simp only [ite_eq_right hdH,hz]
  · intro d hd hnot
    by_cases hdH : d≤H
    · rw [ite_eq_left hdH]
      by_cases hpow : IsPrimePow d
      · obtain ⟨p,r,hp,hr,he⟩ := (isPrimePow_nat_iff d).mp hpow
        have hdv : p^r∣n := he ▸ Nat.dvd_of_mem_divisors hd
        have hsmall : p^r≤H := he ▸ hdH
        have hdg := (pow_dvd_gcd_lcmUpto_iff hp hH).mpr ⟨hdv,hsmall⟩
        exact False.elim (hnot (Nat.mem_divisors.mpr ⟨he.symm ▸ hdg,hg⟩))
      · exact ite_eq_right hpow
    · exact ite_eq_right hdH

/-- The entire constrained GCD is the old truncated Mangoldt divisor sum,
at EVERY nonempty moving prefix; all proper powers and full head retained. -/
theorem log_prefixGcd_eq_tail {n H : ℕ} (hH : 0<H) (hHn : H≤n) :
    Real.log (prefixGcd n H)=
      ∑ d∈n.divisors,if H<d then ArithmeticFunction.vonMangoldt d else 0 := by
  have hn : 0<n := lt_of_lt_of_le hH hHn
  have hc : 0<Nat.gcd n (Nat.lcmUpto H) := Nat.gcd_pos_of_pos_left _ hn
  rw [prefixGcd_eq_quotient hH hHn,
    Nat.cast_div (Nat.gcd_dvd_left n (Nat.lcmUpto H)) (by exact_mod_cast hc.ne'),
    Real.log_div (by exact_mod_cast hn.ne') (by exact_mod_cast hc.ne'),
    log_gcd_lcmUpto_eq_small hn hH,←ArithmeticFunction.vonMangoldt_sum,
    ←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d _
  by_cases hd : d≤H <;> simp [hd]

/-- The arbitrary-array version of the decoded cutoff. Countermodels
are NOT thereby granted the literal binomial or Gamma compatibility. -/
def tailObservation (f : ℕ → ℂ) (n H : ℕ) : ℂ :=
  ∑ d∈n.divisors,if H<d then f d else 0

theorem actual_tailObservation {n H : ℕ} (hH : 0<H) (hHn : H≤n) :
    (Real.log (prefixGcd n H) : ℂ)=
      tailObservation (fun d => (ArithmeticFunction.vonMangoldt d : ℂ)) n H := by
  rw [log_prefixGcd_eq_tail hH hHn,Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro d _
  split_ifs <;> simp

/-- Exact cofactor geometry at a proportional integer cutoff. -/
theorem cutoff_cofactor_iff {n e J : ℕ} (hn : 0<n) (hJ : 0<J) (hd : e∣n) :
    n/J<n/e ↔ e<J := by
  have hep : 0<e := Nat.pos_of_dvd_of_pos hd hn
  have hqp : 0<n/e := Nat.div_pos (Nat.le_of_dvd hn hd) hep
  have he := Nat.div_mul_cancel hd
  rw [Nat.div_lt_iff_lt_mul hJ]
  constructor <;> intro h <;> nlinarith

/-- All relative prefixes, including growing J, join to finite cofactor
dilations of the SAME arbitrary input. No twisted phase is removed. -/
theorem tailObservation_eq_cofactor {n J : ℕ} (hn : 0<n) (hJ : 0<J)
    (f : ℕ → ℂ) :
    tailObservation f n (n/J)=∑ e∈n.divisors,if e<J then f (n/e) else 0 := by
  rw [tailObservation,←Nat.sum_divisorsAntidiagonal (fun d e => if n/J<d then f d else 0),
    Nat.sum_divisorsAntidiagonal' (fun d e => if n/J<d then f d else 0)]
  apply Finset.sum_congr rfl
  intro e he
  simp only [cutoff_cofactor_iff hn hJ (Nat.dvd_of_mem_divisors he)]

/-- The first genuinely incomplete proportional prefix retains two
literal cofactor scales, and nothing more, including every proper power. -/
theorem third_prefix_eq {n : ℕ} (hn : 3≤n) :
    (Real.log (prefixGcd n (n/3)) : ℂ)=
      (ArithmeticFunction.vonMangoldt n : ℂ)+
        if 2∣n then (ArithmeticFunction.vonMangoldt (n/2) : ℂ) else 0 := by
  rw [actual_tailObservation (Nat.div_pos hn (by norm_num)) (Nat.div_le_self _ _),
    tailObservation_eq_cofactor (by omega) (by norm_num)]
  have he : (n.divisors.filter (fun e => e<3))=
      if 2∣n then {1,2} else {1} := by
    have hn0 : n≠0 := by omega
    by_cases h2 : 2∣n
    · rw [ite_eq_left h2]
      ext e
      simp only [Finset.mem_filter,Nat.mem_divisors,Finset.mem_insert,Finset.mem_singleton]
      constructor
      · rintro ⟨⟨hd,_⟩,hl⟩
        have hp := Nat.pos_of_dvd_of_pos hd (by omega : 0<n)
        omega
      · rintro (rfl | rfl) <;> simp [h2,hn0]
    · rw [ite_eq_right h2]
      ext e
      simp only [Finset.mem_filter,Nat.mem_divisors,Finset.mem_singleton]
      constructor
      · rintro ⟨⟨hd,_⟩,hl⟩
        have hp := Nat.pos_of_dvd_of_pos hd (by omega : 0<n)
        have he : e=1 ∨ e=2 := by omega
        rcases he with h | rfl
        · exact h
        · exact False.elim (h2 hd)
      · rintro rfl
        simp [hn0]
  rw [←Finset.sum_filter,he]
  by_cases h2 : 2∣n <;> simp [h2,Finset.sum_pair (by norm_num : (1 : ℕ)≠2)]

/-- Full moving-mask prefix packet. This is an audit observation, not
a new research carrier or an independently bounded expression. -/
def packet (X : ℕ) (H : ℕ → ℕ) (w : ℕ → ℂ) : ℂ :=
  ∑ n∈Finset.Icc 1 X,w n*(Real.log (prefixGcd n (H n)) : ℂ)

/-- Recombination before norms: EVERY moving nonempty prefix mask is
still one literal Mangoldt test with its exact divisor cutoff. -/
theorem packet_eq_old_tail (X : ℕ) (H : ℕ → ℕ) (w : ℕ → ℂ)
    (hH : ∀ n∈Finset.Icc 1 X,0<H n ∧ H n≤n) :
    packet X H w=∑ n∈Finset.Icc 1 X,
      w n*tailObservation (fun d => (ArithmeticFunction.vonMangoldt d : ℂ)) n (H n) := by
  apply Finset.sum_congr rfl
  intro n hn
  rw [actual_tailObservation (hH n hn).1 (hH n hn).2]

private theorem divisors_as_prefix {X n : ℕ} (hn : n∈Finset.Icc 1 X) :
    (Finset.Icc 1 X).filter (fun d => d∣n)=n.divisors := by
  ext d
  simp only [Finset.mem_filter,Finset.mem_Icc,Nat.mem_divisors]
  constructor
  · rintro ⟨_,hd⟩
    exact ⟨hd,by have := (Finset.mem_Icc.mp hn).1; omega⟩
  · rintro ⟨hd,_⟩
    exact ⟨⟨Nat.pos_of_dvd_of_pos hd (by have := (Finset.mem_Icc.mp hn).1; omega),
      (Nat.le_of_dvd (by have := (Finset.mem_Icc.mp hn).1; omega) hd).trans
        (Finset.mem_Icc.mp hn).2⟩,hd⟩

/-- Full collapse AFTER joining the label/denominator incidence. This
identity holds for any array f, while actual binomial data are NOT
asserted for a smooth or generalized-prime control. -/
theorem joined_tail_eq_scalar (X : ℕ) (H : ℕ → ℕ) (w f : ℕ → ℂ) :
    (∑ n∈Finset.Icc 1 X,w n*tailObservation f n (H n))=
      ∑ d∈Finset.Icc 1 X,f d*
        (∑ n∈Finset.Icc 1 X,if d∣n ∧ H n<d then w n else 0) := by
  have he (n : ℕ) (hn : n∈Finset.Icc 1 X) :
      tailObservation f n (H n)=∑ d∈Finset.Icc 1 X,
        if d∣n then (if H n<d then f d else 0) else 0 := by
    rw [←Finset.sum_filter,divisors_as_prefix hn]
    rfl
  calc
    _ = ∑ n∈Finset.Icc 1 X,∑ d∈Finset.Icc 1 X,
        w n*(if d∣n then (if H n<d then f d else 0) else 0) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [he n hn,Finset.mul_sum]
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _
      by_cases hd : d∣n <;> by_cases hH : H n<d <;> simp [hd,hH,mul_comm]

theorem actual_packet_eq_scalar (X : ℕ) (H : ℕ → ℕ) (w : ℕ → ℂ)
    (hH : ∀ n∈Finset.Icc 1 X,0<H n ∧ H n≤n) :
    packet X H w=∑ d∈Finset.Icc 1 X,(ArithmeticFunction.vonMangoldt d : ℂ)*
      (∑ n∈Finset.Icc 1 X,if d∣n ∧ H n<d then w n else 0) := by
  rw [packet_eq_old_tail X H w hH,joined_tail_eq_scalar]

/-- No relative prefix suppresses an ordinary prime while its unit end
is excluded. This is an exact actual-integer delta test. -/
theorem prefixGcd_prime {p H : ℕ} (hp : p.Prime) (hH : 0<H) (hHp : H<p) :
    prefixGcd p H=p := by
  have hd : prefixGcd p H∣p := by
    simpa only [prefixGcd,Nat.choose_one_right] using
      Finset.gcd_dvd (f := p.choose)
        (show 1∈Finset.Icc 1 H from Finset.mem_Icc.mpr ⟨le_rfl,by omega⟩)
  have hv := prefixGcd_factorization hp hH hHp.le
  rw [hp.factorization_self,Nat.log_of_lt hHp,Nat.sub_zero] at hv
  rcases hp.eq_one_or_self_of_dvd (prefixGcd p H) hd with he | he
  · simp only [he,Nat.factorization_one,Finsupp.zero_apply] at hv
    omega
  · exact he

/-- Free outer-weight bounds cannot follow from the complete prefix
identity; a retained genuine prime provides an arbitrarily large test. -/
theorem no_free_weight_bound {X p : ℕ} (hp : p.Prime) (hpX : p≤X)
    (H : ℕ → ℕ) (hH : 0<H p) (hHp : H p<p) (B : ℝ) :
    ¬∀ w : ℕ → ℂ,‖packet X H w‖≤B := by
  intro h
  have hz := (ArithmeticOperatorGramAudit.scalar_bound_forall_weights_iff
    (Finset.Icc 1 X) (fun n => (Real.log (prefixGcd n (H n)) : ℂ)) B).mp h |>.2
  have he := hz p (Finset.mem_Icc.mpr ⟨hp.one_le,hpX⟩)
  rw [prefixGcd_prime hp hH hHp,Complex.ofReal_eq_zero] at he
  exact (Real.log_pos (by exact_mod_cast hp.one_lt)).ne' he

/-- Complete third-prefix array before its SINGLE explicit small head. -/
def thirdCompleted (n : ℕ) : ℂ := (ArithmeticFunction.vonMangoldt n : ℂ)+
  zetaDilationCoefficient 2 (fun d => (ArithmeticFunction.vonMangoldt d : ℂ)) n

/-- Every small cutoff head is retained, including the empty prefix at 2. -/
theorem third_literal_all_heads (n : ℕ) :
    (Real.log (prefixGcd n (n/3)) : ℂ)=
      thirdCompleted n-zetaFiniteCoefficient {2} (fun _ => (Real.log 2 : ℂ)) n := by
  by_cases hn : 3≤n
  · rw [third_prefix_eq hn]
    simp only [thirdCompleted,zetaDilationCoefficient,zetaFiniteCoefficient]
    have h2 : n∉({2} : Finset ℕ) := by simp; omega
    rw [ite_eq_right h2,sub_zero]
  · have he : n=0 ∨ n=1 ∨ n=2 := by omega
    rcases he with rfl | rfl | rfl <;>
      norm_num [prefixGcd,thirdCompleted,zetaDilationCoefficient,zetaFiniteCoefficient,
        ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]

/-- Finite cofactor symbol of the first incomplete proportional prefix. -/
def thirdMultiplier (s : ℂ) : ℂ := 1+zetaPrimeFeature s 2

/-- Meromorphic continuation; its defining prime series is asserted only
on Re(s)>1, and the head and EVERY proper prime power are retained. -/
def thirdResponse (s : ℂ) : ℂ :=
  thirdMultiplier s*(-logDeriv riemannZeta s)-(Real.log 2 : ℂ)*zetaPrimeFeature s 2

theorem third_euler_response {s : ℂ} (hs : 1<s.re) :
    LSeries (fun n => (Real.log (prefixGcd n (n/3)) : ℂ)) s=thirdResponse s := by
  have hm := (ArithmeticFunction.LSeriesSummable_vonMangoldt hs).LSeriesHasSum
  rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs] at hm
  have hd := LSeriesHasSum_zetaDilationCoefficient (by norm_num : 0<(2 : ℕ))
    (by simp : (ArithmeticFunction.vonMangoldt 0 : ℂ)=0) hm
  have hh := LSeriesHasSum_zetaFiniteCoefficient {2}
    (fun _ => (Real.log 2 : ℂ)) (by simp) s
  have ht := ((hm.add hd).sub hh).LSeries_eq
  have he : (fun n => (Real.log (prefixGcd n (n/3)) : ℂ))=
      (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))+
        zetaDilationCoefficient 2 (fun d => (ArithmeticFunction.vonMangoldt d : ℂ))-
          zetaFiniteCoefficient {2} (fun _ => (Real.log 2 : ℂ)) := by
    funext n
    simpa only [thirdCompleted,Pi.sub_apply,Pi.add_apply] using third_literal_all_heads n
  rw [he,ht]
  simp only [thirdResponse,thirdMultiplier,zetaFiniteDirichletSeries,Finset.sum_singleton,
    logDeriv_apply,neg_div]
  ring

/-- Full fixed height, INCLUDING the cofactor phase on the dilation. -/
theorem phased_third_euler_response (y : ℝ) {s : ℂ} (hs : 1<s.re) :
    LSeries (fun n => (Real.log (prefixGcd n (n/3)) : ℂ)*
      SuzukiCarryCorrelation.primePhase y n) s=thirdResponse (s+I*y) := by
  rw [ArithmeticOperatorGammaTwistAudit.LSeries_primePhase]
  exact third_euler_response (by simpa using hs)

theorem thirdMultiplier_analytic (s : ℂ) : AnalyticAt ℂ thirdMultiplier s := by
  unfold thirdMultiplier zetaPrimeFeature
  fun_prop

/-- A quantitative nonzero actual-source factor on the right half-plane. -/
theorem thirdMultiplier_norm_lower (s : ℂ) :
    1-Real.exp (-s.re*Real.log 2)≤‖thirdMultiplier s‖ := by
  have h := norm_sub_norm_le (1 : ℂ) (-zetaPrimeFeature s 2)
  simpa only [norm_one,norm_neg,sub_neg_eq_add,thirdMultiplier,
    norm_zetaPrimeFeature,zetaPrimeExpWeight,Nat.cast_ofNat] using h

theorem thirdMultiplier_ne_zero {s : ℂ} (hs : 0<s.re) : thirdMultiplier s≠0 := by
  have hlog : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hlt : Real.exp (-s.re*Real.log 2)<1 := Real.exp_lt_one_iff.mpr (by nlinarith)
  intro hz
  have hl := thirdMultiplier_norm_lower s
  rw [hz,norm_zero] at hl
  linarith

/-- Density removal before any estimate; no prime head or finite cofactor
phase is deleted. The source below remains nonzero. -/
def thirdCenteredResponse (s : ℂ) : ℂ :=
  thirdMultiplier s*ArithmeticOperatorKummerMinimumAudit.centeredResponse s-
    (Real.log 2 : ℂ)*zetaPrimeFeature s 2

theorem third_centered_eq (s : ℂ) :
    thirdCenteredResponse s=thirdResponse s-thirdMultiplier s/(s-1) := by
  simp only [thirdCenteredResponse,thirdResponse,
    ArithmeticOperatorKummerMinimumAudit.centeredResponse,
    ArithmeticOperatorKummerMinimumAudit.response,div_eq_mul_inv]
  ring

/-- The removed density has an exact analytic germ, not a floating check. -/
theorem third_density_analytic :
    ∃ E : ℂ → ℂ,AnalyticAt ℂ E 1 ∧ thirdCenteredResponse=ᶠ[𝓝[≠] (1 : ℂ)] E := by
  obtain ⟨E,hE,he⟩ := ArithmeticOperatorKummerMinimumAudit.centered_density_analytic
  refine ⟨fun s => thirdMultiplier s*E s-(Real.log 2 : ℂ)*zetaPrimeFeature s 2,
    ((thirdMultiplier_analytic 1).mul hE).sub (by unfold zetaPrimeFeature; fun_prop),?_⟩
  filter_upwards [he] with s hs
  simp only [thirdCenteredResponse,hs]

/-- Every genuine local zero and its ACTUAL analytic multiplicity is
retained by the incomplete prefix response; no exposure is assumed. -/
theorem third_actual_zero_source (rho : NontrivialZetaZero) :
    Tendsto (fun s : ℂ => (s-rho.1)*thirdResponse s) (𝓝[≠] rho.1)
      (𝓝 (-(analyticZetaZeroMultiplicity rho : ℂ)*thirdMultiplier rho.1)) := by
  have hp : Tendsto thirdMultiplier (𝓝[≠] rho.1) (𝓝 (thirdMultiplier rho.1)) :=
    (thirdMultiplier_analytic rho.1).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hz := ArithmeticOperatorKummerMinimumAudit.actual_zero_source rho
  have hc : ContinuousAt (fun s : ℂ => (s-rho.1)*(Real.log 2 : ℂ)*
      zetaPrimeFeature s 2) rho.1 := by unfold zetaPrimeFeature; fun_prop
  have hh : Tendsto (fun s : ℂ => (s-rho.1)*(Real.log 2 : ℂ)*
      zetaPrimeFeature s 2) (𝓝[≠] rho.1) (𝓝 0) := by
    simpa only [sub_self,zero_mul] using hc.tendsto.mono_left nhdsWithin_le_nhds
  convert (hz.mul hp).sub hh using 1
  · ext s
    simp only [thirdResponse,ArithmeticOperatorKummerMinimumAudit.response]
    ring
  · simp only [sub_zero]

theorem third_centered_actual_zero_source (rho : NontrivialZetaZero) :
    Tendsto (fun s : ℂ => (s-rho.1)*thirdCenteredResponse s) (𝓝[≠] rho.1)
      (𝓝 (-(analyticZetaZeroMultiplicity rho : ℂ)*thirdMultiplier rho.1)) := by
  have hc : ContinuousAt (fun s : ℂ => (s-rho.1)*(thirdMultiplier s/(s-1))) rho.1 := by
    exact (continuousAt_id.sub continuousAt_const).mul
      ((thirdMultiplier_analytic rho.1).continuousAt.div
        (continuousAt_id.sub continuousAt_const) (sub_ne_zero.mpr rho.2.2.2))
  have hh : Tendsto (fun s : ℂ => (s-rho.1)*(thirdMultiplier s/(s-1)))
      (𝓝[≠] rho.1) (𝓝 0) := by
    simpa only [sub_self,zero_mul] using hc.tendsto.mono_left nhdsWithin_le_nhds
  have h := (third_actual_zero_source rho).sub hh
  simpa only [third_centered_eq,mul_sub,sub_zero] using h

theorem third_source_ne_zero (rho : NontrivialZetaZero) (hrho : 0<rho.1.re) :
    -(analyticZetaZeroMultiplicity rho : ℂ)*thirdMultiplier rho.1≠0 :=
  mul_ne_zero (ArithmeticOperatorKummerMinimumAudit.source_ne_zero rho)
    (thirdMultiplier_ne_zero hrho)

/-- Pole removal does not turn the incomplete prefix into a paid source.
This failure holds at every genuine right-half zero, with all multiplicities. -/
theorem third_centered_not_source_small (rho : NontrivialZetaZero) (hrho : 0<rho.1.re) :
    ¬Tendsto (fun s : ℂ => (s-rho.1)*thirdCenteredResponse s)
      (𝓝[≠] rho.1) (𝓝 0) := by
  intro h
  exact third_source_ne_zero rho hrho
    (tendsto_nhds_unique (third_centered_actual_zero_source rho) h)

/-- An analytic regularization would already eliminate the actual zeta
zero. It cannot be supplied by the exact prefix GCD observation alone. -/
theorem third_centered_no_analytic_extension (rho : NontrivialZetaZero)
    (hrho : 0<rho.1.re) :
    ¬∃ E : ℂ → ℂ,AnalyticAt ℂ E rho.1 ∧
      thirdCenteredResponse=ᶠ[𝓝[≠] rho.1] E := by
  rintro ⟨E,hE,he⟩
  have hc : ContinuousAt (fun s : ℂ => (s-rho.1)*E s) rho.1 :=
    (continuousAt_id.sub continuousAt_const).mul hE.continuousAt
  have hz : Tendsto (fun s : ℂ => (s-rho.1)*E s) (𝓝[≠] rho.1) (𝓝 0) := by
    simpa only [sub_self,zero_mul] using hc.tendsto.mono_left nhdsWithin_le_nhds
  apply third_centered_not_source_small rho hrho
  apply hz.congr'
  filter_upwards [he] with s hs
  rw [hs]

/-- The arbitrary fixed positive prefix is also exact at n=0 and when
H passes the literal unit endpoint. -/
theorem actual_tail_all_labels {H : ℕ} (hH : 0<H) (n : ℕ) :
    (Real.log (prefixGcd n H) : ℂ)=
      tailObservation (fun d => (ArithmeticFunction.vonMangoldt d : ℂ)) n H := by
  by_cases hn : n=0
  · subst n
    have he : prefixGcd 0 H=0 := by
      apply Finset.gcd_eq_zero_iff.mpr
      intro k hk
      have hk0 : k≠0 := by have := (Finset.mem_Icc.mp hk).1; omega
      exact Nat.choose_eq_zero_of_lt (by omega)
    simp only [he,Nat.cast_zero,Real.log_zero,Complex.ofReal_zero,
      tailObservation,Nat.divisors_zero,Finset.sum_empty]
  by_cases hHn : H≤n
  · exact actual_tailObservation hH hHn
  · rw [prefixGcd_eq_one_of_ge (by omega) (by omega)]
    simp only [Nat.cast_one,Real.log_one,Complex.ofReal_zero,tailObservation]
    symm
    apply Finset.sum_eq_zero
    intro d hd
    have hl := Nat.le_of_dvd (by omega : 0<n) (Nat.dvd_of_mem_divisors hd)
    exact ite_eq_right (by omega)

/-- The complete fixed-prefix Euler continuation, with its full small
prime-power subtraction. It has no logarithmic zero pole. -/
def fixedResponse (H : ℕ) (s : ℂ) : ℂ :=
  -deriv riemannZeta s-riemannZeta s*
    zetaFiniteDirichletSeries (Finset.Icc 1 H) (fun d => (ArithmeticFunction.vonMangoldt d : ℂ)) s

theorem fixed_euler_response {H : ℕ} (hH : 0<H) {s : ℂ} (hs : 1<s.re) :
    LSeries (fun n => (Real.log (prefixGcd n H) : ℂ)) s=fixedResponse H s := by
  let f : ℕ → ℂ := fun d => (ArithmeticFunction.vonMangoldt d : ℂ)
  let g := f-zetaFiniteCoefficient (Finset.Icc 1 H) f
  have he : (fun n => (Real.log (prefixGcd n H) : ℂ))=
      LSeries.convolution g (1 : ℕ → ℂ) := by
    funext n
    rw [actual_tail_all_labels hH n,LSeries.convolution_def]
    dsimp only
    rw [Nat.sum_divisorsAntidiagonal (fun d a => g d*(1 : ℕ → ℂ) a)]
    unfold tailObservation
    apply Finset.sum_congr rfl
    intro d hd
    have hp := Nat.pos_of_dvd_of_pos (Nat.dvd_of_mem_divisors hd)
      (Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_divisors hd))
    dsimp only [g,Pi.sub_apply,Pi.one_apply]
    simp only [mul_one,zetaFiniteCoefficient,Finset.mem_Icc]
    by_cases hdl : d≤H <;> simp [hdl,show 1≤d by omega,f]
  have hf : LSeriesSummable f s := ArithmeticFunction.LSeriesSummable_vonMangoldt hs
  have hc := LSeriesHasSum_zetaFiniteCoefficient (Finset.Icc 1 H) f
    (by simp) s
  have hh := hf.sub hc.LSeriesSummable
  rw [he,LSeries_convolution' hh (LSeriesHasSum_one hs).LSeriesSummable,
    LSeries_sub hf hc.LSeriesSummable,hc.LSeries_eq,(LSeriesHasSum_one hs).LSeries_eq]
  change (LSeries (fun d => (ArithmeticFunction.vonMangoldt d : ℂ)) s-
    zetaFiniteDirichletSeries (Finset.Icc 1 H) f s)*riemannZeta s=fixedResponse H s
  rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs]
  have hz := riemannZeta_ne_zero_of_one_lt_re hs
  simp only [fixedResponse,f,div_eq_mul_inv]
  field_simp [hz]

/-- The fixed-prefix zero source fails at EVERY actual nontrivial zero;
this is an analytic continuation theorem, not a convergent Euler sum
asserted inside the zero strip. -/
theorem fixed_zero_source_blind (H : ℕ) (rho : NontrivialZetaZero) :
    Tendsto (fun s : ℂ => (s-rho.1)*fixedResponse H s) (𝓝[≠] rho.1) (𝓝 0) := by
  have hA := analyticAt_riemannZeta_nontrivialZero rho
  have hF : AnalyticAt ℂ (fixedResponse H) rho.1 := by
    unfold fixedResponse zetaFiniteDirichletSeries zetaPrimeFeature
    exact hA.deriv.neg.sub (hA.mul (by fun_prop))
  have hc : ContinuousAt (fun s : ℂ => (s-rho.1)*fixedResponse H s) rho.1 :=
    (continuousAt_id.sub continuousAt_const).mul hF.continuousAt
  simpa only [sub_self,zero_mul] using hc.tendsto.mono_left nhdsWithin_le_nhds

end RiemannGaussian.ArithmeticOperatorKummerPrefixAudit

#lint+ in RiemannGaussian.ArithmeticOperatorKummerPrefixAudit

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut declarations : Nat := 0
  let mut theorems : Nat := 0
  let mut reports : Array Json := #[]
  for (n,ci) in env.constants.toList do
    if env.isImportedConst n then continue
    declarations := declarations+1
    if ci.isAxiom then throwError "Project-defined axiom: {n}"
    let axs ← Lean.collectAxioms n
    for ax in axs do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom in {n}: {ax}"
    if ci.isTheorem then theorems := theorems+1
    reports := reports.push (Json.mkObj [("declaration",toJson n.toString),
      ("isTheorem",toJson ci.isTheorem),("axioms",toJson (axs.map Name.toString))])
  unless declarations>0 do throwError "Empty constrained Kummer-prefix audit."
  logInfo m!"Kummer-prefix audit: {declarations} declarations, {theorems} theorems; only standard axioms."
  IO.FS.createDirAll ".lake/arithmetic-operator-kummer-prefix"
  IO.FS.writeFile ".lake/arithmetic-operator-kummer-prefix/axioms.json"
    (Json.mkObj [("scope",toJson "literal binomial prefix, exact all-power divisor tail, actual retained zero and complete moving-mask collapse"),
      ("onlyStandardAxioms",toJson true),("namespaceLinters",toJson (15:Nat)),
      ("allLocalDeclarationsByModuleProvenance",toJson true),
      ("declarations",toJson declarations),("theoremsIncludingGeneratedHelpers",toJson theorems),
      ("declarationAxioms",Json.arr reports)]).pretty
