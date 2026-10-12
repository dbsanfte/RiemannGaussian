/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import scripts.ArithmeticOperatorKummerMinimumAudit
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.Tactic.Linter
import Lean.Util.CollectAxioms

/-!
# Even-index binomial rows: literal modular/Kummer source gate

This is a NON-prefix split mask. The empty row at n=2 is kept with
its literal gcd zero; no infinite prime sum is attached to that head.
Every odd-prime support is classified, including all proper powers.
Large-prime valuations are then computed before any estimate.
-/

set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
open scoped BigOperators Classical Topology
namespace RiemannGaussian.ArithmeticOperatorKummerParityAudit
open Complex Filter

/-- Every proper even split, with the exact unit endpoints excluded. -/
def evenSplits (n : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (n-1)).filter (fun k => k%2=0)

/-- Literal common divisor, before any normalization or prime join. -/
def evenGcd (n : ℕ) : ℕ := (evenSplits n).gcd n.choose

theorem mem_evenSplits {n k : ℕ} :
    k∈evenSplits n ↔ 0<k ∧ k<n ∧ k%2=0 := by
  simp only [evenSplits,Finset.mem_filter,Finset.mem_Icc]
  omega

theorem evenGcd_two : evenGcd 2=0 := by
  have hs : evenSplits 2=∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro k hk
    have := mem_evenSplits.mp hk
    omega
  simp only [evenGcd,hs,Finset.gcd_empty]

theorem evenGcd_ne_zero {n : ℕ} (hn : 4≤n) : evenGcd n≠0 := by
  apply Finset.gcd_ne_zero_iff.mpr
  exact ⟨2,mem_evenSplits.mpr ⟨by norm_num,by omega,by norm_num⟩,
    Nat.choose_ne_zero (by omega)⟩

theorem dvd_evenGcd_iff (p n : ℕ) :
    p∣evenGcd n ↔ ∀ k,0<k → k<n → k%2=0 → p∣n.choose k := by
  rw [evenGcd,Finset.dvd_gcd_iff]
  simp only [mem_evenSplits,and_imp]

/-- Exact Lucas divisibility relation, with both literal digit factors. -/
theorem dvd_choose_iff_digits {p : ℕ} (hp : p.Prime) (n k : ℕ) :
    p∣n.choose k ↔ p∣(n%p).choose (k%p)*(n/p).choose (k/p) := by
  let : Fact p.Prime := ⟨hp⟩
  have he := Choose.choose_modEq_choose_mod_mul_choose_div_nat (p := p) (n := n) (k := k)
  rw [Nat.dvd_iff_mod_eq_zero,Nat.dvd_iff_mod_eq_zero]
  rw [he]

/-- A proper even split below the first modulus already refutes common
divisibility when the lowest base-p digit is at least two. -/
theorem evenGcd_not_dvd_of_low_digit {p n : ℕ} (hp : p.Prime)
    (hn : 2<n) (hb : 2≤n%p) : ¬p∣evenGcd n := by
  intro hd
  have h := (dvd_evenGcd_iff p n).mp hd 2 (by norm_num) hn (by norm_num)
  have hp2 : 2<p := hb.trans_lt (Nat.mod_lt n hp.pos)
  rw [dvd_choose_iff_digits hp,Nat.mod_eq_of_lt hp2,Nat.div_eq_of_lt hp2,
    Nat.choose_zero_right,mul_one] at h
  have hc := hp.coprime_choose_of_lt (Nat.mod_lt n hp.pos) hb
  change p.gcd ((n%p).choose 2)=1 at hc
  rw [Nat.gcd_eq_left h] at hc
  exact hp.ne_one hc

/-- Literal parity of the upper digit when n is even and its low digit
is 0 or 1. No smooth residue model is substituted. -/
theorem quotient_parity {p n b : ℕ} (hpo : p%2=1) (hne : n%2=0)
    (hb : n%p=b) (hb2 : b<2) : (n/p)%2=b := by
  have he := congrArg (fun a : ℕ => a%2) (Nat.mod_add_div n p)
  rw [hb,Nat.add_mod,Nat.mul_mod,hpo,one_mul,Nat.mod_eq_of_lt hb2,hne] at he
  have ha := Nat.mod_lt (n/p) (by norm_num : (0 : ℕ)<2)
  omega

/-- Zero lower digit rescales the WHOLE modular split mask exactly.
No complete binomial row replaces its parity restriction. -/
theorem evenGcd_zero_digit {p n : ℕ} (hp : p.Prime) (hp2 : 2<p)
    (hb : n%p=0) :
    p∣evenGcd n ↔ p∣evenGcd (n/p) := by
  have hpo : p%2=1 := hp.eq_two_or_odd.resolve_left (by omega)
  rw [dvd_evenGcd_iff,dvd_evenGcd_iff]
  constructor
  · intro h k hk0 hkn hke
    have heq : n=p*(n/p) := by have := Nat.mod_add_div n p; omega
    have hn : 0<p*k := Nat.mul_pos hp.pos hk0
    have hlt : p*k<n := by rw [heq]; exact Nat.mul_lt_mul_of_pos_left hkn hp.pos
    have hm : (p*k)%2=0 := by rw [Nat.mul_mod,hpo,hke]
    have hd := h (p*k) hn hlt hm
    rw [dvd_choose_iff_digits hp,hb,Nat.mul_mod_right,Nat.mul_div_right _ hp.pos,
      Nat.choose_zero_right,one_mul] at hd
    exact hd
  · intro h k hk0 hkn hke
    rw [dvd_choose_iff_digits hp,hb]
    by_cases hkm : k%p=0
    · rw [hkm,Nat.choose_zero_right,one_mul]
      have heq : k=p*(k/p) := by have := Nat.mod_add_div k p; omega
      have hneq : n=p*(n/p) := by have := Nat.mod_add_div n p; omega
      have hlo : 0<k/p := by nlinarith
      have hhi : k/p<n/p := by nlinarith
      have hpar : (k/p)%2=0 := by
        have he := congrArg (fun a : ℕ => a%2) heq
        simpa only [hke,Nat.mul_mod,hpo,one_mul,Nat.mod_mod,eq_comm] using he
      exact h (k/p) hlo hhi hpar
    · rw [Nat.choose_eq_zero_of_lt (by omega : 0<k%p),zero_mul]
      exact dvd_zero _

/-- Low digit one converts the parity-restricted row to the full
interior upper-digit row. The two endpoints are checked literally. -/
theorem evenGcd_one_digit {p n : ℕ} (hp : p.Prime) (hp2 : 2<p)
    (hne : n%2=0) (hb : n%p=1) :
    p∣evenGcd n ↔ ∀ l,0<l → l<n/p → p∣(n/p).choose l := by
  have hpo : p%2=1 := hp.eq_two_or_odd.resolve_left (by omega)
  have ha : (n/p)%2=1 := quotient_parity hpo hne hb (by norm_num)
  have hneq : n=1+p*(n/p) := by have := Nat.mod_add_div n p; omega
  rw [dvd_evenGcd_iff]
  constructor
  · intro h l hl0 hla
    let k := l%2+p*l
    have hr : l%2<p := (Nat.mod_lt l (by norm_num : (0 : ℕ)<2)).trans hp2
    have hk0 : 0<k := by
      exact (Nat.mul_pos hp.pos hl0).trans_le (Nat.le_add_left _ _)
    have hkn : k<n := by dsimp [k]; nlinarith [Nat.mod_lt l (by norm_num : (0 : ℕ)<2)]
    have hke : k%2=0 := by
      dsimp [k]
      rw [Nat.add_mod,Nat.mul_mod,hpo,one_mul,Nat.mod_mod]
      have hh := Nat.mod_lt l (by norm_num : (0 : ℕ)<2)
      omega
    have hkm : k%p=l%2 := by simp only [k,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt hr]
    have hkd : k/p=l := by
      dsimp only [k]
      rw [Nat.add_mul_div_left (l%2) l hp.pos,Nat.div_eq_of_lt hr,zero_add]
    have hc : (1 : ℕ).choose (l%2)=1 := by
      have hh := Nat.mod_lt l (by norm_num : (0 : ℕ)<2)
      have he : l%2=0 ∨ l%2=1 := by omega
      rcases he with he | he <;> simp only [he,Nat.choose_zero_right,Nat.choose_self]
    have hd := h k hk0 hkn hke
    simpa only [dvd_choose_iff_digits hp,hb,hkm,hkd,hc,one_mul] using hd
  · intro h k hk0 hkn hke
    have hk2 : 2≤k := by omega
    rw [dvd_choose_iff_digits hp,hb]
    by_cases hkm : k%p≤1
    · have heq : k=k%p+p*(k/p) := (Nat.mod_add_div k p).symm
      have hpar := congrArg (fun a : ℕ => a%2) heq
      simp only [hke,Nat.add_mod,Nat.mul_mod,hpo,one_mul,Nat.mod_mod] at hpar
      have hlo : 0<k/p := by
        by_contra hh
        have hh0 : k/p=0 := Nat.eq_zero_of_not_pos hh
        have hkk : k=k%p := by simpa only [hh0,mul_zero,add_zero] using heq
        have hh1 : k≤1 := by rw [hkk]; exact hkm
        exact Nat.not_succ_le_self 1 (hk2.trans hh1)
      have hhi : k/p<n/p := by
        have hle : k/p≤n/p := Nat.div_le_div_right hkn.le
        have hh : k/p≠n/p := by
          intro he
          have hr0 : k%p=0 := by rw [he] at heq; omega
          rw [hr0,he,ha] at hpar
          norm_num at hpar
        omega
      exact dvd_mul_of_dvd_right (h (k/p) hlo hhi) _
    · rw [Nat.choose_eq_zero_of_lt (by omega : 1<k%p),zero_mul]
      exact dvd_zero _

/-- The whole upper row is divisible precisely for one prime power.
This is Lucas' CLASSICAL criterion, not a new prime estimate. -/
theorem whole_row_divisible_iff_power {p a : ℕ} (hp : p.Prime) (ha : 0<a) :
    (∀ l,0<l → l<a → p∣a.choose l) ↔ ∃ j,a=p^j := by
  let : Fact p.Prime := ⟨hp⟩
  constructor
  · intro h
    refine ⟨multiplicity p a,Choose.eq_pow_multiplicity_of_choose_modEq_zero_nat ha ?_⟩
    intro l hl
    rw [Nat.modEq_zero_iff_dvd]
    exact h l (by have := Finset.mem_Icc.mp hl; omega)
      (by have := Finset.mem_Icc.mp hl; omega)
  · rintro ⟨j,rfl⟩ l hl0 hl
    exact hp.dvd_choose_pow hl0.ne' (Nat.ne_of_lt hl)

/-- Exact non-prefix support for EVERY odd prime, including ALL powers.
No large-prime truncation is used. This proves the divisibility part of
the classical two-base-p-digit theorem directly from literal Lucas rows. -/
theorem evenGcd_prime_dvd_iff {p n : ℕ} (hp : p.Prime) (hp2 : 2<p)
    (hne : n%2=0) (hn : 2≤n) :
    p∣evenGcd n ↔ ∃ i j : ℕ,n=p^i+p^j := by
  revert hne hn
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hne hn
    by_cases hn2 : n=2
    · subst n
      simp only [evenGcd_two,dvd_zero, true_iff]
      exact ⟨0,0,by norm_num⟩
    have hn' : 2<n := by omega
    have hpo : p%2=1 := hp.eq_two_or_odd.resolve_left (by omega)
    by_cases hb0 : n%p=0
    · have hqpar := quotient_parity hpo hne hb0 (by norm_num)
      have hneq : n=p*(n/p) := by have := Nat.mod_add_div n p; omega
      have hq0 : 0<n/p := by nlinarith
      have hq2 : 2≤n/p := by omega
      have hlt : n/p<n := Nat.div_lt_self (by omega) hp.one_lt
      rw [evenGcd_zero_digit hp hp2 hb0,ih (n/p) hlt hqpar hq2]
      constructor
      · rintro ⟨i,j,hq⟩
        refine ⟨i+1,j+1,?_⟩
        rw [hneq,hq,pow_succ,pow_succ]
        ring
      · rintro ⟨i,j,he⟩
        cases i with
        | zero =>
          cases j with
          | zero => norm_num at he; omega
          | succ j =>
            have hm := congrArg (fun a : ℕ => a%p) he
            simp only [pow_zero,pow_succ,Nat.add_mod,Nat.mul_mod,Nat.mod_self,
              mul_zero,Nat.zero_mod,Nat.mod_eq_of_lt hp.one_lt,Nat.add_zero,hb0] at hm
            exact False.elim (by omega)
        | succ i =>
          cases j with
          | zero =>
            have hm := congrArg (fun a : ℕ => a%p) he
            simp only [pow_zero,pow_succ,Nat.add_mod,Nat.mul_mod,Nat.mod_self,
              mul_zero,Nat.zero_mod,Nat.mod_eq_of_lt hp.one_lt,Nat.zero_add,hb0] at hm
            exact False.elim (by omega)
          | succ j =>
            refine ⟨i,j,?_⟩
            have he' : n=p*(p^i+p^j) := by rw [he,pow_succ,pow_succ]; ring
            rw [he',Nat.mul_div_right _ hp.pos]
    · by_cases hb1 : n%p=1
      · rw [evenGcd_one_digit hp hp2 hne hb1,
          whole_row_divisible_iff_power hp (by
            have he := Nat.mod_add_div n p
            nlinarith)]
        constructor
        · rintro ⟨j,hj⟩
          refine ⟨j+1,0,?_⟩
          have he := Nat.mod_add_div n p
          rw [hb1,hj] at he
          simpa only [pow_succ,pow_zero,mul_comm,add_comm] using he.symm
        · rintro ⟨i,j,he⟩
          cases i with
          | zero =>
            cases j with
            | zero => norm_num at he; omega
            | succ j =>
              refine ⟨j,?_⟩
              rw [he,pow_zero,pow_succ,mul_comm (p^j) p,
                Nat.add_mul_div_left 1 (p^j) hp.pos,Nat.div_eq_of_lt hp.one_lt,zero_add]
          | succ i =>
            cases j with
            | zero =>
              refine ⟨i,?_⟩
              rw [he,pow_zero,add_comm,pow_succ,mul_comm (p^i) p,
                Nat.add_mul_div_left 1 (p^i) hp.pos,Nat.div_eq_of_lt hp.one_lt,zero_add]
            | succ j =>
              have hm := congrArg (fun a : ℕ => a%p) he
              simp only [pow_succ,Nat.add_mod,Nat.mul_mod,Nat.mod_self,mul_zero,
                Nat.zero_mod,Nat.zero_add,hb1] at hm
              exact False.elim (by omega)
      · have hb : 2≤n%p := by omega
        rw [iff_false_left (evenGcd_not_dvd_of_low_digit hp hn' hb)]
        rintro ⟨i,j,he⟩
        cases i with
        | zero =>
          cases j with
          | zero => norm_num at he; omega
          | succ j =>
            have hm := congrArg (fun a : ℕ => a%p) he
            simp only [pow_zero,pow_succ,Nat.add_mod,Nat.mul_mod,Nat.mod_self,
              mul_zero,Nat.zero_mod,Nat.mod_eq_of_lt hp.one_lt,Nat.add_zero] at hm
            omega
        | succ i =>
          cases j with
          | zero =>
            have hm := congrArg (fun a : ℕ => a%p) he
            simp only [pow_zero,pow_succ,Nat.add_mod,Nat.mul_mod,Nat.mod_self,
              mul_zero,Nat.zero_mod,Nat.mod_eq_of_lt hp.one_lt,Nat.zero_add] at hm
            omega
          | succ j =>
            have hm := congrArg (fun a : ℕ => a%p) he
            simp only [pow_succ,Nat.add_mod,Nat.mul_mod,Nat.mod_self,mul_zero,
              Nat.zero_mod,Nat.zero_add] at hm
            omega

/-- The two-power support reduces to two literal incidences ONLY
above the square-root boundary. The other powers remain outside this
theorem and are never called an aggregate paid error. -/
theorem evenGcd_large_dvd_iff {p n : ℕ} (hp : p.Prime) (hp2 : 2<p)
    (hne : n%2=0) (hn : 4≤n) (hlarge : n<p^2) :
    p∣evenGcd n ↔ n=p+1 ∨ n=2*p := by
  rw [evenGcd_prime_dvd_iff hp hp2 hne (by omega)]
  constructor
  · rintro ⟨i,j,he⟩
    have hi : i≤1 := by
      by_contra hh
      have hh' : 2 ≤ i := by omega
      have hl := Nat.pow_le_pow_right hp.pos hh'
      have hle : p^i≤n := by rw [he]; exact Nat.le_add_right _ _
      exact not_le_of_gt hlarge (hl.trans hle)
    have hj : j≤1 := by
      by_contra hh
      have hh' : 2 ≤ j := by omega
      have hl := Nat.pow_le_pow_right hp.pos hh'
      have hle : p^j≤n := by rw [he]; exact Nat.le_add_left _ _
      exact not_le_of_gt hlarge (hl.trans hle)
    have hii : i=0 ∨ i=1 := by omega
    have hjj : j=0 ∨ j=1 := by omega
    rcases hii with rfl | rfl <;> rcases hjj with rfl | rfl <;>
      simp only [pow_zero,pow_one] at he
    · omega
    · exact Or.inl (by omega)
    · exact Or.inl he
    · exact Or.inr (by omega)
  · rintro (he | he)
    · exact ⟨1,0,by simpa only [pow_one,pow_zero] using he⟩
    · exact ⟨1,1,by simpa only [pow_one,two_mul] using he⟩

theorem evenGcd_factorization_le_log {p n : ℕ} (hn : 4≤n) :
    (evenGcd n).factorization p≤Nat.log p n := by
  have hd : evenGcd n∣n.choose 2 :=
    Finset.gcd_dvd (mem_evenSplits.mpr ⟨by norm_num,by omega,by norm_num⟩)
  exact ((Nat.factorization_le_iff_dvd (evenGcd_ne_zero hn)
    (Nat.choose_ne_zero (by omega))).mpr hd p).trans Nat.factorization_choose_le_log

/-- Exact literal large-prime multiplicity, not merely divisibility. -/
theorem evenGcd_large_factorization {p n : ℕ} (hp : p.Prime) (hp2 : 2<p)
    (hne : n%2=0) (hn : 4≤n) (hlarge : n<p^2) :
    (evenGcd n).factorization p=if n=p+1 ∨ n=2*p then 1 else 0 := by
  have hg := evenGcd_ne_zero hn
  have hd : evenGcd n∣n.choose 2 :=
    Finset.gcd_dvd (mem_evenSplits.mpr ⟨by norm_num,by omega,by norm_num⟩)
  have hl := ((Nat.factorization_le_iff_dvd hg
    (Nat.choose_ne_zero (by omega))).mpr hd p).trans
    (Nat.factorization_choose_le_one (k := 2) hlarge)
  have he := evenGcd_large_dvd_iff hp hp2 hne hn hlarge
  have hv := hp.dvd_iff_one_le_factorization hg
  split_ifs with h
  · have h1 := hv.mp (he.mpr h)
    omega
  · have h0 : ¬1≤(evenGcd n).factorization p := fun h1 => h (he.mp (hv.mpr h1))
    omega

/-- Every omitted odd-prime incidence has a genuine higher-power
geometry. This is support, not a global norm payment of its sum. -/
theorem nonleading_incidence_square_le {p n : ℕ} (hp : p.Prime) (hp2 : 2<p)
    (hne : n%2=0) (hn : 4≤n) (hd : p∣evenGcd n)
    (hshift : n≠p+1) (hdilate : n≠2*p) : p^2≤n := by
  by_contra hh
  have h := (evenGcd_large_dvd_iff hp hp2 hne hn (by omega)).mp hd
  rcases h with h | h <;> contradiction

private theorem digitSum_pow_mul {p m : ℕ} (hp : 1<p) (hm : 0<m) (i : ℕ) :
    (p.digits (p^i*m)).sum=(p.digits m).sum := by
  rw [Nat.digits_base_pow_mul hp hm,List.sum_append,List.sum_replicate]
  simp only [nsmul_zero,zero_add]

private theorem digitSum_power {p : ℕ} (hp : 1<p) (i : ℕ) :
    (p.digits (p^i)).sum=1 := by
  have h := digitSum_pow_mul hp (by norm_num : (0 : ℕ)<1) i
  simpa only [mul_one,Nat.digits_of_lt p 1 (by norm_num) hp,
    List.sum_cons,List.sum_nil,add_zero] using h

/-- Exactly two literal base-p digits, also when the exponents coincide. -/
private theorem digitSum_two_powers {p : ℕ} (hp : 2<p) (i j : ℕ) :
    (p.digits (p^i+p^j)).sum=2 := by
  wlog hij : i≤j generalizing i j
  · simpa only [add_comm] using this j i (by omega)
  obtain ⟨e,rfl⟩ := Nat.exists_eq_add_of_le hij
  have he : p^i+p^(i+e)=p^i*(1+p^e) := by rw [pow_add]; ring
  rw [he,digitSum_pow_mul (by omega) (by positivity)]
  cases e with
  | zero =>
    simp only [pow_zero]
    rw [show (1 : ℕ)+1=2 by norm_num,Nat.digits_of_lt p 2 (by norm_num) hp]
    norm_num
  | succ e =>
    rw [pow_succ',Nat.digits_add p (by omega) 1 (p^e) (by omega) (Or.inl (by norm_num)),
      List.sum_cons,digitSum_power (by omega)]

/-- A concrete proper EVEN split has exactly one p-adic carry for
every two-power label. No split witness is shared between distinct primes. -/
theorem two_power_even_one_carry {p n : ℕ} (hp : p.Prime) (hp2 : 2<p)
    (hn : 2<n) {i j : ℕ} (he : n=p^i+p^j) :
    ∃ k∈evenSplits n,(n.choose k).factorization p=1 := by
  wlog hij : i≤j generalizing i j
  · exact this (i := j) (j := i) (by simpa only [add_comm] using he) (by omega)
  have hj : 0<j := by
    by_contra hh
    have hj0 : j=0 := Nat.eq_zero_of_not_pos hh
    have hi0 : i=0 := by omega
    norm_num [hi0,hj0] at he
    omega
  let k := (p-1)*p^(j-1)
  have hp0 : 0<p := hp.pos
  have hpow : p^j=p*p^(j-1) := by
    rw [← pow_succ',Nat.sub_add_cancel hj]
  have hk0 : 0<k := Nat.mul_pos (by omega) (Nat.pow_pos hp0)
  have hkn : k<n := by
    have hh : k<p^j := by
      dsimp only [k]
      rw [hpow]
      exact Nat.mul_lt_mul_of_pos_right (by omega) (Nat.pow_pos hp0)
    exact hh.trans_le (by rw [he]; exact Nat.le_add_left _ _)
  have hpo : p%2=1 := hp.eq_two_or_odd.resolve_left (by omega)
  have hkpar : k%2=0 := by
    have hh : (p-1)%2=0 := by omega
    simp only [k,Nat.mul_mod,hh,zero_mul,Nat.zero_mod]
  refine ⟨k,mem_evenSplits.mpr ⟨hk0,hkn,hkpar⟩,?_⟩
  let : Fact p.Prime := ⟨hp⟩
  have hval := sub_one_mul_padicValNat_choose_eq_sub_sum_digits
    (p := p) hkn.le
  have hkdigits : (p.digits k).sum=p-1 := by
    have h := digitSum_pow_mul hp.one_lt (show 0<p-1 by omega) (j-1)
    simpa only [k,mul_comm,Nat.digits_of_lt p (p-1) (by omega) (by omega),
      List.sum_cons,List.sum_nil,add_zero] using h
  have hrest : (p.digits (n-k)).sum=2 := by
    have hsplit : p*p^(j-1)=k+p^(j-1) := by
      dsimp only [k]
      rw [← add_one_mul]
      congr 1
      omega
    have hr : n-k=p^i+p^(j-1) := by
      apply Nat.sub_eq_of_eq_add
      rw [he,hpow,hsplit]
      omega
    rw [hr,digitSum_two_powers hp2]
  have hndigits : (p.digits n).sum=2 := by rw [he,digitSum_two_powers hp2]
  rw [hkdigits,hrest,hndigits,Nat.add_sub_cancel] at hval
  rw [Nat.factorization_def _ hp]
  apply Nat.eq_of_mul_eq_mul_left (show 0<p-1 by omega)
  simpa only [mul_one] using hval

/-- The complete odd-prime valuation is exactly zero or one. All
higher-power labels remain; only the valuation within each row is one. -/
theorem evenGcd_factorization {p n : ℕ} (hp : p.Prime) (hp2 : 2<p)
    (hne : n%2=0) (hn : 4≤n) :
    (evenGcd n).factorization p=if ∃ i j : ℕ,n=p^i+p^j then 1 else 0 := by
  have hg := evenGcd_ne_zero hn
  have hd := evenGcd_prime_dvd_iff hp hp2 hne (by omega)
  have hv := hp.dvd_iff_one_le_factorization hg
  split_ifs with h
  · obtain ⟨i,j,he⟩ := h
    obtain ⟨k,hk,hv1⟩ := two_power_even_one_carry hp hp2 (by omega) he
    have hl := (Nat.factorization_le_iff_dvd hg
      (Nat.choose_ne_zero (mem_evenSplits.mp hk).2.1.le)).mpr
      (Finset.gcd_dvd hk) p
    rw [hv1] at hl
    have hlo := hv.mp (hd.mpr ⟨i,j,he⟩)
    omega
  · have hz : ¬1≤(evenGcd n).factorization p := fun h1 => h (hd.mp (hv.mpr h1))
    omega

/-- Literal binary scaling keeps every carry and cancels no order. -/
theorem choose_double_two_factorization {a k : ℕ} (hk0 : 0<k) (hka : k<a) :
    ((2*a).choose (2*k)).factorization 2=(a.choose k).factorization 2 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := sub_one_mul_padicValNat_choose_eq_sub_sum_digits
    (p := 2) hka.le
  have h2 := sub_one_mul_padicValNat_choose_eq_sub_sum_digits
    (p := 2) (show 2*k≤2*a by omega)
  have ha0 : 0<a := hk0.trans hka
  have hak : 0<a-k := by omega
  have da := digitSum_pow_mul (by norm_num : (1 : ℕ)<2) ha0 1
  have dk := digitSum_pow_mul (by norm_num : (1 : ℕ)<2) hk0 1
  have dr := digitSum_pow_mul (by norm_num : (1 : ℕ)<2) hak 1
  simp only [pow_one] at da dk dr
  rw [show 2*a-2*k=2*(a-k) by omega,da,dk,dr] at h2
  simp only [show (2 : ℕ)-1=1 by norm_num,one_mul] at h1 h2
  rw [Nat.factorization_def _ Nat.prime_two,Nat.factorization_def _ Nat.prime_two]
  exact h2.trans h1.symm

/-- The exceptional prime TWO is retained explicitly. -/
theorem evenGcd_two_dvd_iff {n : ℕ} (hne : n%2=0) (hn : 4≤n) :
    2∣evenGcd n ↔ ∃ j : ℕ,n=2^(j+1) := by
  have he : n=2*(n/2) := by omega
  have ha : 0<n/2 := by omega
  have hm : (2∣evenGcd n) ↔ ∀ l,0<l → l<n/2 → 2∣(n/2).choose l := by
    rw [dvd_evenGcd_iff]
    constructor
    · intro h l hl0 hla
      have hk : 2*l<n := by omega
      have hd := h (2*l) (by omega) hk (by omega)
      rw [dvd_choose_iff_digits Nat.prime_two,hne,Nat.mul_mod_right,
        Nat.mul_div_right _ (by norm_num : (0 : ℕ)<2),Nat.choose_zero_right,one_mul] at hd
      exact hd
    · intro h k hk0 hkn hke
      rw [dvd_choose_iff_digits Nat.prime_two,hne,hke,Nat.choose_zero_right,one_mul]
      exact h (k/2) (by omega) (by omega)
  rw [hm,whole_row_divisible_iff_power Nat.prime_two ha]
  constructor
  · rintro ⟨j,hj⟩
    exact ⟨j,by rw [he,hj,pow_succ']⟩
  · rintro ⟨j,hj⟩
    exact ⟨j,by rw [hj,pow_succ',Nat.mul_div_right _ (by norm_num : (0 : ℕ)<2)]⟩

/-- The two-adic valuation is also exactly one on its sparse support;
n=2 is still excluded and has raw empty GCD zero. -/
theorem evenGcd_two_factorization {n : ℕ} (hne : n%2=0) (hn : 4≤n) :
    (evenGcd n).factorization 2=if ∃ j : ℕ,n=2^(j+1) then 1 else 0 := by
  have hg := evenGcd_ne_zero hn
  have hd := evenGcd_two_dvd_iff hne hn
  have hv := Nat.prime_two.dvd_iff_one_le_factorization hg
  split_ifs with h
  · obtain ⟨j,hj⟩ := h
    have hj0 : 0<j := by
      by_contra hh
      have hh0 := Nat.eq_zero_of_not_pos hh
      norm_num [hh0] at hj
      omega
    have hk : 2^j∈evenSplits n := by
      apply mem_evenSplits.mpr
      refine ⟨Nat.pow_pos (by norm_num),?_,?_⟩
      · rw [hj]
        exact Nat.pow_lt_pow_of_lt (by norm_num : (1 : ℕ)<2) (by omega)
      · obtain ⟨j',rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj0.ne'
        rw [pow_succ]
        exact Nat.mul_mod_left _ _
    have hval : (n.choose (2^j)).factorization 2=1 := by
      rw [hj,Nat.factorization_choose_prime_pow Nat.prime_two
        (Nat.pow_le_pow_right (by norm_num) (by omega)) (Nat.pow_pos (by norm_num)).ne',
        Nat.factorization_pow_self Nat.prime_two]
      omega
    have hl := (Nat.factorization_le_iff_dvd hg
      (Nat.choose_ne_zero (mem_evenSplits.mp hk).2.1.le)).mpr (Finset.gcd_dvd hk) 2
    rw [hval] at hl
    have hlo := hv.mp (hd.mpr ⟨j,hj⟩)
    omega
  · have hz : ¬1≤(evenGcd n).factorization 2 := fun h1 => h (hd.mp (hv.mpr h1))
    omega

theorem evenGcd_squarefree {n : ℕ} (hne : n%2=0) (hn : 4≤n) :
    Squarefree (evenGcd n) := by
  apply Nat.squarefree_of_factorization_le_one (evenGcd_ne_zero hn)
  intro p
  by_cases hp : p.Prime
  · rcases hp.eq_two_or_odd with rfl | ho
    · rw [evenGcd_two_factorization hne hn]
      split_ifs <;> omega
    · have hp2 : 2<p := by have := hp.two_le; omega
      rw [evenGcd_factorization hp hp2 hne hn]
      split_ifs <;> omega
  · rw [Nat.factorization_eq_zero_of_not_prime _ hp]
    omega

theorem evenGcd_prime_le {n p : ℕ} (hn : 4≤n) (hp : p.Prime)
    (hd : p∣evenGcd n) : p≤n := by
  have hg : evenGcd n∣n.choose 2 :=
    Finset.gcd_dvd (mem_evenSplits.mpr ⟨by norm_num,by omega,by norm_num⟩)
  have hc : n.choose 2∣n.factorial := by
    refine ⟨(2 : ℕ).factorial*(n-2).factorial,?_⟩
    have he := Nat.choose_mul_factorial_mul_factorial (show 2≤n by omega)
    simpa only [mul_assoc] using he.symm
  exact hp.dvd_factorial.mp (hd.trans (hg.trans hc))

/-- Exact joint incidence, BEFORE norms: the binary endpoint and every
odd-prime proper-power label remain distinct. -/
def incidence (p n : ℕ) : Prop :=
  if p=2 then (∃ j : ℕ,n=2^(j+1)) else (∃ i j : ℕ,n=p^i+p^j)

theorem evenGcd_factorization_incidence {n p : ℕ} (hp : p.Prime)
    (hne : n%2=0) (hn : 4≤n) :
    (evenGcd n).factorization p=if incidence p n then 1 else 0 := by
  by_cases hp2 : p=2
  · subst p
    simp only [incidence,↓reduceIte,evenGcd_two_factorization hne hn]
  · have hpgt : 2<p := by have := hp.two_le; omega
    simp only [incidence,ite_eq_right hp2,evenGcd_factorization hp hpgt hne hn]

/-- Exact finite prime-log formula for the WHOLE even-split GCD.
All prime powers and the literal n=4 binary head are kept. -/
theorem log_evenGcd_eq_incidence {n : ℕ} (hne : n%2=0) (hn : 4≤n) :
    Real.log (evenGcd n)=∑ p∈Finset.Icc 2 n,
      if p.Prime ∧ incidence p n then Real.log p else 0 := by
  have hg := evenGcd_ne_zero hn
  have he : (evenGcd n : ℝ)=∏ p∈(evenGcd n).primeFactors,
      (p : ℝ)^(evenGcd n).factorization p := by
    exact_mod_cast Nat.prod_primeFactors_pow_factorization hg
  rw [he,Real.log_prod (fun p hp => pow_ne_zero _ (by
    exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero))]
  simp_rw [Real.log_pow]
  have hs : (∑ p∈(evenGcd n).primeFactors,
        ((evenGcd n).factorization p : ℝ)*Real.log p)=
      ∑ p∈Finset.Icc 2 n,((evenGcd n).factorization p : ℝ)*Real.log p := by
    apply Finset.sum_subset
    · intro p hp
      exact Finset.mem_Icc.mpr ⟨(Nat.prime_of_mem_primeFactors hp).two_le,
        evenGcd_prime_le hn (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)⟩
    · intro p _ hp
      have hz : (evenGcd n).factorization p=0 := by
        by_cases hprime : p.Prime
        · apply Nat.factorization_eq_zero_of_not_dvd
          intro hd
          exact hp (Nat.mem_primeFactors.mpr ⟨hprime,hd,hg⟩)
        · exact Nat.factorization_eq_zero_of_not_prime _ hprime
      rw [hz,Nat.cast_zero,zero_mul]
  rw [hs]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : p.Prime
  · rw [evenGcd_factorization_incidence hp hne hn]
    by_cases hi : incidence p n <;> simp [hp,hi]
  · rw [Nat.factorization_eq_zero_of_not_prime _ hp]
    simp only [Nat.cast_zero,zero_mul,hp,false_and,↓reduceIte]

/-- Arbitrary-array version of the decoded incidence. Controls are NOT
granted literal binomial/Gamma data by this definition. -/
def observation (f : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ p∈Finset.Icc 2 n,if p.Prime ∧ incidence p n then f p else 0

theorem actual_observation {n : ℕ} (hne : n%2=0) (hn : 4≤n) :
    (Real.log (evenGcd n) : ℂ)=observation (fun p => (Real.log p : ℂ)) n := by
  rw [log_evenGcd_eq_incidence hne hn,Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro p _
  split_ifs <;> simp

/-- The entire weighted packet, with the original phase/mask permitted
in w, not a completed or prime-leg factorized surrogate. -/
def packet (X : ℕ) (w : ℕ → ℂ) : ℂ :=
  ∑ n∈Finset.Icc 4 X,if n%2=0 then w n*(Real.log (evenGcd n) : ℂ) else 0

theorem packet_eq_observation (X : ℕ) (w : ℕ → ℂ) :
    packet X w=∑ n∈Finset.Icc 4 X,
      if n%2=0 then w n*observation (fun p => (Real.log p : ℂ)) n else 0 := by
  apply Finset.sum_congr rfl
  intro n hn
  by_cases he : n%2=0
  · rw [ite_eq_left he,ite_eq_left he,actual_observation he (Finset.mem_Icc.mp hn).1]
  · simp only [ite_eq_right he]

/-- WHOLE masked join collapses to one base-prime test. This incidence
identity holds for any array, with no smooth model compatibility claim. -/
theorem joined_observation_eq_scalar (X : ℕ) (w f : ℕ → ℂ) :
    (∑ n∈Finset.Icc 4 X,if n%2=0 then w n*observation f n else 0)=
      ∑ p∈Finset.Icc 2 X,f p*(∑ n∈Finset.Icc 4 X,
        if n%2=0 ∧ p≤n ∧ p.Prime ∧ incidence p n then w n else 0) := by
  have he (n : ℕ) (hn : n∈Finset.Icc 4 X) :
      observation f n=∑ p∈Finset.Icc 2 X,
        if p≤n ∧ p.Prime ∧ incidence p n then f p else 0 := by
    have hs : (Finset.Icc 2 X).filter (fun p => p≤n)=Finset.Icc 2 n := by
      ext p
      simp only [Finset.mem_filter,Finset.mem_Icc]
      have := (Finset.mem_Icc.mp hn).2
      omega
    rw [observation,←hs,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p _
    by_cases hpn : p≤n <;> simp [hpn]
  calc
    _ = ∑ n∈Finset.Icc 4 X,∑ p∈Finset.Icc 2 X,
        if n%2=0 ∧ p≤n ∧ p.Prime ∧ incidence p n then w n*f p else 0 := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [he n hn]
      by_cases hn2 : n%2=0
      · rw [ite_eq_left hn2,Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p _
        by_cases hc : p≤n ∧ p.Prime ∧ incidence p n <;> simp [hn2,hc]
      · simp only [hn2,false_and,↓reduceIte,Finset.sum_const_zero]
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _
      split_ifs <;> simp only [mul_comm,mul_zero]

/-- A genuinely simultaneous distinct-prime constraint is available,
but its nonlinear zero source is NOT inferred from a linear prime limit. -/
theorem two_large_incidence_ordered {p q n : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hq2 : 2<q) (hqp : q<p) (hne : n%2=0) (hn : 4≤n)
    (hpl : n<p^2) (hql : n<q^2) (hpd : p∣evenGcd n) (hqd : q∣evenGcd n) :
    n=p+1 ∧ n=2*q ∧ p=2*q-1 := by
  have hps := (evenGcd_large_dvd_iff hp (hq2.trans hqp) hne hn hpl).mp hpd
  have hqs := (evenGcd_large_dvd_iff hq hq2 hne hn hql).mp hqd
  rcases hps with hps | hps <;> rcases hqs with hqs | hqs <;> omega

/-- Actual ordinary-prime dilation incidence inside the non-prefix row.
It is only ONE specified channel, not the source of the entire GCD. -/
def markedDilationCoefficient (n : ℕ) : ℂ :=
  if 2∣n then
    if (n/2).Prime ∧ 2<n/2 then
      ((evenGcd n).factorization (n/2) : ℂ)*(Real.log ((n/2 : ℕ) : ℝ) : ℂ)
    else 0
  else 0

/-- Complete ordinary-prime logarithmic array, before its exact head. -/
def fullPrimeCoefficient (p : ℕ) : ℂ := if p.Prime then (Real.log p : ℂ) else 0

/-- Ordinary odd primes; excluding two is a finite analytic head. -/
def oddPrimeCoefficient (p : ℕ) : ℂ :=
  if p.Prime ∧ 2<p then (Real.log p : ℂ) else 0

theorem markedDilationCoefficient_eq (n : ℕ) :
    markedDilationCoefficient n=zetaDilationCoefficient 2 oddPrimeCoefficient n := by
  rw [markedDilationCoefficient,zetaDilationCoefficient]
  by_cases hn : 2∣n
  · rw [ite_eq_left hn,ite_eq_left hn,oddPrimeCoefficient]
    by_cases hp : (n/2).Prime ∧ 2<n/2
    · rw [ite_eq_left hp,ite_eq_left hp]
      have he : n=2*(n/2) := (Nat.mul_div_cancel' hn).symm
      have hn4 : 4≤n := by omega
      have hn2 : n%2=0 := Nat.dvd_iff_mod_eq_zero.mp hn
      have hl : n<(n/2)^2 := by
        calc n=2*(n/2) := he
             _ < (n/2)^2 := by nlinarith [hp.2]
      rw [evenGcd_large_factorization hp.1 hp.2 hn2 hn4 hl,
        ite_eq_left (Or.inr he),Nat.cast_one,one_mul]
    · simp only [ite_eq_right hp]
  · simp only [ite_eq_right hn]

/-- The marked dilation packet still keeps the full WHOLE-label height
phase. It is exactly an old prime array dilation, not a new estimate. -/
theorem marked_dilation_packet_eq (S : Finset ℕ) (w : ℕ → ℂ) :
    (∑ n∈S,markedDilationCoefficient n*w n)=
      ∑ n∈S,zetaDilationCoefficient 2 oddPrimeCoefficient n*w n := by
  simp only [markedDilationCoefficient_eq]

/-- Continued odd-prime series, with all proper powers and head retained. -/
def oddPrimeResponse (s : ℂ) : ℂ :=
  -logDeriv riemannZeta s-zetaProperPrimePowerSeries s-
    (Real.log 2 : ℂ)*zetaPrimeFeature s 2

/-- Exact 2p physical-label response; the cofactor phase remains explicit. -/
def markedDilationResponse (s : ℂ) : ℂ := zetaPrimeFeature s 2*oddPrimeResponse s

/-- Ordinary-prime Euler identity with EVERY proper power subtracted
analytically, and the excluded prime TWO retained as an explicit head. -/
theorem odd_euler_response {s : ℂ} (hs : 1<s.re) :
    LSeriesHasSum oddPrimeCoefficient s (oddPrimeResponse s) := by
  have h := (LSeriesHasSum_zetaMoebiusPrimeDerivative hs).neg
  have he : -(fun n => if n.Prime then zetaMoebiusDerivativeCoefficient n else 0)=
      fullPrimeCoefficient := by
    funext n
    by_cases hp : n.Prime
    · simp [fullPrimeCoefficient,zetaMoebiusDerivativeCoefficient,hp,
        ArithmeticFunction.moebius_apply_prime hp]
    · simp [fullPrimeCoefficient,hp]
  rw [he] at h
  have hh := LSeriesHasSum_zetaFiniteCoefficient {2} fullPrimeCoefficient
    (by simp) s
  have hx : fullPrimeCoefficient-zetaFiniteCoefficient {2} fullPrimeCoefficient=
      oddPrimeCoefficient := by
    funext n
    by_cases hp : n.Prime
    · by_cases hn : n=2
      · subst n
        norm_num [fullPrimeCoefficient,oddPrimeCoefficient,zetaFiniteCoefficient]
      · have hp2 : 2<n := by have := hp.two_le; omega
        simp [fullPrimeCoefficient,oddPrimeCoefficient,zetaFiniteCoefficient,hp,hn,hp2]
    · simp [fullPrimeCoefficient,oddPrimeCoefficient,zetaFiniteCoefficient,hp]
  have hj := h.sub hh
  rw [hx] at hj
  convert hj using 1
  simp only [oddPrimeResponse,zetaFiniteDirichletSeries,Finset.sum_singleton,
    fullPrimeCoefficient,Nat.prime_two,↓reduceIte]
  ring

/-- The physical label remains 2p, hence its dilation phase is retained.
Series convergence is asserted ONLY in the Euler half-plane. -/
theorem marked_dilation_euler_response {s : ℂ} (hs : 1<s.re) :
    LSeriesHasSum markedDilationCoefficient s (markedDilationResponse s) := by
  have h := LSeriesHasSum_zetaDilationCoefficient (by norm_num : (0 : ℕ)<2)
    (a := oddPrimeCoefficient) (by norm_num [oddPrimeCoefficient]) (odd_euler_response hs)
  have hc : markedDilationCoefficient=zetaDilationCoefficient 2 oddPrimeCoefficient := by
    funext n
    exact markedDilationCoefficient_eq n
  rw [hc,markedDilationResponse]
  exact h

theorem marked_dilation_height_response (y : ℝ) {s : ℂ} (hs : 1<s.re) :
    LSeries (fun n => markedDilationCoefficient n*SuzukiCarryCorrelation.primePhase y n) s=
      markedDilationResponse (s+I*y) := by
  rw [ArithmeticOperatorGammaTwistAudit.LSeries_primePhase]
  exact (marked_dilation_euler_response (by simpa using hs)).LSeries_eq

theorem odd_actual_zero_source (rho : NontrivialZetaZero) (hrho : 1/2<rho.1.re) :
    Tendsto (fun s : ℂ => (s-rho.1)*oddPrimeResponse s) (𝓝[≠] rho.1)
      (𝓝 (-(analyticZetaZeroMultiplicity rho : ℂ))) := by
  have hc : ContinuousAt (fun s : ℂ => zetaProperPrimePowerSeries s+
      (Real.log 2 : ℂ)*zetaPrimeFeature s 2) rho.1 := by
    exact (analyticAt_zetaProperPrimePowerSeries hrho).continuousAt.add (by
      unfold zetaPrimeFeature
      fun_prop)
  have hh : ContinuousAt (fun s : ℂ => (s-rho.1)*(zetaProperPrimePowerSeries s+
      (Real.log 2 : ℂ)*zetaPrimeFeature s 2)) rho.1 :=
    (continuousAt_id.sub continuousAt_const).mul hc
  have hz : Tendsto (fun s : ℂ => (s-rho.1)*(zetaProperPrimePowerSeries s+
      (Real.log 2 : ℂ)*zetaPrimeFeature s 2)) (𝓝[≠] rho.1) (𝓝 0) := by
    simpa only [sub_self,zero_mul] using hh.tendsto.mono_left nhdsWithin_le_nhds
  convert (ArithmeticOperatorKummerMinimumAudit.actual_zero_source rho).sub hz using 1
  · ext s
    simp only [oddPrimeResponse,ArithmeticOperatorKummerMinimumAudit.response]
    ring
  · simp only [sub_zero]

/-- Actual all-multiplicity residue for the marked 2p channel. This is
NOT inferred to be a source limit for other incidences or the whole row. -/
theorem marked_dilation_actual_zero_source (rho : NontrivialZetaZero)
    (hrho : 1/2<rho.1.re) :
    Tendsto (fun s : ℂ => (s-rho.1)*markedDilationResponse s) (𝓝[≠] rho.1)
      (𝓝 (-(analyticZetaZeroMultiplicity rho : ℂ)*zetaPrimeFeature rho.1 2)) := by
  have hf : ContinuousAt (fun s => zetaPrimeFeature s 2) rho.1 := by
    unfold zetaPrimeFeature
    fun_prop
  convert (odd_actual_zero_source rho hrho).mul
    (hf.tendsto.mono_left nhdsWithin_le_nhds) using 1
  ext s
  simp only [markedDilationResponse]
  ring

/-- Cancel density BEFORE comparing the actual marked channel source. -/
def markedDilationCenteredResponse (s : ℂ) : ℂ :=
  zetaPrimeFeature s 2*(ArithmeticOperatorKummerMinimumAudit.centeredResponse s-
    zetaProperPrimePowerSeries s-(Real.log 2 : ℂ)*zetaPrimeFeature s 2)

theorem marked_dilation_centered_eq (s : ℂ) :
    markedDilationCenteredResponse s=markedDilationResponse s-zetaPrimeFeature s 2/(s-1) := by
  simp only [markedDilationCenteredResponse,markedDilationResponse,oddPrimeResponse,
    ArithmeticOperatorKummerMinimumAudit.centeredResponse,
    ArithmeticOperatorKummerMinimumAudit.response]
  ring

theorem marked_dilation_density_analytic :
    ∃ E : ℂ → ℂ,AnalyticAt ℂ E 1 ∧
      markedDilationCenteredResponse=ᶠ[𝓝[≠] (1 : ℂ)] E := by
  obtain ⟨E,hE,he⟩ := ArithmeticOperatorKummerMinimumAudit.centered_density_analytic
  refine ⟨fun s => zetaPrimeFeature s 2*(E s-zetaProperPrimePowerSeries s-
      (Real.log 2 : ℂ)*zetaPrimeFeature s 2),?_,?_⟩
  · apply (show AnalyticAt ℂ (fun s => zetaPrimeFeature s 2) 1 from by
      unfold zetaPrimeFeature
      fun_prop).mul
    exact (hE.sub (analyticAt_zetaProperPrimePowerSeries (by norm_num))).sub (by
      unfold zetaPrimeFeature
      fun_prop)
  · filter_upwards [he] with s hs
    simp only [markedDilationCenteredResponse,hs]

theorem marked_dilation_centered_actual_zero_source (rho : NontrivialZetaZero)
    (hrho : 1/2<rho.1.re) :
    Tendsto (fun s : ℂ => (s-rho.1)*markedDilationCenteredResponse s) (𝓝[≠] rho.1)
      (𝓝 (-(analyticZetaZeroMultiplicity rho : ℂ)*zetaPrimeFeature rho.1 2)) := by
  have hc : ContinuousAt (fun s : ℂ => (s-rho.1)*zetaPrimeFeature s 2/(s-1)) rho.1 := by
    unfold zetaPrimeFeature
    fun_prop (disch := exact sub_ne_zero.mpr rho.2.2.2)
  have hz : Tendsto (fun s : ℂ => (s-rho.1)*zetaPrimeFeature s 2/(s-1))
      (𝓝[≠] rho.1) (𝓝 0) := by
    simpa only [sub_self,zero_mul,zero_div] using hc.tendsto.mono_left nhdsWithin_le_nhds
  convert (marked_dilation_actual_zero_source rho hrho).sub hz using 1
  · ext s
    rw [marked_dilation_centered_eq,mul_sub,mul_div_assoc]
  · simp only [sub_zero]

theorem marked_dilation_source_ne_zero (rho : NontrivialZetaZero) :
    -(analyticZetaZeroMultiplicity rho : ℂ)*zetaPrimeFeature rho.1 2≠0 := by
  apply mul_ne_zero (ArithmeticOperatorKummerMinimumAudit.source_ne_zero rho)
  exact Complex.exp_ne_zero _

/-- The selected ordinary channel remains the OLD scalar source after
density removal; it cannot be treated as source-small. -/
theorem marked_dilation_centered_not_source_small (rho : NontrivialZetaZero)
    (hrho : 1/2<rho.1.re) :
    ¬Tendsto (fun s : ℂ => (s-rho.1)*markedDilationCenteredResponse s)
      (𝓝[≠] rho.1) (𝓝 0) := by
  intro h
  exact marked_dilation_source_ne_zero rho
    (tendsto_nhds_unique (marked_dilation_centered_actual_zero_source rho hrho) h)

/-- A full scalar observation has no universal free outer-weight bound.
This is an audit, not a bound for the prescribed RH packet. -/
theorem no_free_weight_payment {X : ℕ} (hX : 6≤X) (B : ℝ) :
    ¬∀ w : ℕ → ℂ,‖packet X w‖≤B := by
  intro h
  let K : ℕ → ℂ := fun n => if n%2=0 then (Real.log (evenGcd n) : ℂ) else 0
  have hh : ∀ w : ℕ → ℂ,‖∑ n∈Finset.Icc 4 X,w n*K n‖≤B := by
    intro w
    simpa only [packet,K,mul_ite,mul_zero] using h w
  have hz := (ArithmeticOperatorGramAudit.scalar_bound_forall_weights_iff
    (Finset.Icc 4 X) K B).mp hh |>.2
  have h6 := hz 6 (Finset.mem_Icc.mpr ⟨by norm_num,hX⟩)
  have hg : 5∣evenGcd 6 := (evenGcd_prime_dvd_iff (by norm_num : Nat.Prime 5)
    (by norm_num) (by norm_num) (by norm_num)).mpr ⟨1,0,by norm_num⟩
  have hp : 1<(evenGcd 6 : ℝ) := by
    have hl := Nat.le_of_dvd (Nat.pos_of_ne_zero (evenGcd_ne_zero (by norm_num))) hg
    exact_mod_cast (show 1<evenGcd 6 by omega)
  have hn : Real.log (evenGcd 6)≠0 := (Real.log_pos hp).ne'
  simp only [K,show 6%2=0 by norm_num,↓reduceIte,Complex.ofReal_eq_zero] at h6
  exact hn h6

end RiemannGaussian.ArithmeticOperatorKummerParityAudit

#lint+ in RiemannGaussian.ArithmeticOperatorKummerParityAudit

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
  unless declarations>0 do throwError "Empty complete even-binomial audit."
  logInfo m!"Kummer-parity audit: {declarations} declarations, {theorems} theorems; only standard axioms."
  IO.FS.createDirAll ".lake/arithmetic-operator-kummer-parity"
  IO.FS.writeFile ".lake/arithmetic-operator-kummer-parity/axioms.json"
    (Json.mkObj [("scope",toJson "literal even split GCD; all-power Lucas support and one-carry witness, binary head, scalar collapse and marked-channel source"),
      ("onlyStandardAxioms",toJson true),("namespaceLinters",toJson (15:Nat)),
      ("allLocalDeclarationsByModuleProvenance",toJson true),
      ("declarations",toJson declarations),("theoremsIncludingGeneratedHelpers",toJson theorems),
      ("declarationAxioms",Json.arr reports)]).pretty
