/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ArithmeticOperatorResidueInverseAudit
import RiemannGaussian.ZetaMoebiusPoleJetFilter
import Mathlib.Algebra.TrivSqZeroExt.Basic

/-!
# Coprime divisor/cofactor masks in the actual logarithmic inverse

The inverse is restricted on its literal integer fibers, not after a
completed analytic filter. The two coordinates below retain the constant
row and the actual logarithmic row together. They are bookkeeping for the
exact finite gate; no signed prime estimate follows from their positivity.
The squarefree restriction collapses exactly to ordinary primes, where
the original filtered source and pole removal apply at every multiplicity.
The full nonsquarefree inverse has no source/cutoff asymptotic here.
-/

namespace RiemannGaussian.ArithmeticOperatorUnitaryInverseAudit
noncomputable section
open Complex Filter
open scoped BigOperators Topology LSeries.notation

/-- Full ordinary integer antidiagonal with a coprime fiber mask. -/
def unitary {R : Type*} [Semiring R] (f g : ℕ → R) (n : ℕ) : R :=
  ∑ da ∈ n.divisorsAntidiagonal,if da.1.Coprime da.2 then f da.1*g da.2 else 0

private theorem sum_antidiagonal_mul {R : Type*} [AddCommMonoid R]
    {m n : ℕ} (hc : m.Coprime n) (F : ℕ × ℕ → R) :
    (∑ da ∈ (m*n).divisorsAntidiagonal,F da)=
      ∑ a∈m.divisorsAntidiagonal,∑ b∈n.divisorsAntidiagonal,
        F (a.1*b.1,a.2*b.2) := by
  rw [← Finset.sum_product']
  symm
  apply Finset.sum_nbij fun ((i,j),k,l) => (i*k,j*l)
  · rintro ⟨⟨a1,a2⟩,⟨b1,b2⟩⟩ h
    simp only [Nat.mem_divisorsAntidiagonal,Ne,Finset.mem_product] at h
    rcases h with ⟨⟨rfl,ha⟩,⟨rfl,hb⟩⟩
    simp only [Nat.mem_divisorsAntidiagonal,mul_eq_zero,Ne]
    rw [mul_eq_zero] at ha hb
    exact ⟨by ring,not_or_intro ha hb⟩
  · simp only [Set.InjOn,Finset.mem_coe,Nat.mem_divisorsAntidiagonal,
      Finset.mem_product,Prod.mk_inj]
    rintro ⟨⟨a1,a2⟩,⟨b1,b2⟩⟩ ⟨⟨rfl,ha⟩,⟨rfl,hb⟩⟩
      ⟨⟨c1,c2⟩,⟨d1,d2⟩⟩ hcd h
    ext
    · trans Nat.gcd (a1*a2) (a1*b1)
      · rw [Nat.gcd_mul_left,hc.coprime_mul_left.coprime_mul_right_right.gcd_eq_one,mul_one]
      · rw [← hcd.1.1,← hcd.2.1] at hc
        rw [← hcd.1.1,h.1,Nat.gcd_mul_left,
          hc.coprime_mul_left.coprime_mul_right_right.gcd_eq_one,mul_one]
    · trans Nat.gcd (a1*a2) (a2*b2)
      · rw [mul_comm,Nat.gcd_mul_left,
          hc.coprime_mul_right.coprime_mul_left_right.gcd_eq_one,mul_one]
      · rw [← hcd.1.1,← hcd.2.1] at hc
        rw [← hcd.1.1,h.2,mul_comm,Nat.gcd_mul_left,
          hc.coprime_mul_right.coprime_mul_left_right.gcd_eq_one,mul_one]
    · trans Nat.gcd (b1*b2) (a1*b1)
      · rw [mul_comm,Nat.gcd_mul_right,
          hc.coprime_mul_right.coprime_mul_left_right.symm.gcd_eq_one,one_mul]
      · rw [← hcd.1.1,← hcd.2.1] at hc
        rw [← hcd.2.1,h.1,mul_comm c1 d1,Nat.gcd_mul_left,
          hc.coprime_mul_right.coprime_mul_left_right.symm.gcd_eq_one,mul_one]
    · trans Nat.gcd (b1*b2) (a2*b2)
      · rw [Nat.gcd_mul_right,
          hc.coprime_mul_left.coprime_mul_right_right.symm.gcd_eq_one,one_mul]
      · rw [← hcd.1.1,← hcd.2.1] at hc
        rw [← hcd.2.1,h.2,Nat.gcd_mul_right,
          hc.coprime_mul_left.coprime_mul_right_right.symm.gcd_eq_one,one_mul]
  · simp only [Set.SurjOn,Set.subset_def,Finset.mem_coe,Nat.mem_divisorsAntidiagonal,
      Finset.mem_product,Set.mem_image]
    rintro ⟨b1,b2⟩ h
    use ((b1.gcd m,b2.gcd m),(b1.gcd n,b2.gcd n))
    rw [← hc.gcd_mul _,← hc.gcd_mul _,← h.1,
      Nat.gcd_mul_gcd_of_coprime_of_mul_eq_mul hc h.1,
      Nat.gcd_mul_gcd_of_coprime_of_mul_eq_mul hc.symm _]
    · rw [Ne,mul_eq_zero,not_or] at h
      simp [h.2.1,h.2.2]
    · rw [mul_comm n m,h.1]
  · intro a _
    rfl

/-- Coprime convolution factors on genuinely coprime integer rows.
The identity does not discard proper powers or unit fibers. -/
theorem unitary_mul {R : Type*} [CommSemiring R] (f g : ℕ → R)
    (hf : ∀ a b,a.Coprime b → f (a*b)=f a*f b)
    (hg : ∀ a b,a.Coprime b → g (a*b)=g a*g b)
    {m n : ℕ} (hc : m.Coprime n) :
    unitary f g (m*n)=unitary f g m*unitary f g n := by
  unfold unitary
  rw [sum_antidiagonal_mul hc,Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  have haP := (Nat.mem_divisorsAntidiagonal.mp ha).1
  have hbP := (Nat.mem_divisorsAntidiagonal.mp hb).1
  have hc' : (a.1*a.2).Coprime (b.1*b.2) := by simpa [haP,hbP] using hc
  have hx : a.1.Coprime b.1 := hc'.coprime_mul_right.coprime_mul_right_right
  have hy : a.2.Coprime b.2 := hc'.coprime_mul_left.coprime_mul_left_right
  have hx' : a.1.Coprime b.2 := hc'.coprime_mul_right.coprime_mul_left_right
  have hy' : b.1.Coprime a.2 := hc'.coprime_mul_left.coprime_mul_right_right.symm
  have hmask : (a.1*b.1).Coprime (a.2*b.2) ↔
      a.1.Coprime a.2 ∧ b.1.Coprime b.2 := by
    simp only [Nat.coprime_mul_iff_left,Nat.coprime_mul_iff_right]
    exact ⟨fun h => ⟨h.1.1,h.2.2⟩,fun h => ⟨⟨h.1,hy'⟩,⟨hx',h.2⟩⟩⟩
  simp only [hmask,hf _ _ hx,hg _ _ hy,ite_and]
  by_cases haC : a.1.Coprime a.2
  · rw [ite_eq_left haC,ite_eq_left haC]
    by_cases hbC : b.1.Coprime b.2
    · rw [ite_eq_left hbC,ite_eq_left hbC]
      ring
    · rw [ite_eq_right hbC,ite_eq_right hbC,mul_zero]
  · rw [ite_eq_right haC,ite_eq_right haC,zero_mul]

/-- Both complete integer rows, in a square-zero extension: multiplication
retains the exact logarithmic Leibniz rule before either coordinate is joined. -/
def gammaJet (n : ℕ) : TrivSqZeroExt ℝ ℝ :=
  TrivSqZeroExt.inl 1+TrivSqZeroExt.inr (Real.log n)

private theorem gammaJet_mul {a b : ℕ} (ha : a≠0) (hb : b≠0) :
    gammaJet (a*b)=gammaJet a*gammaJet b := by
  ext <;> simp [gammaJet,TrivSqZeroExt.snd_mul,Real.log_mul
    (by exact_mod_cast ha : (a : ℝ)≠0) (by exact_mod_cast hb : (b : ℝ)≠0),
    Nat.cast_mul,TrivSqZeroExt.fst_mul,add_comm]

/-- The ACTUAL Möbius coefficient on the masked inverse, without a
unitary-Möbius replacement. -/
def muJet (n : ℕ) : TrivSqZeroExt ℝ ℝ :=
  TrivSqZeroExt.inl (ArithmeticFunction.moebius n : ℝ)

/-- Exact simultaneous constant/logarithmic masked inverse. -/
def inverseJet (n : ℕ) : TrivSqZeroExt ℝ ℝ := unitary muJet gammaJet n

/-- The surviving constant coordinate. -/
def constantInverse (n : ℕ) : ℝ := (inverseJet n).fst

/-- The actual logarithmic coordinate, with the coprime mask inside
the sum. It is not ordinary Möbius inversion. -/
def logInverse (n : ℕ) : ℝ := (inverseJet n).snd

private theorem gammaJet_one : gammaJet 1=1 := by simp [gammaJet]

private theorem gammaJet_coprime {a b : ℕ} (hc : a.Coprime b) :
    gammaJet (a*b)=gammaJet a*gammaJet b := by
  by_cases ha : a=0
  · subst a
    have hb : b=1 := by simpa using hc
    simp [hb,gammaJet_one]
  by_cases hb : b=0
  · subst b
    have ha' : a=1 := by simpa using hc
    simp [ha',gammaJet_one]
  exact gammaJet_mul ha hb

private theorem muJet_coprime {a b : ℕ} (hc : a.Coprime b) :
    muJet (a*b)=muJet a*muJet b := by
  rw [muJet,ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hc]
  simp only [Int.cast_mul,muJet,TrivSqZeroExt.inl_mul]

/-- Exact coprime factorization of both actual inverse coordinates. -/
theorem inverseJet_mul {a b : ℕ} (hc : a.Coprime b) :
    inverseJet (a*b)=inverseJet a*inverseJet b :=
  unitary_mul muJet gammaJet (fun _ _ h => muJet_coprime h)
    (fun _ _ h => gammaJet_coprime h) hc

private theorem inverseJet_zero : inverseJet 0=0 := by simp [inverseJet,unitary]

private theorem inverseJet_one : inverseJet 1=1 := by
  simp [inverseJet,unitary,muJet,gammaJet]

private def jetFunction : ArithmeticFunction (TrivSqZeroExt ℝ ℝ) :=
  ⟨inverseJet,inverseJet_zero⟩

private theorem jetFunction_multiplicative : jetFunction.IsMultiplicative :=
  ⟨inverseJet_one,fun h => inverseJet_mul h⟩

/-- Every actual positive prime-power factor is retained. -/
theorem inverseJet_factorization {n : ℕ} (hn : n≠0) :
    inverseJet n=∏ p∈n.primeFactors,inverseJet (p^n.factorization p) := by
  have h := jetFunction_multiplicative.multiplicative_factorization jetFunction hn
  rw [Nat.prod_factorization_eq_prod_primeFactors] at h
  exact h

private theorem coprime_antidiagonal_prime_pow {p k : ℕ} (hp : p.Prime) :
    ((p^k).divisorsAntidiagonal.filter (fun a => a.1.Coprime a.2))=
      {(1,p^k),(p^k,1)} := by
  ext a
  constructor
  · intro h
    obtain ⟨hA,hC⟩ := Finset.mem_filter.mp h
    have haP := (Nat.mem_divisorsAntidiagonal.mp hA).1
    obtain ⟨i,_,hi⟩ := (Nat.mem_divisors_prime_pow hp k).mp
      (Nat.fst_mem_divisors_of_mem_antidiagonal hA)
    obtain ⟨j,_,hj⟩ := (Nat.mem_divisors_prime_pow hp k).mp
      (Nat.snd_mem_divisors_of_mem_antidiagonal hA)
    by_cases hi0 : i=0
    · have ha1 : a.1=1 := by simpa [hi0] using hi
      have ha2 : a.2=p^k := by simpa [ha1] using haP
      exact Finset.mem_insert.mpr (Or.inl (Prod.ext ha1 ha2))
    have hj0 : j=0 := by
      by_contra hj0
      have hd1 : p∣a.1 := by rw [hi]; exact dvd_pow_self p hi0
      have hd2 : p∣a.2 := by rw [hj]; exact dvd_pow_self p hj0
      exact Nat.not_coprime_of_dvd_of_dvd hp.one_lt hd1 hd2 hC
    have ha2 : a.2=1 := by simpa [hj0] using hj
    have ha1 : a.1=p^k := by simpa [ha2] using haP
    exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr (Prod.ext ha1 ha2)))
  · intro h
    rcases Finset.mem_insert.mp h with rfl | h
    · exact Finset.mem_filter.mpr
        ⟨Nat.mem_divisorsAntidiagonal.mpr ⟨by simp,pow_ne_zero k hp.ne_zero⟩,
          Nat.coprime_one_left _⟩
    · have he := Finset.mem_singleton.mp h
      subst a
      exact Finset.mem_filter.mpr
        ⟨Nat.mem_divisorsAntidiagonal.mpr ⟨by simp,pow_ne_zero k hp.ne_zero⟩,
          Nat.coprime_one_right _⟩

/-- The actual logarithmic row survives on EVERY prime power. Only
the constant coordinate vanishes at exponent one. -/
theorem inverseJet_prime_pow {p k : ℕ} (hp : p.Prime) (hk : 0<k) :
    inverseJet (p^k)=
      TrivSqZeroExt.inl (if k=1 then 0 else (1 : ℝ))+
        TrivSqZeroExt.inr ((k : ℝ)*Real.log p) := by
  have hpk : p^k≠1 := ne_of_gt (one_lt_pow₀ hp.one_lt hk.ne')
  have hneq : (1,p^k)≠(p^k,1) := by
    intro h
    exact hpk (congrArg Prod.fst h |>.symm)
  unfold inverseJet unitary
  rw [← Finset.sum_filter,coprime_antidiagonal_prime_pow hp,
    Finset.sum_pair hneq]
  simp only [muJet,gammaJet,
    ArithmeticFunction.moebius_apply_one,Int.cast_one,
    TrivSqZeroExt.inl_one,one_mul,
    ArithmeticFunction.moebius_apply_prime_pow hp hk.ne',Nat.cast_pow,Real.log_pow]
  by_cases hk1 : k=1 <;> simp [hk1]

theorem constantInverse_prime_pow {p k : ℕ} (hp : p.Prime) (hk : 0<k) :
    constantInverse (p^k)=if k=1 then 0 else 1 := by
  rw [constantInverse,inverseJet_prime_pow hp hk]
  simp

theorem logInverse_prime_pow {p k : ℕ} (hp : p.Prime) (hk : 0<k) :
    logInverse (p^k)=(k : ℝ)*Real.log p := by
  rw [logInverse,inverseJet_prime_pow hp hk]
  simp

/-- A nonnegative actual coefficient is not yet a signed height estimate. -/
theorem inverse_coordinates_nonneg (n : ℕ) :
    0≤constantInverse n ∧ 0≤logInverse n := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | zero => simp [constantInverse,logInverse,inverseJet_zero]
  | one => simp [constantInverse,logInverse,inverseJet_one]
  | prime_pow p k hp hk =>
    rw [constantInverse_prime_pow hp hk,logInverse_prime_pow hp hk]
    exact ⟨by split_ifs <;> norm_num,mul_nonneg (Nat.cast_nonneg k)
      (Real.log_nonneg (by exact_mod_cast hp.one_lt.le))⟩
  | coprime a b _ _ hc ha hb =>
    have hA := congrArg TrivSqZeroExt.fst (inverseJet_mul hc)
    have hB := congrArg TrivSqZeroExt.snd (inverseJet_mul hc)
    simp only [TrivSqZeroExt.fst_mul] at hA
    simp only [TrivSqZeroExt.snd_mul,smul_eq_mul] at hB
    change (inverseJet (a*b)).snd=(inverseJet a).fst*(inverseJet b).snd+
      (inverseJet a).snd*(inverseJet b).fst at hB
    rw [mul_comm (inverseJet a).snd (inverseJet b).fst] at hB
    change constantInverse (a*b)=constantInverse a*constantInverse b at hA
    change logInverse (a*b)=constantInverse a*logInverse b+
      constantInverse b*logInverse a at hB
    rw [hA,hB]
    exact ⟨mul_nonneg ha.1 hb.1,add_nonneg (mul_nonneg ha.1 hb.2)
      (mul_nonneg hb.1 ha.2)⟩

/-- Exactly the ordinary primes with exponent ONE in the original label. -/
def singlePrimes (n : ℕ) : Finset ℕ :=
  n.primeFactors.filter (fun p => n.factorization p=1)

private theorem prime_order_pos {n p : ℕ} (hp : p∈n.primeFactors) :
    0<n.factorization p := by
  rw [← Nat.support_factorization] at hp
  exact Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hp)

private theorem prime_power_jet_of_not_one {p k : ℕ}
    (hp : p.Prime) (hk : 0<k) (hk1 : k≠1) :
    inverseJet (p^k)=gammaJet (p^k) := by
  rw [inverseJet_prime_pow hp hk,ite_eq_right hk1]
  simp only [gammaJet,Nat.cast_pow,Real.log_pow]

private theorem prod_gammaJet {S : Finset ℕ} (f : ℕ → ℕ)
    (hf : ∀ p∈S,f p≠0) :
    (∏ p∈S,gammaJet (f p))=gammaJet (∏ p∈S,f p) := by
  induction S using Finset.induction with
  | empty => simp [gammaJet_one]
  | insert p S hp ih =>
    rw [Finset.prod_insert hp,Finset.prod_insert hp,
      ih (fun q hq => hf q (Finset.mem_insert_of_mem hq)),
      gammaJet_mul (hf p (Finset.mem_insert_self _ _))
        (Finset.prod_ne_zero_iff.mpr (fun q hq => hf q (Finset.mem_insert_of_mem hq)))]

/-- If no exponent-one prime is present, the complete logarithmic row
survives exactly. This includes every powerful label and the unit. -/
theorem inverseJet_of_no_single {n : ℕ} (hn : n≠0) (h : singlePrimes n=∅) :
    inverseJet n=gammaJet n := by
  rw [inverseJet_factorization hn]
  have he : ∀ p∈n.primeFactors,inverseJet (p^n.factorization p)=
      gammaJet (p^n.factorization p) := by
    intro p hp
    have hp1 : n.factorization p≠1 := by
      intro hp1
      have hpS : p∈singlePrimes n := Finset.mem_filter.mpr ⟨hp,hp1⟩
      rw [h] at hpS
      exact Finset.notMem_empty _ hpS
    exact prime_power_jet_of_not_one (Nat.prime_of_mem_primeFactors hp)
      (prime_order_pos hp) hp1
  rw [Finset.prod_congr rfl he,prod_gammaJet]
  · exact congrArg gammaJet (Nat.prod_primeFactors_pow_factorization hn).symm
  · intro p hp
    exact pow_ne_zero _ (Nat.prime_of_mem_primeFactors hp).ne_zero

/-- With one exponent-one prime, all other prime-power logarithms
cancel before the phase or any norm is taken. -/
theorem inverseJet_of_single {n p : ℕ} (hn : n≠0) (h : singlePrimes n={p}) :
    inverseJet n=TrivSqZeroExt.inr (Real.log p) := by
  have hpS : p∈singlePrimes n := by rw [h]; simp
  obtain ⟨hp,hp1⟩ := Finset.mem_filter.mp hpS
  rw [inverseJet_factorization hn,← Finset.mul_prod_erase _ _ hp,hp1,pow_one]
  rw [show inverseJet p=TrivSqZeroExt.inr (Real.log p) by
    simpa using inverseJet_prime_pow (Nat.prime_of_mem_primeFactors hp) (by norm_num : 0<1)]
  have he : ∀ q∈n.primeFactors.erase p,inverseJet (q^n.factorization q)=
      gammaJet (q^n.factorization q) := by
    intro q hq
    obtain ⟨hqp,hqP⟩ := Finset.mem_erase.mp hq
    have hq1 : n.factorization q≠1 := by
      intro hq1
      have hqS : q∈singlePrimes n := Finset.mem_filter.mpr ⟨hqP,hq1⟩
      rw [h] at hqS
      exact hqp (Finset.mem_singleton.mp hqS)
    exact prime_power_jet_of_not_one (Nat.prime_of_mem_primeFactors hqP)
      (prime_order_pos hqP) hq1
  rw [Finset.prod_congr rfl he,prod_gammaJet]
  · ext <;> simp [gammaJet,TrivSqZeroExt.snd_mul]
  · intro q hq
    exact pow_ne_zero _ (Nat.prime_of_mem_primeFactors (Finset.mem_erase.mp hq).2).ne_zero

/-- Two distinct exponent-one primes annihilate the entire actual
masked inverse. No count/radial/height averaging is used. -/
theorem inverseJet_of_many {n : ℕ} (hn : n≠0) (h : 2≤(singlePrimes n).card) :
    inverseJet n=0 := by
  obtain ⟨p,hp,q,hq,hpq⟩ := Finset.one_lt_card.mp (by omega : 1<(singlePrimes n).card)
  obtain ⟨hpP,hp1⟩ := Finset.mem_filter.mp hp
  obtain ⟨hqP,hq1⟩ := Finset.mem_filter.mp hq
  have hqE : q∈n.primeFactors.erase p := Finset.mem_erase.mpr ⟨hpq.symm,hqP⟩
  rw [inverseJet_factorization hn,← Finset.mul_prod_erase _ _ hpP,
    ← Finset.mul_prod_erase _ _ hqE,hp1,hq1,pow_one,pow_one,← mul_assoc]
  have hpp : inverseJet p=TrivSqZeroExt.inr (Real.log p) := by
    simpa using inverseJet_prime_pow (Nat.prime_of_mem_primeFactors hpP) (by norm_num : 0<1)
  have hqq : inverseJet q=TrivSqZeroExt.inr (Real.log q) := by
    simpa using inverseJet_prime_pow (Nat.prime_of_mem_primeFactors hqP) (by norm_num : 0<1)
  rw [hpp,hqq,TrivSqZeroExt.inr_mul_inr,zero_mul]

/-- Exact integer classification suggested by the finite probe, now
without a height, cutoff, or prime-power exception. -/
theorem logInverse_classification {n : ℕ} (hn : n≠0) :
    logInverse n=
      if singlePrimes n=∅ then Real.log n
      else if (singlePrimes n).card=1 then ∑ p∈singlePrimes n,Real.log p else 0 := by
  by_cases h0 : singlePrimes n=∅
  · rw [ite_eq_left h0,logInverse,inverseJet_of_no_single hn h0]
    simp [gammaJet]
  rw [ite_eq_right h0]
  by_cases h1 : (singlePrimes n).card=1
  · obtain ⟨p,hp⟩ := Finset.card_eq_one.mp h1
    rw [ite_eq_left h1,logInverse,inverseJet_of_single hn hp,hp]
    simp
  · have h2 : 2≤(singlePrimes n).card := by
      have hp : 0<(singlePrimes n).card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr h0)
      omega
    rw [ite_eq_right h1,logInverse,inverseJet_of_many hn h2]
    rfl

theorem constantInverse_eq (n : ℕ) :
    constantInverse n=∑ da∈n.divisorsAntidiagonal,
      if da.1.Coprime da.2 then (ArithmeticFunction.moebius da.1 : ℝ) else 0 := by
  unfold constantInverse inverseJet unitary
  rw [TrivSqZeroExt.fst_sum]
  apply Finset.sum_congr rfl
  intro da _
  split_ifs
  · simp only [muJet,gammaJet,TrivSqZeroExt.fst_mul,TrivSqZeroExt.fst_inl,
      TrivSqZeroExt.fst_add,TrivSqZeroExt.fst_inr,add_zero,mul_one]
  · rfl

theorem logInverse_eq (n : ℕ) :
    logInverse n=∑ da∈n.divisorsAntidiagonal,
      if da.1.Coprime da.2 then
        (ArithmeticFunction.moebius da.1 : ℝ)*Real.log da.2 else 0 := by
  unfold logInverse inverseJet unitary
  rw [TrivSqZeroExt.snd_sum]
  apply Finset.sum_congr rfl
  intro da _
  split_ifs
  · simp only [muJet,gammaJet,TrivSqZeroExt.snd_mul,TrivSqZeroExt.fst_inl,
      TrivSqZeroExt.snd_inl,TrivSqZeroExt.fst_add,TrivSqZeroExt.fst_inr,
      TrivSqZeroExt.snd_add,TrivSqZeroExt.snd_inr,add_zero,zero_add,smul_zero]
    rfl
  · rfl

/-- The physical height remains the phase of the whole original label. -/
def phasedLogInverse (y : ℝ) (n : ℕ) : ℂ :=
  (logInverse n : ℂ)*SuzukiCarryCorrelation.primePhase y n


/-- On squarefree labels the coprime mask is identically one on EVERY
divisor/cofactor fiber. The full ordinary inverse is therefore restored. -/
theorem logInverse_squarefree {n : ℕ} (hn : Squarefree n) :
    logInverse n=ArithmeticFunction.vonMangoldt n := by
  rw [logInverse_eq]
  have he : (∑ da∈n.divisorsAntidiagonal,
      if da.1.Coprime da.2 then
        (ArithmeticFunction.moebius da.1 : ℝ)*Real.log da.2 else 0)=
      (∑ da∈n.divisorsAntidiagonal,
        (ArithmeticFunction.moebius da.1 : ℝ)*Real.log da.2) := by
    apply Finset.sum_congr rfl
    intro da hda
    have hc : da.1.Coprime da.2 := Nat.coprime_of_squarefree_mul
      (by simpa only [(Nat.mem_divisorsAntidiagonal.mp hda).1] using hn)
    rw [ite_eq_left hc]
  rw [he]
  have h := congrArg (fun f : ArithmeticFunction ℝ => f n)
    ArithmeticFunction.moebius_mul_log_eq_vonMangoldt
  simpa only [ArithmeticFunction.mul_apply,ArithmeticFunction.intCoe_apply,
    ArithmeticFunction.log_apply] using h

/-- The squarefree candidate is LITERALLY the ordinary-prime sequence;
it is not just equivalent after a completion or an asymptotic. -/
theorem squarefree_logInverse_eq_prime (n : ℕ) :
    (if Squarefree n then logInverse n else 0)=
      if n.Prime then ArithmeticFunction.vonMangoldt n else 0 := by
  by_cases hp : n.Prime
  · rw [ite_eq_left hp.squarefree,ite_eq_left hp,logInverse_squarefree hp.squarefree]
  by_cases hsf : Squarefree n
  · rw [ite_eq_left hsf,ite_eq_right hp,logInverse_squarefree hsf]
    exact ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr
      (fun hpow => hp (Nat.squarefree_and_prime_pow_iff_prime.mp ⟨hsf,hpow⟩))
  · rw [ite_eq_right hsf,ite_eq_right hp]

/-- Arbitrary correlated outer tests, every cutoff and the full height
remain unchanged in the squarefree collapse. -/
theorem squarefree_native_eq_prime (X : ℕ) (y : ℝ) (test : ℕ → ℂ) :
    (∑ n∈Finset.Icc 1 X,test n*
      (if Squarefree n then phasedLogInverse y n else 0))=
      ∑ n∈Finset.Icc 1 X,
        if n.Prime then test n*(ArithmeticFunction.vonMangoldt n : ℂ)*
          SuzukiCarryCorrelation.primePhase y n else 0 := by
  apply Finset.sum_congr rfl
  intro n _
  calc
    _ = test n*((if Squarefree n then logInverse n else 0 : ℝ) : ℂ)*
        SuzukiCarryCorrelation.primePhase y n := by
      split_ifs <;> simp [phasedLogInverse,mul_assoc]
    _ = _ := by
      rw [squarefree_logInverse_eq_prime]
      split_ifs <;> simp [mul_assoc]

/-- Genuine convergent arithmetic moment for the squarefree candidate.
Every allowed ordinary prime is retained, with its original phase. -/
def squarefreeMoment (k : ℕ) (s : ℂ) : ℂ :=
  ∑' n,((if Squarefree n then logInverse n else 0 : ℝ) : ℂ)*
    zetaPrimeLogKernel k s n

theorem squarefreeMoment_eq_ordinaryPrime (k : ℕ) (s : ℂ) :
    squarefreeMoment k s=zetaOrdinaryPrimeLogMoment k s := by
  unfold squarefreeMoment zetaOrdinaryPrimeLogMoment
  apply tsum_congr
  intro n
  rw [squarefree_logInverse_eq_prime]
  split_ifs <;> simp

/-- The original finite polynomial filtering, without a new carrier. -/
def squarefreeFilter (p : Polynomial ℂ) (N : ℕ) (s : ℂ) : ℂ :=
  ∑ k∈p.support,p.coeff k*squarefreeMoment (N+k) s

theorem squarefreeFilter_eq_ordinaryPrime (p : Polynomial ℂ) (N : ℕ) (s : ℂ) :
    squarefreeFilter p N s=zetaOrdinaryPrimeLogFilter p N s := by
  simp only [squarefreeFilter,zetaOrdinaryPrimeLogFilter,squarefreeMoment_eq_ordinaryPrime]

/-- Actual source, with every analytic multiplicity, and exact density
pole-jet removal. It is inherited from the IDENTICAL ordinary-prime
sequence, not inferred from the untwisted coefficient positivity. -/
theorem squarefree_source_and_pole_cancellation (rho : NontrivialZetaZero)
    (hrho : 1/2<rho.1.re) :
    (zetaRightHalfPoleJetFilter rho hrho).eval
      ((3/2+I*rho.1.im)-1)⁻¹=0 ∧
    (zetaRightHalfPoleJetFilter rho hrho).derivative.eval
      ((3/2+I*rho.1.im)-1)⁻¹=0 ∧
    Tendsto (fun N : ℕ => ((3/2-rho.1.re : ℝ) : ℂ)^(N+1)*
      squarefreeFilter (zetaRightHalfPoleJetFilter rho hrho) N (3/2+I*rho.1.im))
      atTop (𝓝 (-(analyticZetaZeroMultiplicity rho : ℂ))) := by
  obtain ⟨hP,hP'⟩ := zetaRightHalfPoleJetFilter_pole_jet rho hrho
  refine ⟨hP,hP',?_⟩
  simp_rw [squarefreeFilter_eq_ordinaryPrime]
  have he (N : ℕ) : zetaOrdinaryPrimeLogFilter (zetaRightHalfPoleJetFilter rho hrho) N
      (3/2+I*rho.1.im)=
      zetaPrimeLogFilter (zetaRightHalfPoleJetFilter rho hrho) N (3/2+I*rho.1.im)-
        zetaProperPrimePowerFilter (zetaRightHalfPoleJetFilter rho hrho) N (3/2+I*rho.1.im) := by
    rw [zetaPrimeLogFilter_eq_prime_add_proper _ _ (by norm_num : 1<(3/2+I*rho.1.im).re)]
    ring
  have hu : ‖((3/2-rho.1.re : ℝ) : ℂ)‖<1 := by
    rw [Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos (by linarith [NontrivialZetaZero.re_lt_one rho] : 0<3/2-rho.1.re)]
    linarith
  simp_rw [he,mul_sub]
  simpa only [sub_zero] using (tendsto_zetaRightHalfPoleJetFilter rho hrho).sub
    (tendsto_zetaProperPrimePowerFilter_mul_pow (zetaRightHalfPoleJetFilter rho hrho) rho.1.im hu)

/-- Actual ordinary-prime fibers also survive the FULL coprime inverse. -/
theorem logInverse_prime {p : ℕ} (hp : p.Prime) : logInverse p=Real.log p := by
  rw [logInverse_squarefree hp.squarefree,ArithmeticFunction.vonMangoldt_apply_prime hp]

/-- Untwisted nonnegativity cannot be promoted to twisted positivity,
even after deleting any finite head. The counterexample is an ACTUAL
prime at the requested fixed height, not a free or generalized-prime row. -/
theorem exists_negative_phased_inverse_above {y : ℝ} (hy : y≠0) (H : ℕ) :
    ∃ p : ℕ,H<p ∧ p.Prime ∧ (phasedLogInverse y p).re<0 := by
  obtain ⟨p,hH,hp,hn⟩ :=
    ArithmeticOperatorTwistedBulkAudit.exists_negative_prime_diagonal_above hy H
  refine ⟨p,hH,hp,?_⟩
  rw [ArithmeticOperatorGcdAudit.gcdKernel, Nat.gcd_self,
    hp.divisors,Finset.sum_pair (by exact hp.ne_one.symm),
    ArithmeticFunction.vonMangoldt_apply_one,Complex.ofReal_zero,zero_mul,
    zero_add,ArithmeticFunction.vonMangoldt_apply_prime hp] at hn
  simpa only [phasedLogInverse,logInverse_prime hp] using hn

theorem not_twisted_inverse_nonnegative {y : ℝ} (hy : y≠0) (H : ℕ) :
    ¬ ∀ n : ℕ,H<n → 0≤(phasedLogInverse y n).re := by
  obtain ⟨p,hp,_,hn⟩ := exists_negative_phased_inverse_above hy H
  exact fun h => (not_lt_of_ge (h p hp)) hn

/-- In particular every genuine zero ordinate has the same pointwise
obstruction, without an exposed/simple-zero hypothesis. -/
theorem negative_phased_inverse_at_zero (rho : NontrivialZetaZero) (H : ℕ) :
    ∃ p : ℕ,H<p ∧ p.Prime ∧ (phasedLogInverse rho.1.im p).re<0 :=
  exists_negative_phased_inverse_above (NontrivialZetaZero.im_ne_zero_of_eta_mass rho) H


/-- Arbitrary cofactor-row input used ONLY for the collapse audit.
These inputs are not assumed to satisfy the actual Gamma/logarithmic
relations or to be a generalized-prime system. -/
def freeNative (X : ℕ) (y : ℝ) (test g : ℕ → ℂ) : ℂ :=
  ∑ n∈Finset.Icc 1 X,test n*SuzukiCarryCorrelation.primePhase y n*
    unitary (fun d => (ArithmeticFunction.moebius d : ℂ)) g n

/-- Exact signed cofactor kernel, including the coprime mask INSIDE
the literal divided prefix, and the phase of the whole original label. -/
def inverseKernel (X : ℕ) (y : ℝ) (test : ℕ → ℂ) (a : ℕ) : ℂ :=
  ∑ d∈Finset.Icc 1 (X/a),if a.Coprime d then
    (ArithmeticFunction.moebius d : ℂ)*test (a*d)*
      SuzukiCarryCorrelation.primePhase y (a*d) else 0

/-- Joining does not remove the coprime or physical mask, but it yields
a single signed scalar test against the cofactor row. -/
theorem freeNative_eq_scalar (X : ℕ) (y : ℝ) (test g : ℕ → ℂ) :
    freeNative X y test g=
      ∑ a∈Finset.Icc 1 X,g a*inverseKernel X y test a := by
  have he : freeNative X y test g=
      ∑ n∈Finset.Icc 1 X,∑ da∈n.divisorsAntidiagonal,
        if da.1.Coprime da.2 then
          g da.1*(ArithmeticFunction.moebius da.2 : ℂ)*
            test (da.1*da.2)*SuzukiCarryCorrelation.primePhase y (da.1*da.2) else 0 := by
    unfold freeNative unitary
    apply Finset.sum_congr rfl
    intro n _
    rw [Finset.mul_sum]
    conv_lhs => rw [← Nat.map_swap_divisorsAntidiagonal,Finset.sum_map]
    apply Finset.sum_congr rfl
    intro da hda
    have hprod := (Nat.mem_divisorsAntidiagonal.mp hda).1
    change test n*SuzukiCarryCorrelation.primePhase y n*
      (if da.2.Coprime da.1 then (ArithmeticFunction.moebius da.2 : ℂ)*g da.1 else 0)=_
    by_cases hc : da.1.Coprime da.2
    · rw [ite_eq_left hc,ite_eq_left hc.symm,hprod]
      ring
    · have hc' : ¬ da.2.Coprime da.1 := fun h => hc h.symm
      rw [ite_eq_right hc,ite_eq_right hc',mul_zero]
  rw [he,sum_Icc_divisorsAntidiagonal_eq_sum_divided_prefix X
    (fun a d => if a.Coprime d then g a*(ArithmeticFunction.moebius d : ℂ)*
      test (a*d)*SuzukiCarryCorrelation.primePhase y (a*d) else 0)]
  apply Finset.sum_congr rfl
  intro a _
  rw [inverseKernel,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _
  split_ifs <;> simp [mul_assoc]

/-- The actual logarithmic row is a constrained specialization.
All proper powers and literal coprime fibers remain. -/
theorem literal_native_eq_scalar (X : ℕ) (y : ℝ) (test : ℕ → ℂ) :
    (∑ n∈Finset.Icc 1 X,test n*phasedLogInverse y n)=
      ∑ a∈Finset.Icc 1 X,(Real.log a : ℂ)*inverseKernel X y test a := by
  rw [← freeNative_eq_scalar]
  unfold freeNative phasedLogInverse
  apply Finset.sum_congr rfl
  intro n _
  have he : (logInverse n : ℂ)=
      unitary (fun d => (ArithmeticFunction.moebius d : ℂ))
        (fun a => (Real.log a : ℂ)) n := by
    rw [logInverse_eq,unitary]
    rw [Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro da _
    split_ifs <;> simp
  rw [he]
  ring

/-- A universal bound for FREE cofactor rows is possible only when
the whole signed kernel vanishes. This says nothing about the existence
of a bound for the constrained ACTUAL logarithmic row. -/
theorem bound_forall_free_rows_iff (X : ℕ) (y : ℝ) (test : ℕ → ℂ) (B : ℝ) :
    (∀ g,‖freeNative X y test g‖≤B) ↔
      0≤B ∧ ∀ a∈Finset.Icc 1 X,inverseKernel X y test a=0 := by
  simp_rw [freeNative_eq_scalar]
  exact ArithmeticOperatorGramAudit.scalar_bound_forall_weights_iff _ _ _

/-- The coprime inverse's logarithmic Leibniz identity is exact on
the actual coefficient coordinates. -/
theorem logInverse_mul {a b : ℕ} (hc : a.Coprime b) :
    logInverse (a*b)=constantInverse a*logInverse b+constantInverse b*logInverse a := by
  have he := congrArg TrivSqZeroExt.snd (inverseJet_mul hc)
  simp only [TrivSqZeroExt.snd_mul,smul_eq_mul] at he
  change logInverse (a*b)=constantInverse a*logInverse b+
    logInverse a*constantInverse b at he
  simpa only [mul_comm (logInverse a)] using he

/-- A fixed powerful cofactor does not extinguish the actual prime
row. This sector is retained, not paid as a prime-power error. -/
theorem powerful_prime_row {a p : ℕ} (ha : a≠0) (hpow : singlePrimes a=∅)
    (hp : p.Prime) (hc : a.Coprime p) :
    logInverse (a*p)=Real.log p := by
  have hA : constantInverse a=1 := by
    rw [constantInverse,inverseJet_of_no_single ha hpow]
    simp [gammaJet]
  have hP : constantInverse p=0 := by
    simpa [pow_one] using constantInverse_prime_pow hp (by norm_num : 0<1)
  rw [logInverse_mul hc,hA,hP,one_mul,zero_mul,add_zero,logInverse_prime hp]

end
end RiemannGaussian.ArithmeticOperatorUnitaryInverseAudit
