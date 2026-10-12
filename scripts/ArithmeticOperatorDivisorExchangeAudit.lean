/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ArithmeticOperatorGammaTwistAudit
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic.Linter
import Lean.Util.CollectAxioms

/-! # Finite native divisor exchange: PSD gate and prescribed prime towers

The prefix matrices below are the actual divisor-incidence and Mobius
inverse entries, with the fixed-height phase kept. The source-retaining
commutator and the centered conjugated operator are different. Their prime
fibers reject universal semidefiniteness; this does not reject a prescribed
Mangoldt signed estimate. The actual prime-power tower has an exact signed
telescope, whose density/source strength is audited separately.
-/
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 2048
noncomputable section
open scoped Classical BigOperators ComplexConjugate
namespace OpenAIReview.DivisorExchange
open RiemannGaussian RiemannGaussian.SuzukiCarryCorrelation

/-- Literal finite-cutoff divisor incidence. -/
def zetaEntry (n d : ℕ) : ℂ := if d ∣ n then 1 else 0

/-- Literal integer Mobius inverse incidence, with every prime power. -/
def moebiusEntry (n d : ℕ) : ℂ :=
  if d ∣ n then (ArithmeticFunction.moebius (n/d) : ℂ) else 0

/-- Both reciprocal fixed-height phases, joined before taking real parts. -/
def phasePair (y : ℝ) (n : ℕ) : ℂ := primePhase y n + primePhase (-y) n

/-- Native prefix M(T_y+T_-y)Z; no cofactor is completed or norm-paid. -/
def conjugatedEntry (X : ℕ) (y : ℝ) (n m : ℕ) : ℂ :=
  ∑ d ∈ Finset.Icc 1 X, moebiusEntry n d * phasePair y d * zetaEntry d m

/-- The centered conjugated operator E=M(T_y+T_-y)Z-2I. -/
def centeredEntry (X : ℕ) (y : ℝ) (n m : ℕ) : ℂ :=
  conjugatedEntry X y n m - if n=m then 2 else 0

/-- The distinct commutator C=M(T_y+T_-y)Z-(T_y+T_-y). -/
def commutatorEntry (X : ℕ) (y : ℝ) (n m : ℕ) : ℂ :=
  conjugatedEntry X y n m - if n=m then phasePair y n else 0

/-- Genuine finite row quadratic, including an explicit head and cutoff. -/
def nativeQuadratic (entry : ℕ → ℕ → ℂ) (head X : ℕ) (a : ℕ → ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc (head+1) X, ∑ m ∈ Finset.Icc (head+1) X,
    conj (a n) * entry n m * a m

theorem phasePair_eq_cos (y : ℝ) (n : ℕ) :
    phasePair y n = ((2 * Real.cos (y*Real.log n) : ℝ) : ℂ) := by
  apply Complex.ext <;>
    simp only [phasePair, primePhase, Complex.exp_re, Complex.exp_im,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, one_mul,
      sub_zero, neg_zero, Real.exp_zero, zero_add,
      Real.cos_neg, Real.sin_neg, one_mul, neg_mul, neg_neg] <;> ring

@[simp] theorem phasePair_one (y : ℝ) : phasePair y 1=2 := by
  norm_num [phasePair, primePhase]

private theorem prefix_divisor_filter {X n : ℕ} (hn : 0<n) (hnX : n≤X) :
    (Finset.Icc 1 X).filter (fun d => d ∣ n)=n.divisors := by
  ext d
  simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨_,_⟩,hd⟩
    exact ⟨hd,hn.ne'⟩
  · rintro ⟨hd,_⟩
    exact ⟨⟨Nat.pos_of_dvd_of_pos hd hn,(Nat.le_of_dvd hn hd).trans hnX⟩,hd⟩

theorem conjugatedEntry_eq_divisors {X n : ℕ} (hn : 0<n) (hnX : n≤X)
    (y : ℝ) (m : ℕ) :
    conjugatedEntry X y n m = ∑ d ∈ n.divisors,
      (ArithmeticFunction.moebius (n/d) : ℂ)*phasePair y d*zetaEntry d m := by
  unfold conjugatedEntry moebiusEntry
  simp only [ite_mul, zero_mul]
  rw [← Finset.sum_filter,prefix_divisor_filter hn hnX]

/-- This is a row of the full native prefix, not an invented 2x2 array. -/
theorem conjugated_prime_row {p X : ℕ} (hp : p.Prime) (hpX : p≤X)
    (y : ℝ) (m : ℕ) :
    conjugatedEntry X y p m = -2*zetaEntry 1 m + phasePair y p*zetaEntry p m := by
  rw [conjugatedEntry_eq_divisors hp.pos hpX, hp.divisors]
  simp [ArithmeticFunction.moebius_apply_prime hp,hp.ne_one.symm,Nat.div_self hp.pos]

theorem conjugated_one_row {X : ℕ} (hX : 0<X) (y : ℝ) (m : ℕ) :
    conjugatedEntry X y 1 m=2*zetaEntry 1 m := by
  rw [conjugatedEntry_eq_divisors (by omega) (by omega)]
  simp

/-- All four entries are inherited from the same literal prefix. -/
theorem centered_prime_fiber {p X : ℕ} (hp : p.Prime) (hpX : p≤X) (y : ℝ) :
    centeredEntry X y 1 1=0 ∧ centeredEntry X y 1 p=0 ∧
    centeredEntry X y p 1=phasePair y p-2 ∧
    centeredEntry X y p p=phasePair y p-2 := by
  have hX : 0<X := hp.pos.trans_le hpX
  simp [centeredEntry, conjugated_one_row hX, conjugated_prime_row hp hpX,
    zetaEntry,hp.ne_one,hp.ne_one.symm,hp.not_dvd_one]
  ring

/-- C has zero diagonal while E has a nonzero prime diagonal. -/
theorem commutator_prime_fiber {p X : ℕ} (hp : p.Prime) (hpX : p≤X) (y : ℝ) :
    commutatorEntry X y 1 1=0 ∧ commutatorEntry X y 1 p=0 ∧
    commutatorEntry X y p 1=phasePair y p-2 ∧
    commutatorEntry X y p p=0 := by
  have hX : 0<X := hp.pos.trans_le hpX
  simp [commutatorEntry, conjugated_one_row hX, conjugated_prime_row hp hpX,
    zetaEntry,hp.ne_one,hp.ne_one.symm,hp.not_dvd_one]
  ring

/-- Two actual rows, with an explicit zero extension to the native cutoff. -/
def primeFiberVector (p : ℕ) (a b : ℂ) (n : ℕ) : ℂ :=
  if n=1 then a else if n=p then b else 0

private theorem quadratic_prime_fiber {p X : ℕ} (hp : p.Prime) (hpX : p≤X)
    (entry : ℕ → ℕ → ℂ) (a b : ℂ) :
    nativeQuadratic entry 0 X (primeFiberVector p a b)=
      conj a*entry 1 1*a + conj a*entry 1 p*b +
        conj b*entry p 1*a + conj b*entry p p*b := by
  have hX : 0<X := hp.pos.trans_le hpX
  have hsub : ({1,p}:Finset ℕ) ⊆ Finset.Icc 1 X := by
    intro n hn
    simp only [Finset.mem_insert,Finset.mem_singleton] at hn
    rcases hn with rfl|rfl
    · exact Finset.mem_Icc.mpr ⟨le_rfl,by omega⟩
    · exact Finset.mem_Icc.mpr ⟨hp.pos,hpX⟩
  have hz (n : ℕ) (hn : n∉({1,p}:Finset ℕ)) : primeFiberVector p a b n=0 := by
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hn
    simp [primeFiberVector,hn.1,hn.2]
  unfold nativeQuadratic
  simp only [zero_add]
  calc
    _ = ∑ n ∈ ({1,p}:Finset ℕ), ∑ m ∈ Finset.Icc 1 X,
        conj (primeFiberVector p a b n)*entry n m*primeFiberVector p a b m := by
      symm
      apply Finset.sum_subset hsub
      intro n _ hn
      simp [hz n hn]
    _ = ∑ n ∈ ({1,p}:Finset ℕ), ∑ m ∈ ({1,p}:Finset ℕ),
        conj (primeFiberVector p a b n)*entry n m*primeFiberVector p a b m := by
      apply Finset.sum_congr rfl
      intro n _
      symm
      apply Finset.sum_subset hsub
      intro m _ hm
      simp [hz m hm]
    _ = _ := by
      simp [primeFiberVector,hp.ne_one,hp.ne_one.symm]
      ring

theorem centered_prime_quadratic {p X : ℕ} (hp : p.Prime) (hpX : p≤X)
    (y : ℝ) (a b : ℂ) :
    nativeQuadratic (centeredEntry X y) 0 X (primeFiberVector p a b)=
      conj b*(phasePair y p-2)*(a+b) := by
  rw [quadratic_prime_fiber hp hpX]
  obtain ⟨h11,h1p,hp1,hpp⟩ := centered_prime_fiber hp hpX y
  rw [h11,h1p,hp1,hpp]
  ring

theorem commutator_prime_quadratic {p X : ℕ} (hp : p.Prime) (hpX : p≤X)
    (y : ℝ) (a b : ℂ) :
    nativeQuadratic (commutatorEntry X y) 0 X (primeFiberVector p a b)=
      conj b*(phasePair y p-2)*a := by
  rw [quadratic_prime_fiber hp hpX]
  obtain ⟨h11,h1p,hp1,hpp⟩ := commutator_prime_fiber hp hpX y
  rw [h11,h1p,hp1,hpp]
  ring

/-- A genuine campaign-height witness, with no floating trigonometry. -/
def witnessHeight : ℝ := 19*Real.pi/Real.log 2

theorem witnessHeight_ge : 54<witnessHeight := by
  have hl : 0<Real.log (2:ℝ) := Real.log_pos (by norm_num)
  have hu : Real.log (2:ℝ)≤1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : 0<(2:ℝ))
    norm_num at h
    exact h
  rw [witnessHeight,lt_div_iff₀ hl]
  nlinarith [Real.pi_gt_three]

theorem phasePair_witness : phasePair witnessHeight 2 = -2 := by
  rw [phasePair_eq_cos]
  have hl : Real.log (2:ℝ)≠0 := (Real.log_pos (by norm_num : 1<(2:ℝ))).ne'
  have he : witnessHeight*Real.log 2=19*Real.pi := by
    unfold witnessHeight
    field_simp
  norm_num only [Nat.cast_ofNat] at *
  rw [he]
  have hc := Real.cos_nat_mul_pi 19
  norm_num at hc
  rw [hc]
  norm_num

theorem actual_centered_negative :
    (nativeQuadratic (centeredEntry 2 witnessHeight) 0 2
      (primeFiberVector 2 0 1)).re = -4 := by
  rw [centered_prime_quadratic Nat.prime_two (by omega),phasePair_witness]
  norm_num

theorem actual_centered_positive :
    (nativeQuadratic (centeredEntry 2 witnessHeight) 0 2
      (primeFiberVector 2 (-2) 1)).re = 4 := by
  rw [centered_prime_quadratic Nat.prime_two (by omega),phasePair_witness]
  norm_num

theorem actual_commutator_negative :
    (nativeQuadratic (commutatorEntry 2 witnessHeight) 0 2
      (primeFiberVector 2 1 1)).re = -4 := by
  rw [commutator_prime_quadratic Nat.prime_two (by omega),phasePair_witness]
  norm_num

theorem actual_commutator_positive :
    (nativeQuadratic (commutatorEntry 2 witnessHeight) 0 2
      (primeFiberVector 2 (-1) 1)).re = 4 := by
  rw [commutator_prime_quadratic Nat.prime_two (by omega),phasePair_witness]
  norm_num

/-- Actual M(T_y+T_-y)Z applied to the literal Mangoldt array. -/
def inverseLogRow (y : ℝ) (n : ℕ) : ℂ :=
  ∑ da ∈ n.divisorsAntidiagonal,
    (ArithmeticFunction.moebius da.1 : ℂ)*phasePair y da.2*(Real.log da.2 : ℂ)

/-- Actual prescribed-vector E response, distinct from a free quadratic. -/
def centeredLambda (y : ℝ) (n : ℕ) : ℂ :=
  inverseLogRow y n-2*(ArithmeticFunction.vonMangoldt n : ℂ)

/-- Source-retaining commutator applied to the same actual vector. -/
def commutatorLambda (y : ℝ) (n : ℕ) : ℂ :=
  inverseLogRow y n-phasePair y n*(ArithmeticFunction.vonMangoldt n : ℂ)

private theorem mangoldt_prefix {X d : ℕ} (hd : 0<d) (hdX : d≤X) :
    (∑ m ∈ Finset.Icc 1 X, zetaEntry d m*(ArithmeticFunction.vonMangoldt m : ℂ))=
      (Real.log d : ℂ) := by
  simp only [zetaEntry,ite_mul,one_mul,zero_mul]
  rw [← Finset.sum_filter,prefix_divisor_filter hd hdX,
    ← Complex.ofReal_sum,ArithmeticFunction.vonMangoldt_sum]

/-- Exact forward/inverse join at the SAME native cutoff. -/
theorem native_mangoldt_conjugated {X n : ℕ} (hn : 0<n) (hnX : n≤X) (y : ℝ) :
    (∑ m ∈ Finset.Icc 1 X,
      conjugatedEntry X y n m*(ArithmeticFunction.vonMangoldt m : ℂ))=
      inverseLogRow y n := by
  simp_rw [conjugatedEntry,Finset.sum_mul]
  rw [Finset.sum_comm]
  have he : (∑ d ∈ Finset.Icc 1 X, ∑ m ∈ Finset.Icc 1 X,
      moebiusEntry n d*phasePair y d*zetaEntry d m*(ArithmeticFunction.vonMangoldt m : ℂ))=
      ∑ d ∈ Finset.Icc 1 X,moebiusEntry n d*phasePair y d*(Real.log d : ℂ) := by
    apply Finset.sum_congr rfl
    intro d hd
    simp only [mul_assoc,← Finset.mul_sum]
    rw [mangoldt_prefix (Finset.mem_Icc.mp hd).1 (Finset.mem_Icc.mp hd).2]
  rw [he]
  unfold moebiusEntry
  simp only [ite_mul,zero_mul]
  rw [← Finset.sum_filter,prefix_divisor_filter hn hnX]
  unfold inverseLogRow
  exact (Nat.sum_divisorsAntidiagonal' (fun a b =>
    (ArithmeticFunction.moebius a : ℂ)*phasePair y b*(Real.log b : ℂ))).symm

/-- No prime power, phase, cutoff or diagonal is deleted in the E join. -/
theorem native_mangoldt_centered {X n : ℕ} (hn : 0<n) (hnX : n≤X) (y : ℝ) :
    (∑ m ∈ Finset.Icc 1 X,
      centeredEntry X y n m*(ArithmeticFunction.vonMangoldt m : ℂ))=
      centeredLambda y n := by
  simp only [centeredEntry,sub_mul,Finset.sum_sub_distrib]
  rw [native_mangoldt_conjugated hn hnX]
  have hn1 : 1≤n := hn
  simp only [ite_mul,zero_mul,Finset.sum_ite_eq,Finset.mem_Icc,
    hn1,hnX,and_self,ite_true,centeredLambda]

/-- C joins to a different prescribed-vector response at the same cutoff. -/
theorem native_mangoldt_commutator {X n : ℕ} (hn : 0<n) (hnX : n≤X) (y : ℝ) :
    (∑ m ∈ Finset.Icc 1 X,
      commutatorEntry X y n m*(ArithmeticFunction.vonMangoldt m : ℂ))=
      commutatorLambda y n := by
  simp only [commutatorEntry,sub_mul,Finset.sum_sub_distrib]
  rw [native_mangoldt_conjugated hn hnX]
  have hn1 : 1≤n := hn
  simp only [ite_mul,zero_mul,Finset.sum_ite_eq,Finset.mem_Icc,
    hn1,hnX,and_self,ite_true,commutatorLambda]

private theorem sum_prime_pow {R : Type*} [AddCommMonoid R] {p : ℕ}
    (hp : p.Prime) (k : ℕ) (F : ℕ → ℕ → R) :
    (∑ da∈(p^k).divisorsAntidiagonal,F da.1 da.2)=
      ∑ i∈Finset.range (k+1),F (p^i) (p^(k-i)) := by
  symm
  apply Finset.sum_nbij (fun i => (p^i,p^(k-i)))
  · intro i hi
    have hik : i≤k := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    exact Nat.mem_divisorsAntidiagonal.mpr
      ⟨by rw [← pow_add,Nat.add_sub_of_le hik],pow_ne_zero _ hp.ne_zero⟩
  · intro i _ j _ he
    exact (Nat.pow_right_inj hp.one_lt).mp (congrArg Prod.fst he)
  · intro da hda
    obtain ⟨i,hi,he⟩ := (Nat.mem_divisors_prime_pow hp k).mp
      (Nat.fst_mem_divisors_of_mem_antidiagonal hda)
    obtain ⟨j,_,hf⟩ := (Nat.mem_divisors_prime_pow hp k).mp
      (Nat.snd_mem_divisors_of_mem_antidiagonal hda)
    have hs : i+j=k := (Nat.pow_right_inj hp.one_lt).mp (by
      rw [pow_add,← he,← hf]; exact (Nat.mem_divisorsAntidiagonal.mp hda).1)
    refine ⟨i,Finset.mem_range.mpr (by omega),?_⟩
    apply Prod.ext
    · exact he.symm
    · change p^(k-i)=da.2
      rw [show k-i=j by omega]; exact hf.symm
  · intro i _
    rfl

/-- Full literal Mobius inversion on a prime-power tower. -/
theorem inverseLogRow_prime_pow {p : ℕ} (hp : p.Prime) (y : ℝ) (k : ℕ) :
    inverseLogRow y (p^(k+1))=
      phasePair y (p^(k+1))*((k+1 : ℕ):ℂ)*(Real.log p : ℂ)-
        phasePair y (p^k)*(k:ℂ)*(Real.log p : ℂ) := by
  unfold inverseLogRow
  rw [sum_prime_pow hp (k+1) (fun a b =>
    (ArithmeticFunction.moebius a : ℂ)*phasePair y b*(Real.log b : ℂ))]
  have hsub : ({0,1}:Finset ℕ)⊆Finset.range (k+1+1) := by
    intro i hi
    simp only [Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl|rfl <;> simp
  have he : (∑ i∈Finset.range (k+1+1),
      (ArithmeticFunction.moebius (p^i):ℂ)*phasePair y (p^(k+1-i))*
        (Real.log (p^(k+1-i):ℕ):ℂ))=
      ∑ i∈({0,1}:Finset ℕ),
        (ArithmeticFunction.moebius (p^i):ℂ)*phasePair y (p^(k+1-i))*
          (Real.log (p^(k+1-i):ℕ):ℂ) := by
    symm
    apply Finset.sum_subset hsub
    intro i _ hi
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hi
    rw [ArithmeticFunction.moebius_apply_prime_pow hp hi.1,ite_eq_right hi.2]
    simp
  rw [he]
  simp [ArithmeticFunction.moebius_apply_prime hp,Nat.cast_pow,Real.log_pow]
  ring

/-- The parenthesized expression has real sign; all phases remain exact. -/
theorem centeredLambda_prime_pow {p : ℕ} (hp : p.Prime) (y : ℝ) (k : ℕ) :
    centeredLambda y (p^(k+1))=
      (2*Real.log p*((k+1:ℕ)*
        (Real.cos (y*Real.log (p^(k+1):ℕ))-1)-
          k*(Real.cos (y*Real.log (p^k:ℕ))-1)):ℝ) := by
  rw [centeredLambda,inverseLogRow_prime_pow hp,
    ArithmeticFunction.vonMangoldt_apply_pow (by omega),
    ArithmeticFunction.vonMangoldt_apply_prime hp,phasePair_eq_cos,phasePair_eq_cos]
  push_cast
  ring

/-- The source-retaining commutator vanishes on ORDINARY prime outputs. -/
theorem commutatorLambda_prime {p : ℕ} (hp : p.Prime) (y : ℝ) :
    commutatorLambda y p=0 := by
  have h:=inverseLogRow_prime_pow hp y 0
  simp only [zero_add,pow_one,pow_zero,Nat.cast_one,Nat.cast_zero,mul_one,
    mul_zero,zero_mul,sub_zero] at h
  rw [commutatorLambda,h,ArithmeticFunction.vonMangoldt_apply_prime hp,sub_self]

/-- Every proper power and low-order endpoint is retained in this formula. -/
theorem commutatorLambda_prime_pow {p : ℕ} (hp : p.Prime) (y : ℝ) (k : ℕ) :
    commutatorLambda y (p^(k+1))=
      (2*Real.log p*k*(Real.cos (y*Real.log (p^(k+1):ℕ))-
        Real.cos (y*Real.log (p^k:ℕ))):ℝ) := by
  rw [commutatorLambda,inverseLogRow_prime_pow hp,
    ArithmeticFunction.vonMangoldt_apply_pow (by omega),
    ArithmeticFunction.vonMangoldt_apply_prime hp,phasePair_eq_cos,phasePair_eq_cos]
  push_cast
  ring

/-- A COMPLETE prime-power tower joins before sign or norm is used. -/
theorem centered_tower_telescope {p : ℕ} (hp : p.Prime) (y : ℝ) (J : ℕ) :
    (∑ k∈Finset.range J,(ArithmeticFunction.vonMangoldt (p^(k+1)):ℂ)*
      centeredLambda y (p^(k+1)))=
      (2*(Real.log p)^2*J*(Real.cos (y*Real.log (p^J:ℕ))-1):ℝ) := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [Finset.sum_range_succ,ih,centeredLambda_prime_pow hp,
      ArithmeticFunction.vonMangoldt_apply_pow (by omega),
      ArithmeticFunction.vonMangoldt_apply_prime hp]
    push_cast
    ring

/-- A genuine prescribed-array sign that is compatible with the zero source.
It is NOT a density-centered saving or a whole-space PSD theorem. -/
theorem centered_tower_nonpos {p : ℕ} (hp : p.Prime) (y : ℝ) (J : ℕ) :
    (∑ k∈Finset.range J,(ArithmeticFunction.vonMangoldt (p^(k+1)):ℂ)*
      centeredLambda y (p^(k+1))).re≤0 := by
  rw [centered_tower_telescope hp,Complex.ofReal_re]
  have hcos := Real.cos_le_one (y*Real.log (p^J:ℕ))
  exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (sub_nonpos.mpr hcos)

/-- Testing C on the actual Mangoldt diagonal removes its ordinary-prime
channel exactly, even though its LINEAR composite-output source survives. -/
theorem commutator_diagonal_prime_zero {p : ℕ} (hp : p.Prime) (y : ℝ) :
    (ArithmeticFunction.vonMangoldt p : ℂ)*commutatorLambda y p=0 := by
  rw [commutatorLambda_prime hp,mul_zero]

/-- Only proper prime powers can survive this prescribed quadratic test. -/
theorem commutator_diagonal_support {n : ℕ} (y : ℝ)
    (hn : (ArithmeticFunction.vonMangoldt n : ℂ)*commutatorLambda y n≠0) :
    IsPrimePow n ∧ ¬n.Prime := by
  constructor
  · apply ArithmeticFunction.vonMangoldt_ne_zero_iff.mp
    intro hzero
    simp [hzero] at hn
  · intro hp
    exact hn (commutator_diagonal_prime_zero hp y)

/-- Universal positive AND negative semidefiniteness fail on genuine
integer-prime rows at a campaign height. This does not reject the
prescribed actual-Mangoldt tower sign proved above. -/
theorem centered_not_universally_semidefinite :
    ¬(∀a : ℕ→ℂ,0≤(nativeQuadratic (centeredEntry 2 witnessHeight) 0 2 a).re) ∧
    ¬(∀a : ℕ→ℂ,(nativeQuadratic (centeredEntry 2 witnessHeight) 0 2 a).re≤0) := by
  constructor
  · intro h
    have hh:=h (primeFiberVector 2 0 1)
    rw [actual_centered_negative] at hh
    norm_num at hh
  · intro h
    have hh:=h (primeFiberVector 2 (-2) 1)
    rw [actual_centered_positive] at hh
    norm_num at hh

end OpenAIReview.DivisorExchange

#lint+ in OpenAIReview.DivisorExchange

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
  unless declarations>0 do throwError "Empty native divisor exchange audit."
  logInfo m!"Native divisor exchange audit: {declarations} declarations, {theorems} theorems; only standard axioms."
  IO.FS.writeFile ".lake/arithmetic-operator-commutator-source-exchange/axioms.json"
    (Json.mkObj [("scope",toJson "actual finite divisor/Mobius exchange, same native cutoff, prime fibers and complete prescribed Mangoldt towers; no density-centered arithmetic payment"),
      ("onlyStandardAxioms",toJson true),("namespaceLinters",toJson (15:Nat)),
      ("allLocalDeclarationsByModuleProvenance",toJson true),
      ("declarations",toJson declarations),("theoremsIncludingGeneratedHelpers",toJson theorems),
      ("declarationAxioms",Json.arr reports)]).pretty
