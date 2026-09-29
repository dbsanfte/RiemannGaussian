/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszJointPrimeEnergy
import RiemannGaussian.ZetaSquarefreeRieszWindows

/-!
# A signed quadratic correction sharpens the coupled carrier enclosure

The second logarithmic divisor moment vanishes above two cofactor primes.
Its exact remaining semiprime response is retained as a signed center,
while projecting the full prime profiles reduces their joint energy.
Counts, orders, masks and phases remain coupled. Neither the signed center
nor the resulting whole source-scale budget is asserted small.
-/

noncomputable section
open scoped BigOperators Classical ArithmeticFunction.Moebius
namespace RiemannGaussian.ZetaRieszQuadraticPrimeEnergy
open Real ZetaRieszJointPrimeEnergy ZetaRieszCenteredPrimeEnergy

/-- The explicit second logarithmic profile; it is not a new moment filter. -/
def logSquare (d : ℕ) : ℝ := log d^2

/-- The actual arithmetic second logarithmic divisor moment. -/
def secondMoment (n : ℕ) : ℝ := divisorResponse logSquare n

/-- Exact prime insertion in the literal divisor response, with coprimality
retained. Higher logarithmic moments reuse the same finite identity. -/
theorem divisor_prime_mul {p n : ℕ} (hp : p.Prime) (hpn : ¬p ∣ n)
    (f : ℕ → ℝ) :
    divisorResponse f (p*n) =
      ∑ d ∈ n.divisors, (μ d : ℝ)*(f d-f (p*d)) := by
  apply Complex.ofReal_injective
  simp only [divisorResponse,Complex.ofReal_sum,Complex.ofReal_mul]
  rw [sum_divisors_coprime_product (hp.coprime_iff_not_dvd.mpr hpn)]
  apply Finset.sum_congr rfl
  intro d hd
  rw [hp.sum_divisors]
  have hcop := (hp.coprime_iff_not_dvd.mpr hpn).of_dvd_right (Nat.dvd_of_mem_divisors hd)
  rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop]
  simp [ArithmeticFunction.moebius_apply_prime hp]
  ring

/-- A third cofactor prime annihilates the entire quadratic logarithmic
moment. The statement is independent of every Riesz/share/phase mask. -/
theorem secondMoment_prime_mul {p n : ℕ} (hp : p.Prime) (hpn : ¬p ∣ n)
    (hn : Squarefree n) (hn1 : n ≠ 1) (hnp : ¬n.Prime) :
    secondMoment (p*n)=0 := by
  have hm : (∑ d ∈ n.divisors, (μ d : ℝ))=0 := by
    exact_mod_cast ZetaRieszPrimeFourier.sum_moebius_eq_zero hn1
  have hl : (∑ d ∈ n.divisors, (μ d : ℝ)*log d)=0 := by
    exact_mod_cast ZetaRieszPrimeFourier.sum_moebius_log_eq_zero hn hnp
  unfold secondMoment
  rw [divisor_prime_mul hp hpn]
  have he : (∑ d ∈ n.divisors, (μ d : ℝ)*(logSquare d-logSquare (p*d))) =
      -2*log p*(∑ d ∈ n.divisors, (μ d : ℝ)*log d)-
        log p^2*(∑ d ∈ n.divisors, (μ d : ℝ)) := by
    simp only [Finset.mul_sum,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mem_divisors hd).ne'
    simp only [logSquare,Nat.cast_mul,log_mul
      hp0 hd0]
    ring
  rw [he,hm,hl]
  ring

/-- On the only surviving composite class the moment is the exact positive
semiprime product, not an absolute-value allowance. -/
theorem secondMoment_two_primes {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    secondMoment (p*q)=2*log p*log q := by
  unfold secondMoment
  rw [divisor_prime_mul hp (fun h => hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp h)),hq.sum_divisors]
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne_zero
  simp only [ArithmeticFunction.moebius_apply_one,Int.cast_one,one_mul,
    ArithmeticFunction.moebius_apply_prime hq,Int.cast_neg,logSquare,Nat.cast_one,log_one,
    zero_pow (by decide : 2 ≠ 0),Nat.mul_one,Nat.cast_mul,
    log_mul hp0 hq0]
  ring

/-- Every higher squarefree cofactor count has zero correction, with no
restriction on its prime shares or the observation height. -/
theorem secondMoment_eq_zero_of_count {n : ℕ} (hn : Squarefree n)
    (hc : 3 ≤ n.primeFactors.card) : secondMoment n=0 := by
  obtain ⟨p,hp⟩ := Finset.card_pos.mp (by omega : 0 < n.primeFactors.card)
  have hpp := Nat.prime_of_mem_primeFactors hp
  have he : p*(n/p)=n := Nat.mul_div_cancel' (Nat.dvd_of_mem_primeFactors hp)
  have hs : Squarefree (p*(n/p)) := by rw [he]; exact hn
  have hm := hs.of_mul_right
  have hnot : ¬p ∣ n/p := hpp.coprime_iff_not_dvd.mp (Nat.coprime_of_squarefree_mul hs)
  have hcard : n.primeFactors.card=(n/p).primeFactors.card+1 := by
    conv_lhs => rw [← he]
    rw [Nat.primeFactors_mul hpp.ne_zero hm.ne_zero,hpp.primeFactors,
      Finset.singleton_union,Finset.card_insert_of_notMem
        (fun h => hnot (Nat.dvd_of_mem_primeFactors h))]
  have hc2 : 2 ≤ (n/p).primeFactors.card := by omega
  have hm1 : n/p ≠ 1 := by intro h; simp [h] at hc2
  have hmp : ¬(n/p).Prime := by intro h; simp [h.primeFactors] at hc2
  simpa only [he] using secondMoment_prime_mul hpp hnot hm hm1 hmp

/-- Center the first differences by the already free logarithmic moment. -/
def centeredDelta (X : ℕ) (f : ℕ → ℝ) (k : ℕ) : ℝ :=
  f k-f (k+1)-(logCross X f/logEnergy X)*logStep k

private theorem energy_delta (X : ℕ) (f : ℕ → ℝ) :
    centeredEnergy X f = ∑ k ∈ Finset.Ico 1 X, (k : ℝ)*centeredDelta X f k^2 := rfl

private theorem cross_sub (X : ℕ) (f g : ℕ → ℝ) (a : ℝ) :
    logCross X (fun d => f d-a*g d)=logCross X f-a*logCross X g := by
  simp only [logCross,Finset.mul_sum,← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun _ _ => by ring)

private theorem delta_sub (X : ℕ) (f g : ℕ → ℝ) (a : ℝ) (k : ℕ) :
    centeredDelta X (fun d => f d-a*g d) k =
      centeredDelta X f k-a*centeredDelta X g k := by
  simp only [centeredDelta,cross_sub]
  ring

/-- The signed correlation with the second logarithmic direction. -/
def quadraticCross (X : ℕ) (f : ℕ → ℝ) : ℝ :=
  ∑ k ∈ Finset.Ico 1 X, (k : ℝ)*centeredDelta X f k*centeredDelta X logSquare k

/-- The exact quadratic projection coefficient, including degenerate populations. -/
def quadraticSlope (X : ℕ) (f : ℕ → ℝ) : ℝ :=
  quadraticCross X f/centeredEnergy X logSquare

/-- The corrected prime profile retains an explicit signed arithmetic center. -/
def quadraticProfile (X : ℕ) (f : ℕ → ℝ) (d : ℕ) : ℝ :=
  f d-quadraticSlope X f*logSquare d

/-- Residual energy after removing the second logarithmic component. -/
def quadraticEnergy (X : ℕ) (f : ℕ → ℝ) : ℝ :=
  centeredEnergy X (quadraticProfile X f)

private theorem energy_sub (X : ℕ) (f : ℕ → ℝ) (a : ℝ) :
    centeredEnergy X (fun d => f d-a*logSquare d) =
      centeredEnergy X f-2*a*quadraticCross X f+a^2*centeredEnergy X logSquare := by
  simp only [energy_delta,delta_sub,quadraticCross,Finset.mul_sum,
    ← Finset.sum_sub_distrib,← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun _ _ => by ring)

/-- The exact energy saving is a squared correlation. No arithmetic sign
or unknown correction has been erased from the carrier by this equality. -/
theorem quadraticEnergy_eq (X : ℕ) (f : ℕ → ℝ) :
    quadraticEnergy X f = centeredEnergy X f-
      quadraticCross X f^2/centeredEnergy X logSquare := by
  change centeredEnergy X (fun d => f d-quadraticSlope X f*logSquare d) = _
  rw [energy_sub,quadraticSlope]
  by_cases h : centeredEnergy X logSquare=0
  · simp [h]
  · field_simp
    ring

/-- The residual quadratic energy is nonnegative at every finite endpoint. -/
theorem quadraticEnergy_nonneg (X : ℕ) (f : ℕ → ℝ) : 0 ≤ quadraticEnergy X f :=
  centeredEnergy_nonneg _ _

/-- For the SAME profile, coordinates and arithmetic constant, the
quadratic correction can only reduce the width of the signed enclosure. -/
theorem quadraticEnergy_le (X : ℕ) (f : ℕ → ℝ) :
    quadraticEnergy X f ≤ centeredEnergy X f := by
  rw [quadraticEnergy_eq]
  exact sub_le_self _ (div_nonneg (sq_nonneg _) (centeredEnergy_nonneg _ _))

/-- The exact divisor response of the removed component remains signed. -/
theorem divisor_quadratic (X n : ℕ) (f : ℕ → ℝ) :
    divisorResponse f n = divisorResponse (quadraticProfile X f) n+
      quadraticSlope X f*secondMoment n := by
  simp only [divisorResponse,quadraticProfile,secondMoment,Finset.mul_sum,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun _ _ => by ring)

/-- All counts stay in one sum. Only the actual second arithmetic moment
can contribute to this signed center; it is never replaced by a norm. -/
def quadraticCenter (X : ℕ) (S I P : Finset ℕ) (O W F : ℕ → ℕ → ℝ) : ℝ :=
  ∑ a ∈ I, quadraticSlope X (fun d => rotate P O a (fun p => F p d))*
    (∑ n ∈ S, rotate P O a (W n)*secondMoment n)

/-- The remaining coupled cost after the exact quadratic projection. -/
def quadraticCost (E : ℝ) (X : ℕ) (S I P : Finset ℕ) (O W F : ℕ → ℕ → ℝ) : ℝ :=
  ∑ a ∈ I, sqrt ((∑ n ∈ S, rotate P O a (W n)^2)*E*X*
    quadraticEnergy X (fun d => rotate P O a (fun p => F p d)))

/-- The width decreases for EVERY common coordinate choice and original
weight matrix. Comparing different centers still requires keeping the exact
signed correction; this is not a free three-prime credit. -/
theorem quadraticCost_le_jointCost {E : ℝ} (hE : 0 ≤ E) (X : ℕ)
    (S I P : Finset ℕ) (O W F : ℕ → ℕ → ℝ) :
    quadraticCost E X S I P O W F ≤ jointCost E X S I P O W F := by
  apply Finset.sum_le_sum
  intro a _
  apply sqrt_le_sqrt
  exact mul_le_mul_of_nonneg_left (quadraticEnergy_le X _)
    (mul_nonneg (mul_nonneg (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) hE) (Nat.cast_nonneg X))

/-- Common coordinates commute with the exact finite divisor response. -/
theorem divisor_rotate (P : Finset ℕ) (O F : ℕ → ℕ → ℝ) (a n : ℕ) :
    divisorResponse (fun d => rotate P O a (fun p => F p d)) n =
      rotate P O a (fun p => divisorResponse (F p) n) := by
  simp only [divisorResponse,rotate,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  exact Finset.sum_congr rfl (fun _ _ => by ring)

/-- Both signed bounds for the original coupled sum, with a PROVED
smaller width and an exact signed semiprime-cofactor center. No split of
the cofactor counts, new arithmetic assumption or completion enters. -/
theorem exists_joint_quadratic_bounds :
    ∃ E : ℝ, 0 < E ∧ ∀ (X : ℕ) (S I P : Finset ℕ) (O W F : ℕ → ℕ → ℝ),
      Coordinates I P O → S ⊆ Finset.Ioc 1 X →
      (∀ n ∈ S, Squarefree n ∧ ¬n.Prime) →
      let J := ∑ n ∈ S, ∑ p ∈ P, W n p*divisorResponse (F p) n;
      let H := quadraticCenter X S I P O W F;
      let K := quadraticCost E X S I P O W F;
      H-K ≤ J ∧ J ≤ H+K ∧ |J| ≤ jointCost E X S I P O W F := by
  obtain ⟨E,hE,hmean⟩ := exists_centered_divisor_mean
  refine ⟨E,hE,fun X S I P O W F hO hS hSF => ?_⟩
  let f := fun a d => rotate P O a (fun p => F p d)
  let w := fun a n => rotate P O a (W n)
  have hpair : (∑ n ∈ S, ∑ p ∈ P, W n p*divisorResponse (F p) n) =
      ∑ a ∈ I, ∑ n ∈ S, w a n*divisorResponse (f a) n := by
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro n _
    simp_rw [f,divisor_rotate]
    exact (coordinate_pairing I P O hO (W n) (fun p => divisorResponse (F p) n)).symm
  have hb0 a : |∑ n ∈ S, w a n*divisorResponse (f a) n| ≤
      sqrt ((∑ n ∈ S, (w a n)^2)*E*X*centeredEnergy X (f a)) := by
    have hs := (Finset.sum_mul_sq_le_sq_mul_sq S (w a) (divisorResponse (f a))).trans
      (mul_le_mul_of_nonneg_left (hmean X S (f a) hS hSF)
        (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
    apply (sq_le_sq₀ (abs_nonneg _) (sqrt_nonneg _)).mp
    rw [sq_abs,sq_sqrt (mul_nonneg (by positivity) (centeredEnergy_nonneg _ _))]
    simpa only [mul_assoc] using hs
  have hbound0 : |∑ n ∈ S, ∑ p ∈ P, W n p*divisorResponse (F p) n| ≤
      jointCost E X S I P O W F := by
    rw [hpair]
    exact (Finset.abs_sum_le_sum_abs _ I).trans (Finset.sum_le_sum (fun a _ => hb0 a))
  have hb a : |∑ n ∈ S, w a n*divisorResponse (quadraticProfile X (f a)) n| ≤
      sqrt ((∑ n ∈ S, (w a n)^2)*E*X*quadraticEnergy X (f a)) := by
    have hs := (Finset.sum_mul_sq_le_sq_mul_sq S (w a)
      (divisorResponse (quadraticProfile X (f a)))).trans
      (mul_le_mul_of_nonneg_left (hmean X S _ hS hSF)
        (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
    apply (sq_le_sq₀ (abs_nonneg _) (sqrt_nonneg _)).mp
    rw [sq_abs,sq_sqrt (mul_nonneg (by positivity) (quadraticEnergy_nonneg _ _))]
    simpa only [quadraticEnergy,mul_assoc] using hs
  have he : (∑ n ∈ S, ∑ p ∈ P, W n p*divisorResponse (F p) n) =
      quadraticCenter X S I P O W F+
        ∑ a ∈ I, ∑ n ∈ S, w a n*divisorResponse (quadraticProfile X (f a)) n := by
    rw [hpair]
    simp only [quadraticCenter,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _
    simp_rw [divisor_quadratic X _ (f a)]
    simp only [Finset.mul_sum,mul_add,← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun _ _ => by dsimp [f,w]; ring)
  have hbound := (Finset.abs_sum_le_sum_abs _ I).trans
    (Finset.sum_le_sum (fun a (_ : a ∈ I) => hb a))
  obtain ⟨hl,hu⟩ := abs_le.mp hbound
  dsimp only [quadraticCost]
  refine ⟨?_,?_,hbound0⟩ <;> rw [he] <;> linarith only [hl,hu]

/-- The center is supported EXACTLY on two-prime cofactors. Every higher
count stays coupled in the residual cost instead of being bounded separately. -/
theorem quadraticCenter_eq_two_prime (X : ℕ) (S I P : Finset ℕ)
    (O W F : ℕ → ℕ → ℝ)
    (hS : ∀ n ∈ S, Squarefree n ∧ 2 ≤ n.primeFactors.card) :
    quadraticCenter X S I P O W F =
      ∑ a ∈ I, quadraticSlope X (fun d => rotate P O a (fun p => F p d))*
        (∑ n ∈ S.filter (fun n => n.primeFactors.card=2),
          rotate P O a (W n)*secondMoment n) := by
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro n hn hnot
  have hc : 3 ≤ n.primeFactors.card := by
    have hge := (hS n hn).2
    have hne : n.primeFactors.card ≠ 2 := fun h => hnot (Finset.mem_filter.mpr ⟨hn,h⟩)
    omega
  rw [secondMoment_eq_zero_of_count (hS n hn).1 hc,mul_zero]

/-- The correction vanishes uniformly on ALL higher cofactor counts, even
when their prime geometries, masks and phases vary within the same population. -/
theorem quadraticCenter_eq_zero_of_count (X : ℕ) (S I P : Finset ℕ)
    (O W F : ℕ → ℕ → ℝ)
    (hS : ∀ n ∈ S, Squarefree n ∧ 3 ≤ n.primeFactors.card) :
    quadraticCenter X S I P O W F=0 := by
  apply Finset.sum_eq_zero
  intro a _
  have hz : (∑ n ∈ S, rotate P O a (W n)*secondMoment n)=0 := by
    apply Finset.sum_eq_zero
    intro n hn
    rw [secondMoment_eq_zero_of_count (hS n hn).1 (hS n hn).2,mul_zero]
  rw [hz,mul_zero]

/-- The actual signed center after retaining every prime-row mask and phase. -/
def primeCenter (X N : ℕ) (A S I P : Finset ℕ) (Q : ℕ → Finset ℕ)
    (O : ℕ → ℕ → ℝ) (L y scale : ℝ) : ℝ :=
  quadraticCenter X S I P O (maskedWeight A Q L y scale N) (hinge L)

/-- The corresponding original-carrier width, with all counts kept together. -/
def primeQuadraticCost (E : ℝ) (X N : ℕ) (A S I P : Finset ℕ)
    (Q : ℕ → Finset ℕ) (O : ℕ → ℕ → ℝ) (L y scale : ℝ) : ℝ :=
  quadraticCost E X S I P O (maskedWeight A Q L y scale N) (hinge L)

/-- Exact real pairing for the original masked prime/composite carrier. -/
theorem literal_sum_eq (N : ℕ) (A S P : Finset ℕ)
    (Q : ℕ → Finset ℕ) (L y scale : ℝ)
    (hSF : ∀ n ∈ S, Squarefree n ∧ 2 ≤ n.primeFactors.card)
    (hQ : ∀ n ∈ S, Q n ⊆ P)
    (hp : ∀ n ∈ S, ∀ p ∈ Q n, p.Prime ∧ ¬p ∣ n) :
    (∑ n ∈ S, ∑ p ∈ P, maskedWeight A Q L y scale N n p*divisorResponse (hinge L p) n) =
      scale*(∑ n ∈ S, ∑ p ∈ Q n,
        ZetaRieszJointAllocation.residualCoefficient A L N (p*n)*
          zetaPrimeLogKernel N (3/2+Complex.I*y) (p*n)).re := by
  simp only [Complex.re_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hfilter : P.filter (fun p => p ∈ Q n)=Q n := by
    rw [Finset.filter_mem_eq_inter,Finset.inter_eq_right.mpr (hQ n hn)]
  simp only [maskedWeight,ite_mul,zero_mul,← Finset.sum_filter,hfilter]
  apply Finset.sum_congr rfl
  intro p hpn
  rw [atom_eq A L y N (hSF n hn).1 (hSF n hn).2 (hp n hn p hpn).1 (hp n hn p hpn).2]
  ring

/-- Both inequalities for the ORIGINAL carrier, with every mask, phase and
factorial order retained. The width is PROVED no larger than the previous
joint cost with the SAME constant and coordinates. The center remains signed. -/
theorem exists_literal_quadratic_bounds :
    ∃ E : ℝ, 0 < E ∧ ∀ (X N : ℕ) (A S I P : Finset ℕ)
      (Q : ℕ → Finset ℕ) (O : ℕ → ℕ → ℝ) (L y scale : ℝ),
      Coordinates I P O → S ⊆ Finset.Ioc 1 X →
      (∀ n ∈ S, Squarefree n ∧ 2 ≤ n.primeFactors.card) →
      (∀ n ∈ S, Q n ⊆ P) → (∀ n ∈ S, ∀ p ∈ Q n, p.Prime ∧ ¬p ∣ n) →
      let J := scale*(∑ n ∈ S, ∑ p ∈ Q n,
        ZetaRieszJointAllocation.residualCoefficient A L N (p*n)*
          zetaPrimeLogKernel N (3/2+Complex.I*y) (p*n)).re;
      let H := primeCenter X N A S I P Q O L y scale;
      let K := primeQuadraticCost E X N A S I P Q O L y scale;
      let C := primeCost E X N A S I P Q O L y scale;
      max (-C) (H-K) ≤ J ∧ J ≤ min C (H+K) ∧ K ≤ C := by
  obtain ⟨E,hE,hbound⟩ := exists_joint_quadratic_bounds
  refine ⟨E,hE,fun X N A S I P Q O L y scale hO hS hSF hQ hp => ?_⟩
  have hnp n (hn : n ∈ S) : ¬n.Prime := by
    intro h
    have hc := (hSF n hn).2
    simp [h.primeFactors] at hc
  have hb := hbound X S I P O (maskedWeight A Q L y scale N) (hinge L) hO hS
    (fun n hn => ⟨(hSF n hn).1,hnp n hn⟩)
  rw [literal_sum_eq N A S P Q L y scale hSF hQ hp] at hb
  obtain ⟨hl,hu⟩ := abs_le.mp hb.2.2
  exact ⟨max_le hl hb.1,le_min hu hb.2.1,quadraticCost_le_jointCost hE.le X S I P O _ _⟩

/-- Every literal prime/composite population with at least three cofactor
primes gets the narrower TWO-SIDED bound without any correction to pay.
All higher counts stay together; no upper count cutoff is imposed. -/
theorem exists_higher_count_bounds :
    ∃ E : ℝ, 0 < E ∧ ∀ (X N : ℕ) (A S I P : Finset ℕ)
      (Q : ℕ → Finset ℕ) (O : ℕ → ℕ → ℝ) (L y scale : ℝ),
      Coordinates I P O → S ⊆ Finset.Ioc 1 X →
      (∀ n ∈ S, Squarefree n ∧ 3 ≤ n.primeFactors.card) →
      (∀ n ∈ S, Q n ⊆ P) → (∀ n ∈ S, ∀ p ∈ Q n, p.Prime ∧ ¬p ∣ n) →
      let J := scale*(∑ n ∈ S, ∑ p ∈ Q n,
        ZetaRieszJointAllocation.residualCoefficient A L N (p*n)*
          zetaPrimeLogKernel N (3/2+Complex.I*y) (p*n)).re;
      let K := primeQuadraticCost E X N A S I P Q O L y scale;
      -K ≤ J ∧ J ≤ K ∧ K ≤ primeCost E X N A S I P Q O L y scale := by
  obtain ⟨E,hE,hbound⟩ := exists_literal_quadratic_bounds
  refine ⟨E,hE,fun X N A S I P Q O L y scale hO hS hSF hQ hp => ?_⟩
  have hb := hbound X N A S I P Q O L y scale hO hS
    (fun n hn => ⟨(hSF n hn).1,by have := (hSF n hn).2; omega⟩) hQ hp
  have hz : primeCenter X N A S I P Q O L y scale=0 :=
    quadraticCenter_eq_zero_of_count X S I P O _ _ hSF
  dsimp only at hb ⊢
  rw [hz,zero_sub,zero_add,max_eq_right (neg_le_neg hb.2.2),min_eq_right hb.2.2] at hb
  exact hb

/-- The exact signed center for canonical ownership of an entire finite support. -/
def wholeCenter (A B I : Finset ℕ) (O : ℕ → ℕ → ℝ) (N : ℕ) (L y scale : ℝ) : ℝ :=
  primeCenter ((cofactors B).sup id) N A (cofactors B) I (ownerPrimes B)
    (ownerRows B) O L y scale

/-- The entire support's narrowed width, without any interval-cover premise. -/
def wholeQuadraticCost (E : ℝ) (A B I : Finset ℕ) (O : ℕ → ℕ → ℝ)
    (N : ℕ) (L y scale : ℝ) : ℝ :=
  primeQuadraticCost E ((cofactors B).sup id) N A (cofactors B) I (ownerPrimes B)
    (ownerRows B) O L y scale

/-- All squarefree labels of count at least three receive the same coupled
enclosure. Its exact center has only triple-prime incidences, and the width
improvement requires no new arithmetic hypothesis. -/
theorem exists_whole_quadratic_bounds :
    ∃ E : ℝ, 0 < E ∧ ∀ (A B I : Finset ℕ) (O : ℕ → ℕ → ℝ)
      (N : ℕ) (L y scale : ℝ),
      (∀ m ∈ B, Squarefree m ∧ 3 ≤ m.primeFactors.card) →
      Coordinates I (ownerPrimes B) O →
      let J := scale*(∑ m ∈ B,
        ZetaRieszJointAllocation.residualCoefficient A L N m*
          zetaPrimeLogKernel N (3/2+Complex.I*y) m).re;
      let H := wholeCenter A B I O N L y scale;
      let K := wholeQuadraticCost E A B I O N L y scale;
      let C := wholeCost E A B I O N L y scale;
      max (-C) (H-K) ≤ J ∧ J ≤ min C (H+K) ∧ K ≤ C := by
  obtain ⟨E,hE,hbound⟩ := exists_literal_quadratic_bounds
  refine ⟨E,hE,fun A B I O N L y scale hB hO => ?_⟩
  have hS : cofactors B ⊆ Finset.Ioc 1 ((cofactors B).sup id) := by
    intro n hn
    have hd := cofactors_data B hB hn
    have hn1 : n ≠ 1 := by intro h; simp [h] at hd
    exact Finset.mem_Ioc.mpr ⟨by have := hd.1.ne_zero; omega,Finset.le_sup (f := id) hn⟩
  have hb := hbound ((cofactors B).sup id) N A (cofactors B) I (ownerPrimes B)
    (ownerRows B) O L y scale hO hS (fun _ hn => cofactors_data B hB hn)
    (fun _ _ => Finset.image_subset_image (Finset.filter_subset _ _))
    (fun _ _ _ hp => ⟨(ownerRows_data B hB hp).1,(ownerRows_data B hB hp).2.1⟩)
  have he := ZetaRieszCoupledWindow.sum_owned_products (cofactors B) (ownerRows B)
    (fun m => ZetaRieszJointAllocation.residualCoefficient A L N m*
      zetaPrimeLogKernel N (3/2+Complex.I*y) m)
    (fun _ hn => (cofactors_data B hB hn).1.ne_zero)
    (fun _ _ _ hp => ⟨(ownerRows_data B hB hp).1,(ownerRows_data B hB hp).2.2⟩)
  rw [owner_labels_eq B hB] at he
  simpa only [he,wholeCenter,wholeQuadraticCost,wholeCost,Nat.mul_comm] using hb

open ZetaRieszParityPacket

/-- A narrower signed enclosure for the ENTIRE source-scaled original core.
The center and width are explicit; their sufficient eventual combined size
is still open, and no simple- or multiple-zero exclusion is claimed. -/
theorem exists_core_quadratic_bounds :
    ∃ E : ℝ, 0 < E ∧ ∀ (u y : ℝ) (N K : ℕ) (I : Finset ℕ) (O : ℕ → ℕ → ℝ),
      let B := (coreBand u N K).filter Squarefree;
      Coordinates I (ownerPrimes B) O →
      let A := ZetaRieszAnnulusJoint.intermediatePrimes u N;
      let L := SquarefreeVaughanLogSource.length u N;
      let H := wholeCenter A B I O N L y (u^(N+1));
      let C := wholeQuadraticCost E A B I O N L y (u^(N+1));
      let B₀ := wholeCost E A B I O N L y (u^(N+1));
      max (-B₀) (H-C) ≤ u^(N+1)*(coreResponse u y N K).re ∧
        u^(N+1)*(coreResponse u y N K).re ≤ min B₀ (H+C) ∧ C ≤ B₀ := by
  obtain ⟨E,hE,hbound⟩ := exists_whole_quadratic_bounds
  refine ⟨E,hE,fun u y N K I O hO => ?_⟩
  have hb := hbound (ZetaRieszAnnulusJoint.intermediatePrimes u N)
    ((coreBand u N K).filter Squarefree) I O N (SquarefreeVaughanLogSource.length u N) y
    (u^(N+1)) (fun m hm => ⟨(Finset.mem_filter.mp hm).2,core_count (Finset.mem_filter.mp hm).1⟩) hO
  simpa only [← core_eq_squarefree] using hb

end RiemannGaussian.ZetaRieszQuadraticPrimeEnergy
