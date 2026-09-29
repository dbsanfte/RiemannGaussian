/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszCoordinateGain

/-!
# A further cubic arithmetic saving for both joint bounds

Remove the third logarithmic divisor direction only after retaining its
exact signed arithmetic contribution. The residual energy decreases at
every finite endpoint. All squarefree cofactor counts at least four
annihilate this correction identically, independently of their geometry.
The original whole carrier receives both bounds with no new mean premise.
-/

noncomputable section
open scoped BigOperators Classical ArithmeticFunction.Moebius
namespace RiemannGaussian.ZetaRieszCubicPrimeEnergy
open Real ZetaRieszJointPrimeEnergy ZetaRieszCenteredPrimeEnergy
  ZetaRieszQuadraticPrimeEnergy

/-- The actual third logarithmic divisor profile. -/
def logCube (d : ℕ) : ℝ := log d^3

/-- The signed third arithmetic divisor moment, before any projection. -/
def thirdMoment (n : ℕ) : ℝ := divisorResponse logCube n

/-- Prime insertion reduces the cubic moment to the already exact
quadratic moment whenever the remaining cofactor is composite. -/
theorem thirdMoment_prime_mul {p n : ℕ} (hp : p.Prime) (hpn : ¬p ∣ n)
    (hn : Squarefree n) (hn1 : n ≠ 1) (hnp : ¬n.Prime) :
    thirdMoment (p*n) = -3*log p*secondMoment n := by
  have hm : (∑ d ∈ n.divisors, (μ d : ℝ))=0 := by
    exact_mod_cast ZetaRieszPrimeFourier.sum_moebius_eq_zero hn1
  have hl : (∑ d ∈ n.divisors, (μ d : ℝ)*log d)=0 := by
    exact_mod_cast ZetaRieszPrimeFourier.sum_moebius_log_eq_zero hn hnp
  unfold thirdMoment
  rw [divisor_prime_mul hp hpn]
  have he : (∑ d ∈ n.divisors, (μ d : ℝ)*(logCube d-logCube (p*d))) =
      -3*log p*secondMoment n-3*log p^2*(∑ d ∈ n.divisors, (μ d : ℝ)*log d)-
        log p^3*(∑ d ∈ n.divisors, (μ d : ℝ)) := by
    simp only [secondMoment,divisorResponse,logSquare,Finset.mul_sum,
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mem_divisors hd).ne'
    simp only [logCube,Nat.cast_mul,log_mul hp0 hd0]
    ring
  rw [he,hm,hl]
  ring

/-- The exact two-prime cubic coefficient is retained, not paid by a norm. -/
theorem thirdMoment_two_primes {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    thirdMoment (p*q)=3*log p*log q*(log p+log q) := by
  unfold thirdMoment
  rw [divisor_prime_mul hp (fun h => hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp h)),hq.sum_divisors]
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne_zero
  simp only [ArithmeticFunction.moebius_apply_one,Int.cast_one,one_mul,
    ArithmeticFunction.moebius_apply_prime hq,Int.cast_neg,logCube,Nat.cast_one,log_one,
    zero_pow (by decide : 3 ≠ 0),Nat.mul_one,Nat.cast_mul,log_mul hp0 hq0]
  ring

/-- Every squarefree cofactor of count at least four annihilates the
whole cubic direction. No share, period, height or count ceiling enters. -/
theorem thirdMoment_eq_zero_of_count {n : ℕ} (hn : Squarefree n)
    (hc : 4 ≤ n.primeFactors.card) : thirdMoment n=0 := by
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
  have hc3 : 3 ≤ (n/p).primeFactors.card := by omega
  have hm1 : n/p ≠ 1 := by intro h; simp [h] at hc3
  have hmp : ¬(n/p).Prime := by intro h; simp [h.primeFactors] at hc3
  have hz := thirdMoment_prime_mul hpp hnot hm hm1 hmp
  rw [secondMoment_eq_zero_of_count hm hc3,mul_zero,he] at hz
  exact hz

private theorem delta_sub (X : ℕ) (f g : ℕ → ℝ) (a : ℝ) (k : ℕ) :
    centeredDelta X (fun d => f d-a*g d) k =
      centeredDelta X f k-a*centeredDelta X g k := by
  have he : logCross X (fun d => f d-a*g d)=logCross X f-a*logCross X g := by
    simp only [logCross,Finset.mul_sum,← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun _ _ => by ring)
  simp only [centeredDelta,he]
  ring

/-- Remove the already accounted quadratic direction from the cubic one. -/
def cubicDirection (X : ℕ) : ℕ → ℝ := quadraticProfile X logCube

/-- The exact signed correlation still contains every prime cross term. -/
def cubicCross (X : ℕ) (f : ℕ → ℝ) : ℝ :=
  ∑ k ∈ Finset.Ico 1 X, (k : ℝ)*centeredDelta X (quadraticProfile X f) k*
    centeredDelta X (cubicDirection X) k

/-- The third projection coefficient, with zero-energy cases included. -/
def cubicSlope (X : ℕ) (f : ℕ → ℝ) : ℝ :=
  cubicCross X f/centeredEnergy X (cubicDirection X)

/-- Residual after both exact logarithmic moment corrections. -/
def cubicProfile (X : ℕ) (f : ℕ → ℝ) (d : ℕ) : ℝ :=
  quadraticProfile X f d-cubicSlope X f*cubicDirection X d

/-- The new nonnegative residual energy. -/
def cubicEnergy (X : ℕ) (f : ℕ → ℝ) : ℝ := centeredEnergy X (cubicProfile X f)

/-- The cubic direction saves its squared signed correlation exactly. -/
theorem cubicEnergy_eq (X : ℕ) (f : ℕ → ℝ) :
    cubicEnergy X f = quadraticEnergy X f-
      cubicCross X f^2/centeredEnergy X (cubicDirection X) := by
  have he (a : ℝ) : centeredEnergy X
      (fun d => quadraticProfile X f d-a*cubicDirection X d) =
      quadraticEnergy X f-2*a*cubicCross X f+a^2*centeredEnergy X (cubicDirection X) := by
    change (∑ k ∈ Finset.Ico 1 X, (k : ℝ)*
      centeredDelta X (fun d => quadraticProfile X f d-a*cubicDirection X d) k^2) =
      (∑ k ∈ Finset.Ico 1 X, (k : ℝ)*centeredDelta X (quadraticProfile X f) k^2)-
      2*a*cubicCross X f+a^2*(∑ k ∈ Finset.Ico 1 X,
        (k : ℝ)*centeredDelta X (cubicDirection X) k^2)
    simp only [delta_sub,cubicCross,Finset.mul_sum,
      ← Finset.sum_sub_distrib,← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun _ _ => by ring)
  change centeredEnergy X (fun d => quadraticProfile X f d-
    cubicSlope X f*cubicDirection X d)=_
  rw [he,cubicSlope]
  by_cases h : centeredEnergy X (cubicDirection X)=0
  · simp [h]
  · field_simp
    ring

/-- No residual energy or degenerate finite endpoint is negative. -/
theorem cubicEnergy_nonneg (X : ℕ) (f : ℕ → ℝ) : 0 ≤ cubicEnergy X f :=
  centeredEnergy_nonneg _ _

/-- The further cubic correction never enlarges the residual width. -/
theorem cubicEnergy_le (X : ℕ) (f : ℕ → ℝ) :
    cubicEnergy X f ≤ quadraticEnergy X f := by
  rw [cubicEnergy_eq]
  exact sub_le_self _ (div_nonneg (sq_nonneg _) (centeredEnergy_nonneg _ _))

/-- The correction is the ACTUAL divisor response of the cubic direction. -/
def cubicMoment (X n : ℕ) : ℝ := divisorResponse (cubicDirection X) n

/-- Keep both arithmetic moments with their exact signs. -/
theorem cubicMoment_eq (X n : ℕ) : cubicMoment X n =
    thirdMoment n-quadraticSlope X logCube*secondMoment n := by
  have he := divisor_quadratic X n logCube
  change thirdMoment n=cubicMoment X n+_ at he
  linarith only [he]

/-- All counts at least four get the energy saving with ZERO extra
arithmetic correction. This holds for every geometry and phase. -/
theorem cubicMoment_eq_zero_of_count (X : ℕ) {n : ℕ} (hn : Squarefree n)
    (hc : 4 ≤ n.primeFactors.card) : cubicMoment X n=0 := by
  rw [cubicMoment_eq,thirdMoment_eq_zero_of_count hn hc,
    secondMoment_eq_zero_of_count hn (by omega),mul_zero,sub_zero]

/-- The cubic removal is an exact signed identity on the original divisor
sum. Neither the quadratic nor cubic correction is discarded. -/
theorem divisor_cubic (X n : ℕ) (f : ℕ → ℝ) :
    divisorResponse f n = divisorResponse (cubicProfile X f) n+
      quadraticSlope X f*secondMoment n+cubicSlope X f*cubicMoment X n := by
  have he : divisorResponse (quadraticProfile X f) n =
      divisorResponse (cubicProfile X f) n+cubicSlope X f*cubicMoment X n := by
    simp only [divisorResponse,cubicProfile,cubicMoment,Finset.mul_sum,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun _ _ => by ring)
  rw [divisor_quadratic X n f,he]
  ring

/-- Both low-count corrections stay signed inside the joint center. -/
def cubicCenter (X : ℕ) (S I P : Finset ℕ) (O W F : ℕ → ℕ → ℝ) : ℝ :=
  quadraticCenter X S I P O W F+
    ∑ a ∈ I, cubicSlope X (fun d => rotate P O a (fun p => F p d))*
      (∑ n ∈ S, rotate P O a (W n)*cubicMoment X n)

/-- The coupled cubic width, retaining the full signed weight matrix. -/
def cubicCost (E : ℝ) (X : ℕ) (S I P : Finset ℕ) (O W F : ℕ → ℕ → ℝ) : ℝ :=
  ∑ a ∈ I, sqrt ((∑ n ∈ S, rotate P O a (W n)^2)*E*X*
    cubicEnergy X (fun d => rotate P O a (fun p => F p d)))

/-- A uniform width improvement for every original population and common
coordinate system, using the SAME arithmetic constant. -/
theorem cubicCost_le_quadraticCost {E : ℝ} (hE : 0 ≤ E) (X : ℕ)
    (S I P : Finset ℕ) (O W F : ℕ → ℕ → ℝ) :
    cubicCost E X S I P O W F ≤ quadraticCost E X S I P O W F := by
  apply Finset.sum_le_sum
  intro a _
  apply sqrt_le_sqrt
  exact mul_le_mul_of_nonneg_left (cubicEnergy_le X _)
    (mul_nonneg (mul_nonneg (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) hE) (Nat.cast_nonneg X))

/-- On ALL higher counts the narrower enclosure has no center to pay.
There is no upper count, share or prime-period restriction. -/
theorem cubicCenter_eq_zero_of_count (X : ℕ) (S I P : Finset ℕ)
    (O W F : ℕ → ℕ → ℝ)
    (hS : ∀ n ∈ S, Squarefree n ∧ 4 ≤ n.primeFactors.card) :
    cubicCenter X S I P O W F=0 := by
  rw [cubicCenter,quadraticCenter_eq_zero_of_count X S I P O W F
    (fun n hn => ⟨(hS n hn).1,by have := (hS n hn).2; omega⟩),zero_add]
  apply Finset.sum_eq_zero
  intro a _
  have hz : (∑ n ∈ S, rotate P O a (W n)*cubicMoment X n)=0 := by
    apply Finset.sum_eq_zero
    intro n hn
    rw [cubicMoment_eq_zero_of_count X (hS n hn).1 (hS n hn).2,mul_zero]
  rw [hz,mul_zero]

/-- Both exact centers are retained in an unconditional joint enclosure.
The cubic width is no larger, but its center is NOT free credit. -/
theorem exists_joint_cubic_bounds :
    ∃ E : ℝ, 0 < E ∧ ∀ (X : ℕ) (S I P : Finset ℕ) (O W F : ℕ → ℕ → ℝ),
      Coordinates I P O → S ⊆ Finset.Ioc 1 X →
      (∀ n ∈ S, Squarefree n ∧ ¬n.Prime) →
      let J := ∑ n ∈ S, ∑ p ∈ P, W n p*divisorResponse (F p) n;
      let H₂ := quadraticCenter X S I P O W F;
      let C₂ := quadraticCost E X S I P O W F;
      let H₃ := cubicCenter X S I P O W F;
      let C₃ := cubicCost E X S I P O W F;
      max (H₂-C₂) (H₃-C₃) ≤ J ∧ J ≤ min (H₂+C₂) (H₃+C₃) ∧ C₃ ≤ C₂ := by
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
  have hb (a : ℕ) (g : ℕ → ℝ) : |∑ n ∈ S, w a n*divisorResponse g n| ≤
      sqrt ((∑ n ∈ S, (w a n)^2)*E*X*centeredEnergy X g) := by
    have hs := (Finset.sum_mul_sq_le_sq_mul_sq S (w a) (divisorResponse g)).trans
      (mul_le_mul_of_nonneg_left (hmean X S g hS hSF)
        (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
    apply (sq_le_sq₀ (abs_nonneg _) (sqrt_nonneg _)).mp
    rw [sq_abs,sq_sqrt (mul_nonneg (by positivity) (centeredEnergy_nonneg _ _))]
    simpa only [mul_assoc] using hs
  have he₂ : (∑ n ∈ S, ∑ p ∈ P, W n p*divisorResponse (F p) n) =
      quadraticCenter X S I P O W F+
        ∑ a ∈ I, ∑ n ∈ S, w a n*divisorResponse (quadraticProfile X (f a)) n := by
    rw [hpair]
    simp only [quadraticCenter,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _
    simp_rw [divisor_quadratic X _ (f a)]
    simp only [Finset.mul_sum,mul_add,← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun _ _ => by dsimp [f,w]; ring)
  have he₃ : (∑ n ∈ S, ∑ p ∈ P, W n p*divisorResponse (F p) n) =
      cubicCenter X S I P O W F+
        ∑ a ∈ I, ∑ n ∈ S, w a n*divisorResponse (cubicProfile X (f a)) n := by
    rw [hpair]
    simp only [cubicCenter,quadraticCenter,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _
    simp_rw [divisor_cubic X _ (f a)]
    simp only [Finset.mul_sum,mul_add,← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun _ _ => by dsimp [f,w]; ring)
  have h₂ := abs_le.mp ((Finset.abs_sum_le_sum_abs _ I).trans
    (Finset.sum_le_sum (fun a (_ : a ∈ I) => hb a (quadraticProfile X (f a)))))
  have h₃ := abs_le.mp ((Finset.abs_sum_le_sum_abs _ I).trans
    (Finset.sum_le_sum (fun a (_ : a ∈ I) => hb a (cubicProfile X (f a)))))
  dsimp only
  refine ⟨max_le ?_ ?_,le_min ?_ ?_,cubicCost_le_quadraticCost hE.le X S I P O W F⟩
  · rw [he₂]
    change _-quadraticCost E X S I P O W F ≤ _+_
    dsimp only [quadraticCost,quadraticEnergy] at *
    linarith only [h₂.1]
  · rw [he₃]
    dsimp only [cubicCost,cubicEnergy] at *
    linarith only [h₃.1]
  · rw [he₂]
    dsimp only [quadraticCost,quadraticEnergy] at *
    linarith only [h₂.2]
  · rw [he₃]
    dsimp only [cubicCost,cubicEnergy] at *
    linarith only [h₃.2]

/-- Both bounds for the literal masked prime/composite sum. All mean
hypotheses are discharged; the cubic center is explicit and signed. -/
theorem exists_literal_cubic_bounds :
    ∃ E : ℝ, 0 < E ∧ ∀ (X N : ℕ) (A S I P : Finset ℕ)
      (Q : ℕ → Finset ℕ) (O : ℕ → ℕ → ℝ) (L y scale : ℝ),
      Coordinates I P O → S ⊆ Finset.Ioc 1 X →
      (∀ n ∈ S, Squarefree n ∧ 2 ≤ n.primeFactors.card) →
      (∀ n ∈ S, Q n ⊆ P) → (∀ n ∈ S, ∀ p ∈ Q n, p.Prime ∧ ¬p ∣ n) →
      let J := scale*(∑ n ∈ S, ∑ p ∈ Q n,
        ZetaRieszJointAllocation.residualCoefficient A L N (p*n)*
          zetaPrimeLogKernel N (3/2+Complex.I*y) (p*n)).re;
      let W := maskedWeight A Q L y scale N;
      let F := hinge L;
      let H₂ := quadraticCenter X S I P O W F;
      let C₂ := quadraticCost E X S I P O W F;
      let H₃ := cubicCenter X S I P O W F;
      let C₃ := cubicCost E X S I P O W F;
      max (H₂-C₂) (H₃-C₃) ≤ J ∧ J ≤ min (H₂+C₂) (H₃+C₃) ∧ C₃ ≤ C₂ := by
  obtain ⟨E,hE,hbound⟩ := exists_joint_cubic_bounds
  refine ⟨E,hE,fun X N A S I P Q O L y scale hO hS hSF hQ hp => ?_⟩
  have hnp n (hn : n ∈ S) : ¬n.Prime := by
    intro h
    have hc := (hSF n hn).2
    simp [h.primeFactors] at hc
  have hb := hbound X S I P O (maskedWeight A Q L y scale N) (hinge L) hO hS
    (fun n hn => ⟨(hSF n hn).1,hnp n hn⟩)
  rw [literal_sum_eq N A S P Q L y scale hSF hQ hp] at hb
  exact hb

/-- Exact signed center for every original label under canonical ownership. -/
def wholeCubicCenter (A B I : Finset ℕ) (O : ℕ → ℕ → ℝ)
    (N : ℕ) (L y scale : ℝ) : ℝ :=
  cubicCenter ((cofactors B).sup id) (cofactors B) I (ownerPrimes B) O
    (maskedWeight A (ownerRows B) L y scale N) (hinge L)

/-- The whole original population's cubic residual cost. -/
def wholeCubicCost (E : ℝ) (A B I : Finset ℕ) (O : ℕ → ℕ → ℝ)
    (N : ℕ) (L y scale : ℝ) : ℝ :=
  cubicCost E ((cofactors B).sup id) (cofactors B) I (ownerPrimes B) O
    (maskedWeight A (ownerRows B) L y scale N) (hinge L)

/-- Canonical ownership transports the cubic saving to the entire
original support. The two signed centers are both retained. -/
theorem exists_whole_cubic_bounds :
    ∃ E : ℝ, 0 < E ∧ ∀ (A B I : Finset ℕ) (O : ℕ → ℕ → ℝ)
      (N : ℕ) (L y scale : ℝ),
      (∀ m ∈ B, Squarefree m ∧ 3 ≤ m.primeFactors.card) →
      Coordinates I (ownerPrimes B) O →
      let J := scale*(∑ m ∈ B,
        ZetaRieszJointAllocation.residualCoefficient A L N m*
          zetaPrimeLogKernel N (3/2+Complex.I*y) m).re;
      let H₂ := wholeCenter A B I O N L y scale;
      let C₂ := wholeQuadraticCost E A B I O N L y scale;
      let H₃ := wholeCubicCenter A B I O N L y scale;
      let C₃ := wholeCubicCost E A B I O N L y scale;
      max (H₂-C₂) (H₃-C₃) ≤ J ∧ J ≤ min (H₂+C₂) (H₃+C₃) ∧ C₃ ≤ C₂ := by
  obtain ⟨E,hE,hbound⟩ := exists_literal_cubic_bounds
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
  simpa only [he,wholeCenter,primeCenter,wholeQuadraticCost,primeQuadraticCost,
    wholeCubicCenter,wholeCubicCost,Nat.mul_comm] using hb

open ZetaRieszParityPacket

/-- Both cubic signed bounds for the ENTIRE source-scaled original core.
The lower-count correction remains explicit. A sufficient eventual
combined bound and both final RH thresholds remain open. -/
theorem exists_core_cubic_bounds :
    ∃ E : ℝ, 0 < E ∧ ∀ (u y : ℝ) (N K : ℕ) (I : Finset ℕ) (O : ℕ → ℕ → ℝ),
      let B := (coreBand u N K).filter Squarefree;
      Coordinates I (ownerPrimes B) O →
      let A := ZetaRieszAnnulusJoint.intermediatePrimes u N;
      let L := SquarefreeVaughanLogSource.length u N;
      let H₂ := wholeCenter A B I O N L y (u^(N+1));
      let C₂ := wholeQuadraticCost E A B I O N L y (u^(N+1));
      let H₃ := wholeCubicCenter A B I O N L y (u^(N+1));
      let C₃ := wholeCubicCost E A B I O N L y (u^(N+1));
      let J := u^(N+1)*(coreResponse u y N K).re;
      max (H₂-C₂) (H₃-C₃) ≤ J ∧ J ≤ min (H₂+C₂) (H₃+C₃) ∧ C₃ ≤ C₂ := by
  obtain ⟨E,hE,hbound⟩ := exists_whole_cubic_bounds
  refine ⟨E,hE,fun u y N K I O hO => ?_⟩
  have hb := hbound (ZetaRieszAnnulusJoint.intermediatePrimes u N)
    ((coreBand u N K).filter Squarefree) I O N (SquarefreeVaughanLogSource.length u N) y
    (u^(N+1)) (fun m hm => ⟨(Finset.mem_filter.mp hm).2,core_count (Finset.mem_filter.mp hm).1⟩) hO
  simpa only [← core_eq_squarefree] using hb

end RiemannGaussian.ZetaRieszCubicPrimeEnergy
