/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszCenteredPrimeEnergy
import RiemannGaussian.ZetaRieszParityWindow
import RiemannGaussian.ZetaRieszOwnedCells

/-!
# Joint prime-profile bounds before splitting factorial orders or masks

The literal allocation, factorial weight and full product phase are combined
first. An exact finite change of prime coordinates retains their correlations
in both factors of the arithmetic mean bound. Arbitrary cofactor-dependent
prime selections are allowed; no binary maximal loss or orderwise triangle
inequality is used. The resulting finite cost still needs a source-scale bound.
-/

noncomputable section
open scoped BigOperators Classical ArithmeticFunction.Moebius
namespace RiemannGaussian.ZetaRieszJointPrimeEnergy
open Real ZetaRieszCenteredPrimeEnergy ZetaRieszJointAllocation

/-- An exact orthogonal coordinate identity on the selected finite prime set. -/
def Coordinates (I P : Finset ℕ) (O : ℕ → ℕ → ℝ) : Prop :=
  ∀ p ∈ P, ∀ q ∈ P, (∑ a ∈ I, O a p*O a q) = if p=q then 1 else 0

/-- The original prime coordinates are always an admissible choice. -/
theorem coordinates_identity (P : Finset ℕ) :
    Coordinates P P (fun a p => if a=p then 1 else 0) := by
  intro p _ q hq
  simp [hq,eq_comm]

/-- Apply the same finite coordinate map before taking either quadratic norm. -/
def rotate (P : Finset ℕ) (O : ℕ → ℕ → ℝ) (a : ℕ) (v : ℕ → ℝ) : ℝ :=
  ∑ p ∈ P, O a p*v p

/-- Signed prime pairing is invariant under the exact common coordinates. -/
theorem coordinate_pairing (I P : Finset ℕ) (O : ℕ → ℕ → ℝ)
    (hO : Coordinates I P O) (w f : ℕ → ℝ) :
    (∑ a ∈ I, rotate P O a w*rotate P O a f) = ∑ p ∈ P, w p*f p := by
  calc
    _ = ∑ p ∈ P, ∑ q ∈ P, w p*f q*(∑ a ∈ I, O a p*O a q) := by
      simp only [rotate,Finset.sum_mul,Finset.mul_sum]
      rw [Finset.sum_comm]
      conv_rhs => rw [Finset.sum_comm (s := P) (t := P)]
      apply Finset.sum_congr rfl
      intro p _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro q _
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = _ := by
      apply Finset.sum_congr rfl
      intro p hp
      simp_rw [Finset.sum_congr rfl (fun q hq => congrArg (fun z : ℝ => w p*f q*z)
        (hO p hp q hq))]
      simp [mul_ite,Finset.sum_ite_eq,hp]

/-- An actual signed divisor response, with no cutoff or norm replacement. -/
def divisorResponse (f : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ d ∈ n.divisors, (μ d : ℝ)*f d

private theorem divisor_rotate (P : Finset ℕ) (O : ℕ → ℕ → ℝ)
    (F : ℕ → ℕ → ℝ) (a n : ℕ) :
    divisorResponse (fun d => rotate P O a (fun p => F p d)) n =
      rotate P O a (fun p => divisorResponse (F p) n) := by
  simp only [divisorResponse,rotate,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro d _
  ring

/-- The joint cost retains cross terms in BOTH the literal cofactor weights
and the centered prime profiles. Its arithmetic constant is not evaluated. -/
def jointCost (E : ℝ) (X : ℕ) (S I P : Finset ℕ) (O : ℕ → ℕ → ℝ)
    (W F : ℕ → ℕ → ℝ) : ℝ :=
  ∑ a ∈ I, sqrt ((∑ n ∈ S, (rotate P O a (W n))^2)*E*X*
    centeredEnergy X (fun d => rotate P O a (fun p => F p d)))

/-- One unconditional mean constant bounds every whole signed matrix of
prime profiles. The coordinate identity is finite algebra, not an arithmetic
cancellation hypothesis; the identity coordinates are always available. -/
theorem exists_joint_bounds :
    ∃ E : ℝ, 0 < E ∧ ∀ (X : ℕ) (S I P : Finset ℕ)
      (O W F : ℕ → ℕ → ℝ), Coordinates I P O →
      S ⊆ Finset.Ioc 1 X → (∀ n ∈ S, Squarefree n ∧ ¬n.Prime) →
      let J := ∑ n ∈ S, ∑ p ∈ P, W n p*divisorResponse (F p) n;
      let K := jointCost E X S I P O W F;
      -K ≤ J ∧ J ≤ K := by
  obtain ⟨E,hE,hmean⟩ := exists_centered_divisor_mean
  refine ⟨E,hE,fun X S I P O W F hO hS hSF => ?_⟩
  let f := fun a d => rotate P O a (fun p => F p d)
  let w := fun a n => rotate P O a (W n)
  have hb a : |∑ n ∈ S, w a n*divisorResponse (f a) n| ≤
      sqrt ((∑ n ∈ S, (w a n)^2)*E*X*centeredEnergy X (f a)) := by
    have hs := (Finset.sum_mul_sq_le_sq_mul_sq S (w a) (divisorResponse (f a))).trans
      (mul_le_mul_of_nonneg_left (hmean X S (f a) hS hSF)
        (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
    apply (sq_le_sq₀ (abs_nonneg _) (sqrt_nonneg _)).mp
    rw [sq_abs,sq_sqrt (mul_nonneg (by positivity) (centeredEnergy_nonneg _ _))]
    simpa only [mul_assoc] using hs
  have he : (∑ n ∈ S, ∑ p ∈ P, W n p*divisorResponse (F p) n) =
      ∑ a ∈ I, ∑ n ∈ S, w a n*divisorResponse (f a) n := by
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro n _
    simp_rw [f,divisor_rotate]
    exact (coordinate_pairing I P O hO (W n) (fun p => divisorResponse (F p) n)).symm
  dsimp only
  apply abs_le.mp
  rw [he]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun a _ => hb a))

/-- The exact two-hinge prime profile. -/
def hinge (L : ℝ) (p d : ℕ) : ℝ :=
  max 0 (L-log d)-max 0 (L-log p-log d)

/-- The full original factorial allocation and product phase, before any
factorial-order split. The minus sign is the exact composite coefficient sign. -/
def primeWeight (A : Finset ℕ) (L y : ℝ) (N n p : ℕ) : ℝ :=
  (-(1-boundedShare A N (p*n))/(L*N.factorial))*
    (exp (-(log p+log n)/2)*(log p+log n)^(N+1))*
      cos (y*(log p+log n))/((n : ℝ)*p)

/-- The weight and hinge recover each original complex carrier atom's real
part exactly, for every factorial order and every composite cofactor count. -/
theorem atom_eq (A : Finset ℕ) (L y : ℝ) (N : ℕ) {n p : ℕ}
    (hn : Squarefree n) (hc : 2 ≤ n.primeFactors.card) (hp : p.Prime) (hpn : ¬p ∣ n) :
    (residualCoefficient A L N (p*n)*zetaPrimeLogKernel N (3/2+Complex.I*y) (p*n)).re =
      primeWeight A L y N n p*divisorResponse (hinge L p) n := by
  have hn1 : n ≠ 1 := by intro h; simp [h] at hc
  have hnp : ¬n.Prime := by intro h; simp [h.primeFactors] at hc
  have hmu : (μ n : ℝ) = (-1 : ℝ)^n.primeFactors.card := by
    exact_mod_cast ZetaRieszReflectedLinear.moebius_eq_primeCount hn
  have hm2 : (μ n : ℝ)^2=1 := by
    exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hn
  have hsign : (-1 : ℝ)^(n.primeFactors.card+1)*(-(μ n : ℝ))=1 := by
    rw [pow_succ,← hmu]
    nlinarith only [hm2]
  have hd : divisorResponse (hinge L p) n =
      VaughanLogAverage.riesz L n-VaughanLogAverage.riesz (L-log p) n := by
    simp only [divisorResponse,hinge,VaughanLogAverage.riesz,mul_sub,Finset.sum_sub_distrib]
  rw [ZetaRieszGlobalPrimePeriod.re_residual_atom hn hc hp hpn,
    ZetaRieszSquarefreeDualMean.response_reflection L (log p) hn hn1 hnp,hd]
  dsimp only [ZetaRieszGlobalPrimePeriod.signedPrimeWeight,primeWeight]
  calc
    _ = ((-1 : ℝ)^(n.primeFactors.card+1)*(-(μ n : ℝ)))*
        (-(1-boundedShare A N (p*n))/(L*N.factorial))*
        (exp (-(log p+log n)/2)*(log p+log n)^(N+1))*
        cos (y*(log p+log n))/((n : ℝ)*p)*
        (VaughanLogAverage.riesz L n-VaughanLogAverage.riesz (L-log p) n) := by ring
    _ = _ := by rw [hsign]; ring

/-- Every original mask stays in its exact row, before coordinate mixing. -/
def maskedWeight (A : Finset ℕ) (Q : ℕ → Finset ℕ) (L y scale : ℝ)
    (N n p : ℕ) : ℝ := if p ∈ Q n then scale*primeWeight A L y N n p else 0

/-- A cost for the actual carrier with all orders and arbitrary moving
prime masks coupled. There is no maximal-interval or prime-count multiplier. -/
def primeCost (E : ℝ) (X N : ℕ) (A S I P : Finset ℕ)
    (Q : ℕ → Finset ℕ) (O : ℕ → ℕ → ℝ) (L y scale : ℝ) : ℝ :=
  jointCost E X S I P O (maskedWeight A Q L y scale N) (hinge L)

/-- BOTH signed inequalities for the ORIGINAL scaled finite carrier. All
factorial orders are already summed, the phase remains correlated with the
actual cofactor, and arbitrary holes in the selected prime rows are retained. -/
theorem exists_literal_joint_bounds :
    ∃ E : ℝ, 0 < E ∧ ∀ (X N : ℕ) (A S I P : Finset ℕ)
      (Q : ℕ → Finset ℕ) (O : ℕ → ℕ → ℝ) (L y scale : ℝ),
      Coordinates I P O → S ⊆ Finset.Ioc 1 X →
      (∀ n ∈ S, Squarefree n ∧ 2 ≤ n.primeFactors.card) →
      (∀ n ∈ S, Q n ⊆ P) → (∀ n ∈ S, ∀ p ∈ Q n, p.Prime ∧ ¬p ∣ n) →
      let J := scale*(∑ n ∈ S, ∑ p ∈ Q n,
        residualCoefficient A L N (p*n)*zetaPrimeLogKernel N (3/2+Complex.I*y) (p*n)).re;
      let K := primeCost E X N A S I P Q O L y scale;
      -K ≤ J ∧ J ≤ K := by
  obtain ⟨E,hE,hbound⟩ := exists_joint_bounds
  refine ⟨E,hE,fun X N A S I P Q O L y scale hO hS hSF hQ hp => ?_⟩
  have hnp n (hn : n ∈ S) : ¬n.Prime := by
    intro h
    have hc := (hSF n hn).2
    simp [h.primeFactors] at hc
  have hb := hbound X S I P O (maskedWeight A Q L y scale N) (hinge L) hO hS
    (fun n hn => ⟨(hSF n hn).1,hnp n hn⟩)
  have he : (∑ n ∈ S, ∑ p ∈ P,
      maskedWeight A Q L y scale N n p*divisorResponse (hinge L p) n) =
      scale*(∑ n ∈ S, ∑ p ∈ Q n,
        residualCoefficient A L N (p*n)*zetaPrimeLogKernel N (3/2+Complex.I*y) (p*n)).re := by
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
  simpa only [he,primeCost] using hb

open ZetaRieszPrimeEndpoint ZetaRieszOwnedCells

/-- Canonical largest-prime ownership leaves an actual squarefree composite
cofactor, and every remaining prime is strictly smaller than its owner. -/
theorem owner_data {m : ℕ} (hm : Squarefree m) (hc : 3 ≤ m.primeFactors.card) :
    (largestPrime m).Prime ∧ largestPrime m*ownerCofactor m=m ∧
      Squarefree (ownerCofactor m) ∧ 2 ≤ (ownerCofactor m).primeFactors.card ∧
      ∀ r : ℕ, r.Prime → r ∣ ownerCofactor m → r < largestPrime m := by
  have hp := largestPrime_mem_of_two (by omega : 2 ≤ m.primeFactors.card)
  have hpp := Nat.prime_of_mem_primeFactors hp
  have he : largestPrime m*ownerCofactor m=m := by
    rw [ownerCofactor,Nat.mul_comm]
    exact Nat.div_mul_cancel (Nat.dvd_of_mem_primeFactors hp)
  have hsq : Squarefree (largestPrime m*ownerCofactor m) := by rw [he]; exact hm
  have hn := hsq.of_mul_right
  have hnot : ¬largestPrime m ∣ ownerCofactor m :=
    hpp.coprime_iff_not_dvd.mp (Nat.coprime_of_squarefree_mul hsq)
  have hcount : m.primeFactors.card=(ownerCofactor m).primeFactors.card+1 := by
    conv_lhs => rw [← he]
    rw [Nat.primeFactors_mul hpp.ne_zero hn.ne_zero,hpp.primeFactors,
      Finset.singleton_union,Finset.card_insert_of_notMem
        (fun h => hnot (Nat.dvd_of_mem_primeFactors h))]
  refine ⟨hpp,he,hn,by omega,?_⟩
  intro r hr hrd
  have hdiv : ownerCofactor m ∣ m := by
    calc
      ownerCofactor m ∣ largestPrime m*ownerCofactor m := dvd_mul_left _ _
      _ = m := he
  have hrm : r ∈ m.primeFactors := Nat.mem_primeFactors.mpr ⟨hr,hrd.trans hdiv,hm.ne_zero⟩
  have hne : m.primeFactors.Nonempty := ⟨largestPrime m,hp⟩
  have hle : r ≤ largestPrime m := by
    rw [largestPrime,dif_pos hne]
    exact Finset.le_max' _ r hrm
  exact lt_of_le_of_ne hle (fun h => hnot (h ▸ hrd))

/-- The actual cofactors of a finite literal label set. -/
def cofactors (B : Finset ℕ) : Finset ℕ := B.image ownerCofactor

/-- The common finite set contains only largest primes actually used by B. -/
def ownerPrimes (B : Finset ℕ) : Finset ℕ := B.image largestPrime

/-- The precise original labels determine each prime row, including every
physical, share, radial and count mask. No interval completion is performed. -/
def ownerRows (B : Finset ℕ) (n : ℕ) : Finset ℕ :=
  (B.filter (fun m => ownerCofactor m=n)).image largestPrime

private theorem ownerRows_subset (B : Finset ℕ) (n : ℕ) : ownerRows B n ⊆ ownerPrimes B :=
  Finset.image_subset_image (Finset.filter_subset _ _)

/-- Every selected row prime is genuine, coprime to its cofactor, and largest. -/
theorem ownerRows_data (B : Finset ℕ)
    (hB : ∀ m ∈ B, Squarefree m ∧ 3 ≤ m.primeFactors.card)
    {n p : ℕ} (hp : p ∈ ownerRows B n) :
    p.Prime ∧ ¬p ∣ n ∧ ∀ r : ℕ, r.Prime → r ∣ n → r < p := by
  obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨hm,he⟩ := Finset.mem_filter.mp hm
  rw [← he]
  have hd := owner_data (hB m hm).1 (hB m hm).2
  exact ⟨hd.1,fun h => (lt_irrefl _) (hd.2.2.2.2 _ hd.1 h),hd.2.2.2.2⟩

/-- The exact owned cofactor population is squarefree with at least two primes. -/
theorem cofactors_data (B : Finset ℕ)
    (hB : ∀ m ∈ B, Squarefree m ∧ 3 ≤ m.primeFactors.card)
    {n : ℕ} (hn : n ∈ cofactors B) : Squarefree n ∧ 2 ≤ n.primeFactors.card := by
  obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp hn
  have hd := owner_data (hB m hm).1 (hB m hm).2
  exact ⟨hd.2.2.1,hd.2.2.2.1⟩

/-- The exact owned rows exhaust B with no duplicate integer labels. -/
theorem owner_labels_eq (B : Finset ℕ)
    (hB : ∀ m ∈ B, Squarefree m ∧ 3 ≤ m.primeFactors.card) :
    (cofactors B).biUnion (fun n => (ownerRows B n).image (fun p => n*p)) = B := by
  ext m
  constructor
  · intro hm
    obtain ⟨n,_,hm⟩ := Finset.mem_biUnion.mp hm
    obtain ⟨p,hp,hpm⟩ := Finset.mem_image.mp hm
    obtain ⟨a,ha,hap⟩ := Finset.mem_image.mp hp
    obtain ⟨ha,han⟩ := Finset.mem_filter.mp ha
    have he := (owner_data (hB a ha).1 (hB a ha).2).2.1
    have ham : a=m := by rw [han,hap,Nat.mul_comm] at he; exact he.symm.trans hpm
    exact ham ▸ ha
  · intro hm
    have hd := owner_data (hB m hm).1 (hB m hm).2
    refine Finset.mem_biUnion.mpr ⟨ownerCofactor m,Finset.mem_image.mpr ⟨m,hm,rfl⟩,?_⟩
    exact Finset.mem_image.mpr ⟨largestPrime m,
      Finset.mem_image.mpr ⟨m,Finset.mem_filter.mpr ⟨hm,rfl⟩,rfl⟩,
      by simpa only [Nat.mul_comm] using hd.2.1⟩

/-- The joint cost of an entire finite literal support, with the smallest
population upper bound attained by its actual canonical cofactors. -/
def wholeCost (E : ℝ) (A B I : Finset ℕ) (O : ℕ → ℕ → ℝ)
    (N : ℕ) (L y scale : ℝ) : ℝ :=
  primeCost E ((cofactors B).sup id) N A (cofactors B) I (ownerPrimes B)
    (ownerRows B) O L y scale

/-- The bound applies to the WHOLE specified squarefree support, without
an unproved covering or ownership premise. All counts >=3 and all moving
masks enter together before the joint cost is taken. -/
theorem exists_whole_bounds :
    ∃ E : ℝ, 0 < E ∧ ∀ (A B I : Finset ℕ) (O : ℕ → ℕ → ℝ)
      (N : ℕ) (L y scale : ℝ),
      (∀ m ∈ B, Squarefree m ∧ 3 ≤ m.primeFactors.card) →
      Coordinates I (ownerPrimes B) O →
      let J := scale*(∑ m ∈ B,
        residualCoefficient A L N m*zetaPrimeLogKernel N (3/2+Complex.I*y) m).re;
      let K := wholeCost E A B I O N L y scale;
      -K ≤ J ∧ J ≤ K := by
  obtain ⟨E,hE,hbound⟩ := exists_literal_joint_bounds
  refine ⟨E,hE,fun A B I O N L y scale hB hO => ?_⟩
  have hS : cofactors B ⊆ Finset.Ioc 1 ((cofactors B).sup id) := by
    intro n hn
    have hd := cofactors_data B hB hn
    have hn1 : n ≠ 1 := by intro h; simp [h] at hd
    exact Finset.mem_Ioc.mpr ⟨by have := hd.1.ne_zero; omega,Finset.le_sup (f := id) hn⟩
  have hb := hbound ((cofactors B).sup id) N A (cofactors B) I (ownerPrimes B)
    (ownerRows B) O L y scale hO hS (fun _ hn => cofactors_data B hB hn)
    (fun n _ => ownerRows_subset B n)
    (fun _ _ _ hp => ⟨(ownerRows_data B hB hp).1,(ownerRows_data B hB hp).2.1⟩)
  have he := ZetaRieszCoupledWindow.sum_owned_products (cofactors B) (ownerRows B)
    (fun m => residualCoefficient A L N m*zetaPrimeLogKernel N (3/2+Complex.I*y) m)
    (fun _ hn => (cofactors_data B hB hn).1.ne_zero)
    (fun _ _ _ hp => ⟨(ownerRows_data B hB hp).1,(ownerRows_data B hB hp).2.2⟩)
  rw [owner_labels_eq B hB] at he
  simpa only [he,wholeCost,Nat.mul_comm] using hb

/-- A disjoint partition pays the sum of its actual joint costs, with the
same arithmetic constant. No maximum-cost or family-cardinality loss enters. -/
theorem exists_partition_bounds :
    ∃ E : ℝ, 0 < E ∧ ∀ (A I : Finset ℕ) (B V : ℕ → Finset ℕ)
      (O : ℕ → ℕ → ℕ → ℝ) (N : ℕ) (L y scale : ℝ),
      (I : Set ℕ).PairwiseDisjoint B →
      (∀ i ∈ I, ∀ m ∈ B i, Squarefree m ∧ 3 ≤ m.primeFactors.card) →
      (∀ i ∈ I, Coordinates (V i) (ownerPrimes (B i)) (O i)) →
      let J := scale*(∑ m ∈ I.biUnion B,
        residualCoefficient A L N m*zetaPrimeLogKernel N (3/2+Complex.I*y) m).re;
      let C := ∑ i ∈ I, wholeCost E A (B i) (V i) (O i) N L y scale;
      -C ≤ J ∧ J ≤ C := by
  obtain ⟨E,hE,hbound⟩ := exists_whole_bounds
  refine ⟨E,hE,fun A I B V O N L y scale hdis hB hO => ?_⟩
  have hb i (hi : i ∈ I) :=
    hbound A (B i) (V i) (O i) N L y scale (hB i hi) (hO i hi)
  dsimp only
  rw [Finset.sum_biUnion hdis,Complex.re_sum,Finset.mul_sum]
  have hlo := Finset.sum_le_sum (fun i hi => (hb i hi).1)
  rw [Finset.sum_neg_distrib] at hlo
  exact ⟨hlo,Finset.sum_le_sum (fun i hi => (hb i hi).2)⟩

open ZetaRieszParityPacket

/-- Every original core label has at least three distinct prime factors. -/
theorem core_count {u : ℝ} {N K m : ℕ} (hm : m ∈ coreBand u N K) :
    3 ≤ m.primeFactors.card := by
  simp only [coreBand,ZetaRieszTypeII.narrowBand,LogarithmicDeviation.deviationBand,
    ZetaRieszDominantAllocation.nondominantBand,ZetaRieszMaskSupport.retainedBand,
    ZetaRieszCompanionMask.originalMask,ZetaRieszHarmonicWindow.fewBand,
    Finset.mem_filter,Finset.mem_sdiff] at hm
  tauto

/-- Nonsquarefree labels have exactly zero original residual coefficient;
retaining only the squarefree core is an equality, not an error estimate. -/
theorem core_eq_squarefree (u y : ℝ) (N K : ℕ) :
    coreResponse u y N K =
      ∑ m ∈ (coreBand u N K).filter Squarefree,
        residualCoefficient (ZetaRieszAnnulusJoint.intermediatePrimes u N)
          (SquarefreeVaughanLogSource.length u N) N m*
          zetaPrimeLogKernel N (3/2+Complex.I*y) m := by
  unfold coreResponse
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro m hm hnot
  have hns : ¬Squarefree m := fun h => hnot (Finset.mem_filter.mpr ⟨hm,h⟩)
  simp [residualCoefficient,SquarefreeVaughanLogSource.coefficient,hns]

/-- BOTH bounds for the ACTUAL source-normalized coreResponse, with every
original mask and factorial order retained. The finite coordinate condition
is always satisfiable by identity coordinates. Only the total numerical
size/asymptotics of this explicit joint cost remain unproved. -/
theorem exists_core_joint_bounds :
    ∃ E : ℝ, 0 < E ∧ ∀ (u y : ℝ) (N K : ℕ) (I : Finset ℕ) (O : ℕ → ℕ → ℝ),
      let B := (coreBand u N K).filter Squarefree;
      Coordinates I (ownerPrimes B) O →
      let C := wholeCost E (ZetaRieszAnnulusJoint.intermediatePrimes u N) B I O N
        (SquarefreeVaughanLogSource.length u N) y (u^(N+1));
      -C ≤ u^(N+1)*(coreResponse u y N K).re ∧
        u^(N+1)*(coreResponse u y N K).re ≤ C := by
  obtain ⟨E,hE,hbound⟩ := exists_whole_bounds
  refine ⟨E,hE,fun u y N K I O hO => ?_⟩
  have hb := hbound (ZetaRieszAnnulusJoint.intermediatePrimes u N)
    ((coreBand u N K).filter Squarefree) I O N (SquarefreeVaughanLogSource.length u N) y
    (u^(N+1)) (fun m hm => ⟨(Finset.mem_filter.mp hm).2,core_count (Finset.mem_filter.mp hm).1⟩) hO
  simpa only [← core_eq_squarefree] using hb

end RiemannGaussian.ZetaRieszJointPrimeEnergy
