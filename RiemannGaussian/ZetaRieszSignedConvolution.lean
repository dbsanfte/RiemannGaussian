/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszSignedCrossing
import RiemannGaussian.ZetaRieszNonownerAllocation
import RiemannGaussian.ZetaRieszJoinedPhysical
import RiemannGaussian.ZetaRoughMoebiusHyperbola
import RiemannGaussian.SuzukiLogarithmicConvolution

/-!
# The joined signed prime-period convolution

The constant moment, first moment and exact cutoff crossing are rejoined
before any inequality. Divisor complementation on the squarefree cofactor
moves both Möbius signs onto its complementary divisor. The resulting hinge
depends on `p*b`; the original allocation, factorial kernel and complex phase
still depend on `p*d*b`. No count, period or owner mask is completed.

The only estimate here is the already proved geometric nonowner payment.
The signed convolution itself, including its prime-pair boundary, is not
asserted bounded at source scale.
-/

noncomputable section
open Filter Topology
open scoped BigOperators Classical ArithmeticFunction.Moebius
namespace RiemannGaussian.ZetaRieszSignedConvolution
open ZetaRieszGlobalPrimePeriod ZetaRieszGlobalCurvature
open ZetaRieszFixedCountPeriod ZetaRieszJointAllocation
open ZetaRieszPrimeEndpoint ZetaRieszParityPacket

/-- Both reflected hinges, after complementing a divisor of the cofactor.
The maxima are the original Riesz hinges, not an allowance for signed terms. -/
def pairHinge (L : ℝ) (p b : ℕ) : ℝ :=
  max 0 (Real.log p+Real.log b-L)-max 0 (Real.log b-L)

/-- The full correlated complex weight. It contains no Möbius sign and
retains the original allocation and the full prime phase on `p*a`. -/
def phaseWeight (A : Finset ℕ) (L : ℝ) (N : ℕ) (y : ℝ) (a p : ℕ) : ℂ :=
  (((1-boundedShare A N (p*a))*Real.log (p*a : ℕ)/L : ℝ) : ℂ)*
    zetaPrimeLogKernel N (3/2+Complex.I*y) (p*a)

theorem moebius_cofactor_real {a d : ℕ} (hs : Squarefree a) (hd : d ∣ a) :
    (μ (a/d) : ℝ) = (μ a : ℝ)*(μ d : ℝ) := by
  exact_mod_cast RoughMoebiusHyperbola.moebius_cofactor hs hd

/-- Exact complement reindexing. The joint hinge no longer depends on the
deleted divisor `d`; its Möbius parity is the parity of the surviving `b`. -/
theorem moebius_response_eq_convolution {a p : ℕ} (hs : Squarefree a) (L : ℝ) :
    (μ a : ℝ)*response L (Real.log p+Real.log a) a =
      ∑ db ∈ a.divisorsAntidiagonal, (μ db.2 : ℝ)*pairHinge L p db.2 := by
  rw [Nat.sum_divisorsAntidiagonal (fun d b => (μ b : ℝ)*pairHinge L p b)]
  simp only [response,VaughanLogAverage.riesz,← Finset.sum_sub_distrib,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hdn := Nat.dvd_of_mem_divisors hd
  have hd0 : d ≠ 0 := (Nat.pos_of_dvd_of_pos hdn (Nat.pos_of_ne_zero hs.ne_zero)).ne'
  have hb0 : a/d ≠ 0 := by
    have he := Nat.mul_div_cancel' hdn
    intro hz
    rw [hz,mul_zero] at he
    exact hs.ne_zero he.symm
  have hl : Real.log a = Real.log d+Real.log (a/d : ℕ) := by
    calc
      _ = Real.log (d*(a/d) : ℕ) := congrArg (fun n : ℕ => Real.log n) (Nat.mul_div_cancel' hdn).symm
      _ = _ := by rw [Nat.cast_mul,
        Real.log_mul (by exact_mod_cast hd0) (by exact_mod_cast hb0)]
  rw [moebius_cofactor_real hs hdn]
  unfold pairHinge
  rw [show Real.log p+Real.log a-L-Real.log d =
      Real.log p+Real.log (a/d : ℕ)-L by rw [hl]; ring,
    show Real.log a-L-Real.log d = Real.log (a/d : ℕ)-L by rw [hl]; ring]
  ring

/-- The exact complex residual atom, before taking a real part. -/
theorem residual_atom_eq_parity_response {a p : ℕ} (hs : Squarefree a)
    (hc : 2 ≤ a.primeFactors.card) (hp : p.Prime) (hpd : ¬p ∣ a)
    (A : Finset ℕ) (L y : ℝ) (N : ℕ) :
    residualCoefficient A L N (p*a)*zetaPrimeLogKernel N (3/2+Complex.I*y) (p*a) =
      phaseWeight A L N y a p*
        (((μ a : ℝ)*response L (Real.log p+Real.log a) a : ℝ) : ℂ) := by
  have hm : (μ a : ℝ) = (-1 : ℝ)^a.primeFactors.card := by
    exact_mod_cast ZetaRieszReflectedLinear.moebius_eq_primeCount hs
  have hlog : Real.log (p*a : ℕ) = Real.log p+Real.log a := by
    rw [Nat.cast_mul,Real.log_mul (by exact_mod_cast hp.ne_zero) (by exact_mod_cast hs.ne_zero)]
  rw [residualCoefficient,coefficient_eq_response hs hc hp hpd,
    phaseWeight,hm,pow_succ,hlog]
  push_cast
  ring

/-- The requested literal bilinear convolution, with every correlated
weight kept inside the exact finite sum. No cancellation hypothesis is used. -/
theorem residual_atom_eq_convolution {a p : ℕ} (hs : Squarefree a)
    (hc : 2 ≤ a.primeFactors.card) (hp : p.Prime) (hpd : ¬p ∣ a)
    (A : Finset ℕ) (L y : ℝ) (N : ℕ) :
    residualCoefficient A L N (p*a)*zetaPrimeLogKernel N (3/2+Complex.I*y) (p*a) =
      ∑ db ∈ a.divisorsAntidiagonal,
        phaseWeight A L N y a p*(μ db.2 : ℂ)*(pairHinge L p db.2 : ℂ) := by
  rw [residual_atom_eq_parity_response hs hc hp hpd,
    moebius_response_eq_convolution hs]
  simp only [Complex.ofReal_sum,Complex.ofReal_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro db _
  push_cast
  ring

/-- These are the literal constant and first signed prime moments; they
have no positive-part or absolute-value replacement. -/
def moment0 (A : ℕ → Finset ℕ) (P : ℕ → Finset ℕ)
    (L : ℝ) (N : ℕ) (y : ℝ) (a : ℕ) : ℝ :=
  ∑ p ∈ P a, signedPrimeWeight (A (p*a)) L N y a p

/-- The literal centered first signed prime moment, with the same
allocation and phase as the constant moment. -/
def moment1 (A : ℕ → Finset ℕ) (P : ℕ → Finset ℕ)
    (L : ℝ) (N : ℕ) (y v : ℝ) (a : ℕ) : ℝ :=
  ∑ p ∈ P a, signedPrimeWeight (A (p*a)) L N y a p*(Real.log p+Real.log a-v)

/-- The signed crossing is retained exactly, not bounded one divisor or
one prime count at a time. -/
def signedCrossing (A : ℕ → Finset ℕ) (P : ℕ → Finset ℕ)
    (L : ℝ) (N : ℕ) (y v : ℝ) (a : ℕ) : ℝ :=
  ∑ p ∈ P a, ZetaRieszSignedCrossing.crossingAtom (A (p*a)) L N y v a p

/-- All counts and all radial periods are joined before the reindexing.
The reference period centers disappear from the final exact convolution. -/
theorem joint_periods_eq_convolution {ι : Type*} (B : Finset ι)
    (S : ι → Finset ℕ) (P : ι → ℕ → Finset ℕ) (A : ℕ → Finset ℕ)
    (L y : ℝ) (N : ℕ) (v : ι → ℝ)
    (hSF : ∀ i ∈ B, ∀ a ∈ S i, Squarefree a ∧ 2 ≤ a.primeFactors.card)
    (hP : ∀ i ∈ B, ∀ a ∈ S i, ∀ p ∈ P i a, p.Prime ∧ ¬p ∣ a) :
    (∑ i ∈ B, ∑ a ∈ S i,
      ((response L (v i) a*moment0 A (P i) L N y a+
        cutoffSlope (v i-L) a*moment1 A (P i) L N y (v i) a)/a+
      signedCrossing A (P i) L N y (v i) a)) =
      ∑ i ∈ B, ∑ a ∈ S i, ∑ p ∈ P i a, ∑ db ∈ a.divisorsAntidiagonal,
        (phaseWeight (A (p*a)) L N y a p).re*(μ db.2 : ℝ)*pairHinge L p db.2 := by
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro a ha
  simp only [moment0,moment1,signedCrossing,Finset.mul_sum,← Finset.sum_add_distrib,
    Finset.sum_div]
  apply Finset.sum_congr rfl
  intro p hp
  rw [ZetaRieszSignedCrossing.crossingAtom]
  calc
    _ = (residualCoefficient (A (p*a)) L N (p*a)*
        zetaPrimeLogKernel N (3/2+Complex.I*y) (p*a)).re := by ring
    _ = _ := by
      rw [residual_atom_eq_convolution (hSF i hi a ha).1 (hSF i hi a ha).2
        (hP i hi a ha p hp).1 (hP i hi a ha p hp).2,Complex.re_sum]
      apply Finset.sum_congr rfl
      intro db _
      simp [Complex.mul_re]

/-- Divisor reindexing retains the entire original cofactor mask. In
particular, coprimality and squarefreeness are not replaced by densities. -/
theorem masked_hyperbola (S : Finset ℕ) (X : ℕ) (hS : S ⊆ Finset.Icc 1 X)
    (f : ℕ → ℕ → ℝ) :
    (∑ a ∈ S, ∑ db ∈ a.divisorsAntidiagonal, f db.1 db.2) =
      ∑ d ∈ Finset.Icc 1 X, ∑ b ∈ Finset.Icc 1 (X/d),
        if d*b ∈ S then f d b else 0 := by
  rw [← ZetaRieszGlobalCurvature.weighted_hyperbola
    (fun d b => if d*b ∈ S then f d b else 0) X]
  calc
    _ = ∑ a ∈ S, ∑ db ∈ a.divisorsAntidiagonal,
        if db.1*db.2 ∈ S then f db.1 db.2 else 0 := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro db hdb
      rw [(Nat.mem_divisorsAntidiagonal.mp hdb).1,if_pos ha]
    _ = _ := by
      apply Finset.sum_subset hS
      intro a _ hnot
      apply Finset.sum_eq_zero
      intro db hdb
      rw [(Nat.mem_divisorsAntidiagonal.mp hdb).1,if_neg hnot]

/-- The actual joint moment/crossing aggregate is one signed bilinear
sum over `a=d*b`. Prime selections, owner weights and phases continue to
depend on the complete original product, not on one factor in isolation. -/
theorem joint_periods_eq_bilinear {ι : Type*} (B : Finset ι)
    (S : ι → Finset ℕ) (P : ι → ℕ → Finset ℕ) (A : ℕ → Finset ℕ)
    (L y : ℝ) (N X : ℕ) (v : ι → ℝ)
    (hSX : ∀ i ∈ B, S i ⊆ Finset.Icc 1 X)
    (hSF : ∀ i ∈ B, ∀ a ∈ S i, Squarefree a ∧ 2 ≤ a.primeFactors.card)
    (hP : ∀ i ∈ B, ∀ a ∈ S i, ∀ p ∈ P i a, p.Prime ∧ ¬p ∣ a) :
    (∑ i ∈ B, ∑ a ∈ S i,
      ((response L (v i) a*moment0 A (P i) L N y a+
        cutoffSlope (v i-L) a*moment1 A (P i) L N y (v i) a)/a+
      signedCrossing A (P i) L N y (v i) a)) =
      ∑ i ∈ B, ∑ d ∈ Finset.Icc 1 X, ∑ b ∈ Finset.Icc 1 (X/d),
        if d*b ∈ S i then ∑ p ∈ P i (d*b),
          (phaseWeight (A (p*(d*b))) L N y (d*b) p).re*(μ b : ℝ)*pairHinge L p b
        else 0 := by
  rw [joint_periods_eq_convolution B S P A L y N v hSF hP]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← masked_hyperbola (S i) X (hSX i hi)]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro db hdb
  rw [(Nat.mem_divisorsAntidiagonal.mp hdb).1]

/-- An exact source-equivalent convolution on the original core. The prime
and all its divisor incidences are the canonical owner of the original label. -/
def coreConvolution (u y : ℝ) (N K : ℕ) : ℂ :=
  ∑ n ∈ (coreBand u N K).filter Squarefree,
    ∑ db ∈ (n/largestPrime n).divisorsAntidiagonal,
      phaseWeight (ZetaRieszAnnulusJoint.intermediatePrimes u N ∩ {largestPrime n})
        (SquarefreeVaughanLogSource.length u N) N y (n/largestPrime n) (largestPrime n)*
        (μ db.2 : ℂ)*(pairHinge (SquarefreeVaughanLogSource.length u N) (largestPrime n) db.2 : ℂ)

/-- The finite original masks are unchanged. Nonsquarefree atoms vanish
exactly; the divisor incidence adds neither a new label nor a completion. -/
theorem coreConvolution_eq_owner (u y : ℝ) (N K : ℕ) :
    coreConvolution u y N K =
      ∑ n ∈ coreBand u N K,
        residualCoefficient (ZetaRieszAnnulusJoint.intermediatePrimes u N ∩ {largestPrime n})
          (SquarefreeVaughanLogSource.length u N) N n*
            zetaPrimeLogKernel N (3/2+Complex.I*y) n := by
  have hf : (∑ n ∈ (coreBand u N K).filter Squarefree,
      residualCoefficient (ZetaRieszAnnulusJoint.intermediatePrimes u N ∩ {largestPrime n})
        (SquarefreeVaughanLogSource.length u N) N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n) =
      ∑ n ∈ coreBand u N K,
        residualCoefficient (ZetaRieszAnnulusJoint.intermediatePrimes u N ∩ {largestPrime n})
          (SquarefreeVaughanLogSource.length u N) N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro n hn hnot
    have hns : ¬Squarefree n := fun h => hnot (Finset.mem_filter.mpr ⟨hn,h⟩)
    simp [residualCoefficient,SquarefreeVaughanLogSource.coefficient,hns]
  rw [← hf,coreConvolution]
  apply Finset.sum_congr rfl
  intro n hn
  obtain ⟨hcore,hs⟩ := Finset.mem_filter.mp hn
  have hc := ZetaRieszJointPrimeEnergy.core_count hcore
  have hp := ZetaRieszOwnedCells.largestPrime_mem_of_two (by omega : 2 ≤ n.primeFactors.card)
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hd := ZetaRieszMarkedSaturation.cofactor_data hs hc hp
  have he : largestPrime n*(n/largestPrime n)=n := Nat.mul_div_cancel' (Nat.dvd_of_mem_primeFactors hp)
  have hcnt : n.primeFactors.card = (n/largestPrime n).primeFactors.card+1 := by
    conv_lhs => rw [← he,Nat.primeFactors_mul hpp.ne_zero hd.1.ne_zero,hpp.primeFactors,
      Finset.singleton_union,Finset.card_insert_of_notMem
        (show largestPrime n ∉ (n/largestPrime n).primeFactors from
          fun h => hd.2.2.2 (Nat.dvd_of_mem_primeFactors h))]
  have hr := residual_atom_eq_convolution hd.1 (by omega) hpp hd.2.2.2
    (ZetaRieszAnnulusJoint.intermediatePrimes u N ∩ {largestPrime n})
    (SquarefreeVaughanLogSource.length u N) y N
  rw [he] at hr
  exact hr.symm

/-- The SINGLE global nonowner payment applies to the entire convolution,
uniformly in the count cutoff and height. No signed main is norm-paid. -/
theorem core_sub_convolution_bound {u : ℝ} (hu : 0 ≤ u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (N K : ℕ) (y : ℝ) :
    ‖(u : ℂ)^(N+1)*(coreResponse u y N K-coreConvolution u y N K)‖ ≤
      (4*((N : ℝ)+1)/3)*(ZetaRieszNonownerAllocation.nonownerRate^N*
        ((1509/1000 : ℝ)*zetaMoebiusLogMajorantMass (2049/2048))) := by
  rw [coreConvolution_eq_owner,coreResponse]
  have h := ZetaRieszNonownerAllocation.residual_sub_owner_bound
    (fun _ => ZetaRieszAnnulusJoint.intermediatePrimes u N) (coreBand u N K)
    (fun _ => 1) (SquarefreeVaughanLogSource.length_pos u N) N
    (ZetaRieszNonownerAllocation.coreBand_subset_literalWindow u N K)
    (by intros; simp) y hu (hU.trans ZetaRieszWideOwnerAudit.radius_lt_source.le)
  simpa only [one_mul,sub_mul,Finset.sum_sub_distrib] using h

/-- Both existing geometric payments connect the convolution directly to
the current endgame carrier. The bound controls only their DIFFERENCE. -/
theorem joined_sub_convolution_bound {u : ℝ} (hu : 0 ≤ u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (N K : ℕ) (y : ℝ)
    (hL : (11/8 : ℝ)*N ≤ SquarefreeVaughanLogSource.length u N) :
    ‖(u : ℂ)^(N+1)*(ZetaRieszGammaJoint.joinedPhysical u y N K-
      coreConvolution u y N K)‖ ≤
      2*(19/20 : ℝ)^N*zetaMoebiusLogMajorantMass (1+1/256)+
        (4*((N : ℝ)+1)/3)*(ZetaRieszNonownerAllocation.nonownerRate^N*
          ((1509/1000 : ℝ)*zetaMoebiusLogMajorantMass (2049/2048))) := by
  have hj : ‖(u : ℂ)^(N+1)*(ZetaRieszGammaJoint.joinedPhysical u y N K-
      coreResponse u y N K)‖ ≤
      2*(19/20 : ℝ)^N*zetaMoebiusLogMajorantMass (1+1/256) := by
    rw [show (u : ℂ)^(N+1)*(ZetaRieszGammaJoint.joinedPhysical u y N K-
      coreResponse u y N K) = -((u : ℂ)^(N+1)*(coreResponse u y N K-
        ZetaRieszGammaJoint.joinedPhysical u y N K)) by ring,norm_neg]
    exact ZetaRieszGammaJoint.core_joined_bound hu hU N K y hL
  rw [show (u : ℂ)^(N+1)*(ZetaRieszGammaJoint.joinedPhysical u y N K-
    coreConvolution u y N K) =
      (u : ℂ)^(N+1)*(ZetaRieszGammaJoint.joinedPhysical u y N K-coreResponse u y N K)+
        (u : ℂ)^(N+1)*(coreResponse u y N K-coreConvolution u y N K) by ring]
  exact (norm_add_le _ _).trans (add_le_add hj (core_sub_convolution_bound hu hU N K y))

theorem tendsto_core_sub_convolution (K : ℕ → ℕ) (y : ℕ → ℝ)
    {u : ℝ} (hu : 0 ≤ u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) :
    Tendsto (fun N => (u : ℂ)^(N+1)*(coreResponse u (y N) N (K N)-
      coreConvolution u (y N) N (K N))) atTop (𝓝 0) := by
  simpa only [coreConvolution_eq_owner] using
    ZetaRieszNonownerAllocation.tendsto_core_sub_owner K y hu hU

/-- The classical linear-plus-prime-pair identity applies to the complete
signed convolution, not to its divisor terms separately. The exact clipped
cutoff remainder is retained. `c` and `r` do not assert any estimate. -/
theorem selberg_cutoff_split {a : ℕ} (ha : Squarefree a) (L c r : ℝ) (p : ℕ) :
    (∑ db ∈ a.divisorsAntidiagonal, (μ db.2 : ℝ)*pairHinge L p db.2) =
      (μ a : ℝ)*c*(ArithmeticFunction.vonMangoldt a*(Real.log a-r)+zetaPrimePairArithmetic a)+
        ∑ db ∈ a.divisorsAntidiagonal, (μ db.2 : ℝ)*
          (pairHinge L p db.2-c*Real.log db.2*(Real.log db.2-r)) := by
  have hs : (∑ db ∈ a.divisorsAntidiagonal,
      (μ db.2 : ℝ)*Real.log db.2*(Real.log db.2-r)) =
      (μ a : ℝ)*(ArithmeticFunction.vonMangoldt a*(Real.log a-r)+zetaPrimePairArithmetic a) := by
    calc
      _ = ∑ d ∈ a.divisors, (μ (a/d) : ℝ)*Real.log (a/d : ℕ)*(Real.log (a/d : ℕ)-r) :=
        Nat.sum_divisorsAntidiagonal (fun _ b => (μ b : ℝ)*Real.log b*(Real.log b-r))
      _ = (μ a : ℝ)*∑ d ∈ a.divisors,
          (μ d : ℝ)*Real.log (a/d : ℕ)*(Real.log (a/d : ℕ)-r) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro d hd
        rw [moebius_cofactor_real ha (Nat.dvd_of_mem_divisors hd)]
        ring
      _ = _ := by
        rw [← Nat.sum_divisorsAntidiagonal (fun d b =>
          (μ d : ℝ)*Real.log b*(Real.log b-r)),sum_moebius_log_mul_sub_center]
  rw [show (μ a : ℝ)*c*(ArithmeticFunction.vonMangoldt a*(Real.log a-r)+
      zetaPrimePairArithmetic a) = c*((μ a : ℝ)*(ArithmeticFunction.vonMangoldt a*
        (Real.log a-r)+zetaPrimePairArithmetic a)) by ring,
    ← hs,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro db _
  ring

/-- The same Selberg split with the full original complex weight. This
does not complete a cofactor, alter an owner mask, or assume a Type-II bound. -/
theorem residual_atom_eq_selberg_cutoff {a p : ℕ} (hs : Squarefree a)
    (hc : 2 ≤ a.primeFactors.card) (hp : p.Prime) (hpd : ¬p ∣ a)
    (A : Finset ℕ) (L y c r : ℝ) (N : ℕ) :
    residualCoefficient A L N (p*a)*zetaPrimeLogKernel N (3/2+Complex.I*y) (p*a) =
      phaseWeight A L N y a p*
        (((μ a : ℝ)*c*(ArithmeticFunction.vonMangoldt a*(Real.log a-r)+zetaPrimePairArithmetic a)+
          ∑ db ∈ a.divisorsAntidiagonal, (μ db.2 : ℝ)*
            (pairHinge L p db.2-c*Real.log db.2*(Real.log db.2-r)) : ℝ) : ℂ) := by
  rw [residual_atom_eq_parity_response hs hc hp hpd,
    moebius_response_eq_convolution hs,selberg_cutoff_split hs]

/-- A squarefree composite cofactor has no ordinary prime-power channel. -/
theorem vonMangoldt_zero_of_squarefree_count {a : ℕ} (ha : Squarefree a)
    (hc : 2 ≤ a.primeFactors.card) : ArithmeticFunction.vonMangoldt a = 0 := by
  apply ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr
  intro hpow
  have hp := Nat.squarefree_and_prime_pow_iff_prime.mp ⟨ha,hpow⟩
  rw [hp.primeFactors,Finset.card_singleton] at hc
  omega

/-- The Selberg pair channel is supported only on at most two prime
factors of a squarefree cofactor. All larger counts retain their signed
cutoff remainder, rather than inheriting a pair allowance. -/
theorem primePair_zero_of_squarefree_count {a : ℕ} (ha : Squarefree a)
    (hc : 3 ≤ a.primeFactors.card) : zetaPrimePairArithmetic a = 0 := by
  rw [zetaPrimePairArithmetic,ArithmeticFunction.mul_apply]
  apply Finset.sum_eq_zero
  intro db hdb
  by_cases hd : ArithmeticFunction.vonMangoldt db.1 = 0
  · rw [hd,zero_mul]
  by_cases hb : ArithmeticFunction.vonMangoldt db.2 = 0
  · rw [hb,mul_zero]
  have he := (Nat.mem_divisorsAntidiagonal.mp hdb).1
  have hs : Squarefree (db.1*db.2) := he.symm ▸ ha
  have hdp := Nat.squarefree_and_prime_pow_iff_prime.mp
    ⟨hs.of_mul_left,not_not.mp (mt ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hd)⟩
  have hbp := Nat.squarefree_and_prime_pow_iff_prime.mp
    ⟨hs.of_mul_right,not_not.mp (mt ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hb)⟩
  have hcard : a.primeFactors.card ≤ 2 := by
    rw [← he,Nat.primeFactors_mul hdp.ne_zero hbp.ne_zero,hdp.primeFactors,hbp.primeFactors]
    exact (Finset.card_union_le _ _).trans (by simp)
  omega

/-- An exact common cancellation across every higher cofactor count:
any centered quadratic may be removed INSIDE the signed profile. The
remaining nonpolynomial cutoff response is explicit and is not norm-paid. -/
theorem higher_count_quadratic_cancellation {a : ℕ} (ha : Squarefree a)
    (hc : 3 ≤ a.primeFactors.card) (L c r : ℝ) (p : ℕ) :
    (∑ db ∈ a.divisorsAntidiagonal, (μ db.2 : ℝ)*pairHinge L p db.2) =
      ∑ db ∈ a.divisorsAntidiagonal, (μ db.2 : ℝ)*
        (pairHinge L p db.2-c*Real.log db.2*(Real.log db.2-r)) := by
  rw [selberg_cutoff_split ha L c r p,vonMangoldt_zero_of_squarefree_count ha (by omega),
    primePair_zero_of_squarefree_count ha hc]
  simp

/-- Every active incidence crosses the SAME prime-product cutoff,
independently of the number of factors in either cofactor. -/
theorem pairHinge_active {L : ℝ} {p b : ℕ} (h : pairHinge L p b ≠ 0) :
    L < Real.log p+Real.log b := by
  by_contra hn
  have hp := Real.log_natCast_nonneg p
  have hb : Real.log b ≤ L := by linarith [le_of_not_gt hn]
  apply h
  simp [pairHinge,max_eq_left (sub_nonpos.mpr (le_of_not_gt hn)),
    max_eq_left (sub_nonpos.mpr hb)]

/-- The unsigned `d` leg is automatically short on every active signed
incidence. This is an exact support inequality, not prime-density transport. -/
theorem active_divisor_short {L : ℝ} {a p d b : ℕ}
    (hdb : (d,b) ∈ a.divisorsAntidiagonal) (h : pairHinge L p b ≠ 0) :
    Real.log d < Real.log p+Real.log a-L := by
  obtain ⟨hd0,hb0⟩ := Nat.ne_zero_of_mem_divisorsAntidiagonal hdb
  have hl : Real.log a = Real.log d+Real.log b := by
    rw [← (Nat.mem_divisorsAntidiagonal.mp hdb).1,Nat.cast_mul,
      Real.log_mul (by exact_mod_cast hd0) (by exact_mod_cast hb0)]
  linarith [pairHinge_active h]

/-- A reflected-large owner makes ownership of the short `d` leg
automatic. The remaining large `b` leg and its signs are still retained. -/
theorem active_divisor_lt_reflected_owner {L : ℝ} {a p d b : ℕ}
    (hp : p.Prime) (hdb : (d,b) ∈ a.divisorsAntidiagonal)
    (h : pairHinge L p b ≠ 0)
    (href : Real.log p+Real.log a-L ≤ Real.log p) : d < p := by
  have hlog := (active_divisor_short hdb h).trans_le href
  by_contra hn
  have hle : (p : ℝ) ≤ d := by exact_mod_cast le_of_not_gt hn
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  exact (not_le_of_gt hlog) (Real.log_le_log hp0 hle)

/-- On the literal core every active unsigned divisor has this uniform
exponential-length ceiling. The count and share masks are untouched. -/
theorem active_divisor_core_log_bound {u : ℝ} {N K n d b : ℕ}
    (hn : n ∈ coreBand u N K)
    (hdb : (d,b) ∈ (n/largestPrime n).divisorsAntidiagonal)
    (h : pairHinge (SquarefreeVaughanLogSource.length u N) (largestPrime n) b ≠ 0)
    (hL : (11/8 : ℝ)*N ≤ SquarefreeVaughanLogSource.length u N) :
    Real.log d < (131/200 : ℝ)*N := by
  have hc := ZetaRieszJointPrimeEnergy.core_count hn
  have hp := ZetaRieszOwnedCells.largestPrime_mem_of_two
    (m := n) (by omega : 2 ≤ n.primeFactors.card)
  have hpd := Nat.dvd_of_mem_primeFactors hp
  have hprod := Nat.mul_div_cancel' hpd
  have hpP := Nat.prime_of_mem_primeFactors hp
  have ha0 : n/largestPrime n ≠ 0 := (Nat.mem_divisorsAntidiagonal.mp hdb).2
  have hl : Real.log n = Real.log (largestPrime n)+Real.log (n/largestPrime n : ℕ) := by
    calc
      _ = Real.log (largestPrime n*(n/largestPrime n) : ℕ) :=
        congrArg (fun m : ℕ => Real.log m) hprod.symm
      _ = _ := by rw [Nat.cast_mul,
        Real.log_mul (by exact_mod_cast hpP.ne_zero) (by exact_mod_cast ha0)]
  have hw : Real.log n ≤ (203/100 : ℝ)*N := (Finset.mem_filter.mp hn).2.2
  have hs := active_divisor_short hdb h
  rw [← hl] at hs
  linarith

/-- The unit complementary divisor contributes exactly zero throughout
the physical prime cutoff. No absolute allowance is charged for it. -/
theorem pairHinge_one {L : ℝ} (hL : 0 ≤ L) {p : ℕ} (hp : Real.log p ≤ L) :
    pairHinge L p 1 = 0 := by
  simp [pairHinge,max_eq_left (sub_nonpos.mpr hp),max_eq_left (by linarith : -L ≤ 0)]

/-- The ordinary-prime complementary divisor is the exact negative
prime-pair boundary. It survives when the prime product crosses the cutoff. -/
theorem prime_pair_boundary {L : ℝ} {p q : ℕ} (hq : q.Prime)
    (hql : Real.log q ≤ L) :
    (μ q : ℝ)*pairHinge L p q = -max 0 (Real.log p+Real.log q-L) := by
  simp [pairHinge,ArithmeticFunction.moebius_apply_prime hq,
    max_eq_left (sub_nonpos.mpr hql)]

end RiemannGaussian.ZetaRieszSignedConvolution
