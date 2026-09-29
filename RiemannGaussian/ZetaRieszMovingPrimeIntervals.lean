/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszRetainedFactorial
import RiemannGaussian.ZetaRieszPrimeTailEnergy
import RiemannGaussian.ZetaRieszOwnerMaximal
import RiemannGaussian.ZetaRieszCoupledWindow

/-!
# Joint signed bounds with cofactor-dependent prime intervals

Binary maximal sums pay the moving prime endpoints without differentiating
the cofactor's masks. Prime sums stay inside each block's quadratic energy;
the final bound retains the exact factorial coefficients, including orders
zero and one. Neither a prime-density approximation nor a zero hypothesis is
used. An application to the whole carrier still requires a disjoint cover
and a bound on the total source-normalized cost.
-/

noncomputable section
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszMovingPrimeIntervals
open Real ZetaRieszOwnerMaximal ZetaRieszPrimeTailEnergy
open ZetaRieszRetainedFactorial ZetaRieszWeightedPrimeTail ZetaRieszJointAllocation

/-- Two moving endpoints cost at most four times the binary prefix budget. -/
theorem interval_sq_le_dyadicCost (f : ℕ → ℝ) (b lo hi : ℕ)
    (hlo : lo ≤ hi) (hhi : hi ≤ 2^b) :
    (∑ i ∈ Finset.Ico lo hi, f i)^2 ≤
      4*((b+1 : ℕ) : ℝ)*dyadicCost
        (fun a m => (∑ i ∈ Finset.Ico a (a+m), f i)^2) b 0 := by
  have hl := prefix_sq_le_dyadicCost f b 0 (hlo.trans hhi)
  have hh := prefix_sq_le_dyadicCost f b 0 hhi
  simp only [Nat.zero_add,Nat.Ico_zero_eq_range] at hl hh
  rw [Finset.sum_Ico_eq_sub _ hlo]
  nlinarith [sq_nonneg ((∑ i ∈ Finset.range hi, f i)+(∑ i ∈ Finset.range lo, f i))]

/-- A common block's literal signed response, with both cutoff hinges. -/
def componentResponse (P : ℕ → Finset ℕ) (I : Finset ℕ) (c : ℕ → ℝ)
    (L : ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ I, ∑ p ∈ P i, c p*
    (VaughanLogAverage.riesz L n-VaughanLogAverage.riesz (L-log p) n)

/-- The finite divisor profile retains every prime cross term in a block. -/
def blockProfile (P : ℕ → Finset ℕ) (I : Finset ℕ) (c : ℕ → ℝ)
    (L : ℝ) (d : ℕ) : ℝ := ∑ i ∈ I, profile (P i) c (fun p => log p) L d

/-- The full cofactor phase rotates two common prime profiles exactly. -/
def blockResponse (P : ℕ → Finset ℕ) (I : Finset ℕ) (G : ℝ → ℝ)
    (y L v : ℝ) (n : ℕ) : ℝ :=
  componentResponse P I (fun p => G (log p)*cos (y*(log p+v))/(p : ℝ)) L n

/-- Joint cosine/sine difference energy of actual primes, before any norm. -/
def blockEnergy (P : ℕ → Finset ℕ) (I : Finset ℕ) (G : ℝ → ℝ)
    (y L : ℝ) (R : ℕ) : ℝ :=
  let f := blockProfile P I (fun p => G (log p)*cos (y*log p)/(p : ℝ)) L
  let g := blockProfile P I (fun p => G (log p)*sin (y*log p)/(p : ℝ)) L
  ∑ k ∈ Finset.Icc 1 R, (k : ℝ)*((f k-f (k+1))^2+(g k-g (k+1))^2)

private theorem blockEnergy_nonneg (P : ℕ → Finset ℕ) (I : Finset ℕ)
    (G : ℝ → ℝ) (y L : ℝ) (R : ℕ) : 0 ≤ blockEnergy P I G y L R := by
  exact Finset.sum_nonneg (fun k _ => mul_nonneg (Nat.cast_nonneg k)
    (add_nonneg (sq_nonneg _) (sq_nonneg _)))

/-- Exact divisor expansion for a block; no boundary or cofactor is completed. -/
theorem component_response_profile (P : ℕ → Finset ℕ) (I : Finset ℕ) (c : ℕ → ℝ)
    (L : ℝ) (R : ℕ) (hR : exp L < R+1) {n : ℕ} (hn : 0 < n) :
    componentResponse P I c L n = ∑ d ∈ Finset.Icc 1 R,
      blockProfile P I c L d*(if d ∣ n then (ArithmeticFunction.moebius d : ℝ) else 0) := by
  have he (p : ℕ) := ZetaRieszCutoffMean.riesz_difference_eq_prefix R
    (sub_le_self L (log_natCast_nonneg p)) hR hn
  simp only [componentResponse,blockProfile,profile,he,Finset.mul_sum,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro p _
  ring

private theorem blockProfile_endpoint (P : ℕ → Finset ℕ) (I : Finset ℕ)
    (c : ℕ → ℝ) (L : ℝ) (R : ℕ) (hR : exp L < R+1) :
    blockProfile P I c L (R+1)=0 := by
  exact Finset.sum_eq_zero (fun i _ => profile_endpoint (P i) c _ L R hR
    (fun p _ => log_natCast_nonneg p))

/-- Rotation keeps the cofactor phase, independently of the prime endpoints. -/
theorem block_phase (P : ℕ → Finset ℕ) (I : Finset ℕ) (G : ℝ → ℝ)
    (y L v : ℝ) (n : ℕ) :
    blockResponse P I G y L v n =
      cos (y*v)*componentResponse P I (fun p => G (log p)*cos (y*log p)/(p : ℝ)) L n-
      sin (y*v)*componentResponse P I (fun p => G (log p)*sin (y*log p)/(p : ℝ)) L n := by
  simp only [blockResponse,componentResponse,Finset.mul_sum,← Finset.sum_sub_distrib,
    mul_add,cos_add]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro p _
  ring

/-- One unconditional squarefree mean controls every common prime block.
The two phase components are combined in the exact energy, with no count cap. -/
theorem exists_block_mean :
    ∃ E : ℝ, 0 < E ∧ ∀ (P : ℕ → Finset ℕ) (I S : Finset ℕ)
      (G : ℝ → ℝ) (v : ℕ → ℝ) (y L : ℝ) (X R : ℕ),
      exp L < R+1 → S ⊆ Finset.Ioc 1 X → (∀ n ∈ S, Squarefree n) →
      (∑ n ∈ S, (blockResponse P I G y L (v n) n)^2) ≤ E*X*blockEnergy P I G y L R := by
  obtain ⟨E,hE,hmean⟩ := ZetaRieszSignedCutoffEnergy.exists_divisor_profile_mean
  refine ⟨E,hE,fun P I S G v y L X R hR hS hSF => ?_⟩
  have hc (c : ℕ → ℝ) : (∑ n ∈ S, (componentResponse P I c L n)^2) ≤
      E*X*(∑ k ∈ Finset.Icc 1 R, (k : ℝ)*
        (blockProfile P I c L k-blockProfile P I c L (k+1))^2) := by
    have he n (hn : n ∈ S) := component_response_profile P I c L R hR
      (show 0 < n by have := (Finset.mem_Ioc.mp (hS hn)).1; omega)
    rw [Finset.sum_congr rfl (fun n hn => congrArg (fun x : ℝ => x^2) (he n hn))]
    exact hmean X R S _ hS hSF (blockProfile_endpoint P I c L R hR)
  let c := fun p : ℕ => G (log p)*cos (y*log p)/(p : ℝ)
  let s := fun p : ℕ => G (log p)*sin (y*log p)/(p : ℝ)
  have hrot n : (blockResponse P I G y L (v n) n)^2 ≤
      (componentResponse P I c L n)^2+(componentResponse P I s L n)^2 := by
    rw [block_phase]
    change (cos (y*v n)*componentResponse P I c L n-
      sin (y*v n)*componentResponse P I s L n)^2 ≤ _
    have ht := sin_sq_add_cos_sq (y*v n)
    have he : (cos (y*v n)*componentResponse P I c L n-
          sin (y*v n)*componentResponse P I s L n)^2+
        (sin (y*v n)*componentResponse P I c L n+
          cos (y*v n)*componentResponse P I s L n)^2 =
        (sin (y*v n)^2+cos (y*v n)^2)*
          ((componentResponse P I c L n)^2+(componentResponse P I s L n)^2) := by ring
    rw [ht,one_mul] at he
    nlinarith only [he,sq_nonneg (sin (y*v n)*componentResponse P I c L n+
      cos (y*v n)*componentResponse P I s L n)]
  have hs := Finset.sum_le_sum (fun n (_ : n ∈ S) => hrot n)
  rw [Finset.sum_add_distrib] at hs
  have hc' := hc c
  have hs' := hc s
  dsimp only [blockEnergy]
  simp only [mul_add,Finset.sum_add_distrib]
  dsimp only [c,s] at hc' hs'
  linarith

/-- All binary blocks retain their internal signed prime correlations. -/
def movingEnergy (P : ℕ → Finset ℕ) (G : ℝ → ℝ) (y L : ℝ) (R b : ℕ) : ℝ :=
  dyadicCost (fun a m => blockEnergy P (Finset.Ico a (a+m)) G y L R) b 0

private theorem movingEnergy_nonneg (P : ℕ → Finset ℕ) (G : ℝ → ℝ)
    (y L : ℝ) (R b : ℕ) : 0 ≤ movingEnergy P G y L R b :=
  dyadicCost_nonneg _ (fun _ _ => blockEnergy_nonneg _ _ _ _ _ _) _ _

/-- Cofactors may choose different prime intervals. Their moving radial,
ownership and other interval endpoints cost binary depth, not cofactor variation. -/
theorem exists_moving_mean :
    ∃ E : ℝ, 0 < E ∧ ∀ (P : ℕ → Finset ℕ) (S : Finset ℕ)
      (G : ℝ → ℝ) (v : ℕ → ℝ) (y L : ℝ) (X R b : ℕ) (lo hi : ℕ → ℕ),
      exp L < R+1 → S ⊆ Finset.Ioc 1 X → (∀ n ∈ S, Squarefree n) →
      (∀ n ∈ S, lo n ≤ hi n ∧ hi n ≤ 2^b) →
      (∑ n ∈ S, (blockResponse P (Finset.Ico (lo n) (hi n)) G y L (v n) n)^2) ≤
        4*((b+1 : ℕ) : ℝ)*E*X*movingEnergy P G y L R b := by
  obtain ⟨E,hE,hmean⟩ := exists_block_mean
  refine ⟨E,hE,fun P S G v y L X R b lo hi hR hS hSF hends => ?_⟩
  let f := fun n i => ∑ p ∈ P i, (G (log p)*cos (y*(log p+v n))/(p : ℝ))*
    (VaughanLogAverage.riesz L n-VaughanLogAverage.riesz (L-log p) n)
  have hp n (hn : n ∈ S) := interval_sq_le_dyadicCost (f n) b (lo n) (hi n)
    (hends n hn).1 (hends n hn).2
  have hs := Finset.sum_le_sum hp
  rw [← Finset.mul_sum,dyadicCost_sum] at hs
  have hm := dyadicCost_mono
    (fun a m => ∑ n ∈ S, (∑ i ∈ Finset.Ico a (a+m), f n i)^2)
    (fun a m => E*X*blockEnergy P (Finset.Ico a (a+m)) G y L R)
    (2^b) b 0 (by omega)
    (fun a m _ => hmean P (Finset.Ico a (a+m)) S G v y L X R hR hS hSF)
  rw [dyadicCost_mul] at hm
  exact hs.trans (by
    have ht := mul_le_mul_of_nonneg_left hm (by positivity : (0 : ℝ) ≤ 4*((b+1 : ℕ) : ℝ))
    simpa only [movingEnergy,mul_assoc] using ht)

/-- Exact cofactor weights have two signed bounds. No binomial cap replaces
their quadratic energy, and no prime phase is bounded term by term. -/
theorem exists_moving_weighted_bounds :
    ∃ E : ℝ, 0 < E ∧ ∀ (P : ℕ → Finset ℕ) (S : Finset ℕ)
      (G : ℝ → ℝ) (v w : ℕ → ℝ) (y L : ℝ) (X R b : ℕ) (lo hi : ℕ → ℕ),
      exp L < R+1 → S ⊆ Finset.Ioc 1 X → (∀ n ∈ S, Squarefree n) →
      (∀ n ∈ S, lo n ≤ hi n ∧ hi n ≤ 2^b) →
      let J := ∑ n ∈ S, w n*blockResponse P (Finset.Ico (lo n) (hi n)) G y L (v n) n;
      let K := sqrt ((∑ n ∈ S, (w n)^2)*
        (4*((b+1 : ℕ) : ℝ)*E*X*movingEnergy P G y L R b));
      -K ≤ J ∧ J ≤ K := by
  obtain ⟨E,hE,hmean⟩ := exists_moving_mean
  refine ⟨E,hE,fun P S G v w y L X R b lo hi hR hS hSF hends => ?_⟩
  dsimp only
  have hs := (Finset.sum_mul_sq_le_sq_mul_sq S w
    (fun n => blockResponse P (Finset.Ico (lo n) (hi n)) G y L (v n) n)).trans
      (mul_le_mul_of_nonneg_left (hmean P S G v y L X R b lo hi hR hS hSF hends)
        (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
  apply abs_le.mp
  apply (sq_le_sq₀ (abs_nonneg _) (sqrt_nonneg _)).mp
  rw [sq_abs,sq_sqrt (mul_nonneg (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    (mul_nonneg (by positivity) (movingEnergy_nonneg P G y L R b)))]
  exact hs

/-- A literal retained carrier's computable budget, using exact coefficients. -/
def retainedMovingCost (E : ℝ) (P : ℕ → Finset ℕ) (S : Finset ℕ)
    (B : ℕ → ℕ → ℝ) (N X R b : ℕ) (y L : ℝ) : ℝ :=
  (1/(L*N.factorial))*(∑ j ∈ Finset.range (N+2),
    sqrt ((∑ n ∈ S, (exp (-log n/2)*B n j/(n : ℝ))^2)*
      (4*((b+1 : ℕ) : ℝ)*E*X*movingEnergy P (factorialAmplitude j) y L R b)))

/-- The ORIGINAL residual-coefficient carrier has both signed bounds with
cofactor-dependent prime intervals and exact factorial coefficients. Eligibility
and coprimality are required only for the selected primes, not completed rows. -/
theorem exists_literal_moving_bounds :
    ∃ E : ℝ, 0 < E ∧ ∀ (A : Finset ℕ) (P : ℕ → Finset ℕ) (S : Finset ℕ)
      (N X R b : ℕ) (y L : ℝ) (lo hi : ℕ → ℕ),
      0 < L → exp L < R+1 → S ⊆ Finset.Ioc 1 X →
      (∀ n ∈ S, Squarefree n ∧ 2 ≤ n.primeFactors.card) →
      (∀ n ∈ S, lo n ≤ hi n ∧ hi n ≤ 2^b) →
      (∀ n ∈ S, ∀ i ∈ Finset.Ico (lo n) (hi n), ∀ p ∈ P i,
        p.Prime ∧ p ∈ A ∧ ¬p ∣ n) →
      ∃ B : ℕ → ℕ → ℝ,
        (∀ n ∈ S, ∀ j ≤ N+1,
          0 ≤ B n j ∧ B n j ≤ ((N+1).choose j : ℝ)*log n^(N+1-j)) ∧
        (∀ n ∈ S, ∀ i ∈ Finset.Ico (lo n) (hi n), ∀ p ∈ P i,
          (1-boundedShare A N (p*n))*log (p*n : ℕ)^(N+1) =
            ∑ j ∈ Finset.range (N+2), B n j*log p^j) ∧
        let J := (∑ n ∈ S, ∑ i ∈ Finset.Ico (lo n) (hi n), ∑ p ∈ P i,
          residualCoefficient A L N (p*n)*zetaPrimeLogKernel N (3/2+Complex.I*y) (p*n)).re;
        let K := retainedMovingCost E P S B N X R b y L;
        -K ≤ J ∧ J ≤ K := by
  obtain ⟨E,hE,hbound⟩ := exists_moving_weighted_bounds
  refine ⟨E,hE,fun A P S N X R b y L lo hi hL hR hS hSF hends hprime => ?_⟩
  have hex n (hn : n ∈ S) := exists_retained_coefficients A N (hSF n hn).1 (hSF n hn).2
  choose B hcoef hid using hex
  let B' := fun n j => if hn : n ∈ S then B n hn j else 0
  have hcoef' n (hn : n ∈ S) j (hj : j ≤ N+1) :
      0 ≤ B' n j ∧ B' n j ≤ ((N+1).choose j : ℝ)*log n^(N+1-j) := by
    simpa only [B',dif_pos hn] using hcoef n hn j hj
  have hid' n (hn : n ∈ S) i (hi : i ∈ Finset.Ico (lo n) (hi n)) p (hp : p ∈ P i) :
      (1-boundedShare A N (p*n))*log (p*n : ℕ)^(N+1) =
        ∑ j ∈ Finset.range (N+2), B' n j*log p^j := by
    have hp' := hprime n hn i hi p hp
    simpa only [B',dif_pos hn] using hid n hn p hp'.1 hp'.2.1 hp'.2.2
  refine ⟨B',hcoef',hid',?_⟩
  let w := fun j (n : ℕ) => exp (-log n/2)*B' n j/(n : ℝ)
  have hi' n (hn : n ∈ S) :
      (∑ i ∈ Finset.Ico (lo n) (hi n), ∑ p ∈ P i,
        residualCoefficient A L N (p*n)*zetaPrimeLogKernel N (3/2+Complex.I*y) (p*n)).re =
      (-1/(L*N.factorial))*(∑ j ∈ Finset.range (N+2), w j n*
        blockResponse P (Finset.Ico (lo n) (hi n)) (factorialAmplitude j) y L (log n) n) := by
    simp only [Complex.re_sum]
    have he i (hi : i ∈ Finset.Ico (lo n) (hi n)) p (hp : p ∈ P i) :=
      atom_expansion A N L y (hSF n hn).1 (hSF n hn).2
        (hprime n hn i hi p hp).1 (hprime n hn i hi p hp).2.2 (B' n) (hid' n hn i hi p hp)
    rw [Finset.sum_congr rfl (fun i hi => Finset.sum_congr rfl (he i hi))]
    simp only [← Finset.mul_sum]
    simp_rw [Finset.sum_comm (s := P _) (t := Finset.range (N+2))]
    rw [Finset.sum_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    simp only [w,blockResponse,componentResponse,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro p _
    ring
  have htotal :
      (∑ n ∈ S, ∑ i ∈ Finset.Ico (lo n) (hi n), ∑ p ∈ P i,
        residualCoefficient A L N (p*n)*zetaPrimeLogKernel N (3/2+Complex.I*y) (p*n)).re =
      (-1/(L*N.factorial))*(∑ j ∈ Finset.range (N+2), ∑ n ∈ S, w j n*
        blockResponse P (Finset.Ico (lo n) (hi n)) (factorialAmplitude j) y L (log n) n) := by
    rw [Complex.re_sum,Finset.sum_congr rfl hi',← Finset.mul_sum,Finset.sum_comm]
  have hj j : |∑ n ∈ S, w j n*
      blockResponse P (Finset.Ico (lo n) (hi n)) (factorialAmplitude j) y L (log n) n| ≤
      sqrt ((∑ n ∈ S, (w j n)^2)*
        (4*((b+1 : ℕ) : ℝ)*E*X*movingEnergy P (factorialAmplitude j) y L R b)) :=
    abs_le.mpr (hbound P S (factorialAmplitude j) (fun n => log n) (w j) y L X R b lo hi
      hR hS (fun n hn => (hSF n hn).1) hends)
  have hs := (Finset.abs_sum_le_sum_abs _ (Finset.range (N+2))).trans
    (Finset.sum_le_sum (fun j (_ : j ∈ Finset.range (N+2)) => hj j))
  apply abs_le.mp
  rw [htotal,abs_mul,abs_div,abs_neg,abs_one,
    abs_of_pos (show 0 < L*(N.factorial : ℝ) by positivity)]
  exact mul_le_mul_of_nonneg_left hs (by positivity)

/-- Disjoint prime cells give the literal selected prime union, without
repeating a prime incidence when the endpoints move. -/
theorem selected_union_sum (P : ℕ → Finset ℕ) (b lo hi : ℕ)
    (hhi : hi ≤ 2^b)
    (hdis : ∀ i < 2^b, ∀ j < 2^b, i ≠ j → Disjoint (P i) (P j))
    (f : ℕ → ℂ) :
    (∑ p ∈ (Finset.Ico lo hi).biUnion P, f p) =
      ∑ i ∈ Finset.Ico lo hi, ∑ p ∈ P i, f p := by
  exact Finset.sum_biUnion (fun i hi' j hj' hij =>
    hdis i ((Finset.mem_Ico.mp hi').2.trans_le hhi)
      j ((Finset.mem_Ico.mp hj').2.trans_le hhi) hij)

/-- The moving bound applies to the actual union of disjoint prime cells;
neither eligibility nor coprimality is imposed outside the retained interval. -/
theorem exists_literal_union_bounds :
    ∃ E : ℝ, 0 < E ∧ ∀ (A : Finset ℕ) (P : ℕ → Finset ℕ) (S : Finset ℕ)
      (N X R b : ℕ) (y L : ℝ) (lo hi : ℕ → ℕ),
      0 < L → exp L < R+1 → S ⊆ Finset.Ioc 1 X →
      (∀ n ∈ S, Squarefree n ∧ 2 ≤ n.primeFactors.card) →
      (∀ n ∈ S, lo n ≤ hi n ∧ hi n ≤ 2^b) →
      (∀ i < 2^b, ∀ j < 2^b, i ≠ j → Disjoint (P i) (P j)) →
      (∀ n ∈ S, ∀ p ∈ (Finset.Ico (lo n) (hi n)).biUnion P,
        p.Prime ∧ p ∈ A ∧ ¬p ∣ n) →
      ∃ B : ℕ → ℕ → ℝ,
        (∀ n ∈ S, ∀ j ≤ N+1,
          0 ≤ B n j ∧ B n j ≤ ((N+1).choose j : ℝ)*log n^(N+1-j)) ∧
        (∀ n ∈ S, ∀ p ∈ (Finset.Ico (lo n) (hi n)).biUnion P,
          (1-boundedShare A N (p*n))*log (p*n : ℕ)^(N+1) =
            ∑ j ∈ Finset.range (N+2), B n j*log p^j) ∧
        let J := (∑ n ∈ S, ∑ p ∈ (Finset.Ico (lo n) (hi n)).biUnion P,
          residualCoefficient A L N (p*n)*zetaPrimeLogKernel N (3/2+Complex.I*y) (p*n)).re;
        let K := retainedMovingCost E P S B N X R b y L;
        -K ≤ J ∧ J ≤ K := by
  obtain ⟨E,hE,hbound⟩ := exists_literal_moving_bounds
  refine ⟨E,hE,fun A P S N X R b y L lo hi hL hR hS hSF hends hdis hp => ?_⟩
  obtain ⟨B,hcoef,hid,hb⟩ := hbound A P S N X R b y L lo hi hL hR hS hSF hends
    (fun n hn i hi p hp' => hp n hn p (Finset.mem_biUnion.mpr ⟨i,hi,hp'⟩))
  refine ⟨B,hcoef,?_,?_⟩
  · intro n hn p hp'
    obtain ⟨i,hi,hpi⟩ := Finset.mem_biUnion.mp hp'
    exact hid n hn i hi p hpi
  · have he n (hn : n ∈ S) := selected_union_sum P b (lo n) (hi n) (hends n hn).2 hdis
      (fun p => residualCoefficient A L N (p*n)*zetaPrimeLogKernel N (3/2+Complex.I*y) (p*n))
    simpa only [Finset.sum_congr rfl he] using hb

/-- One arithmetic constant pays finite radial/count families of moving
literal prime intervals. The cost keeps each block's exact allocation energy;
there is no maximum-order or family-cardinality multiplier. -/
theorem exists_literal_moving_family_bounds :
    ∃ E : ℝ, 0 < E ∧ ∀ (I : Finset ℕ) (A S : ℕ → Finset ℕ)
      (P : ℕ → ℕ → Finset ℕ) (N X R b : ℕ → ℕ) (y L : ℕ → ℝ)
      (lo hi : ℕ → ℕ → ℕ),
      (∀ i ∈ I, 0 < L i ∧ exp (L i) < R i+1) →
      (∀ i ∈ I, S i ⊆ Finset.Ioc 1 (X i)) →
      (∀ i ∈ I, ∀ n ∈ S i, Squarefree n ∧ 2 ≤ n.primeFactors.card) →
      (∀ i ∈ I, ∀ n ∈ S i, lo i n ≤ hi i n ∧ hi i n ≤ 2^(b i)) →
      (∀ i ∈ I, ∀ n ∈ S i, ∀ t ∈ Finset.Ico (lo i n) (hi i n), ∀ p ∈ P i t,
        p.Prime ∧ p ∈ A i ∧ ¬p ∣ n) →
      ∃ B : ℕ → ℕ → ℕ → ℝ,
        (∀ i ∈ I, ∀ n ∈ S i, ∀ j ≤ N i+1,
          0 ≤ B i n j ∧ B i n j ≤ ((N i+1).choose j : ℝ)*log n^(N i+1-j)) ∧
        (∀ i ∈ I, ∀ n ∈ S i, ∀ t ∈ Finset.Ico (lo i n) (hi i n), ∀ p ∈ P i t,
          (1-boundedShare (A i) (N i) (p*n))*log (p*n : ℕ)^(N i+1) =
            ∑ j ∈ Finset.range (N i+2), B i n j*log p^j) ∧
        let J := ∑ i ∈ I, (∑ n ∈ S i, ∑ t ∈ Finset.Ico (lo i n) (hi i n), ∑ p ∈ P i t,
          residualCoefficient (A i) (L i) (N i) (p*n)*
            zetaPrimeLogKernel (N i) (3/2+Complex.I*y i) (p*n)).re;
        let K := ∑ i ∈ I, retainedMovingCost E (P i) (S i) (B i) (N i) (X i) (R i) (b i) (y i) (L i);
        -K ≤ J ∧ J ≤ K := by
  obtain ⟨E,hE,hbound⟩ := exists_literal_moving_bounds
  refine ⟨E,hE,fun I A S P N X R b y L lo hi hL hS hSF hends hp => ?_⟩
  have hex i (hI : i ∈ I) := hbound (A i) (P i) (S i) (N i) (X i) (R i) (b i) (y i) (L i)
    (lo i) (hi i) (hL i hI).1 (hL i hI).2 (hS i hI) (hSF i hI) (hends i hI) (hp i hI)
  choose B hcoef hid hb using hex
  let B' := fun i n j => if hi : i ∈ I then B i hi n j else 0
  refine ⟨B',?_,?_,?_⟩
  · intro i hi n hn j hj
    simpa only [B',dif_pos hi] using hcoef i hi n hn j hj
  · intro i hi n hn t ht p hp'
    simpa only [B',dif_pos hi] using hid i hi n hn t ht p hp'
  · let J := fun i => (∑ n ∈ S i, ∑ t ∈ Finset.Ico (lo i n) (hi i n), ∑ p ∈ P i t,
        residualCoefficient (A i) (L i) (N i) (p*n)*
          zetaPrimeLogKernel (N i) (3/2+Complex.I*y i) (p*n)).re
    have hbi i (hI : i ∈ I) :
        -retainedMovingCost E (P i) (S i) (B' i) (N i) (X i) (R i) (b i) (y i) (L i) ≤ J i ∧
        J i ≤ retainedMovingCost E (P i) (S i) (B' i) (N i) (X i) (R i) (b i) (y i) (L i) := by
      simpa only [J,B',dif_pos hI] using hb i hI
    have hl := Finset.sum_le_sum (fun i (hI : i ∈ I) => (hbi i hI).1)
    have hu := Finset.sum_le_sum (fun i (hI : i ∈ I) => (hbi i hI).2)
    rw [Finset.sum_neg_distrib] at hl
    exact ⟨hl,hu⟩

/-- Unique largest-prime ownership transports the estimate to an actual
finite set of integer labels. No selected label or prime incidence is spent
twice. This does not assert that the selected labels exhaust the core. -/
theorem exists_literal_owned_bounds :
    ∃ E : ℝ, 0 < E ∧ ∀ (A : Finset ℕ) (P : ℕ → Finset ℕ) (S : Finset ℕ)
      (N X R b : ℕ) (y L : ℝ) (lo hi : ℕ → ℕ),
      0 < L → exp L < R+1 → S ⊆ Finset.Ioc 1 X →
      (∀ n ∈ S, Squarefree n ∧ 2 ≤ n.primeFactors.card) →
      (∀ n ∈ S, lo n ≤ hi n ∧ hi n ≤ 2^b) →
      (∀ i < 2^b, ∀ j < 2^b, i ≠ j → Disjoint (P i) (P j)) →
      let Q := fun n => (Finset.Ico (lo n) (hi n)).biUnion P;
      (∀ n ∈ S, ∀ p ∈ Q n,
        p.Prime ∧ p ∈ A ∧ ∀ r : ℕ, r.Prime → r ∣ n → r < p) →
      ∃ B : ℕ → ℕ → ℝ,
        (∀ n ∈ S, ∀ j ≤ N+1,
          0 ≤ B n j ∧ B n j ≤ ((N+1).choose j : ℝ)*log n^(N+1-j)) ∧
        (∀ n ∈ S, ∀ p ∈ Q n,
          (1-boundedShare A N (p*n))*log (p*n : ℕ)^(N+1) =
            ∑ j ∈ Finset.range (N+2), B n j*log p^j) ∧
        let labels := S.biUnion (fun n => (Q n).image (fun p => n*p));
        let J := (∑ n ∈ labels,
          residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re;
        let K := retainedMovingCost E P S B N X R b y L;
        -K ≤ J ∧ J ≤ K := by
  obtain ⟨E,hE,hbound⟩ := exists_literal_union_bounds
  refine ⟨E,hE,fun A P S N X R b y L lo hi hL hR hS hSF hends hdis hp => ?_⟩
  dsimp only at hp ⊢
  obtain ⟨B,hcoef,hid,hb⟩ := hbound A P S N X R b y L lo hi hL hR hS hSF hends hdis
    (fun n hn p hp' => ⟨(hp n hn p hp').1,(hp n hn p hp').2.1,
      fun hpn => (lt_irrefl p) ((hp n hn p hp').2.2 p (hp n hn p hp').1 hpn)⟩)
  refine ⟨B,hcoef,hid,?_⟩
  have he := ZetaRieszCoupledWindow.sum_owned_products S
    (fun n => (Finset.Ico (lo n) (hi n)).biUnion P)
    (fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n)
    (fun n hn => (hSF n hn).1.ne_zero)
    (fun n hn p hp' => ⟨(hp n hn p hp').1,(hp n hn p hp').2.2⟩)
  rw [he]
  simpa only [Nat.mul_comm] using hb

end RiemannGaussian.ZetaRieszMovingPrimeIntervals
