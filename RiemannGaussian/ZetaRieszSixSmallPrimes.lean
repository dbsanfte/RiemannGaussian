/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszSixSmallHinges
import RiemannGaussian.ZetaRieszSixPrimeSecondReflection

/-! # Both signed costs for the six-prime sector with no reflected-large prime

The pair and triple divisor hinges are estimated together. Their cancellation
lowers the original negative coefficient allowance from three least-prime
units to one, retaining the other signed allowance and the actual phase.
The estimates are applied only to literal unpaid core subsets.
-/

namespace RiemannGaussian.ZetaRieszSixSmallPrimes
noncomputable section
open scoped BigOperators Classical
open ZetaRieszContinuumCascade ZetaRieszJointAllocation ZetaRieszOneSidedArithmetic
open ZetaRieszReflectedPrimeBounds

private theorem kernel_image {ι κ : Type*} [DecidableEq κ] (S : Finset ι)
    (f : ι → κ) (hf : Function.Injective f) (x : κ → ℝ) (D : ℝ) :
    kernel (S.image f) x D = kernel S (x ∘ f) D := by
  unfold kernel
  rw [Finset.powerset_image,Finset.sum_image
    (fun _ _ _ _ he => Finset.image_injective hf he)]
  apply Finset.sum_congr rfl
  intro A _
  rw [Finset.card_image_of_injective _ hf,Finset.sum_image (fun _ _ _ _ h => hf h)]
  rfl

/-- The literal six-prime Möbius response costs at most its actual least
prime log on the all-small side of a lower-third reflected cutoff. -/
theorem riesz_le_minFac {n : ℕ} (hs : Squarefree n)
    (hc : n.primeFactors.card = 6) {D : ℝ}
    (hsmall : ∀ p ∈ n.primeFactors, Real.log p ≤ D)
    (hthird : 3*D ≤ Real.log n) :
    VaughanLogAverage.riesz D n ≤ Real.log n.minFac := by
  let v := n.primeFactors.orderEmbOfFin hc
  have hv (i : Fin 6) : v i ∈ n.primeFactors := n.primeFactors.orderEmbOfFin_mem hc i
  have he := n.primeFactors.image_orderEmbOfFin_univ hc
  have hlog : Real.log n = ∑ i : Fin 6, Real.log (v i) := by
    rw [CoprimeEulerPhase.squarefree_log_eq_prime_sum hs,← he,
      Finset.sum_image (fun _ _ _ _ h => v.injective h)]
  have hn1 : n ≠ 1 := by intro h; simp [h] at hc
  have hm : v 0 = n.minFac := by
    apply le_antisymm
    · have hmin := (Nat.minFac_prime hn1).mem_primeFactors (Nat.minFac_dvd n) hs.ne_zero
      rw [← he] at hmin
      obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hmin
      rw [← hi]
      exact v.monotone (Fin.zero_le _)
    · exact Nat.minFac_le_of_dvd (Nat.prime_of_mem_primeFactors (hv 0)).two_le
        (Nat.dvd_of_mem_primeFactors (hv 0))
  have hmono {i j : Fin 6} (hij : i ≤ j) : Real.log (v i) ≤ Real.log (v j) :=
    Real.log_le_log (by exact_mod_cast (Nat.prime_of_mem_primeFactors (hv i)).pos)
      (by exact_mod_cast v.monotone hij)
  have hk : VaughanLogAverage.riesz D n =
      kernel (Finset.univ : Finset (Fin 6)) (fun i => Real.log (v i)) D := by
    rw [← kernel_primeFactors hs,← he,kernel_image _ _ v.injective]
    rfl
  have hx : (fun i : Fin 6 => Real.log (v i)) =
      ![Real.log (v 0),Real.log (v 1),Real.log (v 2),Real.log (v 3),
        Real.log (v 4),Real.log (v 5)] := by
    funext i
    fin_cases i <;> rfl
  rw [hk,hx,← hm]
  exact ZetaRieszSixSmallHinges.kernel_six_le_first (Real.log_natCast_nonneg _)
    (hmono (by decide)) (hmono (by decide)) (hmono (by decide))
    (hmono (by decide)) (hmono (by decide)) (hsmall _ (hv 5))
    (by simpa only [hlog,Fin.sum_univ_six] using hthird)

/-- Reflection gives the interval [-1,4] in original least-prime units,
improving the former [-3,4] without altering any arithmetic label. -/
theorem coefficient_bounds {L : ℝ} (hL : 0 < L) {n : ℕ}
    (hs : Squarefree n) (hc : n.primeFactors.card = 6)
    (hsmall : ∀ p ∈ n.primeFactors, Real.log p ≤ Real.log n-L)
    (hcut : 2*Real.log n ≤ 3*L) :
    -(Real.log n/L*Real.log n.minFac) ≤
        (SquarefreeVaughanLogSource.coefficient L n).re ∧
      (SquarefreeVaughanLogSource.coefficient L n).re ≤
        4*(Real.log n/L*Real.log n.minFac) := by
  have hn1 : n ≠ 1 := by intro h; simp [h] at hc
  have hnp : ¬ n.Prime := by intro h; simp [h.primeFactors] at hc
  have hr := VaughanLogAverage.riesz_reflection L hs hn1 hnp
  rw [ZetaRieszReflectedLinear.moebius_eq_primeCount hs,hc] at hr
  norm_num at hr
  have hh := riesz_le_minFac hs hc hsmall (by linarith : 3*(Real.log n-L) ≤ Real.log n)
  rw [hr] at hh
  have hb := mul_le_mul_of_nonneg_left hh
    (div_nonneg (Real.log_natCast_nonneg n) hL.le)
  refine ⟨?_,?_⟩
  · simp only [SquarefreeVaughanLogSource.coefficient,if_pos (And.intro hs hnp),Complex.ofReal_re]
    rw [show -Real.log n*VaughanLogAverage.riesz L n/L =
      -(Real.log n/L)*VaughanLogAverage.riesz L n by ring]
    nlinarith only [hb]
  · have hu := (ZetaRieszSignedSperner.coefficient_six_bounds hL hs hc).2
    nlinarith only [hu]

/-- One original least-prime coefficient unit, with no replacement by
an average logarithm. -/
def unit (L : ℝ) (n : ℕ) : ℝ := Real.log n/L*Real.log n.minFac

/-- The six-small-prime floor pays one positive-phase unit and four
negative-phase units. -/
def smallFloorCost (L y : ℝ) (n : ℕ) : ℝ :=
  unit L n*(max (Real.cos (y*Real.log n)) 0+4*max (-Real.cos (y*Real.log n)) 0)

/-- The upper comparison exchanges the same two phase orientations. -/
def smallCeilingCost (L y : ℝ) (n : ℕ) : ℝ :=
  unit L n*(4*max (Real.cos (y*Real.log n)) 0+max (-Real.cos (y*Real.log n)) 0)

/-- The improvement is exactly two least-prime units on the relevant
phase side of each whole comparison, relative to the existing [-3,4] bound. -/
theorem small_cost_savings (L y : ℝ) (n : ℕ) :
    unit L n*(3*max (Real.cos (y*Real.log n)) 0+4*max (-Real.cos (y*Real.log n)) 0)-
        smallFloorCost L y n = 2*unit L n*max (Real.cos (y*Real.log n)) 0 ∧
    unit L n*(4*max (Real.cos (y*Real.log n)) 0+3*max (-Real.cos (y*Real.log n)) 0)-
        smallCeilingCost L y n = 2*unit L n*max (-Real.cos (y*Real.log n)) 0 := by
  constructor <;> dsimp only [smallFloorCost,smallCeilingCost] <;> ring

/-- The new small-sector charge is nonnegative in both orientations. -/
theorem small_costs_nonneg {L : ℝ} (hL : 0 < L) (y : ℝ) (n : ℕ) :
    0 ≤ smallFloorCost L y n ∧ 0 ≤ smallCeilingCost L y n := by
  constructor <;> dsimp only [smallFloorCost,smallCeilingCost,unit] <;>
    positivity [Real.log_natCast_nonneg n,Real.log_natCast_nonneg n.minFac]

/-- The independent small-sector interval acts on the actual residual
atom and keeps every favorable observation. -/
theorem residual_small_retained_bounds (A : Finset ℕ) {L : ℝ} (hL : 0 < L)
    (y : ℝ) (N : ℕ) {n : ℕ} (hs : Squarefree n) (hc : n.primeFactors.card = 6)
    (hsmall : ∀ p ∈ n.primeFactors, Real.log p ≤ Real.log n-L)
    (hcut : 2*Real.log n ≤ 3*L) :
    let v := (residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re
    max v 0-weight A N n*smallFloorCost L y n ≤ v ∧
      v ≤ min v 0+weight A N n*smallCeilingCost L y n := by
  have hb := coefficient_bounds hL hs hc hsmall hcut
  change -unit L n ≤ (SquarefreeVaughanLogSource.coefficient L n).re ∧
    (SquarefreeVaughanLogSource.coefficient L n).re ≤ 4*unit L n at hb
  have hw := weight_nonneg A N n
  have hcost := small_costs_nonneg hL y n
  have raw : -(weight A N n*smallFloorCost L y n) ≤
      (residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re ∧
      (residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re ≤
        weight A N n*smallCeilingCost L y n := by
    rw [re_residual_atom]
    suffices hh : -smallFloorCost L y n ≤
        (SquarefreeVaughanLogSource.coefficient L n).re*Real.cos (y*Real.log n) ∧
        (SquarefreeVaughanLogSource.coefficient L n).re*Real.cos (y*Real.log n) ≤
          smallCeilingCost L y n by
      exact ⟨by simpa only [mul_neg,mul_assoc] using mul_le_mul_of_nonneg_left hh.1 hw,
        by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hh.2 hw⟩
    by_cases hp : 0 ≤ Real.cos (y*Real.log n)
    · have hl := mul_le_mul_of_nonneg_right hb.1 hp
      have hu := mul_le_mul_of_nonneg_right hb.2 hp
      simp only [smallFloorCost,smallCeilingCost,max_eq_left hp,
        max_eq_right (neg_nonpos.mpr hp),mul_zero,add_zero]
      constructor <;> nlinarith only [hl,hu]
    · have hp' := le_of_not_ge hp
      have hl := mul_le_mul_of_nonpos_right hb.2 hp'
      have hu := mul_le_mul_of_nonpos_right hb.1 hp'
      simp only [smallFloorCost,smallCeilingCost,max_eq_right hp',
        max_eq_left (neg_nonneg.mpr hp'),mul_zero,zero_add]
      constructor <;> nlinarith only [hl,hu]
  dsimp only
  have hln := mul_nonneg hw hcost.1
  have hun := mul_nonneg hw hcost.2
  by_cases hv : 0 ≤ (residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re
  · rw [max_eq_left hv,min_eq_right hv]
    constructor <;> linarith only [raw.2,hln]
  · have hv' := le_of_not_ge hv
    rw [max_eq_right hv',min_eq_left hv']
    constructor <;> linarith only [raw.1,hun]

/-- The new floor charge includes the existing reflected-large sector
unchanged, so all six-prime labels receive one compatible signed estimate. -/
def floorCost (L y : ℝ) (n : ℕ) : ℝ :=
  if 1 ≤ (outerPrimes (Real.log n-L) n).card then
    ZetaRieszSixPrimeSecondReflection.floorCost L y n else smallFloorCost L y n

/-- The corresponding whole ceiling retains the earlier second reflection. -/
def ceilingCost (L y : ℝ) (n : ℕ) : ℝ :=
  if 1 ≤ (outerPrimes (Real.log n-L) n).card then
    ZetaRieszSixPrimeSecondReflection.ceilingCost L y n else smallCeilingCost L y n

/-- Every actual six-prime atom receives both signed comparisons; its
outer-prime geometry determines which already-paid estimate applies. -/
theorem residual_retained_bounds (A : Finset ℕ) {L : ℝ} (hL : 0 < L)
    (y : ℝ) (N : ℕ) {n : ℕ} (hs : Squarefree n) (hc : n.primeFactors.card = 6)
    (hD : 2*Real.log n ≤ 7*(Real.log n-L)) (hcut : 2*Real.log n ≤ 3*L) :
    let v := (residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re
    max v 0-weight A N n*floorCost L y n ≤ v ∧
      v ≤ min v 0+weight A N n*ceilingCost L y n := by
  by_cases ho : 1 ≤ (outerPrimes (Real.log n-L) n).card
  · simpa only [floorCost,ceilingCost,if_pos ho] using
      ZetaRieszSixPrimeSecondReflection.residual_retained_bounds A hL y N hs hc hD ho
  · have hsmall (p : ℕ) (hp : p ∈ n.primeFactors) : Real.log p ≤ Real.log n-L := by
      by_contra hpD
      have hm : p ∈ outerPrimes (Real.log n-L) n :=
        Finset.mem_filter.mpr ⟨hp,(lt_of_not_ge hpD).le⟩
      have hh := Finset.card_pos.mpr (show (outerPrimes (Real.log n-L) n).Nonempty from ⟨p,hm⟩)
      omega
    simpa only [floorCost,ceilingCost,if_neg ho] using
      residual_small_retained_bounds A hL y N hs hc hsmall hcut

open Filter Topology ZetaRieszParityPacket ZetaRieszAnnulusJoint

/-- Both independent signed inequalities apply to every exact unpaid
subset of the original core. The previously untreated outer-count-zero
sector is included; no favorable term or complementary label is deleted. -/
theorem eventually_core_subset_bounds {u : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) :
    ∀ᶠ N : ℕ in atTop, ∀ (K : ℕ) (y : ℝ) (S : Finset ℕ), S ⊆ coreBand u N K →
      let A := intermediatePrimes u N
      let L := SquarefreeVaughanLogSource.length u N
      let f := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
      u^(N+1)*(∑ n ∈ S, if Squarefree n ∧ n.primeFactors.card = 6 then
        max (f n).re 0-weight A N n*floorCost L y n else (f n).re) ≤
        ((u : ℂ)^(N+1)*∑ n ∈ S, f n).re ∧
      ((u : ℂ)^(N+1)*∑ n ∈ S, f n).re ≤
        u^(N+1)*(∑ n ∈ S, if Squarefree n ∧ n.primeFactors.card = 6 then
          min (f n).re 0+weight A N n*ceilingCost L y n else (f n).re) := by
  filter_upwards [ZetaRieszSixPrimeGeometry.eventually_core_cutoff_thirds hu hU,
    eventually_ge_atTop (2 : ℕ)] with N hcut hN K y S hS
  let A := intermediatePrimes u N
  let L := SquarefreeVaughanLogSource.length u N
  let f := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
  have hp (n : ℕ) (hn : n ∈ S) (hs : Squarefree n ∧ n.primeFactors.card = 6) :=
    residual_retained_bounds A (SquarefreeVaughanLogSource.length_pos u N) y N hs.1 hs.2
      (ZetaRieszSevenPrimeReflection.core_cutoff_two_sevenths hu.le hN (hS hn)).le
      (hcut K n (hS hn))
  have hlo := Finset.sum_le_sum (s := S) (f := fun n : ℕ =>
    if Squarefree n ∧ n.primeFactors.card = 6 then
      max (f n).re 0-weight A N n*floorCost L y n else (f n).re) (g := fun n => (f n).re)
    (fun n hn => by split_ifs with hs; exact (hp n hn hs).1; rfl)
  have hhi := Finset.sum_le_sum (s := S) (f := fun n => (f n).re) (g := fun n : ℕ =>
    if Squarefree n ∧ n.primeFactors.card = 6 then
      min (f n).re 0+weight A N n*ceilingCost L y n else (f n).re)
    (fun n hn => by split_ifs with hs; exact (hp n hn hs).2; rfl)
  rw [← Complex.re_sum] at hlo hhi
  have hulo := mul_le_mul_of_nonneg_left hlo (pow_nonneg (by linarith : 0 ≤ u) (N+1))
  have huhi := mul_le_mul_of_nonneg_left hhi (pow_nonneg (by linarith : 0 ≤ u) (N+1))
  dsimp only
  simpa only [f,A,L,← Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,
    Complex.ofReal_im,zero_mul,sub_zero] using And.intro hulo huhi

end
end RiemannGaussian.ZetaRieszSixSmallPrimes
