/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszCeilingFejerCluster

/-!
# Signed credits across competing modes and logged orders

Keep the exact eight-order competing profile, including its endpoints and
actual multiplicities. A coherent stride mode supplies at least 42 units
of signed credit; an arbitrary other mode costs at most 9. Thus the SAME
native ceiling is paid in balanced clusters without an extra sparsity
cap, rather than only total competing mass <= 4. The full all-height
fixed-strip ceiling remains open outside these explicit geometries.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open Complex Filter Topology
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszCeilingFejerBalance
open ZetaRieszCeilingMomentIsolation ZetaRieszCeilingSignedCluster
open ZetaRieszCeilingFejerCluster

/-- The WHOLE eight-order excess is positive in this tube, even when
individual other logged powers oppose the selected source. -/
theorem fejer_credit_lower {w : ℂ} (hw : ‖w‖ <= 1) (ht : ‖w-1‖ <= 1/8) :
    42 <= fejerPolynomial w 8-9 := by
  have hp (j : ℕ) : 1-((j+1 : ℕ) : ℝ)/8 <= (w^(j+1)).re := by
    have hr := Complex.re_le_norm (1-w^(j+1))
    rw [Complex.sub_re, Complex.one_re, norm_sub_rev] at hr
    have hn := (norm_pow_sub_one_le hw (j+1)).trans
      (mul_le_mul_of_nonneg_left ht (by positivity : (0 : ℝ) <= (j+1 : ℕ)))
    linarith only [hr, hn]
  have hs : (∑ j ∈ Finset.range 8, (8-(j : ℝ))*(1-((j+1 : ℕ) : ℝ)/8)) <=
      ∑ j ∈ Finset.range 8, (8-(j : ℝ))*(w^(j+1)).re := by
    apply Finset.sum_le_sum
    intro j hj
    have hjR : (j : ℝ) <= 8 := by exact_mod_cast (Finset.mem_range.mp hj).le
    exact mul_le_mul_of_nonneg_left (hp j) (by linarith only [hjR])
  have hc : (∑ j ∈ Finset.range 8, (8-(j : ℝ))*(1-((j+1 : ℕ) : ℝ)/8)) = 21 := by
    norm_num [Finset.sum_range_succ]
  rw [hc] at hs
  unfold fejerPolynomial
  norm_num only [Nat.cast_ofNat]
  linarith only [hs]

/-- No sign is imposed on individual opposing powers. Only the exact
square identity bounds their WHOLE profile from below. -/
theorem fejer_excess_lower {w : ℂ} (hw : ‖w‖ <= 1) :
    -9 <= fejerPolynomial w 8-9 := by
  have h := fejerPolynomial_nonneg hw 8
  linarith only [h]

/-- The original selected-erased canonical genuine local divisor. -/
def competingSupport (rho : NontrivialZetaZero) (hrho : 1/2 < rho.1.re) : Finset ℂ :=
  (adaptiveZetaZeroSupport (zetaRightHalfDiscParameter rho hrho) rho.1.im).erase
    (-((3/2-rho.1.re : ℝ) : ℂ))

/-- The exact mode node, with its original exposed source normalization. -/
def normalizedNode (rho : NontrivialZetaZero) (z : ℂ) : ℂ :=
  ((3/2-rho.1.re : ℝ) : ℂ)*(-z⁻¹)

/-- Coherence is imposed on the common STRIDE, not on a single moment
or an unwrapped phase. This permits opposing individual logged powers. -/
def coherentModes (rho : NontrivialZetaZero) (hrho : 1/2 < rho.1.re) : Finset ℂ :=
  (competingSupport rho hrho).filter (fun z => ‖normalizedNode rho z^1100-1‖ <= 1/8)

/-- Exact complementary population; no competing mode is omitted. -/
def otherModes (rho : NontrivialZetaZero) (hrho : 1/2 < rho.1.re) : Finset ℂ :=
  (competingSupport rho hrho).filter (fun z => ¬‖normalizedNode rho z^1100-1‖ <= 1/8)

/-- Multiplicity-weighted coherent mass, counted once. -/
def coherentMass (rho : NontrivialZetaZero) (hrho : 1/2 < rho.1.re) : ℝ :=
  ∑ z ∈ coherentModes rho hrho, modeCoefficient (zetaRightHalfDiscParameter rho hrho) rho.1.im z

/-- Multiplicity-weighted remaining mass, counted once. -/
def otherMass (rho : NontrivialZetaZero) (hrho : 1/2 < rho.1.re) : ℝ :=
  ∑ z ∈ otherModes rho hrho, modeCoefficient (zetaRightHalfDiscParameter rho hrho) rho.1.im z

/-- Natural analytic multiplicity on ANY subpopulation of the genuine
support. This is not the number of distinct zero positions. -/
def naturalMass (rho : NontrivialZetaZero) (hrho : 1/2 < rho.1.re) (S : Finset ℂ) : ℕ :=
  ∑ z ∈ S, (MeromorphicOn.divisor (localZetaPoleRemoved rho.1.im)
    (Metric.ball 0 (adaptiveZetaCanonicalRadius (zetaRightHalfDiscParameter rho hrho)
      rho.1.im)) z).toNat

/-- Every selected subpopulation retains actual multiplicity exactly. -/
theorem sum_coefficients_eq_naturalMass (rho : NontrivialZetaZero)
    (hrho : 1/2 < rho.1.re) (S : Finset ℂ) (hS : S ⊆ competingSupport rho hrho) :
    (∑ z ∈ S, modeCoefficient (zetaRightHalfDiscParameter rho hrho) rho.1.im z) =
      (naturalMass rho hrho S : ℝ) := by
  unfold naturalMass
  rw [Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro z hz
  have hc := coefficient_nonneg (zetaRightHalfDiscParameter rho hrho) rho.1.im
    (Finset.mem_erase.mp (hS hz)).2
  change (0 : ℝ) <= ((MeromorphicOn.divisor (localZetaPoleRemoved rho.1.im)
    (Metric.ball 0 (adaptiveZetaCanonicalRadius (zetaRightHalfDiscParameter rho hrho)
      rho.1.im)) z : ℤ) : ℝ) at hc
  have hi : (0 : ℤ) <= MeromorphicOn.divisor (localZetaPoleRemoved rho.1.im)
    (Metric.ball 0 (adaptiveZetaCanonicalRadius (zetaRightHalfDiscParameter rho hrho)
      rho.1.im)) z := by exact_mod_cast hc
  have ht := congrArg (fun a : ℤ => (a : ℝ)) (Int.toNat_of_nonneg hi)
  simpa only [Int.cast_natCast, modeCoefficient] using ht.symm

/-- Coherent mass is an integer multiplicity total. -/
theorem coherentMass_eq_nat (rho : NontrivialZetaZero) (hrho : 1/2 < rho.1.re) :
    coherentMass rho hrho = (naturalMass rho hrho (coherentModes rho hrho) : ℝ) :=
  sum_coefficients_eq_naturalMass rho hrho _ (Finset.filter_subset _ _)

/-- Every complementary mode is retained at its exact multiplicity. -/
theorem otherMass_eq_nat (rho : NontrivialZetaZero) (hrho : 1/2 < rho.1.re) :
    otherMass rho hrho = (naturalMass rho hrho (otherModes rho hrho) : ℝ) :=
  sum_coefficients_eq_naturalMass rho hrho _ (Finset.filter_subset _ _)

/-- Exact completeness of the coherent/complementary signed ledger.
The split partitions multiplicity, never discards an opposing mode. -/
theorem mass_partition (rho : NontrivialZetaZero) (hrho : 1/2 < rho.1.re) :
    coherentMass rho hrho+otherMass rho hrho = competingMass rho hrho := by
  unfold coherentMass otherMass coherentModes otherModes
  exact Finset.sum_filter_add_sum_filter_not _ _ _

/-- The complete natural multiplicity total is partitioned once. -/
theorem natural_mass_partition (rho : NontrivialZetaZero) (hrho : 1/2 < rho.1.re) :
    naturalMass rho hrho (coherentModes rho hrho)+
      naturalMass rho hrho (otherModes rho hrho) = competingNaturalMass rho hrho := by
  have h := mass_partition rho hrho
  rw [coherentMass_eq_nat, otherMass_eq_nat, competingMass_eq_nat] at h
  exact_mod_cast h

/-- The signed eight-order profile is a constraint on the actual divisor,
not a new arithmetic carrier or a model replacing complete primes. -/
def signedProfile (rho : NontrivialZetaZero) (hrho : 1/2 < rho.1.re) : ℝ :=
  2*∑ j ∈ Finset.range 8, (8-(j : ℝ))*(competingMoment rho hrho (1100*(j+1)-1)).re

/-- Join BOTH indices before taking a real part or bound. The baseline
subtraction is exact; no selected-erased zero receives a second debit. -/
theorem profile_eq_modes (rho : NontrivialZetaZero) (hrho : 1/2 < rho.1.re) :
    signedProfile rho hrho = ∑ z ∈ competingSupport rho hrho,
      modeCoefficient (zetaRightHalfDiscParameter rho hrho) rho.1.im z*
        (fejerPolynomial (normalizedNode rho z^1100) 8-9) := by
  have ht := weighted_fejer_eq (competingSupport rho hrho)
    (modeCoefficient (zetaRightHalfDiscParameter rho hrho) rho.1.im)
    (normalizedNode rho) 8 1100
  have he (j : ℕ) : 1100*(j+1)-1+1 = 1100*(j+1) := by omega
  norm_num only at ht
  have h : (∑ z ∈ competingSupport rho hrho,
      modeCoefficient (zetaRightHalfDiscParameter rho hrho) rho.1.im z*
        fejerPolynomial (normalizedNode rho z^1100) 8) =
      9*competingMass rho hrho+signedProfile rho hrho := by
    simpa only [competingSupport, normalizedNode, competingMass, competingMoment,
      signedProfile, he] using ht
  simp only [mul_sub, Finset.sum_sub_distrib]
  have hm : (∑ z ∈ competingSupport rho hrho,
      modeCoefficient (zetaRightHalfDiscParameter rho hrho) rho.1.im z) =
      competingMass rho hrho := rfl
  rw [<-Finset.sum_mul, hm, h]
  ring

/-- The complete arithmetic test retains the exact signed profile.
It needs no sparse-mass or constructive-phase assumption. -/
theorem multiplicity_profile_lt (rho : NontrivialZetaZero)
    (hnear : 1-rho.1.re <= 1/20000)
    (hheight : localZetaLogHeight rho.1.im <= 10^150) :
    72*(analyticZetaZeroMultiplicity rho : ℝ)+
      signedProfile rho (show 1/2 < rho.1.re by linarith) < 107 := by
  have hrho : 1/2 < rho.1.re := by linarith
  let u := 3/2-rho.1.re
  let m : ℝ := analyticZetaZeroMultiplicity rho
  have hu : 1/2 <= u := by dsimp [u]; linarith [rho.re_lt_one]
  have hU : u <= 10001/20000 := by dsimp [u]; linarith only [hnear]
  have htest (j : ℕ) (hj : j ∈ Finset.range 8) :
      (8-(j : ℝ))*(m+(competingMoment rho hrho (1100*(j+1)-1)).re) <=
      (8-(j : ℝ))*
        ((2*u)^(1100*(j+1))+u^(1100*(j+1))+
          160*u*(localZetaLogHeight rho.1.im+localZetaLogHeight 0)*
            ((1100*(j+1) : ℕ) : ℝ)*(10*u/7)^(1100*(j+1)-1)+
          (localZetaLogHeight rho.1.im+11)*(4*u/3)^(1100*(j+1))) := by
    have hjR : (j : ℝ) <= 8 := by exact_mod_cast (Finset.mem_range.mp hj).le
    apply mul_le_mul_of_nonneg_left _ (by linarith only [hjR])
    have he : 1100*(j+1)-1+1 = 1100*(j+1) := by omega
    have heR : (((1100*(j+1)-1 : ℕ) : ℝ)+1) = ((1100*(j+1) : ℕ) : ℝ) := by
      exact_mod_cast he
    simpa only [he, heR, m, u] using
      multiplicity_add_competing_re_le rho hrho (1100*(j+1)-1)
  have ht := mul_le_mul_of_nonneg_left (Finset.sum_le_sum htest) (by norm_num : (0 : ℝ) <= 2)
  have hc := actual_fejer_cost_lt hu hU hheight
  have he : 2*(∑ j ∈ Finset.range 8,
      (8-(j : ℝ))*(m+(competingMoment rho hrho (1100*(j+1)-1)).re)) =
      72*m+signedProfile rho hrho := by
    simp_rw [mul_add, Finset.sum_add_distrib]
    rw [<-Finset.sum_mul]
    have hw : (∑ j ∈ Finset.range 8, (8-(j : ℝ))) = 36 := by norm_num [Finset.sum_range_succ]
    rw [hw]
    unfold signedProfile
    ring_nf
  rw [he] at ht
  exact ht.trans_lt hc

/-- A surviving multiple candidate forces a genuine negative JOINT
eight-order profile, not merely a large competing count. -/
theorem multiple_forces_profile_neg (rho : NontrivialZetaZero)
    (hnear : 1-rho.1.re <= 1/20000)
    (hheight : localZetaLogHeight rho.1.im <= 10^150)
    (hm : 2 <= analyticZetaZeroMultiplicity rho) :
    signedProfile rho (show 1/2 < rho.1.re by linarith) < -37 := by
  have ht := multiplicity_profile_lt rho hnear hheight
  have hmR : (2 : ℝ) <= analyticZetaZeroMultiplicity rho := by exact_mod_cast hm
  linarith only [ht, hmR]

/-- An independent JOINT profile floor is enough, without any ceiling
on total competing multiplicity. This premise is explicit. -/
theorem simple_of_profile_floor (rho : NontrivialZetaZero)
    (hnear : 1-rho.1.re <= 1/20000)
    (hheight : localZetaLogHeight rho.1.im <= 10^150)
    (hprofile : -36 <= signedProfile rho (show 1/2 < rho.1.re by linarith)) :
    analyticZetaZeroMultiplicity rho = 1 := by
  have hp := analyticZetaZeroMultiplicity_positive rho
  by_contra h
  have hm : 2 <= analyticZetaZeroMultiplicity rho := by omega
  have ht := multiple_forces_profile_neg rho hnear hheight hm
  linarith only [ht, hprofile]

/-- Concrete signed savings across the entire finite ACTUAL divisor:
each coherent unit pays at least 42, each other unit costs at most 9.
Do not replace the coherent credit by a positive count allowance. -/
theorem profile_ge_balance (rho : NontrivialZetaZero) (hrho : 1/2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3/2-rho.1.re < ‖(3/2+I*(rho.1.im : ℂ))-tau.1‖) :
    42*coherentMass rho hrho-9*otherMass rho hrho <= signedProfile rho hrho := by
  rw [profile_eq_modes]
  let c := modeCoefficient (zetaRightHalfDiscParameter rho hrho) rho.1.im
  let f := fun z => c z*(fejerPolynomial (normalizedNode rho z^1100) 8-9)
  have hc : ∀ z ∈ competingSupport rho hrho, 0 <= c z := fun z hz =>
    coefficient_nonneg _ _ (Finset.mem_erase.mp hz).2
  have hn (z : ℂ) (hz : z ∈ competingSupport rho hrho) :
      ‖normalizedNode rho z^1100‖ <= 1 := by
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) (competing_node_norm_le rho hrho hexposed hz)
  have hgood : 42*coherentMass rho hrho <= ∑ z ∈ coherentModes rho hrho, f z := by
    unfold coherentMass
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro z hz
    have hzS := (Finset.mem_filter.mp hz).1
    have ht := fejer_credit_lower (hn z hzS) (Finset.mem_filter.mp hz).2
    simpa only [f, c, mul_comm] using mul_le_mul_of_nonneg_left ht (hc z hzS)
  have hother : -9*otherMass rho hrho <= ∑ z ∈ otherModes rho hrho, f z := by
    unfold otherMass
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro z hz
    have hzS := (Finset.mem_filter.mp hz).1
    have ht := fejer_excess_lower (hn z hzS)
    simpa only [f, c, mul_comm] using mul_le_mul_of_nonneg_left ht (hc z hzS)
  have he : (∑ z ∈ coherentModes rho hrho, f z)+
      (∑ z ∈ otherModes rho hrho, f z) = ∑ z ∈ competingSupport rho hrho, f z := by
    unfold coherentModes otherModes
    exact Finset.sum_filter_add_sum_filter_not _ _ _
  simpa only [sub_eq_add_neg, neg_mul, f, c] using (add_le_add hgood hother).trans_eq he

/-- The whole selected/competing inequality now uses signed credits.
There is no independent upper bound on the total divisor mass. -/
theorem multiplicity_balance_lt (rho : NontrivialZetaZero)
    (hnear : 1-rho.1.re <= 1/20000)
    (hheight : localZetaLogHeight rho.1.im <= 10^150)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3/2-rho.1.re < ‖(3/2+I*(rho.1.im : ℂ))-tau.1‖) :
    72*(analyticZetaZeroMultiplicity rho : ℝ)+
      42*coherentMass rho (show 1/2 < rho.1.re by linarith)-
        9*otherMass rho (show 1/2 < rho.1.re by linarith) < 107 := by
  have ht := multiplicity_profile_lt rho hnear hheight
  have hb := profile_ge_balance rho (show 1/2 < rho.1.re by linarith) hexposed
  linarith only [ht, hb]

/-- This integer balance pays dense clusters without an extra sparsity
cap. The geometry premise is explicit and is not inferred from exposure. -/
theorem simple_of_natural_balance (rho : NontrivialZetaZero)
    (hnear : 1-rho.1.re <= 1/20000)
    (hheight : localZetaLogHeight rho.1.im <= 10^150)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3/2-rho.1.re < ‖(3/2+I*(rho.1.im : ℂ))-tau.1‖)
    (hbalance : 3*naturalMass rho (show 1/2 < rho.1.re by linarith)
        (otherModes rho (show 1/2 < rho.1.re by linarith)) <=
      14*naturalMass rho (show 1/2 < rho.1.re by linarith)
        (coherentModes rho (show 1/2 < rho.1.re by linarith))+12) :
    analyticZetaZeroMultiplicity rho = 1 := by
  apply simple_of_profile_floor rho hnear hheight
  have hb := profile_ge_balance rho (show 1/2 < rho.1.re by linarith) hexposed
  rw [coherentMass_eq_nat, otherMass_eq_nat] at hb
  have hbalR : 3*(naturalMass rho (show 1/2 < rho.1.re by linarith)
      (otherModes rho (show 1/2 < rho.1.re by linarith)) : ℝ) <=
    14*(naturalMass rho (show 1/2 < rho.1.re by linarith)
      (coherentModes rho (show 1/2 < rho.1.re by linarith)) : ℝ)+12 := by exact_mod_cast hbalance
  linarith only [hb, hbalR]

/-- A surviving multiple source must fail the signed population balance
by at least one INTEGER unit. This strengthens the former mass>=5 audit. -/
theorem multiple_forces_unbalanced (rho : NontrivialZetaZero)
    (hnear : 1-rho.1.re <= 1/20000)
    (hheight : localZetaLogHeight rho.1.im <= 10^150)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3/2-rho.1.re < ‖(3/2+I*(rho.1.im : ℂ))-tau.1‖)
    (hm : 2 <= analyticZetaZeroMultiplicity rho) :
    14*naturalMass rho (show 1/2 < rho.1.re by linarith)
        (coherentModes rho (show 1/2 < rho.1.re by linarith))+13 <=
      3*naturalMass rho (show 1/2 < rho.1.re by linarith)
        (otherModes rho (show 1/2 < rho.1.re by linarith)) := by
  by_contra h
  have hbalance : 3*naturalMass rho (show 1/2 < rho.1.re by linarith)
      (otherModes rho (show 1/2 < rho.1.re by linarith)) <=
    14*naturalMass rho (show 1/2 < rho.1.re by linarith)
      (coherentModes rho (show 1/2 < rho.1.re by linarith))+12 := by omega
  have hs := simple_of_natural_balance rho hnear hheight hexposed hbalance
  omega

/-- Exact signed-profile criterion for the SAME native ceiling. The
profile floor remains explicit; no count debit replaces the signed sum. -/
theorem eventually_joinedPhysical_ceiling_of_profile_floor
    (rho : NontrivialZetaZero) (hnear : 1-rho.1.re <= 1/20000)
    (hheight : localZetaLogHeight rho.1.im <= 10^150)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3/2-rho.1.re < ‖(3/2+I*(rho.1.im : ℂ))-tau.1‖)
    (hprofile : -36 <= signedProfile rho (show 1/2 < rho.1.re by linarith)) :
    ∀ᶠ j : ℕ in atTop,
      (((3/2-rho.1.re : ℝ) : ℂ)^(ZetaRieszPrimeCountFrequency.dyadicMomentOrder j+1)*
        ZetaRieszGammaJoint.joinedPhysical (3/2-rho.1.re) rho.1.im
          (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)
          (ZetaRieszPrimeCountFrequency.dyadicPrimeCount j)).re < 42/25 := by
  have hrho : 1/2 < rho.1.re := by linarith
  have hu : 1/2 <= 3/2-rho.1.re := by linarith [rho.re_lt_one]
  have hU : 3/2-rho.1.re <= ZetaRieszWideOwnerAudit.radiusCeiling := by
    unfold ZetaRieszWideOwnerAudit.radiusCeiling
    linarith
  have hm := simple_of_profile_floor rho hnear hheight hprofile
  have hs := Complex.continuous_re.tendsto _ |>.comp
    (ZetaRieszJoinedPhysical.tendsto_joinedPhysical_exact_source rho hrho hexposed hU)
  simp only [hm, Nat.cast_one, one_pow, one_mul, Complex.add_re, Complex.neg_re,
    Complex.one_re, Complex.ofReal_re] at hs
  have hc := ZetaRieszEndgameSlack.retainedCost_upper hu hU
  exact hs.eventually (gt_mem_nhds (show -1+ZetaRieszMaskSupport.retainedCost (3/2-rho.1.re) <
    42/25 by linarith only [hc]))

/-- The SAME native ceiling is genuinely paid for these dense signed
geometries, within the explicit height range. The full all-height objective
is still open; no upper bound on total competing mass is assumed here. -/
theorem eventually_joinedPhysical_ceiling_of_balance
    (rho : NontrivialZetaZero) (hnear : 1-rho.1.re <= 1/20000)
    (hheight : localZetaLogHeight rho.1.im <= 10^150)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3/2-rho.1.re < ‖(3/2+I*(rho.1.im : ℂ))-tau.1‖)
    (hbalance : 3*naturalMass rho (show 1/2 < rho.1.re by linarith)
        (otherModes rho (show 1/2 < rho.1.re by linarith)) <=
      14*naturalMass rho (show 1/2 < rho.1.re by linarith)
        (coherentModes rho (show 1/2 < rho.1.re by linarith))+12) :
    ∀ᶠ j : ℕ in atTop,
      (((3/2-rho.1.re : ℝ) : ℂ)^(ZetaRieszPrimeCountFrequency.dyadicMomentOrder j+1)*
        ZetaRieszGammaJoint.joinedPhysical (3/2-rho.1.re) rho.1.im
          (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)
          (ZetaRieszPrimeCountFrequency.dyadicPrimeCount j)).re < 42/25 := by
  apply eventually_joinedPhysical_ceiling_of_profile_floor rho hnear hheight hexposed
  have hb := profile_ge_balance rho (show 1/2 < rho.1.re by linarith) hexposed
  rw [coherentMass_eq_nat, otherMass_eq_nat] at hb
  have hbalR : 3*(naturalMass rho (show 1/2 < rho.1.re by linarith)
      (otherModes rho (show 1/2 < rho.1.re by linarith)) : ℝ) <=
    14*(naturalMass rho (show 1/2 < rho.1.re by linarith)
      (coherentModes rho (show 1/2 < rho.1.re by linarith)) : ℝ)+12 := by exact_mod_cast hbalance
  linarith only [hb, hbalR]

/-- Every competing mode in the coherent tube pays the native ceiling
regardless of total count/multiplicity or its single-order opposing sign.
This is a proved sector, not an assertion that every cluster is coherent. -/
theorem eventually_joinedPhysical_ceiling_of_coherent_cluster
    (rho : NontrivialZetaZero) (hnear : 1-rho.1.re <= 1/20000)
    (hheight : localZetaLogHeight rho.1.im <= 10^150)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3/2-rho.1.re < ‖(3/2+I*(rho.1.im : ℂ))-tau.1‖)
    (hcoherent : ∀ z ∈ competingSupport rho (show 1/2 < rho.1.re by linarith),
      ‖normalizedNode rho z^1100-1‖ <= 1/8) :
    ∀ᶠ j : ℕ in atTop,
      (((3/2-rho.1.re : ℝ) : ℂ)^(ZetaRieszPrimeCountFrequency.dyadicMomentOrder j+1)*
        ZetaRieszGammaJoint.joinedPhysical (3/2-rho.1.re) rho.1.im
          (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)
          (ZetaRieszPrimeCountFrequency.dyadicPrimeCount j)).re < 42/25 := by
  have hrho : 1/2 < rho.1.re := by linarith
  have ho : otherModes rho hrho = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro z hz
    exact (Finset.mem_filter.mp hz).2 (hcoherent z (Finset.mem_filter.mp hz).1)
  apply eventually_joinedPhysical_ceiling_of_balance rho hnear hheight hexposed
  simp only [naturalMass, ho, Finset.sum_empty, mul_zero]
  omega

end RiemannGaussian.ZetaRieszCeilingFejerBalance
