/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszCeilingMomentIsolation

/-!
# A signed actual-cluster payment of the unchanged ceiling

Keep nearby genuine zero modes joined and signed. Only the distance-separated
exterior is norm-paid. The resulting independent inequality allows nearby
competing zeros to reinforce the selected source for free. It also tolerates
a fixed negative signed cluster budget. No synthetic array is identified with
the actual arithmetic carrier and no all-height ceiling is claimed.
-/

set_option autoImplicit false
set_option maxHeartbeats 2500000
noncomputable section
open Complex Filter Topology Metric
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszCeilingSignedCluster
open ZetaRieszCeilingMomentIsolation

/-- The selected-erased actual local divisor within the stated distance. -/
def nearbyModes (rho : NontrivialZetaZero) (hrho : 1/2 < rho.1.re) (R : ℝ) : Finset ℂ :=
  ((adaptiveZetaZeroSupport (zetaRightHalfDiscParameter rho hrho) rho.1.im).erase
    (-((3/2-rho.1.re : ℝ) : ℂ))).filter (fun z => ‖z‖ <= R)

/-- The signed aggregate of ALL nearby genuine competing modes. -/
def nearbyMoment (rho : NontrivialZetaZero) (hrho : 1/2 < rho.1.re)
    (R : ℝ) (n : ℕ) : ℂ :=
  ∑ z ∈ nearbyModes rho hrho R,
    (modeCoefficient (zetaRightHalfDiscParameter rho hrho) rho.1.im z : ℂ)*
      (((3/2-rho.1.re : ℝ) : ℂ)*(-z⁻¹))^(n+1)

/-- Coefficients in this leaf are actual nonnegative multiplicities. -/
theorem coefficient_nonneg (r : Set.Ico (3/4 : ℝ) 1) (y : ℝ)
    {z : ℂ} (hz : z ∈ adaptiveZetaZeroSupport r y) : 0 <= modeCoefficient r y z := by
  rw [modeCoefficient_eq_multiplicity r y hz]
  positivity

/-- The exact whole competing sum splits into the nearby signed sum and
its distance-separated exterior. No source term is lost. -/
theorem competing_eq_nearby_add_far (rho : NontrivialZetaZero)
    (hrho : 1/2 < rho.1.re) (R : ℝ) (n : ℕ) :
    competingMoment rho hrho n = nearbyMoment rho hrho R n+
      ∑ z ∈ ((adaptiveZetaZeroSupport (zetaRightHalfDiscParameter rho hrho) rho.1.im).erase
        (-((3/2-rho.1.re : ℝ) : ℂ))) \ nearbyModes rho hrho R,
        (modeCoefficient (zetaRightHalfDiscParameter rho hrho) rho.1.im z : ℂ)*
          (((3/2-rho.1.re : ℝ) : ℂ)*(-z⁻¹))^(n+1) := by
  unfold competingMoment nearbyMoment
  exact (Finset.sum_sdiff (Finset.filter_subset _ _)).symm.trans (add_comm _ _)

/-- The exterior is paid ONCE by the multiplicity-weighted height mass.
The nearby signed family is untouched. No global isolation is assumed. -/
theorem far_norm_bound (rho : NontrivialZetaZero) (hrho : 1/2 < rho.1.re)
    {R : ℝ} (hR : 0 < R) (n : ℕ) :
    ‖∑ z ∈ ((adaptiveZetaZeroSupport (zetaRightHalfDiscParameter rho hrho) rho.1.im).erase
        (-((3/2-rho.1.re : ℝ) : ℂ))) \ nearbyModes rho hrho R,
        (modeCoefficient (zetaRightHalfDiscParameter rho hrho) rho.1.im z : ℂ)*
          (((3/2-rho.1.re : ℝ) : ℂ)*(-z⁻¹))^(n+1)‖ <=
      (localZetaLogHeight rho.1.im+11)*((3/2-rho.1.re)/R)^(n+1) := by
  let r := zetaRightHalfDiscParameter rho hrho
  let u := 3/2-rho.1.re
  let S := ((adaptiveZetaZeroSupport r rho.1.im).erase (-(u : ℂ))) \
    nearbyModes rho hrho R
  have hu : 0 <= u := by dsimp [u]; linarith [rho.re_lt_one]
  have hS : S ⊆ adaptiveZetaZeroSupport r rho.1.im :=
    Finset.Subset.trans Finset.sdiff_subset (Finset.erase_subset _ _)
  have hm : (∑ z ∈ S, modeCoefficient r rho.1.im z) <= localZetaLogHeight rho.1.im+11 :=
    (Finset.sum_le_sum_of_subset_of_nonneg hS
      (fun z hz _ => coefficient_nonneg r _ hz)).trans (local_mode_mass_height r _)
  have hn (z : ℂ) (hz : z ∈ S) : ‖(u : ℂ)*(-z⁻¹)‖ <= u/R := by
    have hfar : R < ‖z‖ := by
      by_contra! hc
      exact (Finset.mem_sdiff.mp hz).2
        (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hz).1, hc⟩)
    rw [norm_mul, norm_neg, norm_inv, Complex.norm_real, Real.norm_of_nonneg hu,
      <-div_eq_mul_inv]
    exact div_le_div_of_nonneg_left hu hR hfar.le
  change ‖∑ z ∈ S, (modeCoefficient r rho.1.im z : ℂ)*((u : ℂ)*(-z⁻¹))^(n+1)‖ <= _
  calc
    _ <= ∑ z ∈ S, ‖(modeCoefficient r rho.1.im z : ℂ)*((u : ℂ)*(-z⁻¹))^(n+1)‖ :=
      norm_sum_le _ _
    _ <= ∑ z ∈ S, modeCoefficient r rho.1.im z*(u/R)^(n+1) := by
      apply Finset.sum_le_sum
      intro z hz
      rw [norm_mul, norm_pow, Complex.norm_real,
        Real.norm_of_nonneg (coefficient_nonneg r _ (hS hz))]
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) (hn z hz) _) (coefficient_nonneg r _ (hS hz))
    _ = (∑ z ∈ S, modeCoefficient r rho.1.im z)*(u/R)^(n+1) := by rw [Finset.sum_mul]
    _ <= _ := mul_le_mul_of_nonneg_right hm (pow_nonneg (div_nonneg hu hR.le) _)

/-- Independent actual arithmetic bound on the selected source plus
the WHOLE signed nearby cluster, with a geometric exterior error. -/
theorem multiplicity_add_nearby_re_le (rho : NontrivialZetaZero)
    (hrho : 1/2 < rho.1.re) {R : ℝ} (hR : 0 < R) (n : ℕ) :
    (analyticZetaZeroMultiplicity rho : ℝ)+(nearbyMoment rho hrho R n).re <=
      momentTest (3/2-rho.1.re) rho.1.im R n := by
  have hs := multiplicity_add_competing_re_le rho hrho n
  dsimp only at hs
  rw [competing_eq_nearby_add_far rho hrho R n, Complex.add_re] at hs
  have hb := far_norm_bound rho hrho hR n
  have hr := Complex.re_le_norm
    (-(∑ z ∈ ((adaptiveZetaZeroSupport (zetaRightHalfDiscParameter rho hrho) rho.1.im).erase
      (-((3/2-rho.1.re : ℝ) : ℂ))) \ nearbyModes rho hrho R,
      (modeCoefficient (zetaRightHalfDiscParameter rho hrho) rho.1.im z : ℂ)*
        (((3/2-rho.1.re : ℝ) : ℂ)*(-z⁻¹))^(n+1)))
  simp only [Complex.neg_re, norm_neg] at hr
  unfold momentTest
  linarith only [hs, hb, hr]

/-- A nonempty signed-cluster allowance proves ACTUAL simplicity, even
without an isolation gap. The full all-height target is not replaced. -/
theorem simple_of_nearby_floor (rho : NontrivialZetaZero)
    (hnear : 1-rho.1.re <= 1/20000)
    (hheight : localZetaLogHeight rho.1.im <= 10^150)
    (hcluster : -(1/5 : ℝ) <=
      (nearbyMoment rho (show 1/2 < rho.1.re by linarith) (11/20) 4096).re) :
    analyticZetaZeroMultiplicity rho = 1 := by
  have hrho : 1/2 < rho.1.re := by linarith
  have ht := (multiplicity_add_nearby_re_le rho hrho (by norm_num) 4096).trans_lt
    (momentTest_lt_nine_fifths
      (show 1/2 <= 3/2-rho.1.re by linarith [rho.re_lt_one])
      (show 3/2-rho.1.re <= 10001/20000 by linarith) hheight)
  have hm : (analyticZetaZeroMultiplicity rho : ℝ) < 2 := by linarith only [ht, hcluster]
  have hn : analyticZetaZeroMultiplicity rho < 2 := by exact_mod_cast hm
  have hp := analyticZetaZeroMultiplicity_positive rho
  omega

/-- The exact unpaid nearby signed aggregate is quantitatively negative
if an actual multiple candidate survives. No count or absolute debit. -/
theorem multiple_forces_nearby_counterweight (rho : NontrivialZetaZero)
    (hnear : 1-rho.1.re <= 1/20000)
    (hheight : localZetaLogHeight rho.1.im <= 10^150)
    (hm : 2 <= analyticZetaZeroMultiplicity rho) :
    (nearbyMoment rho (show 1/2 < rho.1.re by linarith) (11/20) 4096).re < -1/5 := by
  by_contra! h
  have hs := simple_of_nearby_floor rho hnear hheight (by simpa only [neg_div] using h)
  omega

/-- The SAME native joinedPhysical ceiling, now paid for a genuinely
signed nearby-cluster sector. Exposure is retained as a separate input. -/
theorem eventually_joinedPhysical_ceiling_of_nearby_floor (rho : NontrivialZetaZero)
    (hnear : 1-rho.1.re <= 1/20000)
    (hheight : localZetaLogHeight rho.1.im <= 10^150)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3/2-rho.1.re < ‖(3/2+I*(rho.1.im : ℂ))-tau.1‖)
    (hcluster : -(1/5 : ℝ) <=
      (nearbyMoment rho (show 1/2 < rho.1.re by linarith) (11/20) 4096).re) :
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
  have hm := simple_of_nearby_floor rho hnear hheight hcluster
  have hs := Complex.continuous_re.tendsto _ |>.comp
    (ZetaRieszJoinedPhysical.tendsto_joinedPhysical_exact_source rho hrho hexposed hU)
  simp only [hm, Nat.cast_one, one_pow, one_mul, Complex.add_re, Complex.neg_re,
    Complex.one_re, Complex.ofReal_re] at hs
  have hc := ZetaRieszEndgameSlack.retainedCost_upper hu hU
  exact hs.eventually (gt_mem_nhds (show -1+ZetaRieszMaskSupport.retainedCost (3/2-rho.1.re) <
    42/25 by linarith only [hc]))

/-- Power perturbations are priced jointly, before splitting phases. -/
theorem norm_pow_sub_one_le {v : ℂ} (hv : ‖v‖ <= 1) (k : ℕ) :
    ‖v^k-1‖ <= (k : ℝ)*‖v-1‖ := by
  induction k with
  | zero => simp
  | succ k hk =>
    have he : v^(k+1)-1 = v*(v^k-1)+(v-1) := by rw [pow_succ]; ring
    rw [he]
    calc
      _ <= ‖v*(v^k-1)‖+‖v-1‖ := norm_add_le _ _
      _ <= ‖v^k-1‖+‖v-1‖ := by
        rw [norm_mul]
        simpa only [add_comm] using
          add_le_add_right (mul_le_of_le_one_left (norm_nonneg (v^k-1)) hv) ‖v-1‖
      _ <= (k : ℝ)*‖v-1‖+‖v-1‖ := by linarith only [hk]
      _ = _ := by push_cast; ring

/-- A narrow ordinate cone is CONSTRUCTIVE for the selected moment.
Its near modes need no separate multiplicity/count allowance. -/
theorem normalized_power_re_nonneg {u : ℝ} (hu : 0 < u) {D : ℂ}
    (ha : 0 < D.re) (k : ℕ)
    (hphase : (k : ℝ)*|D.im| <= D.re) : 0 <= (((u : ℂ)/D)^k).re := by
  let a := D.re
  let v := (a : ℂ)/D
  have hD : D ≠ 0 := Complex.ne_zero_of_re_pos ha
  have hn : a <= ‖D‖ := Complex.re_le_norm D
  have hv : ‖v‖ <= 1 := by
    dsimp only [v]
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg ha.le]
    exact (div_le_one (norm_pos_iff.mpr hD)).mpr hn
  have he : v-1 = (-(I*(D.im : ℂ)))/D := by
    dsimp only [v, a]
    have hc : (D.re : ℂ)-D = -(I*(D.im : ℂ)) := by
      apply Complex.ext <;> simp
    rw [div_sub_one hD, hc]
  have hdiff : ‖v-1‖ <= |D.im|/a := by
    rw [he, norm_div, norm_neg, norm_mul, Complex.norm_I, one_mul,
      Complex.norm_real, Real.norm_eq_abs]
    exact div_le_div_of_nonneg_left (abs_nonneg _) ha hn
  have hbound : ‖v^k-1‖ <= 1 := by
    have h := (norm_pow_sub_one_le hv k).trans
      (mul_le_mul_of_nonneg_left hdiff (by positivity : (0 : ℝ) <= k))
    have hp : (k : ℝ)*|D.im|/a <= 1 := (div_le_one ha).mpr
      (by simpa only [a] using hphase)
    rw [<-mul_div_assoc] at h
    exact h.trans hp
  have hre := Complex.re_le_norm (1-v^k)
  rw [Complex.sub_re, Complex.one_re, norm_sub_rev] at hre
  have hvr : 0 <= (v^k).re := by linarith only [hre, hbound]
  have heq : (u : ℂ)/D = ((u/a : ℝ) : ℂ)*v := by
    dsimp only [v]
    have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
    push_cast
    field_simp [ha0]
  rw [heq, mul_pow, <-Complex.ofReal_pow, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  exact mul_nonneg (pow_nonneg (div_nonneg hu.le ha.le) _) hvr

/-- Every retained cluster index is a DISTINCT genuine zero, at the
exact denominator used in the signed moment. -/
theorem nearby_actual_zero (rho : NontrivialZetaZero) (hrho : 1/2 < rho.1.re)
    (R : ℝ) {z : ℂ} (hz : z ∈ nearbyModes rho hrho R) :
    ∃ tau : NontrivialZetaZero, tau ≠ rho ∧ (3/2+I*(rho.1.im : ℂ))-tau.1 = -z := by
  obtain ⟨hze, _⟩ := Finset.mem_filter.mp hz
  obtain ⟨hne, hs⟩ := Finset.mem_erase.mp hze
  let r := zetaRightHalfDiscParameter rho hrho
  let tau : NontrivialZetaZero :=
    ⟨3/2+I*rho.1.im+z, ZetaZeroFilterCost.support_is_zero r rho.1.im hs⟩
  have htau : tau ≠ rho := by
    intro he
    apply hne
    have hre := congrArg (fun t : NontrivialZetaZero => t.1.re) he
    have him := congrArg (fun t : NontrivialZetaZero => t.1.im) he
    dsimp [tau] at hre him
    norm_num at hre him
    apply Complex.ext <;> simp <;> linarith
  refine ⟨tau, htau, ?_⟩
  change (3/2+I*(rho.1.im : ℂ))-(3/2+I*rho.1.im+z) = -z
  ring

/-- Constructive phases pay the WHOLE nearby aggregate without a
cardinality or multiplicity debit. The actual weights remain joined. -/
theorem nearby_re_nonneg_of_phase (rho : NontrivialZetaZero)
    (hrho : 1/2 < rho.1.re) (R : ℝ) (n : ℕ)
    (hphase : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      ‖(3/2+I*(rho.1.im : ℂ))-tau.1‖ <= R →
      0 <= ((((3/2-rho.1.re : ℝ) : ℂ)/((3/2+I*(rho.1.im : ℂ))-tau.1))^(n+1)).re) :
    0 <= (nearbyMoment rho hrho R n).re := by
  unfold nearbyMoment
  rw [Complex.re_sum]
  apply Finset.sum_nonneg
  intro z hz
  obtain ⟨tau, hne, he⟩ := nearby_actual_zero rho hrho R hz
  have hd : ‖(3/2+I*(rho.1.im : ℂ))-tau.1‖ <= R := by
    rw [he, norm_neg]
    exact (Finset.mem_filter.mp hz).2
  have hp := hphase tau hne hd
  rw [he] at hp
  have hs := (Finset.mem_erase.mp (Finset.mem_filter.mp hz).1).2
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  exact mul_nonneg (coefficient_nonneg _ _ hs)
    (by simpa only [div_eq_mul_inv, inv_neg] using hp)

/-- A very close ordinate is uniformly constructive, regardless of
the competing zero's real part. No rightmost assumption is needed. -/
theorem actual_mode_re_nonneg_of_ordinate (rho tau : NontrivialZetaZero)
    (hclose : |tau.1.im-rho.1.im| <= 1/8194) :
    0 <= ((((3/2-rho.1.re : ℝ) : ℂ)/((3/2+I*(rho.1.im : ℂ))-tau.1))^4097).re := by
  let D : ℂ := (3/2+I*(rho.1.im : ℂ))-tau.1
  have ha : 1/2 < D.re := by simp [D]; linarith [tau.re_lt_one]
  have him : |D.im| = |tau.1.im-rho.1.im| := by simp [D, abs_sub_comm]
  have hb : |D.im| <= 1/8194 := by rwa [him]
  have hp : (4097 : ℝ)*|D.im| <= D.re := by nlinarith only [ha, hb]
  exact normalized_power_re_nonneg
    (show 0 < 3/2-rho.1.re by linarith [rho.re_lt_one])
    (show 0 < D.re by linarith only [ha]) 4097 hp

/-- Actual multiple candidates must have a NEARBY opposing-phase zero,
not merely an arbitrary nearby zero or a large analytic correction. -/
theorem multiple_forces_opposing_phase (rho : NontrivialZetaZero)
    (hnear : 1-rho.1.re <= 1/20000)
    (hheight : localZetaLogHeight rho.1.im <= 10^150)
    (hm : 2 <= analyticZetaZeroMultiplicity rho) :
    ∃ tau : NontrivialZetaZero, tau ≠ rho ∧
      ‖(3/2+I*(rho.1.im : ℂ))-tau.1‖ <= 11/20 ∧
      ((((3/2-rho.1.re : ℝ) : ℂ)/((3/2+I*(rho.1.im : ℂ))-tau.1))^4097).re < 0 := by
  by_contra! h
  have hn := nearby_re_nonneg_of_phase rho
    (show 1/2 < rho.1.re by linarith) (11/20) 4096 h
  have hc := multiple_forces_nearby_counterweight rho hnear hheight hm
  linarith only [hn, hc]

/-- This newly paid signed sector includes actual nearby competitors;
the old empty-cluster isolation hypothesis is not required. -/
theorem simple_of_small_ordinate_cluster (rho : NontrivialZetaZero)
    (hnear : 1-rho.1.re <= 1/20000)
    (hheight : localZetaLogHeight rho.1.im <= 10^150)
    (hclose : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      ‖(3/2+I*(rho.1.im : ℂ))-tau.1‖ <= 11/20 →
      |tau.1.im-rho.1.im| <= 1/8194) : analyticZetaZeroMultiplicity rho = 1 := by
  have hn := nearby_re_nonneg_of_phase rho
    (show 1/2 < rho.1.re by linarith) (11/20) 4096
    (fun tau hne hd => actual_mode_re_nonneg_of_ordinate rho tau (hclose tau hne hd))
  exact simple_of_nearby_floor rho hnear hheight (by linarith only [hn])

/-- The SAME native ceiling is paid when every nearby mode is in the
constructive ordinate cone. Finite height and exposure stay explicit. -/
theorem eventually_joinedPhysical_ceiling_of_small_ordinate_cluster (rho : NontrivialZetaZero)
    (hnear : 1-rho.1.re <= 1/20000)
    (hheight : localZetaLogHeight rho.1.im <= 10^150)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3/2-rho.1.re < ‖(3/2+I*(rho.1.im : ℂ))-tau.1‖)
    (hclose : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      ‖(3/2+I*(rho.1.im : ℂ))-tau.1‖ <= 11/20 →
      |tau.1.im-rho.1.im| <= 1/8194) :
    ∀ᶠ j : ℕ in atTop,
      (((3/2-rho.1.re : ℝ) : ℂ)^(ZetaRieszPrimeCountFrequency.dyadicMomentOrder j+1)*
        ZetaRieszGammaJoint.joinedPhysical (3/2-rho.1.re) rho.1.im
          (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)
          (ZetaRieszPrimeCountFrequency.dyadicPrimeCount j)).re < 42/25 := by
  have hn := nearby_re_nonneg_of_phase rho
    (show 1/2 < rho.1.re by linarith) (11/20) 4096
    (fun tau hne hd => actual_mode_re_nonneg_of_ordinate rho tau (hclose tau hne hd))
  exact eventually_joinedPhysical_ceiling_of_nearby_floor rho hnear hheight hexposed
    (by linarith only [hn])

/-- A surviving multiple candidate forces an explicitly separated,
opposing-phase nearby zero in the original right-half cluster. This is
not a rightward successor, an infinite-chain statement or a zero exclusion. -/
theorem multiple_forces_opposing_cluster (rho : NontrivialZetaZero)
    (hnear : 1-rho.1.re <= 1/20000)
    (hheight : localZetaLogHeight rho.1.im <= 10^150)
    (hm : 2 <= analyticZetaZeroMultiplicity rho) :
    ∃ tau : NontrivialZetaZero, tau ≠ rho ∧ (19/20 : ℝ) <= tau.1.re ∧
      (1/8194 : ℝ) < |tau.1.im-rho.1.im| ∧ |tau.1.im-rho.1.im| < 1/4 ∧
      ((((3/2-rho.1.re : ℝ) : ℂ)/((3/2+I*(rho.1.im : ℂ))-tau.1))^4097).re < 0 := by
  obtain ⟨tau, hne, hd, hp⟩ := multiple_forces_opposing_phase rho hnear hheight hm
  have hlo : (1/8194 : ℝ) < |tau.1.im-rho.1.im| := by
    by_contra! h
    have hn := actual_mode_re_nonneg_of_ordinate rho tau h
    linarith only [hn, hp]
  let D : ℂ := (3/2+I*(rho.1.im : ℂ))-tau.1
  have hre : D.re = 3/2-tau.1.re := by simp [D]
  have him : D.im = rho.1.im-tau.1.im := by simp [D]
  have hβ : (19/20 : ℝ) <= tau.1.re := by
    have h := (Complex.re_le_norm D).trans hd
    rw [hre] at h
    linarith
  have hsq : D.re^2+D.im^2 <= (11/20 : ℝ)^2 := by
    have h := pow_le_pow_left₀ (norm_nonneg D) hd 2
    rw [Complex.sq_norm, Complex.normSq_apply] at h
    nlinarith only [h]
  have hr : 1/2 < D.re := by rw [hre]; linarith [tau.re_lt_one]
  have habs : |D.im| < 1/4 := by nlinarith [sq_abs D.im, abs_nonneg D.im]
  exact ⟨tau, hne, hβ, hlo, by simpa only [him, abs_sub_comm] using habs, hp⟩

end RiemannGaussian.ZetaRieszCeilingSignedCluster
