/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiCarrierFinitePoles
import Mathlib.Topology.Algebra.Module.Cardinality

/-!
# An actual finite rectangular contour formula for Suzuki's carrier

The finite window contains every xi or carrier-denominator zero in the
closed rectangle. All side integrability, local pole models and analytic
remainder hypotheses are discharged for the original mixed channel.
The resulting identity keeps the full complex residue sum and the exact
counterclockwise orientation. No infinite-contour limit is assumed.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Topology
namespace RiemannGaussian
noncomputable section

private lemma compact_rectangle (l r b u : ℝ) :
    IsCompact (Complex.Rectangle ((l : ℂ) + (b : ℂ) * I) ((r : ℂ) + (u : ℂ) * I)) := by
  exact isCompact_uIcc.reProdIm isCompact_uIcc

/-- Every actual xi or carrier-denominator zero in the closed rectangle,
including removable points whose residues are subsequently evaluated. -/
def suzukiXiCarrierPoleWindow (l r b u : ℝ) : Finset ℂ :=
  (IsCompact.inter_suzukiXiCarrierSingularSet_finite (compact_rectangle l r b u)).toFinset

/-- Membership in the finite pole window retains both the actual closed
rectangle and the complete potential singular set. -/
theorem mem_suzukiXiCarrierPoleWindow {l r b u : ℝ} {c : ℂ} :
    c ∈ suzukiXiCarrierPoleWindow l r b u ↔
      c ∈ Complex.Rectangle ((l : ℂ) + (b : ℂ) * I) ((r : ℂ) + (u : ℂ) * I) ∧
        c ∈ suzukiXiCarrierSingularSet := by
  exact Set.Finite.mem_toFinset _

/-- An ordered rectangle whose four complete side lines avoid the actual
xi and carrier denominators. The condition is geometric and will be
available by avoiding the countable coordinate projections. -/
def SuzukiXiCarrierRectangleAdmissible (l r b u : ℝ) : Prop :=
  l < r ∧ b < u ∧ ∀ c ∈ suzukiXiCarrierSingularSet,
    c.re ≠ l ∧ c.re ≠ r ∧ c.im ≠ b ∧ c.im ≠ u

/-- Every retained singularity lies strictly inside an admissible
rectangle. No pole lies on a side or at a corner. -/
theorem suzukiXiCarrierPoleWindow_strict_interior {l r b u : ℝ}
    (hadm : SuzukiXiCarrierRectangleAdmissible l r b u) {c : ℂ}
    (hc : c ∈ suzukiXiCarrierPoleWindow l r b u) :
    l < c.re ∧ c.re < r ∧ b < c.im ∧ c.im < u := by
  have hmem := mem_suzukiXiCarrierPoleWindow.mp hc
  have hbox : (l ≤ c.re ∧ c.re ≤ r) ∧ b ≤ c.im ∧ c.im ≤ u := by
    simpa [Complex.Rectangle, Complex.mem_reProdIm,
      Set.uIcc_of_le hadm.1.le, Set.uIcc_of_le hadm.2.1.le] using hmem.1
  have hn := hadm.2.2 c hmem.2
  exact ⟨lt_of_le_of_ne hbox.1.1 hn.1.symm, lt_of_le_of_ne hbox.1.2 hn.2.1,
    lt_of_le_of_ne hbox.2.1 hn.2.2.1.symm, lt_of_le_of_ne hbox.2.2 hn.2.2.2⟩

/-- The actual mixed channel is continuous, hence integrable, on all
four sides of every admissible rectangle. -/
theorem rectangularBoundaryIntegrable_suzukiXiMixedCarrierChannel
    (rho sigma : NontrivialZetaZero) {l r b u : ℝ}
    (hadm : SuzukiXiCarrierRectangleAdmissible l r b u) :
    rectangularBoundaryIntegrable l r b u (suzukiXiMixedCarrierChannel rho sigma) := by
  have hbottom (x : ℝ) : (x : ℂ) + (b : ℂ) * I ∉ suzukiXiCarrierSingularSet := by
    intro h
    exact (hadm.2.2 _ h).2.2.1 (by simp)
  have htop (x : ℝ) : (x : ℂ) + (u : ℂ) * I ∉ suzukiXiCarrierSingularSet := by
    intro h
    exact (hadm.2.2 _ h).2.2.2 (by simp)
  have hleft (y : ℝ) : (l : ℂ) + (y : ℝ) * I ∉ suzukiXiCarrierSingularSet := by
    intro h
    exact (hadm.2.2 _ h).1 (by simp)
  have hright (y : ℝ) : (r : ℂ) + (y : ℝ) * I ∉ suzukiXiCarrierSingularSet := by
    intro h
    exact (hadm.2.2 _ h).2.1 (by simp)
  have hcont (g : ℝ → ℂ) (hg : Continuous g) (hne : ∀ x, g x ∉ suzukiXiCarrierSingularSet) :
      Continuous (fun x => suzukiXiMixedCarrierChannel rho sigma (g x)) :=
    continuous_comp_of_forall_analyticAt _ _ hg
      (fun x => analyticAt_suzukiXiMixedCarrierChannel_of_not_mem rho sigma (hne x))
  exact ⟨(hcont _ (by fun_prop) hbottom).intervalIntegrable l r,
    (hcont _ (by fun_prop) htop).intervalIntegrable l r,
    (hcont _ (by fun_prop) hright).intervalIntegrable b u,
    (hcont _ (by fun_prop) hleft).intervalIntegrable b u⟩

/-- The original mixed Suzuki carrier has its complete finite rectangular
residue identity. Every analytic and integrability hypothesis is proved
for the actual function; only geometric contour admissibility is required. -/
theorem suzukiXiMixedCarrierChannel_rectangle_eq_residues
    (rho sigma : NontrivialZetaZero) {l r b u : ℝ}
    (hadm : SuzukiXiCarrierRectangleAdmissible l r b u) :
    rectangularBoundaryIntegral l r b u (suzukiXiMixedCarrierChannel rho sigma) =
      (2 * Real.pi : ℝ) * I * ∑ c ∈ suzukiXiCarrierPoleWindow l r b u,
        suzukiXiMixedCarrierLocalResidue rho sigma c := by
  apply rectangularBoundaryIntegral_eq_finitePole_residues l r b u hadm.1.le hadm.2.1.le
    (suzukiXiCarrierPoleWindow l r b u) (suzukiXiMixedCarrierChannel rho sigma)
    suzukiXiMixedCarrierLocalOrder (suzukiXiMixedCarrierLocalNumerator rho sigma)
  · exact fun _ hc => suzukiXiCarrierPoleWindow_strict_interior hadm hc
  · exact rectangularBoundaryIntegrable_suzukiXiMixedCarrierChannel rho sigma hadm
  · intro z hz hzS
    apply analyticAt_suzukiXiMixedCarrierChannel_of_not_mem
    intro hsing
    exact hzS (mem_suzukiXiCarrierPoleWindow.mpr ⟨hz, hsing⟩)
  · exact fun c _ => analyticAt_suzukiXiMixedCarrierLocalNumerator rho sigma c
  · exact fun c _ => suzukiXiMixedCarrierChannel_eventually_eq_local_model rho sigma c

/-- The explicit xi source in an actual mixed contour: only the
reflected pairing survives, with inverse genuine zero multiplicity. -/
def suzukiXiMixedContourXiSource (rho sigma : NontrivialZetaZero) (l r b u : ℝ) : ℂ :=
  if starRingEnd ℂ (zetaSpectralCoordinate rho.1) = zetaSpectralCoordinate sigma.1 ∧
      zetaSpectralCoordinate sigma.1 ∈ suzukiXiCarrierPoleWindow l r b u then
    (analyticZetaZeroMultiplicity sigma : ℂ)⁻¹ else 0

/-- The retained genuine carrier poles in the rectangle. Xi zeros have
their separately evaluated common coefficient and are excluded here. -/
def suzukiXiCarrierGenuinePoleWindow (l r b u : ℝ) : Finset ℂ :=
  (suzukiXiCarrierPoleWindow l r b u).filter fun c => riemannXiSpectral c ≠ 0

private lemma xi_node_sum (rho sigma : NontrivialZetaZero) (S : Finset ℂ) :
    (∑ c ∈ S, suzukiXiMixedXiNodeResidue rho sigma c) =
      if starRingEnd ℂ (zetaSpectralCoordinate rho.1) = zetaSpectralCoordinate sigma.1 ∧
          zetaSpectralCoordinate sigma.1 ∈ S then
        (analyticZetaZeroMultiplicity sigma : ℂ)⁻¹ else 0 := by
  by_cases hpair : starRingEnd ℂ (zetaSpectralCoordinate rho.1) = zetaSpectralCoordinate sigma.1
  · have hterm (c : ℂ) : suzukiXiMixedXiNodeResidue rho sigma c =
        if c = zetaSpectralCoordinate sigma.1 then (analyticZetaZeroMultiplicity sigma : ℂ)⁻¹ else 0 := by
      by_cases hc : c = zetaSpectralCoordinate sigma.1
      · subst c
        simp only [suzukiXiMixedXiNodeResidue, hpair, and_self, if_true,
          analyticOrderNatAt_riemannXiSpectral_zetaSpectralCoordinate]
      · simp only [suzukiXiMixedXiNodeResidue, hpair, and_self, if_neg hc, if_neg (Ne.symm hc)]
    simp_rw [hterm]
    rw [Finset.sum_ite_eq']
    simp only [hpair, true_and]
  · have hterm (c : ℂ) : suzukiXiMixedXiNodeResidue rho sigma c = 0 := by
      apply if_neg
      intro h
      exact hpair (h.1.trans h.2.symm)
    simp only [hterm, Finset.sum_const_zero, hpair, false_and, if_false]

private lemma local_residue_split (rho sigma : NontrivialZetaZero) {c : ℂ}
    (hc : c ∈ suzukiXiCarrierSingularSet) :
    suzukiXiMixedCarrierLocalResidue rho sigma c =
      suzukiXiMixedXiNodeResidue rho sigma c +
        if riemannXiSpectral c ≠ 0 then suzukiXiMixedCarrierPoleResidue rho sigma c else 0 := by
  by_cases hxi : riemannXiSpectral c = 0
  · simp only [suzukiXiMixedCarrierLocalResidue_at_xi_node rho sigma hxi, hxi,
      ne_eq, not_true_eq_false, if_false, add_zero]
  · have hE : suzukiXiEValue c = 0 := hc.resolve_left hxi
    have hsource : suzukiXiMixedXiNodeResidue rho sigma c = 0 := by
      apply if_neg
      intro h
      exact hxi ((riemannXiSpectral_eq_zero_iff_exists_zetaZero c).mpr ⟨sigma, h.2.symm⟩)
    rw [suzukiXiMixedCarrierLocalResidue_at_E_pole rho sigma hE hxi, hsource, if_pos hxi, zero_add]

/-- The complete finite residue sum splits into the reflected xi source
and every genuine carrier pole, independently of boundary admissibility. -/
theorem suzukiXiMixedCarrierLocalResidue_sum_eq_source_add_poles
    (rho sigma : NontrivialZetaZero) (l r b u : ℝ) :
    (∑ c ∈ suzukiXiCarrierPoleWindow l r b u, suzukiXiMixedCarrierLocalResidue rho sigma c) =
      suzukiXiMixedContourXiSource rho sigma l r b u +
        ∑ c ∈ suzukiXiCarrierGenuinePoleWindow l r b u,
          suzukiXiMixedCarrierPoleResidue rho sigma c := by
  have heq : (∑ c ∈ suzukiXiCarrierPoleWindow l r b u,
      suzukiXiMixedCarrierLocalResidue rho sigma c) =
      ∑ c ∈ suzukiXiCarrierPoleWindow l r b u,
        (suzukiXiMixedXiNodeResidue rho sigma c +
          if riemannXiSpectral c ≠ 0 then suzukiXiMixedCarrierPoleResidue rho sigma c else 0) := by
    apply Finset.sum_congr rfl
    intro c hc
    exact local_residue_split rho sigma (mem_suzukiXiCarrierPoleWindow.mp hc).2
  rw [heq, Finset.sum_add_distrib, xi_node_sum]
  simp only [suzukiXiMixedContourXiSource, suzukiXiCarrierGenuinePoleWindow, Finset.sum_filter]

/-- The full actual contour is the explicit reflected xi source plus
the complete complex carrier-pole correction. This is an equality, not
a sign assumption or a bound on that correction. -/
theorem suzukiXiMixedCarrierChannel_rectangle_eq_source_add_poles
    (rho sigma : NontrivialZetaZero) {l r b u : ℝ}
    (hadm : SuzukiXiCarrierRectangleAdmissible l r b u) :
    rectangularBoundaryIntegral l r b u (suzukiXiMixedCarrierChannel rho sigma) =
      (2 * Real.pi : ℝ) * I *
        (suzukiXiMixedContourXiSource rho sigma l r b u +
          ∑ c ∈ suzukiXiCarrierGenuinePoleWindow l r b u,
            suzukiXiMixedCarrierPoleResidue rho sigma c) := by
  rw [suzukiXiMixedCarrierChannel_rectangle_eq_residues rho sigma hadm,
    suzukiXiMixedCarrierLocalResidue_sum_eq_source_add_poles]

/-- The complete actual potential singular set is countable, by its
proved finiteness in every integer-radius compact disk. -/
theorem countable_suzukiXiCarrierSingularSet : suzukiXiCarrierSingularSet.Countable := by
  have hcover : suzukiXiCarrierSingularSet =
      ⋃ n : ℕ, closedBall (0 : ℂ) (n : ℝ) ∩ suzukiXiCarrierSingularSet := by
    rw [← Set.iUnion_inter, Metric.iUnion_closedBall_nat, Set.univ_inter]
  rw [hcover]
  exact Set.countable_iUnion fun n =>
    (IsCompact.inter_suzukiXiCarrierSingularSet_finite (isCompact_closedBall (0 : ℂ) (n : ℝ))).countable

/-- Any open real interval contains a coordinate avoiding both actual
singular-set projections. Thus no zero-free contour choice is assumed. -/
theorem exists_suzukiXiCarrier_safe_coordinate {a b : ℝ} (hab : a < b) :
    ∃ x ∈ Set.Ioo a b, ∀ c ∈ suzukiXiCarrierSingularSet, c.re ≠ x ∧ c.im ≠ x := by
  let bad : Set ℝ := Complex.re '' suzukiXiCarrierSingularSet ∪
    Complex.im '' suzukiXiCarrierSingularSet
  have hbad : bad.Countable := (countable_suzukiXiCarrierSingularSet.image _).union
    (countable_suzukiXiCarrierSingularSet.image _)
  obtain ⟨x, hx, hxgood⟩ := (hbad.dense_compl ℝ).inter_open_nonempty
    (Set.Ioo a b) isOpen_Ioo (Set.nonempty_Ioo.mpr hab)
  refine ⟨x, hx, ?_⟩
  intro c hc
  constructor
  · intro he
    exact hxgood (Or.inl ⟨c, hc, he⟩)
  · intro he
    exact hxgood (Or.inr ⟨c, hc, he⟩)

/-- Arbitrarily large actual admissible rectangles exist. Each strictly
contains the square of radius R, with all four coordinates within one
unit of that square's sides. -/
theorem exists_suzukiXiCarrierRectangleAdmissible (R : ℝ) (hR : 0 ≤ R) :
    ∃ l r b u : ℝ, SuzukiXiCarrierRectangleAdmissible l r b u ∧
      (-R - 1 < l ∧ l < -R) ∧ (R < r ∧ r < R + 1) ∧
      (-R - 1 < b ∧ b < -R) ∧ (R < u ∧ u < R + 1) := by
  obtain ⟨l, hl, hlsafe⟩ := exists_suzukiXiCarrier_safe_coordinate (a := -R - 1) (b := -R) (by linarith)
  obtain ⟨r, hr, hrsafe⟩ := exists_suzukiXiCarrier_safe_coordinate (a := R) (b := R + 1) (by linarith)
  obtain ⟨b, hb, hbsafe⟩ := exists_suzukiXiCarrier_safe_coordinate (a := -R - 1) (b := -R) (by linarith)
  obtain ⟨u, hu, husafe⟩ := exists_suzukiXiCarrier_safe_coordinate (a := R) (b := R + 1) (by linarith)
  refine ⟨l, r, b, u, ⟨by linarith [hl.2, hr.1], by linarith [hb.2, hu.1], ?_⟩, hl, hr, hb, hu⟩
  intro c hc
  exact ⟨(hlsafe c hc).1, (hrsafe c hc).1, (hbsafe c hc).2, (husafe c hc).2⟩

/-- Actual upper rectangles can expand to arbitrary height while their
bottom approaches the real axis independently. All four sides avoid the
complete singular set; no arithmetic or zero-location hypothesis is used. -/
theorem exists_suzukiXiCarrierUpperRectangleAdmissible {R delta : ℝ}
    (hR : 1 ≤ R) (hdelta : 0 < delta) :
    ∃ l r b u : ℝ, SuzukiXiCarrierRectangleAdmissible l r b u ∧
      (-R - 1 < l ∧ l < -R) ∧ (R < r ∧ r < R + 1) ∧
      (0 < b ∧ b < delta ∧ b < 1 / 2) ∧ (R < u ∧ u < R + 1) := by
  obtain ⟨l, hl, hlsafe⟩ := exists_suzukiXiCarrier_safe_coordinate (a := -R - 1) (b := -R) (by linarith)
  obtain ⟨r, hr, hrsafe⟩ := exists_suzukiXiCarrier_safe_coordinate (a := R) (b := R + 1) (by linarith)
  obtain ⟨b, hb, hbsafe⟩ := exists_suzukiXiCarrier_safe_coordinate
    (a := 0) (b := min delta (1 / 2)) (lt_min hdelta (by norm_num))
  obtain ⟨u, hu, husafe⟩ := exists_suzukiXiCarrier_safe_coordinate (a := R) (b := R + 1) (by linarith)
  have hbdelta := hb.2.trans_le (min_le_left _ _)
  have hbhalf := hb.2.trans_le (min_le_right _ _)
  refine ⟨l, r, b, u, ⟨by linarith [hl.2, hr.1], by linarith [hu.1], ?_⟩,
    hl, hr, ⟨hb.1, hbdelta, hbhalf⟩, hu⟩
  intro c hc
  exact ⟨(hlsafe c hc).1, (hrsafe c hc).1, (hbsafe c hc).2, (husafe c hc).2⟩

end
end RiemannGaussian
