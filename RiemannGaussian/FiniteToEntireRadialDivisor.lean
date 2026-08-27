import RiemannGaussian.FiniteToEntireBoundedHeat
import RiemannGaussian.FiniteToEntireRouche

/-!
# Finite spectral-xi divisors in radial disks

The genuine spectral-xi divisor in a bounded radial disk is finite: it is a
subfamily of the existing finite spectral window.  This file identifies that
subfamily exactly and constructs synchronized, pairwise-disjoint isolating
balls around all of its zeros.  Every isolating ball stays strictly inside
the prescribed radial disk, and locally uniform polynomial approximants have
the genuine analytic multiplicity in every ball simultaneously.
-/

open Complex Filter Metric Polynomial Set
open scoped Classical Topology

namespace RiemannGaussian

noncomputable section

/-- The finite family of nontrivial zeta zeros whose spectral coordinates
lie in the open disk of radius `R`. -/
noncomputable def spectralZetaZeroRadialWindow
    (R : ℝ) : Finset NontrivialZetaZero :=
  (spectralZetaZeroWindow R).filter fun rho ↦
    ‖zetaSpectralCoordinate rho.1‖ < R

@[simp]
theorem mem_spectralZetaZeroRadialWindow
    {R : ℝ} (hR : 0 ≤ R) (rho : NontrivialZetaZero) :
    rho ∈ spectralZetaZeroRadialWindow R ↔
      ‖zetaSpectralCoordinate rho.1‖ < R := by
  rw [spectralZetaZeroRadialWindow, Finset.mem_filter]
  constructor
  · exact fun hrho ↦ hrho.2
  · intro hrho
    refine ⟨(mem_spectralZetaZeroWindow hR rho).mpr ?_, hrho⟩
    exact (Complex.abs_re_le_norm _).trans hrho.le

/-- The zeros of spectral xi in an open radial disk are exactly the spectral
coordinates indexed by the finite radial window. -/
theorem riemannXiSpectral_zero_in_ball_iff_exists_radialWindow
    {R : ℝ} (hR : 0 ≤ R) (w : ℂ) :
    w ∈ ball 0 R ∧ riemannXiSpectral w = 0 ↔
      ∃ rho ∈ spectralZetaZeroRadialWindow R,
        w = zetaSpectralCoordinate rho.1 := by
  constructor
  · rintro ⟨hw, hwzero⟩
    obtain ⟨rho, rfl⟩ :=
      (riemannXiSpectral_eq_zero_iff_exists_zetaZero w).mp hwzero
    refine ⟨rho, (mem_spectralZetaZeroRadialWindow hR rho).mpr ?_, rfl⟩
    simpa [mem_ball, dist_zero_right] using hw
  · rintro ⟨rho, hrho, rfl⟩
    constructor
    · simpa [mem_ball, dist_zero_right] using
        (mem_spectralZetaZeroRadialWindow hR rho).mp hrho
    · exact (riemannXiSpectral_eq_zero_iff_exists_zetaZero _).mpr
        ⟨rho, rfl⟩

/-- The genuine analytic multiplicity of the spectral-xi divisor in the
open disk of radius `R`. -/
noncomputable def riemannXiSpectralRadialDivisorCount (R : ℝ) : ℕ :=
  ∑ rho ∈ spectralZetaZeroRadialWindow R,
    analyticZetaZeroMultiplicity rho

/-- A closed ball whose radius is smaller than the radial clearance of its
center lies in the prescribed open disk. -/
theorem closedBall_subset_ball_zero_of_lt_sub_norm
    {c : ℂ} {r R : ℝ} (hr : r < R - ‖c‖) :
    closedBall c r ⊆ ball 0 R := by
  intro w hw
  rw [mem_closedBall] at hw
  rw [mem_ball, dist_zero_right]
  calc
    ‖w‖ = dist w 0 := (dist_zero_right w).symm
    _ ≤ dist w c + dist c 0 := dist_triangle _ _ _
    _ ≤ r + ‖c‖ := by
      rw [dist_zero_right]
      simpa [dist_comm] using add_le_add_right hw ‖c‖
    _ < R := by linarith

/-- All genuine spectral-xi zeros in a radial disk have synchronized,
pairwise-disjoint isolating balls that remain inside that disk.  Every
locally uniform real-polynomial approximation has the exact analytic
multiplicity in all of those balls eventually. -/
theorem exists_pairwiseDisjoint_insideBall_simultaneous_radialRootCounts
    {ι : Type*} {phi : Filter ι} [phi.NeBot] [phi.IsCountablyGenerated]
    (A : ι → ℝ[X])
    (hA : TendstoLocallyUniformlyOn
      (fun n w ↦ ((A n).map Complex.ofRealHom).eval w)
      riemannXiSpectral phi Set.univ)
    {R : ℝ} (hR : 0 < R) :
    let S := spectralZetaZeroRadialWindow R
    ∃ r : S → ℝ,
      (∀ rho : S, 0 < r rho ∧
        (∀ w ∈ closedBall
            (zetaSpectralCoordinate rho.1.1) (r rho),
          w ≠ zetaSpectralCoordinate rho.1.1 →
            riemannXiSpectral w ≠ 0) ∧
        closedBall (zetaSpectralCoordinate rho.1.1) (r rho) ⊆
          ball 0 R) ∧
      (Set.univ : Set S).PairwiseDisjoint (fun rho : S ↦
        closedBall (zetaSpectralCoordinate rho.1.1) (r rho)) ∧
      ∀ᶠ n in phi, ∀ rho : S,
        realPolynomialRootCountInBall (A n)
          (zetaSpectralCoordinate rho.1.1) (r rho) =
            analyticZetaZeroMultiplicity rho.1 := by
  dsimp only
  let S := spectralZetaZeroRadialWindow R
  let center : S → ℂ := fun rho ↦ zetaSpectralCoordinate rho.1.1
  have hcenterInj : Function.Injective center := by
    intro rho sigma hcenter
    apply Subtype.ext
    apply Subtype.ext
    exact zetaSpectralCoordinate_injective hcenter
  obtain ⟨U, hU, hUdisjoint⟩ :=
    (Set.finite_range center).t2_separation
  have hexBall (rho : S) :
      ∃ d : ℝ, 0 < d ∧ ball (center rho) d ⊆ U (center rho) := by
    exact (Metric.isOpen_iff.mp (hU (center rho)).2)
      (center rho) (hU (center rho)).1
  choose d hd hball using hexBall
  have hclearance (rho : S) : 0 < R - ‖center rho‖ := by
    apply sub_pos.mpr
    exact (mem_spectralZetaZeroRadialWindow hR.le rho.1).mp rho.2
  let bound : S → ℝ := fun rho ↦ min (d rho) (R - ‖center rho‖)
  have hbound (rho : S) : 0 < bound rho := by
    exact lt_min (hd rho) (hclearance rho)
  obtain ⟨r, hr, hcount⟩ :=
    exists_simultaneous_riemannXiSpectral_localRootCounts
      A hA S bound hbound
  refine ⟨r, ?_, ?_, hcount⟩
  · intro rho
    refine ⟨(hr rho).1, (hr rho).2.2, ?_⟩
    apply closedBall_subset_ball_zero_of_lt_sub_norm
    exact (hr rho).2.1.trans_le (min_le_right _ _)
  · intro rho _ sigma _ hrs
    have hcenters : center rho ≠ center sigma :=
      hcenterInj.ne hrs
    have hdisjoint : Disjoint (U (center rho)) (U (center sigma)) :=
      hUdisjoint (Set.mem_range_self rho) (Set.mem_range_self sigma)
        hcenters
    apply hdisjoint.mono
    · exact (closedBall_subset_ball
        ((hr rho).2.1.trans_le (min_le_left _ _))).trans (hball rho)
    · exact (closedBall_subset_ball
        ((hr sigma).2.1.trans_le (min_le_left _ _))).trans (hball sigma)

end

end RiemannGaussian
