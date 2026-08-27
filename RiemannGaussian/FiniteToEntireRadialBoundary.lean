import RiemannGaussian.FiniteToEntireBoundaryLowerBound

/-!
# Quantitatively separated expanding spectral circles

The fixed-height rectangles used for local divisor comparisons do not send
every unused polynomial root to infinity.  This file replaces them with
genuinely expanding circles.  In each radial unit interval it selects a
radius separated from the norm of every spectral xi zero by an explicit
positive amount.  Consequently every point on the selected circle is
uniformly separated from the full zero set.
-/

open Complex Filter MeromorphicOn Metric Set Topology
open scoped Classical ComplexOrder Topology

namespace RiemannGaussian

noncomputable section

/-- The finitely many spectral zero radii relevant to the `n`th radial unit
interval, together with both endpoints. -/
noncomputable def spectralRadialBoundaryObstructions (n : ℕ) : Finset ℝ :=
  insert (n : ℝ) <|
    insert ((n : ℝ) + 1) <|
      (spectralZetaZeroWindow ((n : ℝ) + 1)).image
        (fun rho => ‖zetaSpectralCoordinate rho.1‖)

/-- Adding the two endpoints costs at most two elements beyond the finite
spectral zero window. -/
theorem spectralRadialBoundaryObstructions_card_le (n : ℕ) :
    (spectralRadialBoundaryObstructions n).card ≤
      (spectralZetaZeroWindow ((n : ℝ) + 1)).card + 2 := by
  classical
  unfold spectralRadialBoundaryObstructions
  have houter := Finset.card_insert_le (n : ℝ)
    (insert ((n : ℝ) + 1)
      ((spectralZetaZeroWindow ((n : ℝ) + 1)).image
        (fun rho => ‖zetaSpectralCoordinate rho.1‖)))
  have hinner := Finset.card_insert_le ((n : ℝ) + 1)
    ((spectralZetaZeroWindow ((n : ℝ) + 1)).image
      (fun rho => ‖zetaSpectralCoordinate rho.1‖))
  have himage := Finset.card_image_le
    (s := spectralZetaZeroWindow ((n : ℝ) + 1))
    (f := fun rho : NontrivialZetaZero =>
      ‖zetaSpectralCoordinate rho.1‖)
  omega

/-- Explicit radial separation delivered by the finite-set gap lemma. -/
noncomputable def spectralRadialBoundarySeparation (n : ℕ) : ℝ :=
  1 / (3 * (((spectralRadialBoundaryObstructions n).card : ℝ) + 2))

theorem spectralRadialBoundarySeparation_pos (n : ℕ) :
    0 < spectralRadialBoundarySeparation n := by
  unfold spectralRadialBoundarySeparation
  positivity

/-- Quadratic xi growth bounds the reciprocal radial separation by an
explicit quadratic expression. -/
theorem one_div_spectralRadialBoundarySeparation_le_of_growth
    {A : ℝ} (hA : 1 ≤ A)
    (hbound : ∀ z : ℂ,
      ‖riemannXi z‖ ≤ Real.exp (A * (‖z‖ + 1) ^ 2))
    (n : ℕ) :
    1 / spectralRadialBoundarySeparation n ≤
      3 *
        (A * (2 * ((n : ℝ) + 2) + 1) ^ 2 / Real.log 2 + 4) := by
  have hwindow := spectralZetaZeroWindow_card_le_of_growth hA
    (show 0 ≤ (n : ℝ) + 1 by positivity) hbound
  have hwindow' :
      ((spectralZetaZeroWindow ((n : ℝ) + 1)).card : ℝ) ≤
        A * (2 * ((n : ℝ) + 2) + 1) ^ 2 / Real.log 2 := by
    convert hwindow using 1
    ring
  have hobstructions :
      ((spectralRadialBoundaryObstructions n).card : ℝ) ≤
        ((spectralZetaZeroWindow ((n : ℝ) + 1)).card : ℝ) + 2 := by
    exact_mod_cast spectralRadialBoundaryObstructions_card_le n
  have hcard :
      ((spectralRadialBoundaryObstructions n).card : ℝ) + 2 ≤
        A * (2 * ((n : ℝ) + 2) + 1) ^ 2 / Real.log 2 + 4 := by
    linarith
  rw [show 1 / spectralRadialBoundarySeparation n =
      3 * (((spectralRadialBoundaryObstructions n).card : ℝ) + 2) by
    unfold spectralRadialBoundarySeparation
    field_simp]
  exact mul_le_mul_of_nonneg_left hcard (by norm_num)

/-- Every radial unit interval contains a radius separated from the norm of
every nontrivial spectral zero by the explicit positive radius above. -/
theorem exists_quantitativeSpectralRadialBoundary_between_nat (n : ℕ) :
    ∃ r : ℝ,
      (n : ℝ) < r ∧ r < (n : ℝ) + 1 ∧
        ∀ rho : NontrivialZetaZero,
          spectralRadialBoundarySeparation n ≤
            |r - ‖zetaSpectralCoordinate rho.1‖| := by
  let S := spectralRadialBoundaryObstructions n
  obtain ⟨r, hrlo, hrhi, hrsep⟩ :=
    exists_real_in_Ioo_avoiding_finset S
      (show (n : ℝ) < (n : ℝ) + 1 by linarith)
  have hscale :
      ((n : ℝ) + 1 - (n : ℝ)) /
          (3 * ((S.card : ℝ) + 2)) =
        spectralRadialBoundarySeparation n := by
    simp [S, spectralRadialBoundarySeparation]
  refine ⟨r, hrlo, hrhi, fun rho => ?_⟩
  by_cases hrhoWindow :
      |(zetaSpectralCoordinate rho.1).re| ≤ (n : ℝ) + 1
  · rw [← hscale]
    apply hrsep
    dsimp [S, spectralRadialBoundaryObstructions]
    simp only [Finset.mem_insert, Finset.mem_image]
    right
    right
    exact ⟨rho,
      (mem_spectralZetaZeroWindow (by positivity) rho).mpr hrhoWindow,
      rfl⟩
  · have hendpoint : spectralRadialBoundarySeparation n ≤
        |r - ((n : ℝ) + 1)| := by
      rw [← hscale]
      apply hrsep
      dsimp [S, spectralRadialBoundaryObstructions]
      simp
    have haboveRe : (n : ℝ) + 1 <
        |(zetaSpectralCoordinate rho.1).re| :=
      lt_of_not_ge hrhoWindow
    have haboveNorm : (n : ℝ) + 1 <
        ‖zetaSpectralCoordinate rho.1‖ :=
      haboveRe.trans_le (Complex.abs_re_le_norm _)
    rw [abs_of_nonpos (sub_nonpos.mpr hrhi.le)] at hendpoint
    rw [abs_of_nonpos (sub_nonpos.mpr (hrhi.le.trans haboveNorm.le))]
    linarith

/-- A fixed quantitative choice of one separated radius in each unit
interval. -/
noncomputable def quantitativeSpectralRadialBoundary (n : ℕ) : ℝ :=
  Classical.choose (exists_quantitativeSpectralRadialBoundary_between_nat n)

theorem quantitativeSpectralRadialBoundary_spec (n : ℕ) :
    (n : ℝ) < quantitativeSpectralRadialBoundary n ∧
      quantitativeSpectralRadialBoundary n < (n : ℝ) + 1 ∧
      ∀ rho : NontrivialZetaZero,
        spectralRadialBoundarySeparation n ≤
          |quantitativeSpectralRadialBoundary n -
            ‖zetaSpectralCoordinate rho.1‖| :=
  Classical.choose_spec
    (exists_quantitativeSpectralRadialBoundary_between_nat n)

theorem quantitativeSpectralRadialBoundary_pos (n : ℕ) :
    0 < quantitativeSpectralRadialBoundary n :=
  (Nat.cast_nonneg n).trans_lt
    (quantitativeSpectralRadialBoundary_spec n).1

/-- The selected radii tend to infinity. -/
theorem tendsto_quantitativeSpectralRadialBoundary_atTop :
    Tendsto quantitativeSpectralRadialBoundary atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro B
  obtain ⟨n, hn⟩ := exists_nat_ge B
  refine ⟨n, fun m hnm => ?_⟩
  have hcast : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
  exact hn.trans
    (hcast.trans (quantitativeSpectralRadialBoundary_spec m).1.le)

/-- Every point on a selected circle stays at least the explicit separation
radius from every spectral xi zero. -/
theorem quantitativeSpectralRadialBoundary_dist_zero_ge
    (n : ℕ) {w : ℂ}
    (hw : ‖w‖ = quantitativeSpectralRadialBoundary n)
    (rho : NontrivialZetaZero) :
    spectralRadialBoundarySeparation n ≤
      ‖w - zetaSpectralCoordinate rho.1‖ := by
  calc
    spectralRadialBoundarySeparation n ≤
        |quantitativeSpectralRadialBoundary n -
          ‖zetaSpectralCoordinate rho.1‖| :=
      (quantitativeSpectralRadialBoundary_spec n).2.2 rho
    _ = |‖w‖ - ‖zetaSpectralCoordinate rho.1‖| := by rw [hw]
    _ ≤ ‖w - zetaSpectralCoordinate rho.1‖ := by
      rw [abs_le]
      constructor
      · have h := norm_sub_norm_le (zetaSpectralCoordinate rho.1) w
        rw [norm_sub_rev] at h
        linarith
      · exact norm_sub_norm_le _ _

/-- Spectral xi is nonzero on every selected radial circle. -/
theorem riemannXiSpectral_ne_zero_on_quantitativeRadialBoundary
    (n : ℕ) {w : ℂ}
    (hw : ‖w‖ = quantitativeSpectralRadialBoundary n) :
    riemannXiSpectral w ≠ 0 := by
  intro hzero
  obtain ⟨rho, hrho⟩ :=
    (riemannXiSpectral_eq_zero_iff_exists_zetaZero w).mp hzero
  have hsep := quantitativeSpectralRadialBoundary_dist_zero_ge n hw rho
  rw [hrho, sub_self, norm_zero] at hsep
  exact (not_lt_of_ge hsep) (spectralRadialBoundarySeparation_pos n)

/-- A selected spectral circle maps into the inner quarter of its enclosing
canonical xi disk. -/
theorem norm_completedSpectralCoordinate_radial_le_quarter
    (n : ℕ) {w : ℂ}
    (hw : ‖w‖ = quantitativeSpectralRadialBoundary n) :
    ‖completedSpectralCoordinate w‖ ≤ xiCanonicalRadius n / 4 := by
  have hrhi : quantitativeSpectralRadialBoundary n < (n : ℝ) + 1 :=
    (quantitativeSpectralRadialBoundary_spec n).2.1
  have hRquarter : (n : ℝ) + 3 < xiCanonicalRadius n / 4 := by
    have hR := (xiCanonicalRadius_spec n).1
    linarith
  apply le_of_lt
  calc
    ‖completedSpectralCoordinate w‖ =
        ‖(1 / 2 : ℂ) + Complex.I * w‖ := by
      rfl
    _ ≤ ‖(1 / 2 : ℂ)‖ + ‖Complex.I * w‖ := norm_add_le _ _
    _ = (1 : ℝ) / 2 + ‖w‖ := by simp
    _ < (n : ℝ) + 3 := by rw [hw]; linarith
    _ < xiCanonicalRadius n / 4 := hRquarter

/-- Radial separation transfers isometrically to the completed coordinate
used by `riemannXi`. -/
theorem spectralRadialBoundarySeparation_le_norm_completedCoordinate_sub_zero
    (n : ℕ) {w i : ℂ}
    (hw : ‖w‖ = quantitativeSpectralRadialBoundary n)
    (hi : divisor riemannXi (ball 0 (xiCanonicalRadius n)) i ≠ 0) :
    spectralRadialBoundarySeparation n ≤
      ‖completedSpectralCoordinate w - i‖ := by
  let rho : NontrivialZetaZero :=
    ⟨i, (riemannXi_eq_zero_iff_isNontrivialZetaZero i).mp
      (riemannXi_eq_zero_of_divisor_ball_ne_zero hi)⟩
  calc
    spectralRadialBoundarySeparation n ≤
        ‖w - zetaSpectralCoordinate rho.1‖ :=
      quantitativeSpectralRadialBoundary_dist_zero_ge n hw rho
    _ = ‖completedSpectralCoordinate w - i‖ := by
      symm
      exact norm_completedSpectralCoordinate_sub w i

/-- The canonical lower exponent specialized to the separated radial
circles. -/
noncomputable def xiQuantitativeRadialBoundaryLowerExponent
    (A : ℝ) (n : ℕ) : ℝ :=
  2 * A * (xiCanonicalRadius n + 1) ^ 2 +
    (A * (2 * xiCanonicalRadius n + 1) ^ 2 / Real.log 2) *
      Real.log
        (1 + 2 * xiCanonicalRadius n /
          spectralRadialBoundarySeparation n)

/-- The canonical factorization lower bound controls spectral xi uniformly
on the entire selected circle. -/
theorem exp_neg_xiQuantitativeRadialBoundaryLowerExponent_le_norm_riemannXiSpectral
    {A : ℝ} (hA : 1 ≤ A)
    (hbound : ∀ u : ℂ,
      ‖riemannXi u‖ ≤ Real.exp (A * (‖u‖ + 1) ^ 2))
    (n : ℕ) {w : ℂ}
    (hw : ‖w‖ = quantitativeSpectralRadialBoundary n) :
    Real.exp (-xiQuantitativeRadialBoundaryLowerExponent A n) ≤
      ‖riemannXiSpectral w‖ := by
  let s : ℂ := completedSpectralCoordinate w
  have hspec : riemannXiSpectral w ≠ 0 :=
    riemannXiSpectral_ne_zero_on_quantitativeRadialBoundary n hw
  have hxi : riemannXi s ≠ 0 := by
    simpa [riemannXiSpectral, s] using hspec
  have hlower := exp_neg_xiCanonicalLowerExponent_le_norm_riemannXi
    hA hbound n (z := s) (delta := spectralRadialBoundarySeparation n)
      (spectralRadialBoundarySeparation_pos n)
      (by simpa [s] using
        norm_completedSpectralCoordinate_radial_le_quarter n hw)
      hxi
      (fun i hi => by
        simpa [s] using
          spectralRadialBoundarySeparation_le_norm_completedCoordinate_sub_zero
            n hw hi)
  simpa [xiQuantitativeRadialBoundaryLowerExponent, riemannXiSpectral,
    s] using hlower

/-- A generic exponential majorant for the canonical inner-quarter
logarithmic-derivative expression.  It only assumes that the observation
scale exceeds `n` and that the reciprocal zero separation has the quadratic
bound supplied by the finite-set construction. -/
theorem canonicalInnerQuarterBound_le_exponential
    {A T delta : ℝ} (hA : 1 ≤ A) (n : ℕ)
    (hTlo : (n : ℝ) < T) (hdelta : 0 < delta)
    (hsepRaw : 1 / delta ≤
      3 *
        (A * (2 * ((n : ℝ) + 2) + 1) ^ 2 / Real.log 2 + 4)) :
    (2 * (A * (xiCanonicalRadius n + 1) ^ 2)) /
          (xiCanonicalRadius n / 4) +
        (A * (2 * xiCanonicalRadius n + 1) ^ 2 / Real.log 2) *
          (2 / xiCanonicalRadius n + 1 / delta) ≤
      (392 * A + 729 * (A / Real.log 2) *
          (13 + 75 * (A / Real.log 2))) *
        Real.exp (4 * T) := by
  let R := xiCanonicalRadius n
  let E := Real.exp T
  let B := A / Real.log 2
  let X := 2 * ((n : ℝ) + 2) + 1
  have hA0 : 0 ≤ A := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hT0 : 0 ≤ T := (Nat.cast_nonneg n).trans hTlo.le
  have hEpos : 0 < E := by dsimp [E]; positivity
  have hEone : 1 ≤ E := by
    dsimp [E]
    exact Real.one_le_exp hT0
  have hE2one : 1 ≤ E ^ 2 := by nlinarith [sq_nonneg (E - 1)]
  have hE2nonneg : 0 ≤ E ^ 2 := sq_nonneg E
  have hE2E4 : E ^ 2 ≤ E ^ 4 := by
    calc
      E ^ 2 = E ^ 2 * 1 := by ring
      _ ≤ E ^ 2 * E ^ 2 :=
        mul_le_mul_of_nonneg_left hE2one hE2nonneg
      _ = E ^ 4 := by ring
  have hTexp : T + 1 ≤ E := by
    simpa [E] using Real.add_one_le_exp T
  have hR : 0 < R := xiCanonicalRadius_pos n
  have hRupper : R ≤ 4 * T + 13 := by
    have hr := (xiCanonicalRadius_spec n).2.1
    dsimp [R]
    linarith
  have hRfour : 1 ≤ R / 4 := by
    have hr := (xiCanonicalRadius_spec n).1
    have hn : 0 ≤ (n : ℝ) := by positivity
    dsimp [R]
    linarith
  have hR1 : R + 1 ≤ 14 * E := by
    calc
      R + 1 ≤ 4 * T + 14 := by linarith
      _ ≤ 14 * (T + 1) := by linarith
      _ ≤ 14 * E := mul_le_mul_of_nonneg_left hTexp (by norm_num)
  have htwoR1 : 2 * R + 1 ≤ 27 * E := by
    calc
      2 * R + 1 ≤ 8 * T + 27 := by linarith
      _ ≤ 27 * (T + 1) := by linarith
      _ ≤ 27 * E := mul_le_mul_of_nonneg_left hTexp (by norm_num)
  have hX0 : 0 ≤ X := by dsimp [X]; positivity
  have hX : X ≤ 5 * E := by
    calc
      X ≤ 2 * T + 5 := by
        dsimp [X]
        linarith
      _ ≤ 5 * (T + 1) := by linarith
      _ ≤ 5 * E := mul_le_mul_of_nonneg_left hTexp (by norm_num)
  have hR1sq : (R + 1) ^ 2 ≤ (14 * E) ^ 2 :=
    (sq_le_sq₀ (by positivity) (by positivity)).mpr hR1
  have htwoR1sq : (2 * R + 1) ^ 2 ≤ (27 * E) ^ 2 :=
    (sq_le_sq₀ (by positivity) (by positivity)).mpr htwoR1
  have hXsq : X ^ 2 ≤ (5 * E) ^ 2 :=
    (sq_le_sq₀ hX0 (by positivity)).mpr hX
  have hresidual :
      (2 * (A * (R + 1) ^ 2)) / (R / 4) ≤
        392 * A * E ^ 2 := by
    let N := 2 * (A * (R + 1) ^ 2)
    have hN : 0 ≤ N := by dsimp [N]; positivity
    calc
      (2 * (A * (R + 1) ^ 2)) / (R / 4) = N / (R / 4) := rfl
      _ ≤ N := (div_le_iff₀ (by positivity : 0 < R / 4)).mpr (by
        calc
          N = N * 1 := by ring
          _ ≤ N * (R / 4) := mul_le_mul_of_nonneg_left hRfour hN)
      _ ≤ 2 * A * (14 * E) ^ 2 := by
        dsimp [N]
        calc
          2 * (A * (R + 1) ^ 2) = (2 * A) * (R + 1) ^ 2 := by ring
          _ ≤ (2 * A) * (14 * E) ^ 2 :=
            mul_le_mul_of_nonneg_left hR1sq (by positivity)
          _ = 2 * A * (14 * E) ^ 2 := by ring
      _ = 392 * A * E ^ 2 := by ring
  have hcountFactor :
      A * (2 * R + 1) ^ 2 / Real.log 2 ≤
        729 * B * E ^ 2 := by
    calc
      A * (2 * R + 1) ^ 2 / Real.log 2 =
          B * (2 * R + 1) ^ 2 := by dsimp [B]; ring
      _ ≤ B * (27 * E) ^ 2 :=
        mul_le_mul_of_nonneg_left htwoR1sq hB
      _ = 729 * B * E ^ 2 := by ring
  have hsep :
      1 / delta ≤ 3 * (25 * B * E ^ 2 + 4) := by
    calc
      1 / delta ≤ 3 * (A * X ^ 2 / Real.log 2 + 4) := by
        simpa [X] using hsepRaw
      _ = 3 * (B * X ^ 2 + 4) := by dsimp [B]; ring
      _ ≤ 3 * (B * (5 * E) ^ 2 + 4) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact add_le_add (mul_le_mul_of_nonneg_left hXsq hB) le_rfl
      _ = 3 * (25 * B * E ^ 2 + 4) := by ring
  have htwoDiv : 2 / R ≤ 1 :=
    (div_le_one hR).mpr (by linarith)
  have hsecond :
      2 / R + 1 / delta ≤ (13 + 75 * B) * E ^ 2 := by
    calc
      2 / R + 1 / delta ≤
          1 + 3 * (25 * B * E ^ 2 + 4) :=
        add_le_add htwoDiv hsep
      _ = 13 + 75 * B * E ^ 2 := by ring
      _ ≤ 13 * E ^ 2 + 75 * B * E ^ 2 := by
        have h13 : 13 ≤ 13 * E ^ 2 := by nlinarith
        exact add_le_add h13 le_rfl
      _ = (13 + 75 * B) * E ^ 2 := by ring
  have hcanonical :
      (A * (2 * R + 1) ^ 2 / Real.log 2) *
          (2 / R + 1 / delta) ≤
        729 * B * (13 + 75 * B) * E ^ 4 := by
    have hsecond0 : 0 ≤ 2 / R + 1 / delta := by positivity
    calc
      (A * (2 * R + 1) ^ 2 / Real.log 2) *
          (2 / R + 1 / delta) ≤
          (729 * B * E ^ 2) * ((13 + 75 * B) * E ^ 2) :=
        mul_le_mul hcountFactor hsecond hsecond0 (by positivity)
      _ = 729 * B * (13 + 75 * B) * E ^ 4 := by ring
  have hpoly :
      (2 * (A * (R + 1) ^ 2)) / (R / 4) +
          (A * (2 * R + 1) ^ 2 / Real.log 2) *
            (2 / R + 1 / delta) ≤
        (392 * A + 729 * B * (13 + 75 * B)) * E ^ 4 := by
    calc
      (2 * (A * (R + 1) ^ 2)) / (R / 4) +
          (A * (2 * R + 1) ^ 2 / Real.log 2) *
            (2 / R + 1 / delta) ≤
          392 * A * E ^ 2 +
            729 * B * (13 + 75 * B) * E ^ 4 :=
        add_le_add hresidual hcanonical
      _ ≤ 392 * A * E ^ 4 +
          729 * B * (13 + 75 * B) * E ^ 4 := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hE2E4 (by positivity)) le_rfl
      _ = (392 * A + 729 * B * (13 + 75 * B)) * E ^ 4 := by ring
  have hEpow : E ^ 4 = Real.exp (4 * T) := by
    simpa [E] using (Real.exp_nat_mul T 4).symm
  simpa [R, B, hEpow] using hpoly

/-- The canonical inner-quarter expression has the same explicit
single-exponential majorant along the selected radial circles. -/
theorem radialCanonicalInnerQuarterBound_le_exponential
    {A : ℝ} (hA : 1 ≤ A)
    (hbound : ∀ z : ℂ,
      ‖riemannXi z‖ ≤ Real.exp (A * (‖z‖ + 1) ^ 2))
    (n : ℕ) :
    (2 * (A * (xiCanonicalRadius n + 1) ^ 2)) /
          (xiCanonicalRadius n / 4) +
        (A * (2 * xiCanonicalRadius n + 1) ^ 2 / Real.log 2) *
          (2 / xiCanonicalRadius n +
            1 / spectralRadialBoundarySeparation n) ≤
      (392 * A + 729 * (A / Real.log 2) *
          (13 + 75 * (A / Real.log 2))) *
        Real.exp (4 * quantitativeSpectralRadialBoundary n) := by
  exact canonicalInnerQuarterBound_le_exponential hA n
    (quantitativeSpectralRadialBoundary_spec n).1
    (spectralRadialBoundarySeparation_pos n)
    (one_div_spectralRadialBoundarySeparation_le_of_growth hA hbound n)

/-- The radial canonical lower exponent has a coarse explicit
single-exponential majorant. -/
theorem xiQuantitativeRadialBoundaryLowerExponent_le_exponential
    {A : ℝ} (hA : 1 ≤ A)
    (hbound : ∀ w : ℂ,
      ‖riemannXi w‖ ≤ Real.exp (A * (‖w‖ + 1) ^ 2))
    (n : ℕ) :
    xiQuantitativeRadialBoundaryLowerExponent A n ≤
      26 * (392 * A + 729 * (A / Real.log 2) *
        (13 + 75 * (A / Real.log 2))) *
          Real.exp (5 * quantitativeSpectralRadialBoundary n) := by
  let R : ℝ := xiCanonicalRadius n
  let delta : ℝ := spectralRadialBoundarySeparation n
  let r : ℝ := quantitativeSpectralRadialBoundary n
  let count : ℝ := A * (2 * R + 1) ^ 2 / Real.log 2
  let residual : ℝ := (2 * (A * (R + 1) ^ 2)) / (R / 4)
  let canonical : ℝ := count * (2 / R + 1 / delta)
  let Q : ℝ := 392 * A + 729 * (A / Real.log 2) *
    (13 + 75 * (A / Real.log 2))
  have hR : 0 < R := by simpa [R] using xiCanonicalRadius_pos n
  have hdelta : 0 < delta := by
    simpa [delta] using spectralRadialBoundarySeparation_pos n
  have hcount0 : 0 ≤ count := by
    dsimp only [count]
    positivity
  have hQ0 : 0 ≤ Q := by
    dsimp only [Q]
    positivity
  have hlog :
      Real.log (1 + 2 * R / delta) ≤ 2 * R / delta := by
    have harg : 0 < 1 + 2 * R / delta := by positivity
    simpa using Real.log_le_sub_one_of_pos harg
  have hresidualScale :
      2 * A * (R + 1) ^ 2 ≤ 2 * R * residual := by
    have hterm : 0 ≤ 2 * A * (R + 1) ^ 2 := by positivity
    calc
      2 * A * (R + 1) ^ 2 ≤
          8 * (2 * A * (R + 1) ^ 2) := by
        nlinarith
      _ = 2 * R * residual := by
        dsimp only [residual]
        field_simp [hR.ne']
        all_goals ring
  have hinner :
      2 * R / delta ≤ 2 * R * (2 / R + 1 / delta) := by
    calc
      2 * R / delta ≤ 4 + 2 * R / delta := by linarith
      _ = 2 * R * (2 / R + 1 / delta) := by
        field_simp [hR.ne', hdelta.ne']
        all_goals ring
  have hcanonicalScale :
      count * Real.log (1 + 2 * R / delta) ≤
        2 * R * canonical := by
    calc
      count * Real.log (1 + 2 * R / delta) ≤
          count * (2 * R / delta) :=
        mul_le_mul_of_nonneg_left hlog hcount0
      _ ≤ count * (2 * R * (2 / R + 1 / delta)) :=
        mul_le_mul_of_nonneg_left hinner hcount0
      _ = 2 * R * canonical := by simp [canonical]; ring
  have hexponentScale :
      xiQuantitativeRadialBoundaryLowerExponent A n ≤
        2 * R * (residual + canonical) := by
    calc
      xiQuantitativeRadialBoundaryLowerExponent A n =
          2 * A * (R + 1) ^ 2 +
            count * Real.log (1 + 2 * R / delta) := by
        rfl
      _ ≤ 2 * R * residual + 2 * R * canonical :=
        add_le_add hresidualScale hcanonicalScale
      _ = 2 * R * (residual + canonical) := by ring
  have htotal : residual + canonical ≤ Q * Real.exp (4 * r) := by
    simpa [R, delta, r, count, residual, canonical, Q] using
      radialCanonicalInnerQuarterBound_le_exponential hA hbound n
  have hr0 : 0 ≤ r := by
    simpa [r] using (quantitativeSpectralRadialBoundary_pos n).le
  have hRupper : R ≤ 4 * r + 13 := by
    have hRraw := (xiCanonicalRadius_spec n).2.1
    have hrraw := (quantitativeSpectralRadialBoundary_spec n).1
    dsimp only [R, r]
    linarith
  have hRexp : R ≤ 13 * Real.exp r := by
    calc
      R ≤ 4 * r + 13 := hRupper
      _ ≤ 13 * (r + 1) := by linarith
      _ ≤ 13 * Real.exp r :=
        mul_le_mul_of_nonneg_left (Real.add_one_le_exp r) (by norm_num)
  have hexpMul :
      Real.exp r * Real.exp (4 * r) = Real.exp (5 * r) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    xiQuantitativeRadialBoundaryLowerExponent A n ≤
        2 * R * (residual + canonical) := hexponentScale
    _ ≤ 2 * R * (Q * Real.exp (4 * r)) :=
      mul_le_mul_of_nonneg_left htotal (by positivity)
    _ ≤ 2 * (13 * Real.exp r) * (Q * Real.exp (4 * r)) := by
      gcongr
    _ = 26 * Q * Real.exp (5 * r) := by rw [← hexpMul]; ring
    _ = 26 * (392 * A + 729 * (A / Real.log 2) *
        (13 + 75 * (A / Real.log 2))) *
          Real.exp (5 * quantitativeSpectralRadialBoundary n) := by
      rfl

/-- One positive constant gives a uniform double-exponential modulus floor
on every selected expanding spectral circle. -/
theorem exists_riemannXiSpectral_quantitativeRadialBoundary_lower_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) {w : ℂ},
      ‖w‖ = quantitativeSpectralRadialBoundary n →
      Real.exp
          (-C * Real.exp
            (5 * quantitativeSpectralRadialBoundary n)) ≤
        ‖riemannXiSpectral w‖ := by
  obtain ⟨A, hA, hbound⟩ := riemannXi_quadraticGrowth
  let C : ℝ := 26 * (392 * A + 729 * (A / Real.log 2) *
    (13 + 75 * (A / Real.log 2)))
  have hC : 0 < C := by
    dsimp only [C]
    have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
    positivity
  refine ⟨C, hC, ?_⟩
  intro n w hw
  have hexponent :=
    xiQuantitativeRadialBoundaryLowerExponent_le_exponential
      hA hbound n
  have hlower :=
    exp_neg_xiQuantitativeRadialBoundaryLowerExponent_le_norm_riemannXiSpectral
      hA hbound n hw
  calc
    Real.exp
        (-C * Real.exp
          (5 * quantitativeSpectralRadialBoundary n)) ≤
      Real.exp (-xiQuantitativeRadialBoundaryLowerExponent A n) := by
        apply Real.exp_le_exp.mpr
        have hneg := neg_le_neg hexponent
        simpa [C] using hneg
    _ ≤ ‖riemannXiSpectral w‖ := hlower

end

end RiemannGaussian
