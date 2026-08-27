import RiemannGaussian.GaussianXiLogDerivativeGrowth

/-!
# Quantitative lower bounds on expanding spectral-xi boundaries

Zero-free contours alone do not suffice for a stage-dependent Rouché
argument: the polynomial approximation error must be strictly smaller than
the modulus of spectral xi along the same expanding boundary.  This file
derives the required modulus floor from previously checked contour data.

Inside a large canonical circle, xi is decomposed into its finite zero divisor
and a zero-free analytic residual.  Borel--Carathéodory controls the logarithm
of the residual, quantitative contour separation bounds every canonical
factor, and Jensen's theorem bounds their total multiplicity.  The resulting
estimate is transferred to all four sides of the canonical expanding spectral
rectangle.  For one constant `C > 0`, Lean proves the uniform lower bound

`exp (-C * exp (5 * T_n)) ≤ ‖riemannXiSpectral w‖`

at every boundary point `w`, where `T_n` is the quantitative zero-free
truncation.  This explicit scale can be compared directly with rapidly
reindexed Taylor, root-pinning, and separability errors.
-/

open Complex Filter MeromorphicOn Metric Set Topology
open scoped Classical ComplexOrder Topology

namespace RiemannGaussian

noncomputable section

/-- A canonical factor evaluated in the inner quarter-disk is bounded by its
distance from the corresponding divisor point. -/
lemma norm_canonicalFactor_le_of_inner_of_separated
    {R delta : ℝ} (hR : 0 < R) (hdelta : 0 < delta)
    {i z : ℂ} (hi : i ∈ ball 0 R) (hz : ‖z‖ ≤ R / 4)
    (hsep : delta ≤ ‖z - i‖) :
    ‖Complex.canonicalFactor R i z‖ ≤ 2 * R / delta := by
  have hiNorm : ‖i‖ < R := by
    simpa [mem_ball, dist_zero_right] using hi
  have hzNorm : ‖z‖ < R := hz.trans_lt (by linarith)
  have hnum : ‖(R : ℂ) ^ 2 - starRingEnd ℂ i * z‖ ≤ 2 * R ^ 2 := by
    calc
      ‖(R : ℂ) ^ 2 - starRingEnd ℂ i * z‖ ≤
          ‖(R : ℂ) ^ 2‖ + ‖starRingEnd ℂ i * z‖ := norm_sub_le _ _
      _ = R ^ 2 + ‖i‖ * ‖z‖ := by simp [abs_of_pos hR]
      _ ≤ 2 * R ^ 2 := by nlinarith [norm_nonneg i, norm_nonneg z]
  rw [Complex.canonicalFactor_apply, norm_div, norm_mul]
  simp only [norm_real]
  calc
    ‖(R : ℂ) ^ 2 - starRingEnd ℂ i * z‖ /
          (|R| * ‖z - i‖) ≤
        (2 * R ^ 2) / (R * delta) := by
      rw [abs_of_pos hR]
      exact div_le_div₀ (by positivity) hnum (mul_pos hR hdelta)
        (mul_le_mul_of_nonneg_left hsep hR.le)
    _ = 2 * R / delta := by field_simp

/-- A finitely supported real sum with nonnegative integer weights is bounded
by the total weight times a common pointwise upper bound. -/
lemma finsum_intCast_mul_le_of_nonneg
    {ι : Type*} {d : ι → ℤ} {f : ι → ℝ}
    (hd : (Function.support d).Finite)
    (hdnonneg : ∀ i, 0 ≤ d i) {C : ℝ}
    (hf : ∀ i, d i ≠ 0 → f i ≤ C) :
    (∑ᶠ i, ((d i : ℤ) : ℝ) * f i) ≤
      ((∑ᶠ i, d i : ℤ) : ℝ) * C := by
  classical
  have hsub : Function.support (fun i ↦ ((d i : ℤ) : ℝ) * f i) ⊆
      hd.toFinset := by
    intro i hi
    apply hd.mem_toFinset.mpr
    intro hdi
    apply hi
    simp [hdi]
  rw [finsum_eq_sum_of_support_subset _ hsub]
  calc
    ∑ i ∈ hd.toFinset, ((d i : ℤ) : ℝ) * f i ≤
        ∑ i ∈ hd.toFinset, ((d i : ℤ) : ℝ) * C := by
      apply Finset.sum_le_sum
      intro i hi
      by_cases hdi : d i = 0
      · simp [hdi]
      · exact mul_le_mul_of_nonneg_left (hf i hdi) (by
          exact_mod_cast hdnonneg i)
    _ = (∑ i ∈ hd.toFinset, ((d i : ℤ) : ℝ)) * C := by
      rw [Finset.sum_mul]
    _ = (∑ᶠ i, ((d i : ℤ) : ℝ)) * C := by
      congr 1
      symm
      exact finsum_eq_sum_of_support_subset _ (by
        intro i hi
        apply hd.mem_toFinset.mpr
        intro hdi
        apply hi
        simp [hdi])
    _ = ((∑ᶠ i, d i : ℤ) : ℝ) * C := by
      congr 1
      exact (map_finsum (Int.castRingHom ℝ) hd).symm

/-- Canonical decomposition gives a quantitative lower bound for xi at an
inner point separated from every zero in the enclosing divisor. -/
theorem exp_neg_xiCanonicalLowerExponent_le_norm_riemannXi
    {A : ℝ} (hA : 1 ≤ A)
    (hbound : ∀ w : ℂ,
      ‖riemannXi w‖ ≤ Real.exp (A * (‖w‖ + 1) ^ 2))
    (n : ℕ) {z : ℂ} {delta : ℝ} (hdelta : 0 < delta)
    (hz : ‖z‖ ≤ xiCanonicalRadius n / 4)
    (hxi : riemannXi z ≠ 0)
    (hsep : ∀ i,
      divisor riemannXi (ball 0 (xiCanonicalRadius n)) i ≠ 0 →
        delta ≤ ‖z - i‖) :
    Real.exp (- (
        2 * A * (xiCanonicalRadius n + 1) ^ 2 +
        (A * (2 * xiCanonicalRadius n + 1) ^ 2 / Real.log 2) *
          Real.log (1 + 2 * xiCanonicalRadius n / delta))) ≤
      ‖riemannXi z‖ := by
  let R : ℝ := xiCanonicalRadius n
  let g : ℂ → ℂ := riemannXiCanonicalResidual n
  let L : ℂ → ℂ := riemannXiCanonicalLog n
  let d : ℂ → ℤ := fun i ↦ divisor riemannXi (ball 0 R) i
  let C : ℝ := Real.log (1 + 2 * R / delta)
  let M : ℝ := 2 * A * (R + 1) ^ 2
  let N : ℝ := (A * (2 * R + 1) ^ 2 / Real.log 2) * C
  have hR : 0 < R := by simpa [R] using xiCanonicalRadius_pos n
  have hzball : z ∈ ball 0 R := by
    rw [mem_ball, dist_zero_right]
    exact hz.trans_lt (by dsimp only [R] at hz ⊢; linarith)
  have hzclosed : z ∈ closedBall 0 R := ball_subset_closedBall hzball
  have hLraw := norm_riemannXiCanonicalLog_le_of_growth
    hA hbound n hzball
  have hden : 0 < R - ‖z‖ := by
    have hz' : ‖z‖ ≤ R / 4 := by simpa [R] using hz
    linarith
  have hratio : ‖z‖ / (R - ‖z‖) ≤ 1 := by
    rw [div_le_one hden]
    have hz' : ‖z‖ ≤ R / 4 := by simpa [R] using hz
    linarith
  have hL : ‖L z‖ ≤ M := by
    calc
      ‖L z‖ ≤ 2 * (A * (R + 1) ^ 2) * ‖z‖ /
          (R - ‖z‖) := by simpa [L, R] using hLraw
      _ = (2 * A * (R + 1) ^ 2) *
          (‖z‖ / (R - ‖z‖)) := by ring
      _ ≤ (2 * A * (R + 1) ^ 2) * 1 := by
        exact mul_le_mul_of_nonneg_left hratio (by positivity)
      _ = M := by simp [M]
  have hnormResidual := congrArg norm
    (exp_riemannXiCanonicalLog_mul_zero_eq n hzball)
  have hnormResidual' :
      Real.exp (L z).re * ‖g 0‖ = ‖g z‖ := by
    simpa [L, g, norm_mul, Complex.norm_exp] using hnormResidual
  have hLre : -‖L z‖ ≤ (L z).re :=
    (abs_le.mp (Complex.abs_re_le_norm (L z))).1
  have hg0 : 1 ≤ ‖g 0‖ := by
    simpa [g] using one_le_norm_riemannXiCanonicalResidual_zero n
  have hexpResidual : Real.exp (-M) ≤ ‖g z‖ := by
    calc
      Real.exp (-M) ≤ Real.exp (-‖L z‖) :=
        Real.exp_le_exp.mpr (neg_le_neg hL)
      _ ≤ Real.exp (L z).re := Real.exp_le_exp.mpr hLre
      _ = Real.exp (L z).re * 1 := by ring
      _ ≤ Real.exp (L z).re * ‖g 0‖ :=
        mul_le_mul_of_nonneg_left hg0 (Real.exp_pos _).le
      _ = ‖g z‖ := hnormResidual'
  have hlogResidual : -M ≤ Real.log ‖g z‖ := by
    calc
      -M = Real.log (Real.exp (-M)) := by rw [Real.log_exp]
      _ ≤ Real.log ‖g z‖ :=
        Real.log_le_log (Real.exp_pos _) hexpResidual
  have hdFinite : (Function.support d).Finite := by
    simpa [d, R] using
      (riemannXiCanonicalResidual_decomp n).meromorphicOn.divisor_ball_support_finite
  have hdnonneg : ∀ i, 0 ≤ d i := by
    intro i
    exact (analyticOnNhd_riemannXi.mono (subset_univ _)).divisor_nonneg i
  have hC : 0 ≤ C := by
    apply Real.log_nonneg
    have hquot : 0 ≤ 2 * R / delta := by positivity
    linarith
  have hfactorLog : ∀ i, d i ≠ 0 →
      Real.log ‖Complex.canonicalFactor R i z‖ ≤ C := by
    intro i hi
    have hiBall : i ∈ ball 0 R :=
      (divisor riemannXi (ball 0 R)).supportWithinDomain
        (by simpa [d] using hi)
    have hsepi : delta ≤ ‖z - i‖ := by
      apply hsep i
      simpa [d, R] using hi
    have hfactor := norm_canonicalFactor_le_of_inner_of_separated
      hR hdelta hiBall (by simpa [R] using hz) hsepi
    have hzi : z ≠ i := by
      intro hzi
      subst i
      simpa using (hdelta.trans_le hsepi).ne'
    have hfactorPos : 0 < ‖Complex.canonicalFactor R i z‖ :=
      norm_pos_iff.mpr
        (Complex.canonicalFactor_ne_zero hiBall hzclosed hzi)
    apply Real.log_le_log hfactorPos
    exact hfactor.trans (by linarith)
  have hcanonicalRaw := finsum_intCast_mul_le_of_nonneg
    hdFinite hdnonneg hfactorLog
  have hcount := sum_divisor_riemannXi_ball_le_of_growth hA hbound n
  have hcanonical :
      (∑ᶠ i, ((d i : ℤ) : ℝ) *
        Real.log ‖Complex.canonicalFactor R i z‖) ≤ N := by
    calc
      (∑ᶠ i, ((d i : ℤ) : ℝ) *
          Real.log ‖Complex.canonicalFactor R i z‖) ≤
        ((∑ᶠ i, d i : ℤ) : ℝ) * C := hcanonicalRaw
      _ ≤ (A * (2 * R + 1) ^ 2 / Real.log 2) * C := by
        apply mul_le_mul_of_nonneg_right
        · simpa [d, R] using hcount
        · exact hC
      _ = N := by rfl
  have horder : meromorphicOrderAt riemannXi z = 0 :=
    (analyticAt_riemannXi z).meromorphicNFAt
      |>.meromorphicOrderAt_eq_zero_iff.mpr hxi
  have hlog := (riemannXiCanonicalResidual_decomp n).log_norm_eq
    hzclosed horder hR
  have hsphereSum :
      (∑ᶠ i : ℂ,
        ((divisor riemannXi (sphere 0 R) i : ℤ) : ℝ) *
          Real.log ‖z - i‖) = 0 := by
    rw [show divisor riemannXi (sphere 0 R) = 0 by
      simpa [R] using
        divisor_riemannXi_sphere_xiCanonicalRadius_eq_zero n]
    exact finsum_eq_zero_of_forall_eq_zero (fun i ↦ by simp)
  have htrailing : meromorphicTrailingCoeffAt riemannXi z = riemannXi z :=
    (analyticAt_riemannXi z).meromorphicTrailingCoeffAt_of_ne_zero hxi
  change Real.log ‖g z‖ = _ at hlog
  rw [hsphereSum, htrailing] at hlog
  simp only [sub_zero] at hlog
  have hlogXi : Real.log ‖riemannXi z‖ =
      Real.log ‖g z‖ -
        (∑ᶠ i, ((d i : ℤ) : ℝ) *
          Real.log ‖Complex.canonicalFactor R i z‖) := by
    change Real.log ‖g z‖ =
      (∑ᶠ i, ((d i : ℤ) : ℝ) *
        Real.log ‖Complex.canonicalFactor R i z‖) +
          Real.log ‖riemannXi z‖ at hlog
    linarith
  have hlowerLog : -(M + N) ≤ Real.log ‖riemannXi z‖ := by
    rw [hlogXi]
    linarith
  have hlower := Real.exp_le_exp.mpr hlowerLog
  rw [Real.exp_log (norm_pos_iff.mpr hxi)] at hlower
  simpa only [M, N, C, R, neg_add_rev] using hlower

/-- The explicit lower-modulus exponent on the quantitatively separated
spectral boundary. -/
noncomputable def xiQuantitativeBoundaryLowerExponent
    (A : ℝ) (n : ℕ) : ℝ :=
  2 * A * (xiCanonicalRadius n + 1) ^ 2 +
    (A * (2 * xiCanonicalRadius n + 1) ^ 2 / Real.log 2) *
      Real.log
        (1 + 2 * xiCanonicalRadius n / spectralBoundarySeparation n)

/-- The canonical lower exponent controls spectral xi uniformly along the
selected right vertical boundary. -/
theorem exp_neg_xiQuantitativeBoundaryLowerExponent_le_norm_riemannXiSpectral
    {A : ℝ} (hA : 1 ≤ A)
    (hbound : ∀ w : ℂ,
      ‖riemannXi w‖ ≤ Real.exp (A * (‖w‖ + 1) ^ 2))
    (n : ℕ) {y : ℝ} (hylo : -1 ≤ y) (hyhi : y ≤ 1) :
    Real.exp (-xiQuantitativeBoundaryLowerExponent A n) ≤
      ‖riemannXiSpectral
        ((quantitativeSpectralBoundaryTruncation n : ℂ) +
          (y : ℂ) * Complex.I)‖ := by
  let w : ℂ :=
    (quantitativeSpectralBoundaryTruncation n : ℂ) +
      (y : ℂ) * Complex.I
  let s : ℂ := completedSpectralCoordinate w
  have hlower := exp_neg_xiCanonicalLowerExponent_le_norm_riemannXi
    hA hbound n (z := s) (delta := spectralBoundarySeparation n)
      (spectralBoundarySeparation_pos n)
      (by simpa [s, w] using
        norm_quantitativeCompletedCoordinate_le_quarter n hylo hyhi)
      (by simpa [s, w] using
        riemannXi_quantitativeCompletedCoordinate_ne_zero n y)
      (fun i hi ↦ by
        simpa [s, w] using
          spectralBoundarySeparation_le_norm_completedCoordinate_sub_zero
            n y hi)
  simpa [xiQuantitativeBoundaryLowerExponent, riemannXiSpectral,
    s, w] using hlower

/-- The canonical lower exponent has a coarse but explicit single-exponential
majorant along the quantitative boundaries. -/
theorem xiQuantitativeBoundaryLowerExponent_le_exponential
    {A : ℝ} (hA : 1 ≤ A)
    (hbound : ∀ w : ℂ,
      ‖riemannXi w‖ ≤ Real.exp (A * (‖w‖ + 1) ^ 2))
    (n : ℕ) :
    xiQuantitativeBoundaryLowerExponent A n ≤
      26 * (392 * A + 729 * (A / Real.log 2) *
        (13 + 75 * (A / Real.log 2))) *
          Real.exp (5 * quantitativeSpectralBoundaryTruncation n) := by
  let R : ℝ := xiCanonicalRadius n
  let delta : ℝ := spectralBoundarySeparation n
  let T : ℝ := quantitativeSpectralBoundaryTruncation n
  let count : ℝ := A * (2 * R + 1) ^ 2 / Real.log 2
  let residual : ℝ := (2 * (A * (R + 1) ^ 2)) / (R / 4)
  let canonical : ℝ := count * (2 / R + 1 / delta)
  let Q : ℝ := 392 * A + 729 * (A / Real.log 2) *
    (13 + 75 * (A / Real.log 2))
  have hR : 0 < R := by simpa [R] using xiCanonicalRadius_pos n
  have hdelta : 0 < delta := by
    simpa [delta] using spectralBoundarySeparation_pos n
  have hA0 : 0 ≤ A := by linarith
  have hcount0 : 0 ≤ count := by
    dsimp only [count]
    positivity
  have hresidual0 : 0 ≤ residual := by
    dsimp only [residual]
    positivity
  have hcanonical0 : 0 ≤ canonical := by
    dsimp only [canonical]
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
      2 * A * (R + 1) ^ 2 ≤ 8 * (2 * A * (R + 1) ^ 2) := by
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
      xiQuantitativeBoundaryLowerExponent A n ≤
        2 * R * (residual + canonical) := by
    calc
      xiQuantitativeBoundaryLowerExponent A n =
          2 * A * (R + 1) ^ 2 +
            count * Real.log (1 + 2 * R / delta) := by
        rfl
      _ ≤ 2 * R * residual + 2 * R * canonical :=
        add_le_add hresidualScale hcanonicalScale
      _ = 2 * R * (residual + canonical) := by ring
  have htotal : residual + canonical ≤
      Q * Real.exp (4 * T) := by
    simpa [R, delta, T, count, residual, canonical, Q] using
      explicit_logDeriv_bound_le_exponential hA hbound n
  have hT0 : 0 ≤ T := by
    exact (Nat.cast_nonneg n).trans
      (by simpa [T] using
        (quantitativeSpectralBoundaryTruncation_spec n).1.le)
  have hRupper : R ≤ 4 * T + 13 := by
    have hr := (xiCanonicalRadius_spec n).2.1
    have ht := (quantitativeSpectralBoundaryTruncation_spec n).1
    dsimp only [R, T]
    linarith
  have hRexp : R ≤ 13 * Real.exp T := by
    calc
      R ≤ 4 * T + 13 := hRupper
      _ ≤ 13 * (T + 1) := by linarith
      _ ≤ 13 * Real.exp T :=
        mul_le_mul_of_nonneg_left (Real.add_one_le_exp T) (by norm_num)
  have hexpMul : Real.exp T * Real.exp (4 * T) = Real.exp (5 * T) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    xiQuantitativeBoundaryLowerExponent A n ≤
        2 * R * (residual + canonical) := hexponentScale
    _ ≤ 2 * R * (Q * Real.exp (4 * T)) :=
      mul_le_mul_of_nonneg_left htotal (by positivity)
    _ ≤ 2 * (13 * Real.exp T) * (Q * Real.exp (4 * T)) := by
      gcongr
    _ = 26 * Q * Real.exp (5 * T) := by rw [← hexpMul]; ring
    _ = 26 * (392 * A + 729 * (A / Real.log 2) *
        (13 + 75 * (A / Real.log 2))) *
          Real.exp (5 * quantitativeSpectralBoundaryTruncation n) := by
      rfl

/-- One positive constant gives a double-exponential modulus floor on every
selected right vertical spectral boundary. -/
theorem exists_riemannXiSpectral_quantitativeVerticalBoundary_lower_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) {y : ℝ}, -1 ≤ y → y ≤ 1 →
      Real.exp
          (-C * Real.exp
            (5 * quantitativeSpectralBoundaryTruncation n)) ≤
        ‖riemannXiSpectral
          ((quantitativeSpectralBoundaryTruncation n : ℂ) +
            (y : ℂ) * Complex.I)‖ := by
  obtain ⟨A, hA, hbound⟩ := riemannXi_quadraticGrowth
  let C : ℝ := 26 * (392 * A + 729 * (A / Real.log 2) *
    (13 + 75 * (A / Real.log 2)))
  have hC : 0 < C := by
    dsimp only [C]
    have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
    positivity
  refine ⟨C, hC, ?_⟩
  intro n y hylo hyhi
  have hexponent :=
    xiQuantitativeBoundaryLowerExponent_le_exponential
      hA hbound n
  have hlower :=
    exp_neg_xiQuantitativeBoundaryLowerExponent_le_norm_riemannXiSpectral
      hA hbound n hylo hyhi
  calc
    Real.exp
        (-C * Real.exp
          (5 * quantitativeSpectralBoundaryTruncation n)) ≤
      Real.exp (-xiQuantitativeBoundaryLowerExponent A n) := by
        apply Real.exp_le_exp.mpr
        have hneg := neg_le_neg hexponent
        simpa [C] using hneg
    _ ≤ ‖riemannXiSpectral
          ((quantitativeSpectralBoundaryTruncation n : ℂ) +
            (y : ℂ) * Complex.I)‖ := hlower

/-- The quantitative separation radius is at most one half. -/
theorem spectralBoundarySeparation_le_half (n : ℕ) :
    spectralBoundarySeparation n ≤ (1 : ℝ) / 2 := by
  rw [spectralBoundarySeparation]
  have hcard : 0 ≤ ((spectralBoundaryObstructions n).card : ℝ) := by
    positivity
  have hden : 0 < 3 * (((spectralBoundaryObstructions n).card : ℝ) + 2) := by
    positivity
  rw [div_le_iff₀ hden]
  nlinarith

/-- Every point on either horizontal side of the spectral rectangle lies in
the inner quarter of the corresponding canonical circle. -/
theorem norm_completedSpectralCoordinate_horizontal_le_quarter
    (n : ℕ) {x y : ℝ}
    (hx : |x| ≤ quantitativeSpectralBoundaryTruncation n)
    (hy : |y| = 1) :
    ‖completedSpectralCoordinate
        ((x : ℂ) + (y : ℂ) * Complex.I)‖ ≤
      xiCanonicalRadius n / 4 := by
  let w : ℂ := (x : ℂ) + (y : ℂ) * Complex.I
  let s : ℂ := completedSpectralCoordinate w
  let T : ℝ := quantitativeSpectralBoundaryTruncation n
  let R : ℝ := xiCanonicalRadius n
  have hsreEq : s.re = (1 : ℝ) / 2 - y := by
    dsimp [s, w, completedSpectralCoordinate]
    simp
    ring
  have hsre : |s.re| ≤ (3 : ℝ) / 2 := by
    calc
      |s.re| = |(1 : ℝ) / 2 - y| := by rw [hsreEq]
      _ ≤ |(1 : ℝ) / 2| + |y| := abs_sub _ _
      _ = (3 : ℝ) / 2 := by rw [hy]; norm_num
  have hsim : |s.im| ≤ T := by
    simpa [s, w, T, completedSpectralCoordinate] using hx
  have hTupper : T < (n : ℝ) + 1 := by
    simpa [T] using (quantitativeSpectralBoundaryTruncation_spec n).2.1
  have hRlower : (n : ℝ) + 3 < R / 4 := by
    have hraw := (xiCanonicalRadius_spec n).1
    dsimp only [R]
    linarith
  change ‖s‖ ≤ R / 4
  apply le_of_lt
  calc
    ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
    _ ≤ (3 : ℝ) / 2 + T := add_le_add hsre hsim
    _ < (n : ℝ) + 3 := by linarith
    _ < R / 4 := hRlower

/-- A horizontal boundary point at imaginary height one is separated from
every enclosed xi zero by at least the quantitative separation radius. -/
theorem spectralBoundarySeparation_le_norm_completedCoordinate_sub_zero_horizontal
    (n : ℕ) {x y : ℝ} (hy : |y| = 1) {i : ℂ}
    (hi : divisor riemannXi (ball 0 (xiCanonicalRadius n)) i ≠ 0) :
    spectralBoundarySeparation n ≤
      ‖completedSpectralCoordinate
          ((x : ℂ) + (y : ℂ) * Complex.I) - i‖ := by
  let w : ℂ := (x : ℂ) + (y : ℂ) * Complex.I
  have hzero : riemannXi i = 0 :=
    riemannXi_eq_zero_of_divisor_ball_ne_zero hi
  let rho : NontrivialZetaZero :=
    ⟨i, (riemannXi_eq_zero_iff_isNontrivialZetaZero i).mp hzero⟩
  have him : |(zetaSpectralCoordinate i).im| < (1 : ℝ) / 2 := by
    simpa [rho] using
      NontrivialZetaZero.abs_spectralCoordinate_im_lt_half rho
  have htriangle :
      1 ≤ |y - (zetaSpectralCoordinate i).im| +
        |(zetaSpectralCoordinate i).im| := by
    calc
      1 = |y| := hy.symm
      _ = |(y - (zetaSpectralCoordinate i).im) +
          (zetaSpectralCoordinate i).im| := by congr 1; ring
      _ ≤ |y - (zetaSpectralCoordinate i).im| +
          |(zetaSpectralCoordinate i).im| := abs_add_le _ _
  have hdiff :
      (1 : ℝ) / 2 < |y - (zetaSpectralCoordinate i).im| := by
    linarith
  calc
    spectralBoundarySeparation n ≤ (1 : ℝ) / 2 :=
      spectralBoundarySeparation_le_half n
    _ ≤ |y - (zetaSpectralCoordinate i).im| := hdiff.le
    _ = |(w - zetaSpectralCoordinate i).im| := by simp [w]
    _ ≤ ‖w - zetaSpectralCoordinate i‖ := Complex.abs_im_le_norm _
    _ = ‖completedSpectralCoordinate w - i‖ :=
      (norm_completedSpectralCoordinate_sub w i).symm

/-- The canonical lower exponent controls spectral xi uniformly along both
horizontal sides of the quantitative rectangle. -/
theorem exp_neg_xiQuantitativeBoundaryLowerExponent_le_norm_riemannXiSpectral_horizontal
    {A : ℝ} (hA : 1 ≤ A)
    (hbound : ∀ u : ℂ,
      ‖riemannXi u‖ ≤ Real.exp (A * (‖u‖ + 1) ^ 2))
    (n : ℕ) {x y : ℝ}
    (hx : |x| ≤ quantitativeSpectralBoundaryTruncation n)
    (hy : |y| = 1) :
    Real.exp (-xiQuantitativeBoundaryLowerExponent A n) ≤
      ‖riemannXiSpectral ((x : ℂ) + (y : ℂ) * Complex.I)‖ := by
  let w : ℂ := (x : ℂ) + (y : ℂ) * Complex.I
  let s : ℂ := completedSpectralCoordinate w
  have hspec : riemannXiSpectral w ≠ 0 := by
    intro hzero
    obtain ⟨rho, hw⟩ :=
      (riemannXiSpectral_eq_zero_iff_exists_zetaZero w).mp hzero
    have him := NontrivialZetaZero.abs_spectralCoordinate_im_lt_half rho
    have hwim : |w.im| = 1 := by simpa [w] using hy
    rw [hw] at hwim
    linarith
  have hxi : riemannXi s ≠ 0 := by
    simpa [riemannXiSpectral, s] using hspec
  have hlower := exp_neg_xiCanonicalLowerExponent_le_norm_riemannXi
    hA hbound n (z := s) (delta := spectralBoundarySeparation n)
      (spectralBoundarySeparation_pos n)
      (by simpa [s, w] using
        (norm_completedSpectralCoordinate_horizontal_le_quarter
          n (x := x) (y := y) hx hy))
      hxi
      (fun i hi ↦ by
        simpa [s, w] using
          (spectralBoundarySeparation_le_norm_completedCoordinate_sub_zero_horizontal
            n (x := x) (y := y) (i := i) hy hi))
  simpa [xiQuantitativeBoundaryLowerExponent, riemannXiSpectral,
    s, w] using hlower

/-- Boundary of the symmetric quantitative spectral rectangle with vertical
sides at the selected truncation and horizontal sides at imaginary height
one. -/
def quantitativeSpectralRectangleBoundary (n : ℕ) : Set ℂ :=
  {w | (|w.re| = quantitativeSpectralBoundaryTruncation n ∧ |w.im| ≤ 1) ∨
    (|w.re| ≤ quantitativeSpectralBoundaryTruncation n ∧ |w.im| = 1)}

/-- One positive constant gives a uniform double-exponential modulus floor on
all four sides of every expanding quantitative spectral rectangle. -/
theorem exists_riemannXiSpectral_quantitativeRectangleBoundary_lower_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) {w : ℂ},
      w ∈ quantitativeSpectralRectangleBoundary n →
      Real.exp
          (-C * Real.exp
            (5 * quantitativeSpectralBoundaryTruncation n)) ≤
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
  let T : ℝ := quantitativeSpectralBoundaryTruncation n
  have hT0 : 0 ≤ T := by
    exact (Nat.cast_nonneg n).trans
      (by simpa [T] using
        (quantitativeSpectralBoundaryTruncation_spec n).1.le)
  have hexponent :=
    xiQuantitativeBoundaryLowerExponent_le_exponential
      hA hbound n
  have hfloor :
      Real.exp (-C * Real.exp (5 * T)) ≤
        Real.exp (-xiQuantitativeBoundaryLowerExponent A n) := by
    apply Real.exp_le_exp.mpr
    have hneg := neg_le_neg hexponent
    simpa [C, T] using hneg
  have hwrepr : (w.re : ℂ) + (w.im : ℂ) * Complex.I = w := by
    apply Complex.ext <;> simp
  rcases hw with hvertical | hhorizontal
  · obtain ⟨hre, him⟩ := hvertical
    obtain ⟨himlo, himhi⟩ := abs_le.mp him
    rcases (abs_eq hT0).mp hre with hre | hre
    · have hpoint : (T : ℂ) + (w.im : ℂ) * Complex.I = w := by
        apply Complex.ext
        · simpa using hre.symm
        · simp
      have hraw :=
        exp_neg_xiQuantitativeBoundaryLowerExponent_le_norm_riemannXiSpectral
          hA hbound n himlo himhi
      rw [show quantitativeSpectralBoundaryTruncation n = T by rfl,
        hpoint] at hraw
      exact hfloor.trans hraw
    · have hpoint :
          (T : ℂ) + ((-w.im : ℝ) : ℂ) * Complex.I = -w := by
        apply Complex.ext
        · simp [hre]
        · simp
      have hraw :=
        exp_neg_xiQuantitativeBoundaryLowerExponent_le_norm_riemannXiSpectral
          hA hbound n (y := -w.im) (by linarith) (by linarith)
      rw [show quantitativeSpectralBoundaryTruncation n = T by rfl,
        hpoint] at hraw
      have heven : riemannXiSpectral (-w) = riemannXiSpectral w := by
        unfold riemannXiSpectral
        rw [completedSpectralCoordinate_neg, riemannXi_one_sub]
      rw [heven] at hraw
      exact hfloor.trans hraw
  · obtain ⟨hre, him⟩ := hhorizontal
    have hraw :=
      exp_neg_xiQuantitativeBoundaryLowerExponent_le_norm_riemannXiSpectral_horizontal
        hA hbound n (x := w.re) (y := w.im)
          (by simpa [T] using hre) him
    rw [hwrepr] at hraw
    exact hfloor.trans hraw

end

end RiemannGaussian
