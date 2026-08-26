import RiemannGaussian.GaussianXiDivisorContour

/-!
# Quantitatively separated xi contours

The finite divisor theorem only needs a vertical side that contains no xi
zero.  Bounds for the logarithmic derivative need more: the side must stay a
controlled positive distance from every zero.  This file begins that
quantitative refinement by proving an elementary finite-set gap lemma and
using it to select one uniformly described vertical line in every unit height
interval.
-/

namespace RiemannGaussian

noncomputable section

open Filter MeromorphicOn Set
open scoped Topology

/-! ## An elementary quantitative finite-set gap -/

/-- Inside any nonempty real interval there is a point whose distance from a
given finite set is bounded below explicitly in terms of the set's cardinality.

The proof samples `s.card + 1` equally spaced candidates.  If every candidate
were closer than one third of the spacing to `s`, nearest-point choices would
give an injection from a type of cardinality `s.card + 1` into one of
cardinality `s.card`. -/
theorem exists_real_in_Ioo_avoiding_finset
    (s : Finset ℝ) {a b : ℝ} (hab : a < b) :
    ∃ x : ℝ, a < x ∧ x < b ∧
      ∀ y ∈ s,
        (b - a) / (3 * ((s.card : ℝ) + 2)) ≤ |x - y| := by
  classical
  let q : ℝ := (b - a) / ((s.card : ℝ) + 2)
  have hden : 0 < (s.card : ℝ) + 2 := by positivity
  have hq : 0 < q := div_pos (sub_pos.mpr hab) hden
  have hqden : q * ((s.card : ℝ) + 2) = b - a := by
    dsimp [q]
    field_simp
  let candidate : Fin (s.card + 1) → ℝ := fun i =>
    a + ((i.1 : ℝ) + 1) * q
  have hcandidate_lo (i : Fin (s.card + 1)) :
      a < candidate i := by
    dsimp [candidate]
    have hi : 0 < (i.1 : ℝ) + 1 := by positivity
    nlinarith [mul_pos hi hq]
  have hcandidate_hi (i : Fin (s.card + 1)) :
      candidate i < b := by
    have hiNat : i.1 + 1 < s.card + 2 := by omega
    have hi : (i.1 : ℝ) + 1 < (s.card : ℝ) + 2 := by
      exact_mod_cast hiNat
    have hmul := mul_lt_mul_of_pos_right hi hq
    dsimp [candidate]
    nlinarith [hqden]
  have hcandidate_sep {i j : Fin (s.card + 1)} (hij : i ≠ j) :
      q ≤ |candidate i - candidate j| := by
    have hijval : i.1 ≠ j.1 := Fin.val_ne_of_ne hij
    have hz : (i.1 : ℤ) - (j.1 : ℤ) ≠ 0 := sub_ne_zero.mpr (by
      exact_mod_cast hijval)
    have honeInt : (1 : ℤ) ≤ |(i.1 : ℤ) - (j.1 : ℤ)| :=
      Int.one_le_abs hz
    have hone : (1 : ℝ) ≤ |(i.1 : ℝ) - (j.1 : ℝ)| := by
      exact_mod_cast honeInt
    calc
      q ≤ |(i.1 : ℝ) - (j.1 : ℝ)| * q := by
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right hone hq.le
      _ = |candidate i - candidate j| := by
        dsimp [candidate]
        rw [show
          (a + ((i.1 : ℝ) + 1) * q) -
              (a + ((j.1 : ℝ) + 1) * q) =
            ((i.1 : ℝ) - (j.1 : ℝ)) * q by ring,
          abs_mul, abs_of_pos hq]
  by_contra hresult
  push Not at hresult
  have hnear : ∀ i : Fin (s.card + 1),
      ∃ y : ℝ, y ∈ s ∧ |candidate i - y| < q / 3 := by
    intro i
    obtain ⟨y, hy, hdist⟩ := hresult (candidate i)
      (hcandidate_lo i) (hcandidate_hi i)
    refine ⟨y, hy, ?_⟩
    have hscale :
        (b - a) / (3 * ((s.card : ℝ) + 2)) = q / 3 := by
      dsimp [q]
      field_simp
    rw [← hscale]
    exact hdist
  let picked : Fin (s.card + 1) → ℝ := fun i =>
    Classical.choose (hnear i)
  have hpicked_mem (i : Fin (s.card + 1)) : picked i ∈ s :=
    (Classical.choose_spec (hnear i)).1
  have hpicked_dist (i : Fin (s.card + 1)) :
      |candidate i - picked i| < q / 3 :=
    (Classical.choose_spec (hnear i)).2
  let f : Fin (s.card + 1) → {y : ℝ // y ∈ s} := fun i =>
    ⟨picked i, hpicked_mem i⟩
  have hf : Function.Injective f := by
    intro i j hfij
    by_contra hij
    have hsep := hcandidate_sep hij
    have hpick : picked i = picked j := congrArg Subtype.val hfij
    have htri := abs_sub_le (candidate i) (picked i) (candidate j)
    have hsecond : |picked i - candidate j| < q / 3 := by
      rw [abs_sub_comm, hpick]
      exact hpicked_dist j
    nlinarith [hpicked_dist i]
  have hcard := Fintype.card_le_of_injective f hf
  simp at hcard

/-! ## Quantitative spectral truncations -/

/-- The finitely many zero ordinates relevant to the `n`th unit interval,
together with both endpoints.  Including the upper endpoint controls zeros
just beyond the finite window as well as zeros inside it. -/
noncomputable def spectralBoundaryObstructions (n : ℕ) : Finset ℝ :=
  insert (n : ℝ) <|
    insert ((n : ℝ) + 1) <|
      (spectralZetaZeroWindow ((n : ℝ) + 1)).image
        (fun ρ => |(zetaSpectralCoordinate ρ.1).re|)

/-- The number of distinct zeros in a spectral window is bounded by the xi
divisor in the corresponding centered complex ball. -/
theorem spectralZetaZeroWindow_card_le_riemannXi_divisor
    {T : ℝ} (hT : 0 ≤ T) :
    ((spectralZetaZeroWindow T).card : ℝ) ≤
      ((∑ᶠ u,
        divisor riemannXi (Metric.closedBall 0 (T + 1)) u : ℤ) : ℝ) := by
  classical
  let S := spectralZetaZeroWindow T
  have hSinBall : ∀ ρ ∈ S, ‖(ρ.1 : ℂ)‖ ≤ T + 1 := by
    intro ρ hρ
    have hwindow : |(zetaSpectralCoordinate ρ.1).re| ≤ T :=
      (mem_spectralZetaZeroWindow hT ρ).mp hρ
    have hnorm := Complex.norm_le_abs_re_add_abs_im ρ.1
    have hre : |ρ.1.re| < 1 := by
      rw [abs_of_pos (NontrivialZetaZero.zero_lt_re ρ)]
      exact NontrivialZetaZero.re_lt_one ρ
    have him : |ρ.1.im| ≤ T := by
      simpa only [zetaSpectralCoordinate_re] using hwindow
    linarith
  calc
    ((spectralZetaZeroWindow T).card : ℝ) =
        ∑ ρ ∈ S, (1 : ℝ) := by simp [S]
    _ ≤ ∑ ρ ∈ S, (analyticZetaZeroMultiplicity ρ : ℝ) := by
      apply Finset.sum_le_sum
      intro ρ _
      exact_mod_cast analyticZetaZeroMultiplicity_positive ρ
    _ ≤ ((∑ᶠ u,
        divisor riemannXi (Metric.closedBall 0 (T + 1)) u : ℤ) : ℝ) :=
      sum_analyticZetaZeroMultiplicity_le_riemannXi_divisor S hSinBall

/-- Quadratic xi growth gives a concrete quadratic upper bound for the
number of distinct zeros in every nonnegative spectral window. -/
theorem spectralZetaZeroWindow_card_le_of_growth
    {A T : ℝ} (hA : 1 ≤ A) (hT : 0 ≤ T)
    (hbound : ∀ z : ℂ,
      ‖riemannXi z‖ ≤ Real.exp (A * (‖z‖ + 1) ^ 2)) :
    ((spectralZetaZeroWindow T).card : ℝ) ≤
      A * (2 * (T + 1) + 1) ^ 2 / Real.log 2 := by
  exact (spectralZetaZeroWindow_card_le_riemannXi_divisor hT).trans
    (jensen_riemannXi_divisor_le hA (by linarith) hbound)

/-- Adding two endpoints and then forgetting duplicate zero ordinates costs
at most two elements beyond the distinct-zero window cardinality. -/
theorem spectralBoundaryObstructions_card_le (n : ℕ) :
    (spectralBoundaryObstructions n).card ≤
      (spectralZetaZeroWindow ((n : ℝ) + 1)).card + 2 := by
  classical
  unfold spectralBoundaryObstructions
  have houter := Finset.card_insert_le (n : ℝ)
    (insert ((n : ℝ) + 1)
      ((spectralZetaZeroWindow ((n : ℝ) + 1)).image
        (fun ρ => |(zetaSpectralCoordinate ρ.1).re|)))
  have hinner := Finset.card_insert_le ((n : ℝ) + 1)
    ((spectralZetaZeroWindow ((n : ℝ) + 1)).image
      (fun ρ => |(zetaSpectralCoordinate ρ.1).re|))
  have himage := Finset.card_image_le
    (s := spectralZetaZeroWindow ((n : ℝ) + 1))
    (f := fun ρ : NontrivialZetaZero =>
      |(zetaSpectralCoordinate ρ.1).re|)
  omega

/-- Explicit separation radius delivered by the finite-set gap lemma. -/
noncomputable def spectralBoundarySeparation (n : ℕ) : ℝ :=
  1 / (3 * (((spectralBoundaryObstructions n).card : ℝ) + 2))

theorem spectralBoundarySeparation_pos (n : ℕ) :
    0 < spectralBoundarySeparation n := by
  unfold spectralBoundarySeparation
  positivity

/-- The already-proved xi quadratic growth bounds the reciprocal separation
radius by an explicit quadratic expression. -/
theorem one_div_spectralBoundarySeparation_le_of_growth
    {A : ℝ} (hA : 1 ≤ A)
    (hbound : ∀ z : ℂ,
      ‖riemannXi z‖ ≤ Real.exp (A * (‖z‖ + 1) ^ 2))
    (n : ℕ) :
    1 / spectralBoundarySeparation n ≤
      3 *
        (A * (2 * ((n : ℝ) + 2) + 1) ^ 2 / Real.log 2 + 4) := by
  have hwindow := spectralZetaZeroWindow_card_le_of_growth hA
    (show 0 ≤ (n : ℝ) + 1 by positivity) hbound
  have hwindow' :
      ((spectralZetaZeroWindow ((n : ℝ) + 1)).card : ℝ) ≤
        A * (2 * ((n : ℝ) + 2) + 1) ^ 2 / Real.log 2 := by
    convert hwindow using 1 <;> ring
  have hobstructions :
      ((spectralBoundaryObstructions n).card : ℝ) ≤
        ((spectralZetaZeroWindow ((n : ℝ) + 1)).card : ℝ) + 2 := by
    exact_mod_cast spectralBoundaryObstructions_card_le n
  have hcard :
      ((spectralBoundaryObstructions n).card : ℝ) + 2 ≤
        A * (2 * ((n : ℝ) + 2) + 1) ^ 2 / Real.log 2 + 4 := by
    linarith
  rw [show 1 / spectralBoundarySeparation n =
      3 * (((spectralBoundaryObstructions n).card : ℝ) + 2) by
    unfold spectralBoundarySeparation
    field_simp]
  exact mul_le_mul_of_nonneg_left hcard (by norm_num)

/-- Unconditionally, one fixed quadratic majorant controls all reciprocal
separation radii. -/
theorem exists_one_div_spectralBoundarySeparation_quadratic_bound :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ n : ℕ,
      1 / spectralBoundarySeparation n ≤
        3 *
          (A * (2 * ((n : ℝ) + 2) + 1) ^ 2 / Real.log 2 + 4) := by
  rcases riemannXi_quadraticGrowth with ⟨A, hA, hbound⟩
  exact ⟨A, hA,
    one_div_spectralBoundarySeparation_le_of_growth hA hbound⟩

/-- Every unit interval contains a vertical line separated from every
nontrivial zeta zero by the explicit positive radius above. -/
theorem exists_quantitativeSpectralBoundary_between_nat (n : ℕ) :
    ∃ T : ℝ,
      (n : ℝ) < T ∧ T < (n : ℝ) + 1 ∧
        ∀ ρ : NontrivialZetaZero,
          spectralBoundarySeparation n ≤
            abs (T - abs (zetaSpectralCoordinate ρ.1).re) := by
  let S := spectralBoundaryObstructions n
  obtain ⟨T, hTlo, hThi, hTsep⟩ :=
    exists_real_in_Ioo_avoiding_finset S
      (show (n : ℝ) < (n : ℝ) + 1 by linarith)
  have hscale :
      ((n : ℝ) + 1 - (n : ℝ)) /
          (3 * ((S.card : ℝ) + 2)) =
        spectralBoundarySeparation n := by
    simp [S, spectralBoundarySeparation]
  refine ⟨T, hTlo, hThi, fun ρ => ?_⟩
  by_cases hρwindow :
      |(zetaSpectralCoordinate ρ.1).re| ≤ (n : ℝ) + 1
  · rw [← hscale]
    apply hTsep
    dsimp [S, spectralBoundaryObstructions]
    simp only [Finset.mem_insert, Finset.mem_image]
    right
    right
    exact ⟨ρ,
      (mem_spectralZetaZeroWindow (by positivity) ρ).mpr hρwindow,
      rfl⟩
  · have hendpoint : spectralBoundarySeparation n ≤
        |T - ((n : ℝ) + 1)| := by
      rw [← hscale]
      apply hTsep
      dsimp [S, spectralBoundaryObstructions]
      simp
    have hρabove : (n : ℝ) + 1 <
        |(zetaSpectralCoordinate ρ.1).re| := lt_of_not_ge hρwindow
    rw [abs_of_nonpos (sub_nonpos.mpr hThi.le)] at hendpoint
    rw [abs_of_nonpos (sub_nonpos.mpr (hThi.le.trans hρabove.le))]
    linarith

/-- A fixed quantitative choice of one separated contour per unit interval. -/
noncomputable def quantitativeSpectralBoundaryTruncation (n : ℕ) : ℝ :=
  Classical.choose (exists_quantitativeSpectralBoundary_between_nat n)

theorem quantitativeSpectralBoundaryTruncation_spec (n : ℕ) :
    (n : ℝ) < quantitativeSpectralBoundaryTruncation n ∧
      quantitativeSpectralBoundaryTruncation n < (n : ℝ) + 1 ∧
      ∀ ρ : NontrivialZetaZero,
        spectralBoundarySeparation n ≤
          abs (quantitativeSpectralBoundaryTruncation n -
            abs (zetaSpectralCoordinate ρ.1).re) :=
  Classical.choose_spec (exists_quantitativeSpectralBoundary_between_nat n)

theorem quantitativeSpectralBoundaryTruncation_zeroFree
    (n : ℕ) (ρ : NontrivialZetaZero) :
    |(zetaSpectralCoordinate ρ.1).re| ≠
      quantitativeSpectralBoundaryTruncation n := by
  intro hρ
  have hsep := (quantitativeSpectralBoundaryTruncation_spec n).2.2 ρ
  rw [hρ, sub_self, abs_zero] at hsep
  exact (not_lt_of_ge hsep) (spectralBoundarySeparation_pos n)

/-- Every point on the selected vertical segment stays at least the explicit
separation radius from every spectral xi zero.  Only the real coordinate is
needed, so the estimate is uniform for all vertical parameters `y`. -/
theorem quantitativeSpectralBoundaryTruncation_dist_zero_ge
    (n : ℕ) (y : ℝ) (ρ : NontrivialZetaZero) :
    spectralBoundarySeparation n ≤
      ‖((quantitativeSpectralBoundaryTruncation n : ℂ) +
          (y : ℂ) * Complex.I) - zetaSpectralCoordinate ρ.1‖ := by
  let T := quantitativeSpectralBoundaryTruncation n
  let z := zetaSpectralCoordinate ρ.1
  have hTnonneg : 0 ≤ T :=
    (Nat.cast_nonneg n).trans
      (quantitativeSpectralBoundaryTruncation_spec n).1.le
  have hsep : spectralBoundarySeparation n ≤
      abs (T - abs z.re) := by
    simpa [T, z] using
      (quantitativeSpectralBoundaryTruncation_spec n).2.2 ρ
  have habs : abs (T - abs z.re) ≤ abs (T - z.re) := by
    simpa [abs_of_nonneg hTnonneg] using
      (abs_abs_sub_abs_le T z.re)
  calc
    spectralBoundarySeparation n ≤ abs (T - abs z.re) := hsep
    _ ≤ abs (T - z.re) := habs
    _ = abs ((((T : ℂ) + (y : ℂ) * Complex.I) - z).re) := by
      simp [T, z]
    _ ≤ ‖((T : ℂ) + (y : ℂ) * Complex.I) - z‖ :=
      Complex.abs_re_le_norm _

theorem tendsto_quantitativeSpectralBoundaryTruncation_atTop :
    Tendsto quantitativeSpectralBoundaryTruncation atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro B
  obtain ⟨n, hn⟩ := exists_nat_ge B
  refine ⟨n, fun m hnm => ?_⟩
  have hcast : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
  exact hn.trans
    (hcast.trans (quantitativeSpectralBoundaryTruncation_spec m).1.le)

/-- A logarithmic-derivative bound on the quantitatively separated contours
is enough to inhabit the generic exponential-bound interface. -/
theorem xiSpectralVerticalLogDerivativeExponentialBound_of_quantitative
    {C A : ℝ} (hC : 0 ≤ C)
    (hlog : ∀ (n : ℕ) (y : ℝ), -1 ≤ y → y ≤ 1 →
      ‖xiSpectralNegativeLogDerivative
          ((quantitativeSpectralBoundaryTruncation n : ℂ) +
            (y : ℂ) * Complex.I)‖ ≤
        C * Real.exp
          (A * quantitativeSpectralBoundaryTruncation n)) :
    XiSpectralVerticalLogDerivativeExponentialBound := by
  refine ⟨quantitativeSpectralBoundaryTruncation,
    tendsto_quantitativeSpectralBoundaryTruncation_atTop, ?_, ?_,
    C, A, hC, hlog⟩
  · intro n
    exact (Nat.cast_nonneg n).trans
      (quantitativeSpectralBoundaryTruncation_spec n).1.le
  · exact quantitativeSpectralBoundaryTruncation_zeroFree

end

end RiemannGaussian
