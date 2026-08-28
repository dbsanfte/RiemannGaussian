import RiemannGaussian.RiemannXiSuzukiCarrierNevanlinnaGram

/-!
# Cayley-unitary realization of the Suzuki carrier features

The finite carrier measure turns every genuine xi-node into the rational
feature

`F_z(x) = (x - i) / (x - z)`.

This file puts all of those features into the resolvent geometry of one
operator.  Multiplication on `L²(μ)` by the real-boundary Cayley coordinate

`u(x) = (x - i) / (x + i)`

is constructed as a complex-linear isometric equivalence.  If

`a(z) = (z - i) / (z + i)`,

then every genuine node feature satisfies the exact operator equation

`U F_z - a(z) F_z = (1 - a(z)) U 1`.

The equation is also summed with the exact Suzuki normalization coefficients.
At a real node the underlying rational identity has one totalized collision;
the proof explicitly removes that singleton using the null-singleton property
of the finite carrier measure.

No approximation, tail vanishing, rigidity theorem, or RH conclusion is
asserted here.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ComplexConjugate ENNReal Topology lp

namespace RiemannGaussian

noncomputable section

/-- The unit-circle Cayley coordinate on the real boundary. -/
def suzukiXiCarrierCayleyBoundaryCoordinate (x : ℝ) : ℂ :=
  ((x : ℂ) - Complex.I) / ((x : ℂ) + Complex.I)

/-- The inverse boundary coordinate, written without conjugation so that its
measurability and multiplier action are transparent. -/
def suzukiXiCarrierCayleyBoundaryInverseCoordinate (x : ℝ) : ℂ :=
  ((x : ℂ) + Complex.I) / ((x : ℂ) - Complex.I)

/-- The disk coordinate associated with a nonexceptional spectral
parameter.  Division remains total at `z = -i`; genuine xi nodes are proved
below never to be exceptional. -/
def suzukiXiCarrierCayleyParameter (z : ℂ) : ℂ :=
  (z - Complex.I) / (z + Complex.I)

/-- The boundary Cayley coordinate is Borel measurable. -/
theorem measurable_suzukiXiCarrierCayleyBoundaryCoordinate :
    Measurable suzukiXiCarrierCayleyBoundaryCoordinate := by
  unfold suzukiXiCarrierCayleyBoundaryCoordinate
  exact (Complex.continuous_ofReal.measurable.sub measurable_const).div
    (Complex.continuous_ofReal.measurable.add measurable_const)

/-- The inverse boundary Cayley coordinate is Borel measurable. -/
theorem measurable_suzukiXiCarrierCayleyBoundaryInverseCoordinate :
    Measurable suzukiXiCarrierCayleyBoundaryInverseCoordinate := by
  unfold suzukiXiCarrierCayleyBoundaryInverseCoordinate
  exact (Complex.continuous_ofReal.measurable.add measurable_const).div
    (Complex.continuous_ofReal.measurable.sub measurable_const)

/-- The boundary Cayley coordinate has unit modulus at every real point. -/
@[simp] theorem norm_suzukiXiCarrierCayleyBoundaryCoordinate (x : ℝ) :
    ‖suzukiXiCarrierCayleyBoundaryCoordinate x‖ = 1 := by
  unfold suzukiXiCarrierCayleyBoundaryCoordinate
  have hden : (x : ℂ) + Complex.I ≠ 0 := by
    simpa [sub_eq_add_neg] using
      (ofReal_sub_ne_zero_of_im_ne_zero
        (z := -Complex.I) (by simp) x)
  have hconj :
      (x : ℂ) - Complex.I =
        starRingEnd ℂ ((x : ℂ) + Complex.I) := by
    simp only [map_add, Complex.conj_ofReal, Complex.conj_I,
      sub_eq_add_neg]
  rw [norm_div, hconj]
  have hnorm := RCLike.norm_conj ((x : ℂ) + Complex.I)
  rw [hnorm, div_self (norm_ne_zero_iff.mpr hden)]

/-- The inverse boundary Cayley coordinate also has unit modulus. -/
@[simp] theorem norm_suzukiXiCarrierCayleyBoundaryInverseCoordinate (x : ℝ) :
    ‖suzukiXiCarrierCayleyBoundaryInverseCoordinate x‖ = 1 := by
  unfold suzukiXiCarrierCayleyBoundaryInverseCoordinate
  have hden : (x : ℂ) - Complex.I ≠ 0 :=
    ofReal_sub_ne_zero_of_im_ne_zero (by simp) x
  have hconj :
      (x : ℂ) + Complex.I =
        starRingEnd ℂ ((x : ℂ) - Complex.I) := by
    simp
  rw [norm_div, hconj]
  have hnorm := RCLike.norm_conj ((x : ℂ) - Complex.I)
  rw [hnorm, div_self (norm_ne_zero_iff.mpr hden)]

/-- The two real-boundary Cayley coordinates are pointwise inverses. -/
@[simp] theorem suzukiXiCarrierCayleyBoundaryCoordinate_mul_inverse
    (x : ℝ) :
    suzukiXiCarrierCayleyBoundaryCoordinate x *
        suzukiXiCarrierCayleyBoundaryInverseCoordinate x = 1 := by
  unfold suzukiXiCarrierCayleyBoundaryCoordinate
    suzukiXiCarrierCayleyBoundaryInverseCoordinate
  have hminus : (x : ℂ) - Complex.I ≠ 0 :=
    ofReal_sub_ne_zero_of_im_ne_zero (by simp) x
  have hplus : (x : ℂ) + Complex.I ≠ 0 := by
    simpa [sub_eq_add_neg] using
      (ofReal_sub_ne_zero_of_im_ne_zero
        (z := -Complex.I) (by simp) x)
  field_simp [hminus, hplus]

/-- The inverse-first product is also one. -/
@[simp] theorem suzukiXiCarrierCayleyBoundaryInverseCoordinate_mul
    (x : ℝ) :
    suzukiXiCarrierCayleyBoundaryInverseCoordinate x *
        suzukiXiCarrierCayleyBoundaryCoordinate x = 1 := by
  rw [mul_comm, suzukiXiCarrierCayleyBoundaryCoordinate_mul_inverse]

/-- Multiplication by the unit-modulus Cayley boundary coordinate preserves
every `MemLp` class for the finite carrier measure. -/
theorem suzukiXiCarrierCayleyBoundaryCoordinate_mul_memLp
    {q : ℝ≥0∞} {f : ℝ → ℂ}
    (hf : MemLp f q suzukiXiCarrierNevanlinnaMeasure) :
    MemLp (fun x : ℝ ↦
      suzukiXiCarrierCayleyBoundaryCoordinate x * f x) q
      suzukiXiCarrierNevanlinnaMeasure := by
  apply hf.congr_norm
  · exact measurable_suzukiXiCarrierCayleyBoundaryCoordinate.aestronglyMeasurable.mul
      hf.aestronglyMeasurable
  · exact Eventually.of_forall fun x ↦ by simp

/-- Multiplication by the inverse unit-modulus boundary coordinate also
preserves every `MemLp` class. -/
theorem suzukiXiCarrierCayleyBoundaryInverseCoordinate_mul_memLp
    {q : ℝ≥0∞} {f : ℝ → ℂ}
    (hf : MemLp f q suzukiXiCarrierNevanlinnaMeasure) :
    MemLp (fun x : ℝ ↦
      suzukiXiCarrierCayleyBoundaryInverseCoordinate x * f x) q
      suzukiXiCarrierNevanlinnaMeasure := by
  apply hf.congr_norm
  · exact
      measurable_suzukiXiCarrierCayleyBoundaryInverseCoordinate.aestronglyMeasurable.mul
        hf.aestronglyMeasurable
  · exact Eventually.of_forall fun x ↦ by simp

/-- Multiplication by the Cayley boundary coordinate on actual `L²(μ)`
equivalence classes. -/
noncomputable def suzukiXiCarrierCayleyLpLinearMap :
    Lp ℂ 2 suzukiXiCarrierNevanlinnaMeasure →ₗ[ℂ]
      Lp ℂ 2 suzukiXiCarrierNevanlinnaMeasure where
  toFun f :=
    (suzukiXiCarrierCayleyBoundaryCoordinate_mul_memLp (Lp.memLp f)).toLp
      (fun x : ℝ ↦ suzukiXiCarrierCayleyBoundaryCoordinate x * f x)
  map_add' f g := by
    let hf := suzukiXiCarrierCayleyBoundaryCoordinate_mul_memLp (Lp.memLp f)
    let hg := suzukiXiCarrierCayleyBoundaryCoordinate_mul_memLp (Lp.memLp g)
    calc
      (suzukiXiCarrierCayleyBoundaryCoordinate_mul_memLp
          (Lp.memLp (f + g))).toLp
          (fun x : ℝ ↦
            suzukiXiCarrierCayleyBoundaryCoordinate x * (f + g) x) =
          (hf.add hg).toLp
            ((fun x : ℝ ↦
                suzukiXiCarrierCayleyBoundaryCoordinate x * f x) +
              fun x : ℝ ↦
                suzukiXiCarrierCayleyBoundaryCoordinate x * g x) := by
        apply MemLp.toLp_congr
        filter_upwards [Lp.coeFn_add f g] with x hx
        simp only [Pi.add_apply]
        rw [hx]
        simp only [Pi.add_apply]
        ring
      _ = hf.toLp
            (fun x : ℝ ↦
              suzukiXiCarrierCayleyBoundaryCoordinate x * f x) +
          hg.toLp
            (fun x : ℝ ↦
              suzukiXiCarrierCayleyBoundaryCoordinate x * g x) :=
        MemLp.toLp_add hf hg
  map_smul' c f := by
    let hf := suzukiXiCarrierCayleyBoundaryCoordinate_mul_memLp (Lp.memLp f)
    calc
      (suzukiXiCarrierCayleyBoundaryCoordinate_mul_memLp
          (Lp.memLp (c • f))).toLp
          (fun x : ℝ ↦
            suzukiXiCarrierCayleyBoundaryCoordinate x * (c • f) x) =
          (hf.const_smul c).toLp
            (c • fun x : ℝ ↦
              suzukiXiCarrierCayleyBoundaryCoordinate x * f x) := by
        apply MemLp.toLp_congr
        filter_upwards [Lp.coeFn_smul c f] with x hx
        simp only [Pi.smul_apply]
        rw [hx]
        simp only [Pi.smul_apply, smul_eq_mul]
        ring
      _ = c • hf.toLp
          (fun x : ℝ ↦
            suzukiXiCarrierCayleyBoundaryCoordinate x * f x) :=
        MemLp.toLp_const_smul c hf

/-- Almost-everywhere action of the Cayley multiplier. -/
theorem suzukiXiCarrierCayleyLpLinearMap_ae
    (f : Lp ℂ 2 suzukiXiCarrierNevanlinnaMeasure) :
    suzukiXiCarrierCayleyLpLinearMap f =ᵐ[
      suzukiXiCarrierNevanlinnaMeasure]
        fun x : ℝ ↦ suzukiXiCarrierCayleyBoundaryCoordinate x * f x :=
  MemLp.coeFn_toLp
    (suzukiXiCarrierCayleyBoundaryCoordinate_mul_memLp (Lp.memLp f))

/-- The Cayley multiplier preserves the `L²(μ)` norm. -/
theorem suzukiXiCarrierCayleyLpLinearMap_norm
    (f : Lp ℂ 2 suzukiXiCarrierNevanlinnaMeasure) :
    ‖suzukiXiCarrierCayleyLpLinearMap f‖ = ‖f‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  congr 1
  calc
    eLpNorm (suzukiXiCarrierCayleyLpLinearMap f) 2
        suzukiXiCarrierNevanlinnaMeasure =
        eLpNorm
          (fun x : ℝ ↦ suzukiXiCarrierCayleyBoundaryCoordinate x * f x)
          2 suzukiXiCarrierNevanlinnaMeasure :=
      eLpNorm_congr_ae (suzukiXiCarrierCayleyLpLinearMap_ae f)
    _ = eLpNorm f 2 suzukiXiCarrierNevanlinnaMeasure := by
      apply eLpNorm_congr_norm_ae
      exact Eventually.of_forall fun x ↦ by simp

/-- The Cayley multiplier as a complex-linear isometry. -/
noncomputable def suzukiXiCarrierCayleyLpLinearIsometry :
    Lp ℂ 2 suzukiXiCarrierNevanlinnaMeasure →ₗᵢ[ℂ]
      Lp ℂ 2 suzukiXiCarrierNevanlinnaMeasure where
  toLinearMap := suzukiXiCarrierCayleyLpLinearMap
  norm_map' := suzukiXiCarrierCayleyLpLinearMap_norm

@[simp] theorem suzukiXiCarrierCayleyLpLinearIsometry_apply
    (f : Lp ℂ 2 suzukiXiCarrierNevanlinnaMeasure) :
    suzukiXiCarrierCayleyLpLinearIsometry f =
      suzukiXiCarrierCayleyLpLinearMap f :=
  rfl

/-- The explicit inverse-coordinate preimage of an `L²(μ)` vector. -/
noncomputable def suzukiXiCarrierCayleyInversePreimage
    (f : Lp ℂ 2 suzukiXiCarrierNevanlinnaMeasure) :
    Lp ℂ 2 suzukiXiCarrierNevanlinnaMeasure :=
  (suzukiXiCarrierCayleyBoundaryInverseCoordinate_mul_memLp
    (Lp.memLp f)).toLp
      (fun x : ℝ ↦
        suzukiXiCarrierCayleyBoundaryInverseCoordinate x * f x)

/-- The explicit inverse preimage has its literal multiplier formula almost
everywhere. -/
theorem suzukiXiCarrierCayleyInversePreimage_ae
    (f : Lp ℂ 2 suzukiXiCarrierNevanlinnaMeasure) :
    suzukiXiCarrierCayleyInversePreimage f =ᵐ[
      suzukiXiCarrierNevanlinnaMeasure]
        fun x : ℝ ↦
          suzukiXiCarrierCayleyBoundaryInverseCoordinate x * f x :=
  MemLp.coeFn_toLp
    (suzukiXiCarrierCayleyBoundaryInverseCoordinate_mul_memLp (Lp.memLp f))

/-- Applying the Cayley multiplier to the explicit inverse preimage recovers
the original vector. -/
theorem suzukiXiCarrierCayleyLpLinearIsometry_inversePreimage
    (f : Lp ℂ 2 suzukiXiCarrierNevanlinnaMeasure) :
    suzukiXiCarrierCayleyLpLinearIsometry
        (suzukiXiCarrierCayleyInversePreimage f) = f := by
  change suzukiXiCarrierCayleyLpLinearMap
      (suzukiXiCarrierCayleyInversePreimage f) = f
  apply Lp.ext
  filter_upwards [suzukiXiCarrierCayleyLpLinearMap_ae
      (suzukiXiCarrierCayleyInversePreimage f),
    suzukiXiCarrierCayleyInversePreimage_ae f]
      with x hforward hinverse
  rw [hforward, hinverse]
  rw [← mul_assoc,
    suzukiXiCarrierCayleyBoundaryCoordinate_mul_inverse, one_mul]

/-- The Cayley isometry is surjective. -/
theorem suzukiXiCarrierCayleyLpLinearIsometry_surjective :
    Function.Surjective suzukiXiCarrierCayleyLpLinearIsometry := by
  intro f
  exact ⟨suzukiXiCarrierCayleyInversePreimage f,
    suzukiXiCarrierCayleyLpLinearIsometry_inversePreimage f⟩

/-- Multiplication by the boundary Cayley coordinate is therefore a genuine
unitary operator, represented as a complex-linear isometric equivalence. -/
noncomputable def suzukiXiCarrierCayleyUnitary :
    Lp ℂ 2 suzukiXiCarrierNevanlinnaMeasure ≃ₗᵢ[ℂ]
      Lp ℂ 2 suzukiXiCarrierNevanlinnaMeasure :=
  LinearIsometryEquiv.ofSurjective
    suzukiXiCarrierCayleyLpLinearIsometry
    suzukiXiCarrierCayleyLpLinearIsometry_surjective

@[simp] theorem suzukiXiCarrierCayleyUnitary_apply
    (f : Lp ℂ 2 suzukiXiCarrierNevanlinnaMeasure) :
    suzukiXiCarrierCayleyUnitary f =
      suzukiXiCarrierCayleyLpLinearIsometry f :=
  rfl

/-- The unitary acts by the Cayley boundary multiplier almost everywhere. -/
theorem suzukiXiCarrierCayleyUnitary_ae
    (f : Lp ℂ 2 suzukiXiCarrierNevanlinnaMeasure) :
    suzukiXiCarrierCayleyUnitary f =ᵐ[
      suzukiXiCarrierNevanlinnaMeasure]
        fun x : ℝ ↦ suzukiXiCarrierCayleyBoundaryCoordinate x * f x := by
  change suzukiXiCarrierCayleyLpLinearMap f =ᵐ[
    suzukiXiCarrierNevanlinnaMeasure]
      fun x : ℝ ↦ suzukiXiCarrierCayleyBoundaryCoordinate x * f x
  exact suzukiXiCarrierCayleyLpLinearMap_ae f

/-- The inverse unitary is exactly multiplication by the inverse Cayley
boundary coordinate. -/
theorem suzukiXiCarrierCayleyUnitary_symm_eq_inversePreimage
    (f : Lp ℂ 2 suzukiXiCarrierNevanlinnaMeasure) :
    suzukiXiCarrierCayleyUnitary.symm f =
      suzukiXiCarrierCayleyInversePreimage f := by
  apply suzukiXiCarrierCayleyUnitary.injective
  simp only [LinearIsometryEquiv.apply_symm_apply]
  simpa [suzukiXiCarrierCayleyUnitary] using
    (suzukiXiCarrierCayleyLpLinearIsometry_inversePreimage f).symm

/-- Almost-everywhere action of the inverse unitary. -/
theorem suzukiXiCarrierCayleyUnitary_symm_ae
    (f : Lp ℂ 2 suzukiXiCarrierNevanlinnaMeasure) :
    suzukiXiCarrierCayleyUnitary.symm f =ᵐ[
      suzukiXiCarrierNevanlinnaMeasure]
        fun x : ℝ ↦
          suzukiXiCarrierCayleyBoundaryInverseCoordinate x * f x := by
  rw [suzukiXiCarrierCayleyUnitary_symm_eq_inversePreimage]
  exact suzukiXiCarrierCayleyInversePreimage_ae f

/-- The literal constant-one function in the finite carrier space. -/
def suzukiXiCarrierNevanlinnaOneFunction (_x : ℝ) : ℂ :=
  1

/-- The constant-one function belongs to `L²(μ)` because the carrier measure
is finite. -/
theorem memLp_two_suzukiXiCarrierNevanlinnaOneFunction :
    MemLp suzukiXiCarrierNevanlinnaOneFunction 2
      suzukiXiCarrierNevanlinnaMeasure := by
  exact memLp_const (μ := suzukiXiCarrierNevanlinnaMeasure) 1

/-- The constant-one vector in the finite carrier Hilbert space. -/
noncomputable def suzukiXiCarrierNevanlinnaOneLp :
    Lp ℂ 2 suzukiXiCarrierNevanlinnaMeasure :=
  memLp_two_suzukiXiCarrierNevanlinnaOneFunction.toLp
    suzukiXiCarrierNevanlinnaOneFunction

/-- The packaged constant-one vector is literally one almost everywhere. -/
theorem suzukiXiCarrierNevanlinnaOneLp_ae :
    suzukiXiCarrierNevanlinnaOneLp =ᵐ[
      suzukiXiCarrierNevanlinnaMeasure]
        suzukiXiCarrierNevanlinnaOneFunction :=
  MemLp.coeFn_toLp memLp_two_suzukiXiCarrierNevanlinnaOneFunction

/-- A fixed complex parameter collides with the embedded real axis only on
a carrier-null set.  This is the step needed for totalized real-node
features: no pointwise cancellation at the collision is silently assumed. -/
theorem ae_ofReal_sub_ne_zero_suzukiXiCarrierNevanlinnaMeasure
    (z : ℂ) :
    ∀ᵐ x : ℝ ∂suzukiXiCarrierNevanlinnaMeasure, (x : ℂ) - z ≠ 0 := by
  by_cases him : z.im = 0
  · have hzreal : z = (z.re : ℂ) := by
      apply Complex.ext
      · simp
      · simp [him]
    have hne :
        ∀ᵐ x ∂suzukiXiCarrierNevanlinnaMeasure, x ≠ z.re := by
      have hsingleton :
          suzukiXiCarrierNevanlinnaMeasure {z.re} = 0 := by
        unfold suzukiXiCarrierNevanlinnaMeasure
        exact withDensity_absolutelyContinuous volume _ (measure_singleton _)
      simpa [ae_iff] using hsingleton
    filter_upwards [hne] with x hx
    rw [hzreal]
    exact sub_ne_zero.mpr (Complex.ofReal_injective.ne hx)
  · exact Eventually.of_forall fun x ↦
      ofReal_sub_ne_zero_of_im_ne_zero him x

/-- A genuine spectral-xi node is never the exceptional Cayley parameter
`-i`; this follows from the already-proved strict spectral strip. -/
theorem zetaSpectralCoordinate_add_I_ne_zero
    (rho : NontrivialZetaZero) :
    zetaSpectralCoordinate rho.1 + Complex.I ≠ 0 := by
  intro hzero
  have himEq := congrArg Complex.im hzero
  have him : (zetaSpectralCoordinate rho.1).im = -1 := by
    simp only [Complex.add_im, Complex.I_im, Complex.zero_im] at himEq
    linarith
  have hstrip := NontrivialZetaZero.abs_spectralCoordinate_im_lt_half rho
  rw [him] at hstrip
  norm_num at hstrip

/-- Cayley parameter of one genuine spectral-xi node. -/
def suzukiXiCarrierCayleyNodeParameter
    (rho : NontrivialZetaZero) : ℂ :=
  suzukiXiCarrierCayleyParameter (zetaSpectralCoordinate rho.1)

/-- Away from the one possible real collision, the canonical rational
feature obeys the exact Cayley resolvent identity pointwise. -/
theorem suzukiXiCarrierCayley_resolvent_identity
    (z : ℂ) (hz : z + Complex.I ≠ 0) (x : ℝ)
    (hx : (x : ℂ) - z ≠ 0) :
    suzukiXiCarrierCayleyBoundaryCoordinate x *
        suzukiXiCarrierNevanlinnaFeature z x -
      suzukiXiCarrierCayleyParameter z *
        suzukiXiCarrierNevanlinnaFeature z x =
      (1 - suzukiXiCarrierCayleyParameter z) *
        suzukiXiCarrierCayleyBoundaryCoordinate x := by
  unfold suzukiXiCarrierCayleyBoundaryCoordinate
    suzukiXiCarrierCayleyParameter
    suzukiXiCarrierNevanlinnaFeature
  have hplus : (x : ℂ) + Complex.I ≠ 0 := by
    simpa [sub_eq_add_neg] using
      (ofReal_sub_ne_zero_of_im_ne_zero
        (z := -Complex.I) (by simp) x)
  field_simp [hplus, hz, hx]
  ring

/-- Every genuine xi-node feature is an exact resolvent vector for the one
Cayley unitary:

`U F_rho - a_rho F_rho = (1 - a_rho) U 1`.

This includes real and multiple nodes.  The real collision is removed only
almost everywhere, using the preceding null-singleton theorem. -/
theorem suzukiXiCarrierCayleyUnitary_nodeFeature_resolvent
    (rho : NontrivialZetaZero) :
    suzukiXiCarrierCayleyUnitary
        (suzukiXiCarrierNevanlinnaNodeFeatureLp rho) -
      suzukiXiCarrierCayleyNodeParameter rho •
        suzukiXiCarrierNevanlinnaNodeFeatureLp rho =
      (1 - suzukiXiCarrierCayleyNodeParameter rho) •
        suzukiXiCarrierCayleyUnitary
          suzukiXiCarrierNevanlinnaOneLp := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_sub
      (suzukiXiCarrierCayleyUnitary
        (suzukiXiCarrierNevanlinnaNodeFeatureLp rho))
      (suzukiXiCarrierCayleyNodeParameter rho •
        suzukiXiCarrierNevanlinnaNodeFeatureLp rho),
    suzukiXiCarrierCayleyUnitary_ae
      (suzukiXiCarrierNevanlinnaNodeFeatureLp rho),
    Lp.coeFn_smul (suzukiXiCarrierCayleyNodeParameter rho)
      (suzukiXiCarrierNevanlinnaNodeFeatureLp rho),
    suzukiXiCarrierNevanlinnaNodeFeatureLp_ae rho,
    Lp.coeFn_smul (1 - suzukiXiCarrierCayleyNodeParameter rho)
      (suzukiXiCarrierCayleyUnitary suzukiXiCarrierNevanlinnaOneLp),
    suzukiXiCarrierCayleyUnitary_ae suzukiXiCarrierNevanlinnaOneLp,
    suzukiXiCarrierNevanlinnaOneLp_ae,
    ae_ofReal_sub_ne_zero_suzukiXiCarrierNevanlinnaMeasure
      (zetaSpectralCoordinate rho.1)]
      with x hsub hunitary hsmulFeature hfeature hsmulOne hunitaryOne
        hone hcollision
  rw [hsub]
  simp only [Pi.sub_apply]
  rw [hunitary, hsmulFeature, hsmulOne]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hfeature, hunitaryOne, hone]
  simp only [suzukiXiCarrierNevanlinnaOneFunction, mul_one]
  exact suzukiXiCarrierCayley_resolvent_identity
    (zetaSpectralCoordinate rho.1)
    (zetaSpectralCoordinate_add_I_ne_zero rho) x hcollision

/-- Equivalent adjoint-resolvent form of the node equation:

`F_rho - a_rho U⁻¹ F_rho = (1 - a_rho) 1`. -/
theorem suzukiXiCarrierCayleyUnitary_symm_nodeFeature_resolvent
    (rho : NontrivialZetaZero) :
    suzukiXiCarrierNevanlinnaNodeFeatureLp rho -
      suzukiXiCarrierCayleyNodeParameter rho •
        suzukiXiCarrierCayleyUnitary.symm
          (suzukiXiCarrierNevanlinnaNodeFeatureLp rho) =
      (1 - suzukiXiCarrierCayleyNodeParameter rho) •
        suzukiXiCarrierNevanlinnaOneLp := by
  have h := congrArg
    (fun f : Lp ℂ 2 suzukiXiCarrierNevanlinnaMeasure ↦
      suzukiXiCarrierCayleyUnitary.symm f)
    (suzukiXiCarrierCayleyUnitary_nodeFeature_resolvent rho)
  simpa only [map_sub, map_smul,
    LinearIsometryEquiv.symm_apply_apply] using h

/-- Finite synthesis with one additional Cayley node parameter in every
Suzuki-normalized coefficient. -/
def suzukiXiCarrierNevanlinnaCayleyWeightedFiniteSynthesis
    (c : NontrivialZetaZero →₀ ℂ) :
    Lp ℂ 2 suzukiXiCarrierNevanlinnaMeasure :=
  ∑ rho ∈ c.support,
    (((suzukiXiZeroNormalization rho : ℂ) * c rho) *
        suzukiXiCarrierCayleyNodeParameter rho) •
      suzukiXiCarrierNevanlinnaNodeFeatureLp rho

/-- The scalar rank-one defect left by the finite Cayley-weighted synthesis. -/
def suzukiXiCarrierNevanlinnaCayleyFiniteDefect
    (c : NontrivialZetaZero →₀ ℂ) : ℂ :=
  ∑ rho ∈ c.support,
    ((suzukiXiZeroNormalization rho : ℂ) * c rho) *
      (1 - suzukiXiCarrierCayleyNodeParameter rho)

/-- Exact finite operator-pencil identity for every finitely supported Suzuki
coefficient family:

`U S(c) - S(a c) = d(c) U 1`.

Thus all moving rational features are resolvents of one unitary, and the
failure of exact Cayley covariance is a single rank-one scalar term. -/
theorem suzukiXiCarrierCayleyUnitary_finiteSynthesis_resolvent
    (c : NontrivialZetaZero →₀ ℂ) :
    suzukiXiCarrierCayleyUnitary
        (suzukiXiCarrierNevanlinnaFeatureFiniteSynthesis c) -
      suzukiXiCarrierNevanlinnaCayleyWeightedFiniteSynthesis c =
      suzukiXiCarrierNevanlinnaCayleyFiniteDefect c •
        suzukiXiCarrierCayleyUnitary
          suzukiXiCarrierNevanlinnaOneLp := by
  unfold suzukiXiCarrierNevanlinnaFeatureFiniteSynthesis
    suzukiXiCarrierNevanlinnaCayleyWeightedFiniteSynthesis
    suzukiXiCarrierNevanlinnaCayleyFiniteDefect
  rw [map_sum]
  simp_rw [map_smul]
  rw [← Finset.sum_sub_distrib, Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro rho _hrho
  let q : ℂ := (suzukiXiZeroNormalization rho : ℂ) * c rho
  let a : ℂ := suzukiXiCarrierCayleyNodeParameter rho
  let F : Lp ℂ 2 suzukiXiCarrierNevanlinnaMeasure :=
    suzukiXiCarrierNevanlinnaNodeFeatureLp rho
  let Uone : Lp ℂ 2 suzukiXiCarrierNevanlinnaMeasure :=
    suzukiXiCarrierCayleyUnitary suzukiXiCarrierNevanlinnaOneLp
  have hnode :
      suzukiXiCarrierCayleyUnitary F - a • F = (1 - a) • Uone := by
    simpa [F, a, Uone] using
      suzukiXiCarrierCayleyUnitary_nodeFeature_resolvent rho
  change q • suzukiXiCarrierCayleyUnitary F -
      (q * a) • F = (q * (1 - a)) • Uone
  calc
    q • suzukiXiCarrierCayleyUnitary F - (q * a) • F =
        q • (suzukiXiCarrierCayleyUnitary F - a • F) := by
      rw [smul_sub, smul_smul]
    _ = q • ((1 - a) • Uone) := congrArg (fun v ↦ q • v) hnode
    _ = (q * (1 - a)) • Uone := by rw [smul_smul]

/-- Exact norm form of the finite operator-pencil identity.  Because `U` is
unitary, the original synthesis norm is the norm of a Cayley-weighted
synthesis plus one explicit rank-one vector. -/
theorem norm_suzukiXiCarrierNevanlinnaFeatureFiniteSynthesis_eq_cayleyResolved
    (c : NontrivialZetaZero →₀ ℂ) :
    ‖suzukiXiCarrierNevanlinnaFeatureFiniteSynthesis c‖ =
      ‖suzukiXiCarrierNevanlinnaCayleyWeightedFiniteSynthesis c +
        suzukiXiCarrierNevanlinnaCayleyFiniteDefect c •
          suzukiXiCarrierCayleyUnitary
            suzukiXiCarrierNevanlinnaOneLp‖ := by
  calc
    ‖suzukiXiCarrierNevanlinnaFeatureFiniteSynthesis c‖ =
        ‖suzukiXiCarrierCayleyUnitary
          (suzukiXiCarrierNevanlinnaFeatureFiniteSynthesis c)‖ :=
      (suzukiXiCarrierCayleyUnitary.norm_map _).symm
    _ = ‖suzukiXiCarrierNevanlinnaCayleyWeightedFiniteSynthesis c +
        suzukiXiCarrierNevanlinnaCayleyFiniteDefect c •
          suzukiXiCarrierCayleyUnitary
            suzukiXiCarrierNevanlinnaOneLp‖ := by
      congr 1
      have h := (sub_eq_iff_eq_add).mp
        (suzukiXiCarrierCayleyUnitary_finiteSynthesis_resolvent c)
      simpa only [add_comm] using h

/-- Cayley-weighted synthesis of one genuine Suzuki coefficient-window
tail. -/
def suzukiXiCoefficientTailNevanlinnaCayleyWeightedSynthesis
    (t T U : ℝ) : Lp ℂ 2 suzukiXiCarrierNevanlinnaMeasure :=
  suzukiXiCarrierNevanlinnaCayleyWeightedFiniteSynthesis
    (riemannXiSuzukiSpectralCoefficientTailFinsupp t T U)

/-- Scalar rank-one Cayley defect of one genuine Suzuki coefficient-window
tail. -/
def suzukiXiCoefficientTailNevanlinnaCayleyDefect
    (t T U : ℝ) : ℂ :=
  suzukiXiCarrierNevanlinnaCayleyFiniteDefect
    (riemannXiSuzukiSpectralCoefficientTailFinsupp t T U)

/-- The exact unitary resolvent equation for every genuine coefficient
window tail. -/
theorem suzukiXiCarrierCayleyUnitary_coefficientTail_resolvent
    (t T U : ℝ) :
    suzukiXiCarrierCayleyUnitary
        (suzukiXiCoefficientTailNevanlinnaFeatureSynthesis t T U) -
      suzukiXiCoefficientTailNevanlinnaCayleyWeightedSynthesis t T U =
      suzukiXiCoefficientTailNevanlinnaCayleyDefect t T U •
        suzukiXiCarrierCayleyUnitary
          suzukiXiCarrierNevanlinnaOneLp := by
  exact suzukiXiCarrierCayleyUnitary_finiteSynthesis_resolvent
    (riemannXiSuzukiSpectralCoefficientTailFinsupp t T U)

/-- The unresolved tail norm is exactly a Cayley-weighted tail plus one
explicit rank-one scalar defect. -/
theorem norm_suzukiXiCoefficientTailNevanlinnaFeatureSynthesis_eq_cayleyResolved
    (t T U : ℝ) :
    ‖suzukiXiCoefficientTailNevanlinnaFeatureSynthesis t T U‖ =
      ‖suzukiXiCoefficientTailNevanlinnaCayleyWeightedSynthesis t T U +
        suzukiXiCoefficientTailNevanlinnaCayleyDefect t T U •
          suzukiXiCarrierCayleyUnitary
            suzukiXiCarrierNevanlinnaOneLp‖ := by
  exact
    norm_suzukiXiCarrierNevanlinnaFeatureFiniteSynthesis_eq_cayleyResolved
      (riemannXiSuzukiSpectralCoefficientTailFinsupp t T U)

/-- The sharpened tail frontier after the Cayley-unitary transformation. -/
def SuzukiXiCoefficientTailCayleyResolvedNormVanishing (t : ℝ) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon → ∃ R : ℝ,
    ∀ T ≥ R, ∀ U ≥ R,
      ‖suzukiXiCoefficientTailNevanlinnaCayleyWeightedSynthesis t T U +
        suzukiXiCoefficientTailNevanlinnaCayleyDefect t T U •
          suzukiXiCarrierCayleyUnitary
            suzukiXiCarrierNevanlinnaOneLp‖ ^ 2 < epsilon

/-- The finite-measure norm frontier is exactly the Cayley-resolved norm
frontier; no estimate is lost in the unitary transformation. -/
theorem coefficientTailNevanlinnaNormVanishing_iff_cayleyResolved
    (t : ℝ) :
    SuzukiXiCoefficientTailNevanlinnaNormVanishing t ↔
      SuzukiXiCoefficientTailCayleyResolvedNormVanishing t := by
  unfold SuzukiXiCoefficientTailNevanlinnaNormVanishing
    SuzukiXiCoefficientTailCayleyResolvedNormVanishing
  simp_rw [
    norm_suzukiXiCoefficientTailNevanlinnaFeatureSynthesis_eq_cayleyResolved]

/-- Consequently, the original zero-function Gram frontier is exactly the
Cayley-resolved unitary norm frontier. -/
theorem coefficientTailGramVanishing_iff_cayleyResolved
    (t : ℝ) :
    SuzukiXiCoefficientTailGramVanishing t ↔
      SuzukiXiCoefficientTailCayleyResolvedNormVanishing t := by
  rw [coefficientTailGramVanishing_iff_nevanlinnaNormVanishing,
    coefficientTailNevanlinnaNormVanishing_iff_cayleyResolved]

end

end RiemannGaussian
