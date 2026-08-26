import RiemannGaussian.SymmetricPickDisk
import Mathlib.Analysis.Matrix.Order

/-!
# Pick-kernel positivity for finite upper-half-plane Blaschke products

The positivity in this file is proved from an explicit rank-one factorization
of one elementary Blaschke kernel and the Schur product theorem.  It is not an
appeal to an unformalized Nevanlinna--Pick theorem.
-/

namespace RiemannGaussian

noncomputable section

open Polynomial
open scoped ComplexConjugate ComplexOrder Matrix

/-- The scalar Pick kernel on the upper half-plane. -/
def upperHalfPlanePickKernel (f : ℂ → ℂ) (z w : ℂ) : ℂ :=
  Complex.I * (1 - f z * starRingEnd ℂ (f w)) /
    (z - starRingEnd ℂ w)

/-- A finite sampling of the scalar upper-half-plane Pick kernel. -/
def upperHalfPlanePickMatrix {n : Type*}
    (f : ℂ → ℂ) (nodes : n → ℂ) : Matrix n n ℂ :=
  fun i j => upperHalfPlanePickKernel f (nodes i) (nodes j)

/-- One elementary upper-half-plane Blaschke factor. -/
def elementaryUpperHalfPlaneBlaschke (alpha z : ℂ) : ℂ :=
  (z - alpha) / (z - starRingEnd ℂ alpha)

theorem sub_conj_ne_zero_of_im_pos
    {z w : ℂ} (hz : 0 < z.im) (hw : 0 < w.im) :
    z - starRingEnd ℂ w ≠ 0 := by
  intro h
  have him := congrArg Complex.im h
  change z.im - (conj w).im = 0 at him
  rw [Complex.conj_im] at him
  linarith

/-- Diagonal value of the upper-half-plane Pick kernel. -/
theorem upperHalfPlanePickKernel_self
    (f : ℂ → ℂ) {z : ℂ} (hz : 0 < z.im) :
    upperHalfPlanePickKernel f z z =
      (((1 - Complex.normSq (f z)) / (2 * z.im) : ℝ) : ℂ) := by
  have hdiff : z - starRingEnd ℂ z = (2 * z.im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
    ring
  unfold upperHalfPlanePickKernel
  rw [show f z * starRingEnd ℂ (f z) =
      (Complex.normSq (f z) : ℂ) by
    rw [mul_comm, Complex.normSq_eq_conj_mul_self]]
  rw [hdiff]
  calc
    Complex.I * (1 - (Complex.normSq (f z) : ℂ)) /
          ((2 * z.im : ℂ) * Complex.I) =
        (1 - (Complex.normSq (f z) : ℂ)) / (2 * z.im : ℂ) := by
      field_simp [hz.ne']
    _ = (((1 - Complex.normSq (f z)) / (2 * z.im) : ℝ) : ℂ) := by
      norm_cast

/-- Exact rank-one rational form of one elementary Pick kernel. -/
theorem upperHalfPlanePickKernel_elementary
    {alpha z w : ℂ} (halpha : 0 < alpha.im)
    (hz : 0 < z.im) (hw : 0 < w.im) :
    upperHalfPlanePickKernel
        (elementaryUpperHalfPlaneBlaschke alpha) z w =
      (2 * alpha.im : ℂ) /
        ((z - starRingEnd ℂ alpha) *
          (starRingEnd ℂ w - alpha)) := by
  have hza := sub_conj_ne_zero_of_im_pos hz halpha
  have hwa := sub_conj_ne_zero_of_im_pos hw halpha
  have hzw := sub_conj_ne_zero_of_im_pos hz hw
  have hconjwa : starRingEnd ℂ w - alpha ≠ 0 := by
    intro h
    apply hwa
    have h' := congrArg (starRingEnd ℂ) h
    simpa using h'
  unfold upperHalfPlanePickKernel elementaryUpperHalfPlaneBlaschke
  simp only [map_div₀, map_sub]
  field_simp [hza, hwa, hzw, hconjwa]
  apply Complex.ext <;> simp
  <;> ring

/-- Explicit feature whose Gram kernel is the elementary Pick kernel. -/
def elementaryPickFeature (alpha z : ℂ) : ℂ :=
  (Real.sqrt (2 * alpha.im) : ℂ) /
    (z - starRingEnd ℂ alpha)

theorem upperHalfPlanePickKernel_elementary_eq_feature_mul_conj
    {alpha z w : ℂ} (halpha : 0 < alpha.im)
    (hz : 0 < z.im) (hw : 0 < w.im) :
    upperHalfPlanePickKernel
        (elementaryUpperHalfPlaneBlaschke alpha) z w =
      elementaryPickFeature alpha z *
        starRingEnd ℂ (elementaryPickFeature alpha w) := by
  rw [upperHalfPlanePickKernel_elementary halpha hz hw]
  have hsqrt : Real.sqrt (2 * alpha.im) ^ 2 = 2 * alpha.im := by
    exact Real.sq_sqrt (by positivity)
  have hsqrtC : ((Real.sqrt (2 * alpha.im) : ℂ) ^ 2) =
      (2 * alpha.im : ℂ) := by
    exact_mod_cast hsqrt
  unfold elementaryPickFeature
  simp only [map_div₀, map_sub, Complex.conj_ofReal]
  have hza := sub_conj_ne_zero_of_im_pos hz halpha
  have hwa := sub_conj_ne_zero_of_im_pos hw halpha
  have hconjwa : starRingEnd ℂ w - alpha ≠ 0 := by
    intro h
    apply hwa
    have h' := congrArg (starRingEnd ℂ) h
    simpa using h'
  have hstaralpha :
      starRingEnd ℂ (starRingEnd ℂ alpha) = alpha := by simp
  field_simp [hza, hwa, hconjwa]
  rw [hsqrtC]
  rw [hstaralpha]
  ring

/-- Every matrix obtained by sampling one elementary Blaschke Pick kernel at
upper-half-plane nodes is positive semidefinite. -/
theorem elementaryUpperHalfPlaneBlaschke_pickMatrix_posSemidef
    {n : Type*} [Finite n] (alpha : ℂ) (nodes : n → ℂ)
    (halpha : 0 < alpha.im) (hnodes : ∀ i, 0 < (nodes i).im) :
    (upperHalfPlanePickMatrix
      (elementaryUpperHalfPlaneBlaschke alpha) nodes).PosSemidef := by
  let feature : n → ℂ := fun i => elementaryPickFeature alpha (nodes i)
  have heq :
      upperHalfPlanePickMatrix
        (elementaryUpperHalfPlaneBlaschke alpha) nodes =
          Matrix.vecMulVec feature (star feature) := by
    ext i j
    exact upperHalfPlanePickKernel_elementary_eq_feature_mul_conj
      halpha (hnodes i) (hnodes j)
  rw [heq]
  exact Matrix.posSemidef_vecMulVec_self_star feature

/-- Product rule for upper-half-plane Pick kernels. -/
theorem upperHalfPlanePickKernel_mul
    (f g : ℂ → ℂ) (z w : ℂ) :
    upperHalfPlanePickKernel (fun u => f u * g u) z w =
      upperHalfPlanePickKernel f z w +
        f z * starRingEnd ℂ (f w) *
          upperHalfPlanePickKernel g z w := by
  unfold upperHalfPlanePickKernel
  simp only [map_mul]
  ring

/-- Positive-semidefinite Pick kernels are closed under pointwise products
of their underlying functions. -/
theorem pickMatrix_posSemidef_mul
    {n : Type*} [Finite n] (f g : ℂ → ℂ) (nodes : n → ℂ)
    (hf : (upperHalfPlanePickMatrix f nodes).PosSemidef)
    (hg : (upperHalfPlanePickMatrix g nodes).PosSemidef) :
    (upperHalfPlanePickMatrix (fun z => f z * g z) nodes).PosSemidef := by
  let _ := Fintype.ofFinite n
  let values : n → ℂ := fun i => f (nodes i)
  let valueGram : Matrix n n ℂ := Matrix.vecMulVec values (star values)
  let gPick : Matrix n n ℂ := fun i j =>
    upperHalfPlanePickKernel g (nodes i) (nodes j)
  have hvalue : valueGram.PosSemidef :=
    Matrix.posSemidef_vecMulVec_self_star values
  have hweighted : (valueGram ⊙ gPick).PosSemidef :=
    hvalue.hadamard hg
  let fPick : Matrix n n ℂ := fun i j =>
    upperHalfPlanePickKernel f (nodes i) (nodes j)
  change fPick.PosSemidef at hf
  change gPick.PosSemidef at hg
  have hsum :
      (fPick + valueGram ⊙ gPick).PosSemidef := by
    exact hf.add hweighted
  have hmatrix :
      upperHalfPlanePickMatrix (fun z => f z * g z) nodes =
        fPick + valueGram ⊙ gPick := by
    ext i j
    change upperHalfPlanePickKernel (fun z => f z * g z)
      (nodes i) (nodes j) =
        upperHalfPlanePickKernel f (nodes i) (nodes j) +
          f (nodes i) * starRingEnd ℂ (f (nodes j)) *
            upperHalfPlanePickKernel g (nodes i) (nodes j)
    rw [upperHalfPlanePickKernel_mul]
  rw [hmatrix]
  exact hsum

/-- A finite list of upper-half-plane zeros gives a literal finite Blaschke
product, retaining repeated zeros. -/
def finiteUpperHalfPlaneBlaschke (zeros : List ℂ) (z : ℂ) : ℂ :=
  (zeros.map fun alpha => elementaryUpperHalfPlaneBlaschke alpha z).prod

/-- Pick-matrix positivity for every finite Blaschke product follows by
induction from rank-one positivity and the Schur product theorem. -/
theorem finiteUpperHalfPlaneBlaschke_pickMatrix_posSemidef
    {n : Type*} [Finite n] (zeros : List ℂ) (nodes : n → ℂ)
    (hzeros : ∀ alpha ∈ zeros, 0 < alpha.im)
    (hnodes : ∀ i, 0 < (nodes i).im) :
    (upperHalfPlanePickMatrix
      (finiteUpperHalfPlaneBlaschke zeros) nodes).PosSemidef := by
  induction zeros with
  | nil =>
      have hzero :
          upperHalfPlanePickMatrix
            (finiteUpperHalfPlaneBlaschke []) nodes = 0 := by
        ext i j
        change upperHalfPlanePickKernel (fun _ => 1) (nodes i) (nodes j) = 0
        simp [upperHalfPlanePickKernel]
      rw [hzero]
      exact Matrix.PosSemidef.zero
  | cons alpha zeros ih =>
      have halpha : 0 < alpha.im := hzeros alpha (by simp)
      have htail : ∀ beta ∈ zeros, 0 < beta.im := by
        intro beta hbeta
        exact hzeros beta (by simp [hbeta])
      have hhead := elementaryUpperHalfPlaneBlaschke_pickMatrix_posSemidef
        alpha nodes halpha hnodes
      have hrest := ih htail
      have hproduct := pickMatrix_posSemidef_mul
        (elementaryUpperHalfPlaneBlaschke alpha)
        (finiteUpperHalfPlaneBlaschke zeros) nodes hhead hrest
      change (upperHalfPlanePickMatrix
        (fun z => elementaryUpperHalfPlaneBlaschke alpha z *
          (zeros.map fun beta => elementaryUpperHalfPlaneBlaschke beta z).prod)
        nodes).PosSemidef
      exact hproduct

/-- Multiset version of the finite Blaschke product, convenient for root
multisets and retaining multiplicity definitionally. -/
def multisetUpperHalfPlaneBlaschke (zeros : Multiset ℂ) (z : ℂ) : ℂ :=
  (zeros.map fun alpha => elementaryUpperHalfPlaneBlaschke alpha z).prod

theorem multisetUpperHalfPlaneBlaschke_pickMatrix_posSemidef
    {n : Type*} [Finite n] (zeros : Multiset ℂ) (nodes : n → ℂ)
    (hzeros : ∀ alpha ∈ zeros, 0 < alpha.im)
    (hnodes : ∀ i, 0 < (nodes i).im) :
    (upperHalfPlanePickMatrix
      (multisetUpperHalfPlaneBlaschke zeros) nodes).PosSemidef := by
  induction zeros using Multiset.induction_on with
  | empty =>
      have hzero :
          upperHalfPlanePickMatrix
            (multisetUpperHalfPlaneBlaschke 0) nodes = 0 := by
        ext i j
        change upperHalfPlanePickKernel (fun _ => 1) (nodes i) (nodes j) = 0
        simp [upperHalfPlanePickKernel]
      rw [hzero]
      exact Matrix.PosSemidef.zero
  | @cons alpha zeros ih =>
      have halpha : 0 < alpha.im := hzeros alpha (by simp)
      have htail : ∀ beta ∈ zeros, 0 < beta.im := by
        intro beta hbeta
        exact hzeros beta (by simp [hbeta])
      have hhead := elementaryUpperHalfPlaneBlaschke_pickMatrix_posSemidef
        alpha nodes halpha hnodes
      have hrest := ih htail
      have hproduct := pickMatrix_posSemidef_mul
        (elementaryUpperHalfPlaneBlaschke alpha)
        (multisetUpperHalfPlaneBlaschke zeros) nodes hhead hrest
      have hcons : multisetUpperHalfPlaneBlaschke (alpha ::ₘ zeros) =
          fun z => elementaryUpperHalfPlaneBlaschke alpha z *
            multisetUpperHalfPlaneBlaschke zeros z := by
        funext z
        simp [multisetUpperHalfPlaneBlaschke]
      rw [hcons]
      exact hproduct

/-- The residual finite inner factor already used by the polynomial
Gram--Weil development has a positive-semidefinite Pick matrix at every
finite family of upper-half-plane nodes. -/
theorem lowerRootInnerValue_pickMatrix_posSemidef
    {n : Type*} [Finite n] (p : ℂ[X]) (nodes : n → ℂ)
    (hnodes : ∀ i, 0 < (nodes i).im) :
    (upperHalfPlanePickMatrix (lowerRootInnerValue p) nodes).PosSemidef := by
  let zeros : Multiset ℂ :=
    (p.roots.filter fun w => w.im < 0).map (starRingEnd ℂ)
  have hzeros : ∀ alpha ∈ zeros, 0 < alpha.im := by
    intro alpha halpha
    change alpha ∈
      (p.roots.filter fun w => w.im < 0).map (starRingEnd ℂ) at halpha
    rw [Multiset.mem_map] at halpha
    obtain ⟨w, hw, rfl⟩ := halpha
    have hwneg : w.im < 0 := (Multiset.mem_filter.mp hw).2
    rw [Complex.conj_im]
    linarith
  have hpositive :=
    multisetUpperHalfPlaneBlaschke_pickMatrix_posSemidef zeros nodes
      hzeros hnodes
  have hvalue : lowerRootInnerValue p =
      multisetUpperHalfPlaneBlaschke zeros := by
    funext z
    rw [lowerRootInnerValue_eq_prod]
    simp [zeros, multisetUpperHalfPlaneBlaschke,
      elementaryUpperHalfPlaneBlaschke]
  rw [hvalue]
  exact hpositive

end

end RiemannGaussian
