import RiemannGaussian.MontgomeryTaylorInverseSampling
import Zeta23.ZeroSide.Mult
import Mathlib.Analysis.Matrix.Order

/-!
# Spectral remainder in the Zeta23 simple-zero rank--trace argument

The multiplicity-aware baseline ultimately replaces a convex spectral term by
diagonal norm information.  For inverse sampling we retain that term, pinch
the literal simple-zero Gram into disjoint triples, and prove the resulting
capped correlation energy directly inside the concrete Zeta23 zero side.
-/

noncomputable section

open Matrix Finset RHLinalg
open scoped ComplexOrder BigOperators MatrixOrder

namespace RiemannGaussian
namespace Zeta23InverseSampling

open Zeta23.ZeroSide.RankTraceMult

variable {𝕜 : Type*} [RCLike 𝕜]
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Rank--trace with the full convex spectral remainder retained.  This is the
step immediately before Schur--Jensen in the multiplicity-aware proof. -/
theorem rankTraceSpectralGc {P Q : Matrix n n 𝕜}
    (hP : P.PosSemidef) (hQ : Q.IsHermitian)
    {b : ℕ} (hb : posIndex hQ ≤ b) {c : ℝ} (hc : 0 < c) :
    c * rtrace P + (∑ i, gc c (hP.1.eigenvalues i)) +
        2 * c * rtrace Q - c ^ 2 * b ≤ frobSq (P + Q) := by
  classical
  set Qp := hermPosPart hQ with hQp_def
  set Qm := hermNegPart hQ with hQm_def
  have hQdec : Q = Qp - Qm := (hermPosPart_sub_hermNegPart hQ).symm
  have hQp_psd : Qp.PosSemidef := hermPosPart_posSemidef hQ
  have hQm_psd : Qm.PosSemidef := hermNegPart_posSemidef hQ
  have hQpQm : Qp * Qm = 0 := hermPosPart_mul_hermNegPart hQ
  set d := Fintype.card n
  set p : Fin d → ℝ := hP.isHermitian.eigenvalues₀
  set m : Fin d → ℝ := hQm_psd.isHermitian.eigenvalues₀
  have hp_nn : ∀ k, 0 ≤ p k := fun k => by
    rw [show p k = hP.isHermitian.eigenvalues (eigEquiv k) from
      (eigenvalues_eigEquiv hP.isHermitian k).symm]
    exact hP.eigenvalues_nonneg _
  have hm_nn : ∀ k, 0 ≤ m k := fun k => by
    rw [show m k = hQm_psd.isHermitian.eigenvalues (eigEquiv k) from
      (eigenvalues_eigEquiv hQm_psd.isHermitian k).symm]
    exact hQm_psd.eigenvalues_nonneg _
  have htraceP : rtrace P = ∑ k, p k := by
    rw [rtrace_eq_sum_eigenvalues hP.isHermitian]
    exact sum_eigenvalues_reindex hP.isHermitian id
  have htraceQm : rtrace Qm = ∑ k, m k := by
    rw [rtrace_eq_sum_eigenvalues hQm_psd.isHermitian]
    exact sum_eigenvalues_reindex hQm_psd.isHermitian id
  have hfrobP : frobSq P = ∑ k, (p k) ^ 2 := by
    rw [frobSq_hermitian_eq_sum_sq_eigenvalues hP.isHermitian]
    exact sum_eigenvalues_reindex hP.isHermitian (· ^ 2)
  have hfrobQm : frobSq Qm = ∑ k, (m k) ^ 2 := by
    rw [frobSq_hermitian_eq_sum_sq_eigenvalues hQm_psd.isHermitian]
    exact sum_eigenvalues_reindex hQm_psd.isHermitian (· ^ 2)
  have hgc : ∑ i, gc c (hP.1.eigenvalues i) = ∑ k, gc c (p k) :=
    sum_eigenvalues_reindex hP.isHermitian (gc c)
  have hexpand : frobSq (P + Q) =
      frobSq P + 2 * RCLike.re (P * Qp).trace -
        2 * RCLike.re (P * Qm).trace + frobSq Qp + frobSq Qm := by
    have h1 : frobSq (-Qm) = frobSq Qm := by
      unfold frobSq
      rw [conjTranspose_neg, neg_mul_neg]
    have h2 : RCLike.re (Qp * -Qm).trace = 0 := by
      rw [mul_neg, hQpQm]
      simp
    rw [hQdec, frobSq_add_hermitian hP.isHermitian
        (hQp_psd.isHermitian.sub hQm_psd.isHermitian),
      sub_eq_add_neg Qp Qm,
      frobSq_add_hermitian hQp_psd.isHermitian hQm_psd.isHermitian.neg,
      h1, h2, mul_add, mul_neg, trace_add, trace_neg, map_add, map_neg]
    ring
  have hPQp : 0 ≤ RCLike.re (P * Qp).trace :=
    trace_mul_nonneg_of_posSemidef hP hQp_psd
  have hvN : RCLike.re (P * Qm).trace ≤ ∑ k, p k * m k :=
    vonNeumann_trace_ineq hP.isHermitian hQm_psd.isHermitian
  have hstep4 : ∑ k, (p k - m k) ^ 2 ≤
      frobSq P - 2 * RCLike.re (P * Qm).trace + frobSq Qm := by
    have hsplit : ∑ k, (p k - m k) ^ 2 =
        ∑ k, (p k) ^ 2 - 2 * ∑ k, p k * m k + ∑ k, (m k) ^ 2 := by
      simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        Finset.mul_sum, mul_assoc]
    rw [hsplit, hfrobP, hfrobQm]
    linarith
  have hstep5 : c * rtrace P + (∑ k, gc c (p k)) -
      2 * c * rtrace Qm ≤ ∑ k, (p k - m k) ^ 2 := by
    rw [htraceP, htraceQm]
    exact sum_sq_sub_ge_gc hp_nn hm_nn hc.le
  have hstep6 : 2 * c * rtrace Qp - c ^ 2 * b ≤ frobSq Qp := by
    rw [hQp_def, rtrace_hermPosPart, frobSq_hermPosPart]
    refine sum_sq_lower_of_card_pos_le ?_ c
    calc
      #{i | (hQ.eigenvalues i)⁺ ≠ 0} = #{i | 0 < hQ.eigenvalues i} := by
        congr 1
        ext i
        simp [posPart_eq_zero, not_le]
      _ ≤ b := hb
  have htraceQ : 2 * c * rtrace Q =
      2 * c * rtrace Qp - 2 * c * rtrace Qm := by
    rw [hQdec, rtrace_sub]
    ring
  rw [hgc]
  linarith [hstep4, hstep5, hstep6, hPQp, hexpand, htraceQ]

/-- The `c = 2` form used for simple critical zeros. -/
theorem rankTraceSpectralGcTwo {P Q : Matrix n n 𝕜}
    (hP : P.PosSemidef) (hQ : Q.IsHermitian)
    {b : ℕ} (hb : posIndex hQ ≤ b) :
    2 * rtrace P + (∑ i, gc 2 (hP.1.eigenvalues i)) +
        4 * rtrace Q - 4 * b ≤ frobSq (P + Q) := by
  have h := rankTraceSpectralGc hP hQ hb (c := 2) (by norm_num)
  norm_num at h ⊢
  exact h

lemma sumEigenvalues_congr_matrix {A B : Matrix n n 𝕜}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hAB : A = B) (g : ℝ → ℝ) :
    (∑ i, g (hA.eigenvalues i)) = ∑ i, g (hB.eigenvalues i) := by
  subst B
  rfl

/-! ## Retaining the simple-zero Gram spectrum -/

open Zeta23.ZeroSide

section Block

variable {ι d : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype d] [DecidableEq d]

namespace ZeroBlockData

variable (D : Zeta23.ZeroSide.ZeroBlockData ι d)

/-- The unnormalised contribution of the simple on-line zeros alone. -/
def simplePart : Matrix d d ℂ :=
  ∑ z ∈ D.S₁, (D.m z : ℂ) • vecMulVec (D.v z) (D.v z)

/-- The unnormalised contribution of the multiple on-line zeros. -/
def multiplePart : Matrix d d ℂ :=
  ∑ z ∈ D.S₂, (D.m z : ℂ) • vecMulVec (D.v z) (D.v z)

lemma onPart_eq_simplePart_add_multiplePart :
    D.onPart = simplePart D + multiplePart D := by
  unfold Zeta23.ZeroSide.ZeroBlockData.onPart simplePart multiplePart
  rw [D.onLine_eq_S₁_union_S₂, sum_union D.disjoint_S₁_S₂]

/-- The simple on-line block in the normalised `hat` units. -/
def simpleP (c : ℝ) : Matrix d d ℂ :=
  ((c⁻¹ : ℝ) : ℂ) • simplePart D

/-- The normalized sampling vector attached to a literal simple on-line zero. -/
def simpleVhat (c : ℝ) : D.S₁ → d → ℂ :=
  fun z k => D.v z k / (Real.sqrt c : ℂ)

/-- The Gram matrix on the literal simple-zero index set. -/
def simpleGram (c : ℝ) : Matrix D.S₁ D.S₁ ℂ :=
  (Wmat (fun _ : D.S₁ => (1 : ℝ)) (simpleVhat D c))ᴴ *
    Wmat (fun _ : D.S₁ => (1 : ℝ)) (simpleVhat D c)

omit [DecidableEq d] in
lemma simpleGram_posSemidef (c : ℝ) : (simpleGram D c).PosSemidef :=
  Matrix.posSemidef_conjTranspose_mul_self _

/-- The multiple on-line block in the normalised `hat` units. -/
def multipleP (c : ℝ) : Matrix d d ℂ :=
  ((c⁻¹ : ℝ) : ℂ) • multiplePart D

/-- Everything except the simple on-line block.  Unlike the old `blockQ`,
this includes the positive multiple-zero block. -/
def retainedQ (c : ℝ) : Matrix d d ℂ :=
  multipleP D c + D.blockQ c

lemma blockP_eq_simpleP_add_multipleP (c : ℝ) :
    D.blockP c = simpleP D c + multipleP D c := by
  unfold Zeta23.ZeroSide.ZeroBlockData.blockP simpleP multipleP
  rw [onPart_eq_simplePart_add_multiplePart D, smul_add]

lemma simpleP_add_retainedQ (c : ℝ) :
    simpleP D c + retainedQ D c = D.blockP c + D.blockQ c := by
  rw [blockP_eq_simpleP_add_multipleP D]
  unfold retainedQ
  abel

lemma simplePart_posSemidef : (simplePart D).PosSemidef := by
  unfold simplePart
  refine posSemidef_sum _ fun z hz => ?_
  have hzOn : z ∈ D.onLine := by
    rw [D.onLine_eq_S₁_union_S₂]
    exact Finset.mem_union_left _ hz
  exact Zeta23.ZeroSide.ZeroBlockData.posSemidef_smul_vecMulVec
    (D.star_v_of_onLine ((D.mem_onLine).mp hzOn))
    (Nat.cast_nonneg (D.m z))

lemma multiplePart_posSemidef : (multiplePart D).PosSemidef := by
  unfold multiplePart
  refine posSemidef_sum _ fun z hz => ?_
  have hzOn : z ∈ D.onLine := by
    rw [D.onLine_eq_S₁_union_S₂]
    exact Finset.mem_union_right _ hz
  exact Zeta23.ZeroSide.ZeroBlockData.posSemidef_smul_vecMulVec
    (D.star_v_of_onLine ((D.mem_onLine).mp hzOn))
    (Nat.cast_nonneg (D.m z))

lemma simpleP_posSemidef {c : ℝ} (hc : 0 < c) :
    (simpleP D c).PosSemidef :=
  (simplePart_posSemidef D).smul
    (Complex.zero_le_real.mpr (inv_nonneg.mpr hc.le))

lemma multipleP_posSemidef {c : ℝ} (hc : 0 < c) :
    (multipleP D c).PosSemidef :=
  (multiplePart_posSemidef D).smul
    (Complex.zero_le_real.mpr (inv_nonneg.mpr hc.le))

/-- The ambient simple block is `W Wᴴ` for the normalized simple sampling
vectors. -/
theorem simpleP_eq_Pmat {c : ℝ} (hc : 0 < c) :
    simpleP D c = Pmat (𝕜 := ℂ) (fun _ : D.S₁ => (1 : ℝ)) (simpleVhat D c) := by
  ext a b
  rw [Pmat_apply (fun _ => zero_le_one)]
  simp only [simpleP, simplePart, Matrix.smul_apply, Matrix.sum_apply,
    Matrix.vecMulVec_apply, smul_eq_mul, Finset.mul_sum]
  rw [← Finset.sum_coe_sort D.S₁]
  refine Finset.sum_congr rfl fun z _ => ?_
  have hzData : D.σ z = z ∧ D.m z = 1 := by
    simpa [Zeta23.ZeroSide.ZeroBlockData.S₁] using z.2
  have hreal : starRingEnd ℂ (D.v z b) = D.v z b := by
    have h := congrFun (D.star_v_of_onLine hzData.1) b
    rwa [Pi.star_apply, RCLike.star_def] at h
  simp only [simpleVhat]
  rw [map_div₀, hreal, Complex.conj_ofReal, hzData.2]
  norm_num
  have hsq : ((Real.sqrt c : ℂ)) ^ 2 = (c : ℂ) := by
    rw [sq, ← Complex.ofReal_mul, Real.mul_self_sqrt hc.le]
  have hsqrt : (Real.sqrt c : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hc).ne'
  have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  rw [div_mul_div_comm, ← sq, hsq]
  field_simp

/-- The retained ambient spectral sum is exactly the spectral sum of the
simple-zero Gram matrix; zero eigenvalues disappear because `g₂(0)=0`. -/
theorem sumGc_simpleP_eq_simpleGram {c : ℝ} (hc : 0 < c) :
    (∑ i, gc 2 ((simpleP_posSemidef D hc).1.eigenvalues i)) =
      ∑ z, gc 2 ((simpleGram_posSemidef D c).1.eigenvalues z) := by
  let W := Wmat (fun _ : D.S₁ => (1 : ℝ)) (simpleVhat D c)
  have hP : simpleP D c = W * Wᴴ := simpleP_eq_Pmat D hc
  calc
    (∑ i, gc 2 ((simpleP_posSemidef D hc).1.eigenvalues i)) =
        ∑ i, gc 2 ((Matrix.posSemidef_self_mul_conjTranspose W).1.eigenvalues i) := by
      exact sumEigenvalues_congr_matrix (simpleP_posSemidef D hc).1
        (Matrix.posSemidef_self_mul_conjTranspose W).1 hP (gc 2)
    _ = ∑ z, gc 2 ((Matrix.posSemidef_conjTranspose_mul_self W).1.eigenvalues z) :=
      sum_eigenvalues_comm W (gc 2) (by norm_num)
    _ = ∑ z, gc 2 ((simpleGram_posSemidef D c).1.eigenvalues z) := rfl

/-- Devine's nonnegative convex defect, written without a numerical oracle. -/
def simpleDefect (x : ℝ) : ℝ := 1 + gc 2 x

lemma simpleDefect_eq_sq_sub_one {x : ℝ} (hx : x ≤ 2) :
    simpleDefect x = (x - 1) ^ 2 := by
  rw [simpleDefect, gc_of_le hx]
  ring

lemma simpleDefect_eq_two_mul_sub_three {x : ℝ} (hx : 2 ≤ x) :
    simpleDefect x = 2 * x - 3 := by
  rw [simpleDefect, gc_of_ge hx]
  ring

lemma simpleDefect_nonneg (x : ℝ) : 0 ≤ simpleDefect x := by
  rcases le_or_gt x 2 with h | h
  · rw [simpleDefect_eq_sq_sub_one h]
    positivity
  · rw [simpleDefect_eq_two_mul_sub_three h.le]
    linarith

/-- The three pairwise off-diagonal energies of a `3 × 3` Hermitian block. -/
def tripleOffDiagEnergy (K : Matrix (Fin 3) (Fin 3) ℂ) : ℝ :=
  2 * (‖K 0 1‖ ^ 2 + ‖K 1 2‖ ^ 2 + ‖K 0 2‖ ^ 2)

omit [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d] in
lemma frobSq_eq_sum_norm_sq_local
    {n : Type*} [Fintype n] (K : Matrix n n ℂ) :
    frobSq K = ∑ i, ∑ j, ‖K i j‖ ^ 2 := by
  unfold frobSq
  simp only [trace, diag_apply, mul_apply, conjTranspose_apply, map_sum,
    RCLike.star_def]
  rw [Finset.sum_comm]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  rw [RCLike.conj_mul, ← RCLike.ofReal_pow, RCLike.ofReal_re]

omit [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d] in
/-- A three-dimensional spectral block pays either its full off-diagonal
quadratic energy or one unit of convex defect.  The cap at one is what lets the
qualitative Montgomery--Taylor certificate avoid any interval arithmetic. -/
theorem min_tripleOffDiagEnergy_one_le_sum_simpleDefect
    {K : Matrix (Fin 3) (Fin 3) ℂ} (hK : K.IsHermitian) :
    min (tripleOffDiagEnergy K) 1 ≤
      ∑ i, simpleDefect (hK.eigenvalues i) := by
  by_cases hle : ∀ i, hK.eigenvalues i ≤ 2
  · have hdef : (∑ i, simpleDefect (hK.eigenvalues i)) =
        ∑ i, (hK.eigenvalues i - 1) ^ 2 := by
      refine Finset.sum_congr rfl fun i _ => simpleDefect_eq_sq_sub_one (hle i)
    have hspec : (∑ i, (hK.eigenvalues i - 1) ^ 2) =
        frobSq K - 2 * rtrace K + 3 := by
      rw [rtrace_eq_sum_eigenvalues hK,
        frobSq_hermitian_eq_sum_sq_eigenvalues hK]
      simp_rw [sub_sq]
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
      simp
    have hsymm : ∀ i j, ‖K j i‖ = ‖K i j‖ := by
      intro i j
      have hij := congrFun (congrFun hK i) j
      rw [conjTranspose_apply] at hij
      calc
        ‖K j i‖ = ‖starRingEnd ℂ (K j i)‖ := by simp
        _ = ‖K i j‖ := congrArg norm hij
    have hgap : ∀ i, 0 ≤ ‖K i i‖ ^ 2 - 2 * (K i i).re + 1 := by
      intro i
      nlinarith [sq_nonneg (‖K i i‖ - 1), Complex.re_le_norm (K i i)]
    have hentry : tripleOffDiagEnergy K ≤ frobSq K - 2 * rtrace K + 3 := by
      rw [frobSq_eq_sum_norm_sq_local]
      unfold tripleOffDiagEnergy rtrace trace
      simp only [diag_apply, Fin.sum_univ_succ, Finset.univ_unique,
        Finset.sum_singleton, map_add]
      norm_num
      have h10 := congrArg (fun x : ℝ => x ^ 2) (hsymm (0 : Fin 3) 1)
      have h20 := congrArg (fun x : ℝ => x ^ 2) (hsymm (0 : Fin 3) 2)
      have h21 := congrArg (fun x : ℝ => x ^ 2) (hsymm (1 : Fin 3) 2)
      nlinarith [hgap 0, hgap 1, hgap 2, h10, h20, h21]
    rw [hdef, hspec]
    exact (min_le_left _ _).trans hentry
  · push Not at hle
    obtain ⟨i, hi⟩ := hle
    have hiDef : 1 < simpleDefect (hK.eigenvalues i) := by
      rw [simpleDefect_eq_two_mul_sub_three hi.le]
      linarith
    have hsingle : simpleDefect (hK.eigenvalues i) ≤
        ∑ j, simpleDefect (hK.eigenvalues j) := by
      exact Finset.single_le_sum (fun j _ => simpleDefect_nonneg _) (Finset.mem_univ i)
    exact (min_le_right _ _).trans (hiDef.le.trans hsingle)

omit [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d] in
/-- Schur--Jensen in an arbitrary orthonormal basis.  The proof factors a
positive matrix through its canonical square root and uses the already checked
`WWᴴ`/`WᴴW` spectral transfer, so no unproved eigenvalue-invariance principle
is assumed. -/
theorem sumGc_diag_unitaryConj_le_sumGc_eigenvalues
    {n : Type*} [Fintype n] [DecidableEq n]
    {K : Matrix n n ℂ} (hK : K.PosSemidef)
    (U : Matrix.unitaryGroup n ℂ) {c : ℝ} (hc : 0 ≤ c) :
    (∑ j, gc c (RCLike.re
      (((U : Matrix n n ℂ)ᴴ * K * (U : Matrix n n ℂ)) j j))) ≤
        ∑ i, gc c (hK.1.eigenvalues i) := by
  let S : Matrix n n ℂ := CFC.sqrt K
  let W : Matrix n n ℂ := S * (U : Matrix n n ℂ)
  have hSstar : Sᴴ = S := by
    change star S = S
    exact (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg K)).star_eq
  have hSsq : S * S = K := by
    exact CFC.sqrt_mul_sqrt_self K
  have hUU : (U : Matrix n n ℂ) * (U : Matrix n n ℂ)ᴴ = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using Unitary.coe_mul_star_self U
  have hWW : W * Wᴴ = K := by
    unfold W
    rw [conjTranspose_mul, hSstar]
    rw [mul_assoc, ← mul_assoc (U : Matrix n n ℂ), hUU, one_mul, hSsq]
  have hWtW : Wᴴ * W =
      (U : Matrix n n ℂ)ᴴ * K * (U : Matrix n n ℂ) := by
    unfold W
    rw [conjTranspose_mul, hSstar]
    simp only [mul_assoc, ← hSsq]
  have hM : (Wᴴ * W).PosSemidef := Matrix.posSemidef_conjTranspose_mul_self W
  have hSchur := sum_gc_diag_le_sum_gc_eigenvalues hM hc
  calc
    (∑ j, gc c (RCLike.re
        (((U : Matrix n n ℂ)ᴴ * K * (U : Matrix n n ℂ)) j j))) =
        ∑ j, gc c (RCLike.re ((Wᴴ * W) j j)) := by rw [hWtW]
    _ ≤ ∑ i, gc c (hM.1.eigenvalues i) := hSchur
    _ = ∑ i, gc c
        ((Matrix.posSemidef_self_mul_conjTranspose W).1.eigenvalues i) :=
      (sum_eigenvalues_comm W (gc c) (gc_zero hc)).symm
    _ = ∑ i, gc c (hK.1.eigenvalues i) :=
      sumEigenvalues_congr_matrix
        (Matrix.posSemidef_self_mul_conjTranspose W).1 hK.1 hWW (gc c)

omit [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d] in
/-- Pinching a positive matrix into disjoint three-dimensional principal
blocks can only decrease the total `g_c` spectral sum. -/
theorem sumGc_tripleBlocks_le_sumGc_eigenvalues
    {β : Type*} [Fintype β] [DecidableEq β]
    {K : Matrix (Fin 3 × β) (Fin 3 × β) ℂ} (hK : K.PosSemidef)
    {c : ℝ} (hc : 0 ≤ c) :
    (∑ b, ∑ i, gc c
      ((hK.1.submatrix (fun j : Fin 3 => (j, b))).eigenvalues i)) ≤
        ∑ p, gc c (hK.1.eigenvalues p) := by
  let H : β → Matrix (Fin 3) (Fin 3) ℂ :=
    fun b => K.submatrix (fun j : Fin 3 => (j, b)) (fun j : Fin 3 => (j, b))
  let hH : ∀ b, (H b).IsHermitian := fun b => hK.1.submatrix _
  let Ub : β → Matrix (Fin 3) (Fin 3) ℂ :=
    fun b => (hH b).eigenvectorUnitary
  let Umat : Matrix (Fin 3 × β) (Fin 3 × β) ℂ := Matrix.blockDiagonal Ub
  have hUstarU : Umatᴴ * Umat = 1 := by
    unfold Umat
    rw [Matrix.blockDiagonal_conjTranspose, ← Matrix.blockDiagonal_mul,
      ← Matrix.blockDiagonal_one]
    congr 1
    funext b
    exact Unitary.coe_star_mul_self (hH b).eigenvectorUnitary
  let U : Matrix.unitaryGroup (Fin 3 × β) ℂ :=
    ⟨Umat, Matrix.mem_unitaryGroup_iff'.2 (by
      simpa [Matrix.star_eq_conjTranspose] using hUstarU)⟩
  have hdiag : ∀ b i,
      RCLike.re (((U : Matrix (Fin 3 × β) (Fin 3 × β) ℂ)ᴴ * K *
          (U : Matrix (Fin 3 × β) (Fin 3 × β) ℂ)) (i, b) (i, b)) =
        (hH b).eigenvalues i := by
    intro b i
    have hblock :
        (((U : Matrix (Fin 3 × β) (Fin 3 × β) ℂ)ᴴ * K *
            (U : Matrix (Fin 3 × β) (Fin 3 × β) ℂ)) (i, b) (i, b)) =
          ((Ub b)ᴴ * H b * Ub b) i i := by
      simp only [U, Umat, Matrix.mul_apply, Matrix.blockDiagonal_apply,
        Matrix.conjTranspose_apply, RCLike.star_def]
      simp only [Fintype.sum_prod_type]
      simp [H, Matrix.submatrix]
      have hinner : ∀ x : Fin 3,
          (∑ x₁ : Fin 3, ∑ x₂ : β,
              starRingEnd ℂ (if x₂ = b then Ub x₂ x₁ i else 0) *
                K (x₁, x₂) (x, b)) =
            ∑ x₁ : Fin 3, starRingEnd ℂ (Ub b x₁ i) * K (x₁, b) (x, b) := by
        intro x
        refine Finset.sum_congr rfl fun x₁ _ => ?_
        rw [Finset.sum_eq_single b]
        · simp
        · intro b' _ hb'
          rw [if_neg hb']
          simp
        · simp
      simp_rw [hinner]
    have hspectral := (hH b).conjStarAlgAut_star_eigenvectorUnitary
    rw [Unitary.conjStarAlgAut_star_apply] at hspectral
    have hii := congrFun (congrFun hspectral i) i
    simp only [Matrix.diagonal_apply_eq, Function.comp_apply] at hii
    have heq : ((Ub b)ᴴ * H b * Ub b) i i =
        ((hH b).eigenvalues i : ℂ) := by
      simpa [Ub, Matrix.star_eq_conjTranspose] using hii
    rw [hblock, heq]
    exact RCLike.ofReal_re _
  have hSchur := sumGc_diag_unitaryConj_le_sumGc_eigenvalues hK U hc
  calc
    (∑ b, ∑ i, gc c
        ((hK.1.submatrix (fun j : Fin 3 => (j, b))).eigenvalues i)) =
        ∑ p : Fin 3 × β, gc c
          ((hK.1.submatrix (fun j : Fin 3 => (j, p.2))).eigenvalues p.1) := by
      rw [Fintype.sum_prod_type, Finset.sum_comm]
    _ = ∑ p, gc c (RCLike.re
        (((U : Matrix (Fin 3 × β) (Fin 3 × β) ℂ)ᴴ * K *
          (U : Matrix (Fin 3 × β) (Fin 3 × β) ℂ)) p p)) := by
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [hdiag p.2 p.1]
    _ ≤ ∑ p, gc c (hK.1.eigenvalues p) := hSchur

omit [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d] in
theorem sumSimpleDefect_tripleBlocks_le_sumSimpleDefect_eigenvalues
    {β : Type*} [Fintype β] [DecidableEq β]
    {K : Matrix (Fin 3 × β) (Fin 3 × β) ℂ} (hK : K.PosSemidef) :
    (∑ b, ∑ i, simpleDefect
      ((hK.1.submatrix (fun j : Fin 3 => (j, b))).eigenvalues i)) ≤
        ∑ p, simpleDefect (hK.1.eigenvalues p) := by
  have hgc := sumGc_tripleBlocks_le_sumGc_eigenvalues hK (c := 2) (by norm_num)
  unfold simpleDefect
  simp only [Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    Nat.cast_ofNat, nsmul_eq_mul]
  have hcard : (Fintype.card (Fin 3 × β) : ℝ) = 3 * Fintype.card β := by
    simp [Fintype.card_prod]
  rw [hcard]
  norm_num
  linarith

omit [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d] in
/-- Disjoint triples pay additively: the global convex defect dominates the
sum of the capped three-correlation energies of all principal blocks. -/
theorem sum_min_tripleOffDiagEnergy_le_sum_simpleDefect
    {β : Type*} [Fintype β] [DecidableEq β]
    {K : Matrix (Fin 3 × β) (Fin 3 × β) ℂ} (hK : K.PosSemidef) :
    (∑ b, min
      (tripleOffDiagEnergy
        (K.submatrix (fun j : Fin 3 => (j, b)) (fun j : Fin 3 => (j, b)))) 1) ≤
      ∑ p, simpleDefect (hK.1.eigenvalues p) := by
  calc
    (∑ b, min
        (tripleOffDiagEnergy
          (K.submatrix (fun j : Fin 3 => (j, b)) (fun j : Fin 3 => (j, b)))) 1) ≤
        ∑ b, ∑ i, simpleDefect
          ((hK.1.submatrix (fun j : Fin 3 => (j, b))).eigenvalues i) := by
      refine Finset.sum_le_sum fun b _ => ?_
      exact min_tripleOffDiagEnergy_one_le_sum_simpleDefect
        (hK.1.submatrix (fun j : Fin 3 => (j, b)))
    _ ≤ ∑ p, simpleDefect (hK.1.eigenvalues p) :=
      sumSimpleDefect_tripleBlocks_le_sumSimpleDefect_eigenvalues hK

/-- Gram matrix of a finite family of complex columns. -/
def columnGram {α n : Type*} [Fintype n]
    (v : α → n → ℂ) : Matrix α α ℂ :=
  (Wmat (fun _ : α => (1 : ℝ)) v)ᴴ * Wmat (fun _ : α => (1 : ℝ)) v

lemma columnGram_posSemidef {α n : Type*} [Fintype α]
    [Fintype n] (v : α → n → ℂ) :
    (columnGram v).PosSemidef := Matrix.posSemidef_conjTranspose_mul_self _

/-- Reindex a family into triples after adjoining explicit zero columns. -/
def paddedPackedFamily
    {α κ β n : Type*} (e : Fin 3 × β ≃ Sum α κ)
    (v : α → n → ℂ) :
    Fin 3 × β → n → ℂ :=
  fun p => Sum.elim v (fun _ _ => 0) (e p)

omit [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d] in
/-- Exact packing ledger.  Adding `r` zero columns costs exactly `r` units
because `f(0)=1`; apart from that explicit padding cost, all disjoint triple
energies are paid by the original Gram defect. -/
theorem packedTripleEnergy_le_originalDefect_add_padding
    {α κ β n : Type*}
    [Fintype α] [DecidableEq α] [Fintype κ]
    [Fintype β] [DecidableEq β] [Fintype n] [DecidableEq n]
    (v : α → n → ℂ) (e : Fin 3 × β ≃ Sum α κ) :
    let vp := paddedPackedFamily e v
    (∑ b, min
      (tripleOffDiagEnergy
        ((columnGram vp).submatrix (fun j : Fin 3 => (j, b))
          (fun j : Fin 3 => (j, b)))) 1) ≤
      (∑ i, simpleDefect ((columnGram_posSemidef v).1.eigenvalues i)) +
        Fintype.card κ := by
  let vp := paddedPackedFamily e v
  let W₀ := Wmat (fun _ : α => (1 : ℝ)) v
  let Wp := Wmat (fun _ : Fin 3 × β => (1 : ℝ)) vp
  have hP : Wp * Wpᴴ = W₀ * W₀ᴴ := by
    change Pmat (fun _ : Fin 3 × β => (1 : ℝ)) vp =
      Pmat (fun _ : α => (1 : ℝ)) v
    ext a b
    rw [Pmat_apply (fun _ => zero_le_one), Pmat_apply (fun _ => zero_le_one)]
    norm_num
    let g : Sum α κ → ℂ := fun s =>
      Sum.elim v (fun _ _ => 0) s a * starRingEnd ℂ (Sum.elim v (fun _ _ => 0) s b)
    change (∑ x, g (e x)) = ∑ x, v x a * starRingEnd ℂ (v x b)
    rw [e.sum_comp]
    simp [g, Fintype.sum_sum_type]
  have hgc :
      (∑ p, gc 2 ((columnGram_posSemidef vp).1.eigenvalues p)) =
        ∑ i, gc 2 ((columnGram_posSemidef v).1.eigenvalues i) := by
    calc
      (∑ p, gc 2 ((columnGram_posSemidef vp).1.eigenvalues p)) =
          ∑ p, gc 2
            ((Matrix.posSemidef_conjTranspose_mul_self Wp).1.eigenvalues p) := rfl
      _ = ∑ j, gc 2
          ((Matrix.posSemidef_self_mul_conjTranspose Wp).1.eigenvalues j) :=
        (sum_eigenvalues_comm Wp (gc 2) (by norm_num)).symm
      _ = ∑ j, gc 2
          ((Matrix.posSemidef_self_mul_conjTranspose W₀).1.eigenvalues j) :=
        sumEigenvalues_congr_matrix
          (Matrix.posSemidef_self_mul_conjTranspose Wp).1
          (Matrix.posSemidef_self_mul_conjTranspose W₀).1 hP (gc 2)
      _ = ∑ i, gc 2
          ((Matrix.posSemidef_conjTranspose_mul_self W₀).1.eigenvalues i) :=
        sum_eigenvalues_comm W₀ (gc 2) (by norm_num)
      _ = ∑ i, gc 2 ((columnGram_posSemidef v).1.eigenvalues i) := rfl
  have hcard : Fintype.card (Fin 3 × β) =
      Fintype.card α + Fintype.card κ := by
    calc
      Fintype.card (Fin 3 × β) = Fintype.card (Sum α κ) := Fintype.card_congr e
      _ = Fintype.card α + Fintype.card κ := Fintype.card_sum
  have hdefect :
      (∑ p, simpleDefect ((columnGram_posSemidef vp).1.eigenvalues p)) =
        (∑ i, simpleDefect ((columnGram_posSemidef v).1.eigenvalues i)) +
          Fintype.card κ := by
    unfold simpleDefect
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
    norm_num
    rw [hgc]
    have hcardNat : 3 * Fintype.card β =
        Fintype.card α + Fintype.card κ := by
      simpa [Fintype.card_prod] using hcard
    have hcardReal : (3 : ℝ) * Fintype.card β =
        Fintype.card α + Fintype.card κ := by
      exact_mod_cast hcardNat
    linarith
  calc
    (∑ b, min
        (tripleOffDiagEnergy
          ((columnGram vp).submatrix (fun j : Fin 3 => (j, b))
            (fun j : Fin 3 => (j, b)))) 1) ≤
        ∑ p, simpleDefect ((columnGram_posSemidef vp).1.eigenvalues p) :=
      sum_min_tripleOffDiagEnergy_le_sum_simpleDefect
        (columnGram_posSemidef vp)
    _ = (∑ i, simpleDefect ((columnGram_posSemidef v).1.eigenvalues i)) +
        Fintype.card κ := hdefect

/-- The exact packing ledger specialized to the literal simple-zero columns
of a `ZeroBlockData`.  The only loss is the displayed number of zero padding
columns needed to complete the disjoint triples. -/
theorem packedTripleEnergy_simpleVhat_le_retainedDefect_add_padding
    {κ β : Type*} [Fintype κ]
    [Fintype β] [DecidableEq β]
    (c : ℝ) (e : Fin 3 × β ≃ Sum D.S₁ κ) :
    let vp := paddedPackedFamily e (simpleVhat D c)
    (∑ b, min
      (tripleOffDiagEnergy
        ((columnGram vp).submatrix (fun j : Fin 3 => (j, b))
          (fun j : Fin 3 => (j, b)))) 1) ≤
      (∑ z, simpleDefect ((simpleGram_posSemidef D c).1.eigenvalues z)) +
        Fintype.card κ := by
  simpa only [columnGram, simpleGram] using
    (packedTripleEnergy_le_originalDefect_add_padding
      (v := simpleVhat D c) e)

/-- `s₁ + Σ g₂` is precisely `tr f(K)` on the `s₁ × s₁` simple Gram
matrix. -/
theorem retainedTerm_eq_sum_simpleDefect {c : ℝ} (hc : 0 < c) :
    (D.s₁ : ℝ) + ∑ i, gc 2 ((simpleP_posSemidef D hc).1.eigenvalues i) =
      ∑ z, simpleDefect ((simpleGram_posSemidef D c).1.eigenvalues z) := by
  rw [sumGc_simpleP_eq_simpleGram D hc]
  unfold simpleDefect
  rw [Finset.sum_add_distrib]
  simp [Zeta23.ZeroSide.ZeroBlockData.s₁]

omit [DecidableEq d] in
lemma rank_multiplePart_le : (multiplePart D).rank ≤ D.s₂ := by
  unfold multiplePart Zeta23.ZeroSide.ZeroBlockData.s₂
  exact (Zeta23.ZeroSide.rank_sum_le _ _ (fun _ => 1)
    (fun z _ => Zeta23.ZeroSide.rank_smul_vecMulVec_le _ _ _)).trans (by simp)

lemma rank_multipleP_le {c : ℝ} (hc : 0 < c) :
    (multipleP D c).rank ≤ D.s₂ := by
  unfold multipleP
  rw [Zeta23.ZeroSide.rank_smul_of_ne_zero _ (by
    exact_mod_cast (inv_ne_zero hc.ne'))]
  exact rank_multiplePart_le D

lemma retainedQ_isHermitian (c : ℝ) : (retainedQ D c).IsHermitian :=
  (Zeta23.ZeroSide.ZeroBlockData.isHermitian_real_smul
    (multiplePart_posSemidef D).isHermitian c⁻¹).add (D.blockQ_isHermitian c)

/-- Moving the multiple on-line block into the remainder costs at most `s₂`
additional positive directions. -/
theorem posIndex_retainedQ_le (Pr : D.PairReps) {c : ℝ} (hc : 0 < c) :
    posIndex (retainedQ_isHermitian D c) ≤ D.s₂ + Pr.p := by
  have hM := multipleP_posSemidef D hc
  have h := posIndex_add_le hM.isHermitian (D.blockQ_isHermitian c)
  rw [posIndex_eq_rank_of_posSemidef hM] at h
  exact h.trans (Nat.add_le_add (rank_multipleP_le D hc)
    (D.posIndex_blockQ_le Pr hc))

/-- The trace of the unnormalised simple block is exactly the sum of the
squared sample norms of the simple-zero vectors. -/
lemma rtrace_simplePart :
    rtrace (simplePart D) = ∑ z ∈ D.S₁, ∑ k, ‖D.v z k‖ ^ 2 := by
  unfold simplePart rtrace
  rw [trace_sum, map_sum]
  refine sum_congr rfl fun z hz => ?_
  have hzData : D.σ z = z ∧ D.m z = 1 := by
    simpa [Zeta23.ZeroSide.ZeroBlockData.S₁] using hz
  have h := congrFun (D.star_v_of_onLine hzData.1)
  rw [trace_smul, trace_vecMulVec, smul_eq_mul, dotProduct]
  have hsq : ∑ k, D.v z k * D.v z k =
      ((∑ k, ‖D.v z k‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    refine sum_congr rfl fun k _ => ?_
    have hk : (starRingEnd ℂ) (D.v z k) = D.v z k := by
      have := h k
      rwa [Pi.star_apply, RCLike.star_def] at this
    calc
      D.v z k * D.v z k = (starRingEnd ℂ) (D.v z k) * D.v z k := by rw [hk]
      _ = _ := RCLike.conj_mul (D.v z k)
  rw [hsq, ← Complex.ofReal_natCast, ← Complex.ofReal_mul,
    RCLike.re_to_complex, Complex.ofReal_re, hzData.2]
  simp

/-- Each normalized simple vector has squared norm at most one, so the trace
of the simple block is bounded by the literal number `s₁` of simple on-line
zeros. -/
theorem rtrace_simpleP_le {c : ℝ} (hc : 0 < c)
    (hPois : ∀ z ∈ D.onLine, ∑ k, ‖D.v z k‖ ^ 2 ≤ c) :
    rtrace (simpleP D c) ≤ (D.s₁ : ℝ) := by
  have htr : rtrace (simpleP D c) = c⁻¹ * rtrace (simplePart D) := by
    simp only [rtrace, simpleP, trace_smul, smul_eq_mul,
      RCLike.re_to_complex, Complex.re_ofReal_mul]
  rw [htr, rtrace_simplePart D, Finset.mul_sum]
  calc
    ∑ z ∈ D.S₁, c⁻¹ * ∑ k, ‖D.v z k‖ ^ 2 ≤ ∑ _z ∈ D.S₁, (1 : ℝ) := by
      refine sum_le_sum fun z hz => ?_
      have hzOn : z ∈ D.onLine := by
        rw [D.onLine_eq_S₁_union_S₂]
        exact Finset.mem_union_left _ hz
      calc
        c⁻¹ * ∑ k, ‖D.v z k‖ ^ 2 ≤ c⁻¹ * c := by
          exact mul_le_mul_of_nonneg_left (hPois z hzOn)
            (inv_nonneg.mpr hc.le)
        _ = 1 := inv_mul_cancel₀ hc.ne'
    _ = (D.s₁ : ℝ) := by
      simp [Zeta23.ZeroSide.ZeroBlockData.s₁]

/-- The multiplicity-aware zero-side inequality with the full simple Gram
spectrum retained.  This is a strict strengthening of the checked `c = 2`
baseline: the extra term is `s₁ + Σ g₂(λ)`, which will become the nonnegative
convex defect `tr f(K)` on the simple-zero Gram matrix. -/
theorem multTwoRetainedSpectrum (Pr : D.PairReps) {c : ℝ} (hc : 0 < c)
    (hPois : ∀ z ∈ D.onLine, ∑ k, ‖D.v z k‖ ^ 2 ≤ c) :
    4 * rtrace (D.blockP c + D.blockQ c) -
        frobSq (D.blockP c + D.blockQ c) - 2 * (D.Ncount : ℝ) +
        ((D.s₁ : ℝ) + ∑ i, gc 2 ((simpleP_posSemidef D hc).1.eigenvalues i))
      ≤ (D.s₁ : ℝ) := by
  have hR := rankTraceSpectralGcTwo (simpleP_posSemidef D hc)
    (retainedQ_isHermitian D c) (posIndex_retainedQ_le D Pr hc)
  have htr := rtrace_simpleP_le D hc hPois
  have hNnat := D.s₁_add_two_s₂_add_two_p_le_Ncount Pr
  have hN : (D.s₁ : ℝ) + 2 * D.s₂ + 2 * Pr.p ≤ D.Ncount := by
    exact_mod_cast hNnat
  have hA := simpleP_add_retainedQ D c
  rw [← hA, rtrace_add]
  norm_num at hR
  linarith

/-- The strengthened zero-side inequality in its intrinsic Gram form.  Every
summand in the retained term is nonnegative by `simpleDefect_nonneg`. -/
theorem multTwoRetainedDefect (Pr : D.PairReps) {c : ℝ} (hc : 0 < c)
    (hPois : ∀ z ∈ D.onLine, ∑ k, ‖D.v z k‖ ^ 2 ≤ c) :
    4 * rtrace (D.blockP c + D.blockQ c) -
        frobSq (D.blockP c + D.blockQ c) - 2 * (D.Ncount : ℝ) +
        (∑ z, simpleDefect ((simpleGram_posSemidef D c).1.eigenvalues z))
      ≤ (D.s₁ : ℝ) := by
  rw [← retainedTerm_eq_sum_simpleDefect D hc]
  exact multTwoRetainedSpectrum D Pr hc hPois

end ZeroBlockData
end Block

/-! ## Concrete zeta-zero instantiation -/

section Inst

open Zeta23 Classical
open Zeta23.ZeroSide

variable (Z : ZeroConfig) (T : ℝ) (P : Params)

/-- The finite Gram matrix indexed by the literal simple critical zeros in
the enlarged Zeta23 window. -/
def zetaSimpleGram (hconj : PhiHatConj T P) :
    Matrix (blockData Z T P hconj).S₁ (blockData Z T P hconj).S₁ ℂ :=
  ZeroBlockData.simpleGram (blockData Z T P hconj)
    (P.a T * P.L T ^ 2)

/-- The literal simple-zero Gram after an explicit packing into disjoint
triples, with every added column identically zero. -/
def zetaSimplePackedGram
    {κ β : Type*}
    (hconj : PhiHatConj T P)
    (e : Fin 3 × β ≃ Sum (blockData Z T P hconj).S₁ κ) :
    Matrix (Fin 3 × β) (Fin 3 × β) ℂ :=
  ZeroBlockData.columnGram (ZeroBlockData.paddedPackedFamily e
    (ZeroBlockData.simpleVhat (blockData Z T P hconj)
      (P.a T * P.L T ^ 2)))

lemma zetaSimpleGram_posSemidef (hconj : PhiHatConj T P) :
    (zetaSimpleGram Z T P hconj).PosSemidef :=
  ZeroBlockData.simpleGram_posSemidef _ _

/-- Concrete strengthened zero-side theorem for the actual Zeta23 window.
No abstract count or undischarged certificate premise remains: the right side
is the literal number `Z.s1 T` of simple critical zeros, and the retained
nonnegative term is the spectrum of their actual finite sampling Gram matrix. -/
theorem hatAz_mult2_retained (hconj : PhiHatConj T P)
    (hreal : PhiHatReal T P) (hPois : PoissonSq T P)
    (hc : 0 < P.a T * P.L T ^ 2) :
    4 * rtrace (P.hat T (Z.Az P T)) -
        frobSq (P.hat T (Z.Az P T)) - 2 * (Z.NIprime T : ℝ) +
        (∑ z, ZeroBlockData.simpleDefect
          ((zetaSimpleGram_posSemidef Z T P hconj).1.eigenvalues z))
      ≤ (Z.s1 T : ℝ) := by
  unfold zetaSimpleGram
  rw [hat_Az_eq_hatP_add_hatQ Z T P hconj,
    NIprime_eq_mk Z T _ (evalVec_reflect hconj),
    s1_eq_mk Z T _ (evalVec_reflect hconj)]
  exact ZeroBlockData.multTwoRetainedDefect _
    (mkPairReps Z T _ (evalVec_reflect hconj)) hc
    (sum_normSq_v_le Z T P hconj hreal hPois)

/-- A literal inverse-sampling strengthening of the multiplicity-aware
Zeta23 zero side.  For any explicit partition of the simple critical zeros
into disjoint triples (and `card κ` zero padding columns), the old zero-side
quantity pays the sum of the capped three-correlation energies. -/
theorem hatAz_mult2_tripleCertificate
    {κ β : Type*} [Fintype κ]
    [Fintype β] [DecidableEq β]
    (hconj : PhiHatConj T P) (hreal : PhiHatReal T P)
    (hPois : PoissonSq T P) (hc : 0 < P.a T * P.L T ^ 2)
    (e : Fin 3 × β ≃ Sum (blockData Z T P hconj).S₁ κ) :
    4 * rtrace (P.hat T (Z.Az P T)) -
        frobSq (P.hat T (Z.Az P T)) - 2 * (Z.NIprime T : ℝ) +
        (∑ b, min
          (ZeroBlockData.tripleOffDiagEnergy
            ((zetaSimplePackedGram Z T P hconj e).submatrix
              (fun j : Fin 3 => (j, b)) (fun j : Fin 3 => (j, b)))) 1)
      ≤ (Z.s1 T : ℝ) + Fintype.card κ := by
  have hzero := hatAz_mult2_retained Z T P hconj hreal hPois hc
  have hpack := ZeroBlockData.packedTripleEnergy_simpleVhat_le_retainedDefect_add_padding
    (blockData Z T P hconj) (P.a T * P.L T ^ 2) e
  change (∑ b, min
      (ZeroBlockData.tripleOffDiagEnergy
        ((zetaSimplePackedGram Z T P hconj e).submatrix
          (fun j : Fin 3 => (j, b)) (fun j : Fin 3 => (j, b)))) 1) ≤
    (∑ z, ZeroBlockData.simpleDefect
      ((zetaSimpleGram_posSemidef Z T P hconj).1.eigenvalues z)) +
      Fintype.card κ at hpack
  linarith

end Inst

end Zeta23InverseSampling
end RiemannGaussian
