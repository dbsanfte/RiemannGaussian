/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ArithmeticOperatorSchurProjectionAudit
import Mathlib.Analysis.InnerProductSpace.Trace

/-!
# Finite jet constraints cannot rescue unit-diagonal Schur PSD

Actual coprime squarefree semiprime rows have real native diagonals at
most -1/25 and off-diagonals one. Positive Schur damping has trace equal
to the row count. Repairing the native matrix on a constrained subspace
would consume at least 26/25 for every surviving dimension. Thus more
than 26 times the number of complex constraints forces a negative test.

The profiles and damping may vary with the native cutoff. This refutes
whole-space PSD, not a prescribed signed packet or an RH endpoint.
-/

namespace RiemannGaussian.ArithmeticOperatorSchurJetAudit
noncomputable section
open Complex Filter
open ArithmeticOperatorMoebiusCoprimeAudit ArithmeticOperatorGcdAudit
open ArithmeticOperatorSchurProjectionAudit
open scoped BigOperators Classical Topology ComplexConjugate InnerProductSpace

/-- Positivity bounds every subspace's real quadratic trace by the
whole trace. Hermitian symmetry is not an additional hypothesis. -/
theorem subspace_trace_bound {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (T : E →ₗ[ℂ] E) (V : Submodule ℂ E) (c : ℝ)
    (hpos : ∀ x : E,0≤(inner ℂ x (T x)).re)
    (hV : ∀ x : V,c*‖(x : E)‖^2≤(inner ℂ (x : E) (T x)).re) :
    c*(Module.finrank ℂ V : ℝ)≤(T.trace ℂ E).re := by
  let b := stdOrthonormalBasis ℂ V
  let v : Fin (Module.finrank ℂ V) → E := fun i => (b i : E)
  have hv : Orthonormal ℂ v := b.orthonormal.comp_linearIsometry V.subtypeₗᵢ
  obtain ⟨w,bw,hsub,hbw⟩ := hv.toSubtypeRange.exists_orthonormalBasis_extension
  let U := Finset.univ.image v
  have hUw : U⊆w := by
    intro x hx
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
    exact hsub ⟨i,rfl⟩
  have hsmall : c*(Module.finrank ℂ V : ℝ)≤
      ∑ x∈U,(inner ℂ x (T x)).re := by
    rw [Finset.sum_image (fun _ _ _ _ h => hv.linearIndependent.injective h)]
    calc
      _ = ∑ _ : Fin (Module.finrank ℂ V),c := by simp [mul_comm]
      _ ≤ _ := Finset.sum_le_sum (fun i _ => by
        simpa only [v,Submodule.norm_coe,b.norm_eq_one,one_pow,mul_one] using hV (b i))
  have hlarge : (∑ x∈U,(inner ℂ x (T x)).re)≤
      ∑ x∈w,(inner ℂ x (T x)).re :=
    Finset.sum_le_sum_of_subset_of_nonneg hUw (fun x _ _ => hpos x)
  have htrace : (T.trace ℂ E).re=∑ x∈w,(inner ℂ x (T x)).re := by
    rw [T.trace_eq_sum_inner bw,Complex.re_sum]
    simp_rw [hbw]
    exact Finset.sum_coe_sort w (fun x => (inner ℂ x (T x)).re)
  exact hsmall.trans (hlarge.trans_eq htrace.symm)

/-- Both ordered incidences are joined before reading the real part. -/
def quadratic {ι : Type*} [Fintype ι] (K : ι → ι → ℂ) (a : ι → ℂ) : ℂ :=
  ∑ i,∑ j,a i*conj (a j)*K i j

/-- The transpose matches the native convention for complex coefficients. -/
def rowOperator {ι : Type*} [Fintype ι] [DecidableEq ι] (K : ι → ι → ℂ) :
    EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι :=
  Matrix.toLpLin 2 2 (Matrix.of fun i j => K j i)

theorem rowOperator_inner {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : ι → ι → ℂ) (x : EuclideanSpace ℂ ι) :
    inner ℂ x (rowOperator K x)=quadratic K x := by
  simp only [rowOperator,PiLp.inner_apply,Matrix.toLpLin_apply,
    RCLike.inner_apply',Matrix.mulVec,dotProduct,
    Matrix.of_apply,Finset.mul_sum,quadratic]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem rowOperator_trace {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : ι → ι → ℂ) : (rowOperator K).trace ℂ (EuclideanSpace ℂ ι)=∑ i,K i i := by
  rw [LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun ι ℂ)]
  apply Finset.sum_congr rfl
  intro i _
  rw [EuclideanSpace.basisFun_inner]
  simp [rowOperator,EuclideanSpace.basisFun_apply,Matrix.toLpLin_apply]

/-- Literal complex constraints on an indexed row vector. -/
def profileMap {L r : ℕ} (profiles : Fin r → Fin L → ℂ) :
    EuclideanSpace ℂ (Fin L) →ₗ[ℂ] (Fin r → ℂ) :=
  (Matrix.toLin' (Matrix.of profiles)).comp
    (WithLp.linearEquiv 2 ℂ (Fin L → ℂ)).toLinearMap

theorem profileMap_apply {L r : ℕ} (profiles : Fin r → Fin L → ℂ)
    (x : EuclideanSpace ℂ (Fin L)) (j : Fin r) :
    profileMap profiles x j=∑ i,x i*profiles j i := by
  simp [profileMap,Matrix.toLin'_apply,Matrix.mulVec,dotProduct,mul_comm]

theorem profile_kernel_dimension {L r : ℕ} (profiles : Fin r → Fin L → ℂ) :
    L≤r+Module.finrank ℂ (LinearMap.ker (profileMap profiles)) := by
  have h := (profileMap profiles).finrank_range_add_finrank_ker
  have hr := (LinearMap.range (profileMap profiles)).finrank_le
  simp only [finrank_euclideanSpace_fin,Module.finrank_fintype_fun_eq_card,
    Fintype.card_fin] at h hr
  omega

/-- Exact matrix on coprime native rows after unit-diagonal damping. -/
def dampedMatrix {ι : Type*} [DecidableEq ι] (K : ι → ι → ℂ) (D : ι → ℂ)
    (i j : ι) : ℂ := K i j+if i=j then D i-1 else 0

theorem quadratic_damped_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : ι → ι → ℂ) (D : ι → ℂ) (a : ι → ℂ) :
    quadratic (dampedMatrix K D) a=quadratic K a+
      ∑ i,(normSq (a i) : ℂ)*(D i-1) := by
  simp_rw [quadratic,dampedMatrix,mul_add,Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp [mul_ite,mul_conj]

/-- A quantitative diagonal deficit, read only after the complex join. -/
theorem quadratic_damped_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : ι → ι → ℂ) (D : ι → ℂ)
    (hD : ∀ i,(D i).re≤-(1/25 : ℝ)) (x : EuclideanSpace ℂ ι) :
    (quadratic (dampedMatrix K D) x).re≤
      (quadratic K x).re-(26/25 : ℝ)*‖x‖^2 := by
  rw [quadratic_damped_eq,Complex.add_re,Complex.re_sum]
  have hm : ∑ i,normSq (x i)=‖x‖^2 := by
    simp_rw [normSq_eq_norm_sq]
    exact (EuclideanSpace.norm_sq_eq x).symm
  have hb : (∑ i,((normSq (x i) : ℂ)*(D i-1)).re)≤
      -(26/25 : ℝ)*∑ i,normSq (x i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
      Complex.sub_re,Complex.one_re,zero_mul,sub_zero]
    nlinarith [hD i,normSq_nonneg (x i)]
  rw [hm] at hb
  linarith

/-- Any fixed finite collection of complex constraints leaves a
negative vector whenever the row count exceeds 26 times its size.
Only real quadratic positivity and a unit diagonal of K are required. -/
theorem exists_negative_damped_constrained {L r : ℕ}
    (K : Fin L → Fin L → ℂ) (D : Fin L → ℂ)
    (hd : ∀ i,K i i=1) (hD : ∀ i,(D i).re≤-(1/25 : ℝ))
    (hpos : ∀ a : Fin L → ℂ,0≤(quadratic K a).re)
    (hsize : 26*r<L) (profiles : Fin r → Fin L → ℂ) :
    ∃ a : Fin L → ℂ,(∀ j,∑ i,a i*profiles j i=0) ∧
      (quadratic (dampedMatrix K D) a).re<0 := by
  by_contra h
  push Not at h
  let V := LinearMap.ker (profileMap profiles)
  have hV : ∀ x : V,(26/25 : ℝ)*‖(x : EuclideanSpace ℂ (Fin L))‖^2≤
      (inner ℂ (x : EuclideanSpace ℂ (Fin L)) (rowOperator K x)).re := by
    intro x
    have hz (j : Fin r) : ∑ i,(x : EuclideanSpace ℂ (Fin L)) i*profiles j i=0 := by
      have hx : profileMap profiles x=0 := x.property
      simpa only [profileMap_apply,Pi.zero_apply] using congrFun hx j
    have hn := h (x : EuclideanSpace ℂ (Fin L)) hz
    have hb := quadratic_damped_bound K D hD (x : EuclideanSpace ℂ (Fin L))
    rw [rowOperator_inner]
    linarith
  have ht := subspace_trace_bound (rowOperator K) V (26/25 : ℝ)
    (fun x => by rw [rowOperator_inner]; exact hpos x) hV
  rw [rowOperator_trace] at ht
  simp only [hd,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    nsmul_eq_mul,mul_one,Complex.natCast_re] at ht
  have hdim : (L : ℝ)≤(r : ℝ)+(Module.finrank ℂ V : ℝ) := by
    exact_mod_cast profile_kernel_dimension profiles
  have hs : 26*(r : ℝ)<(L : ℝ) := by exact_mod_cast hsize
  nlinarith

/-- A repair on the whole constrained space would need at least one
complex constraint per 26 negative coprime native rows. -/
theorem necessary_constraint_count {L r : ℕ}
    (K : Fin L → Fin L → ℂ) (D : Fin L → ℂ)
    (hd : ∀ i,K i i=1) (hD : ∀ i,(D i).re≤-(1/25 : ℝ))
    (hpos : ∀ a : Fin L → ℂ,0≤(quadratic K a).re)
    (profiles : Fin r → Fin L → ℂ)
    (hrepair : ∀ a : Fin L → ℂ,(∀ j,∑ i,a i*profiles j i=0) →
      0≤(quadratic (dampedMatrix K D) a).re) : L≤26*r := by
  by_contra h
  obtain ⟨a,ha,hneg⟩ := exists_negative_damped_constrained K D hd hD hpos
    (Nat.lt_of_not_ge h) profiles
  exact not_lt_of_ge (hrepair a ha) hneg

/-- Native positivity restricts to any injectively indexed physical
row family without dropping either complex incidence. -/
theorem positiveSchur_indexed {ι : Type*} [Fintype ι]
    (K : ℕ → ℕ → ℂ) (hK : PositiveSchur K) (n : ι → ℕ)
    (hinj : Function.Injective n) (a : ι → ℂ) :
    0≤(quadratic (fun i j => K (n i) (n j)) a).re := by
  have h := hK (Finset.univ.image n) (Function.extend n a 0)
  simpa only [quadratic,Finset.sum_image (fun _ _ _ _ h => hinj h),
    hinj.extend_apply] using h

/-- Exact native finite quadratic in the original integer cutoff. -/
theorem quadratic_eq_native {ι : Type*} [Fintype ι]
    (B : ℕ → ℕ → ℂ) (n : ι → ℕ) (hinj : Function.Injective n) (a : ι → ℂ) :
    quadratic (fun i j => B (n i) (n j)) a=
      ∑ p∈Finset.univ.image n,∑ q∈Finset.univ.image n,
        (Function.extend n a 0) p*conj ((Function.extend n a 0) q)*B p q := by
  simp only [quadratic,Finset.sum_image (fun _ _ _ _ h => hinj h),hinj.extend_apply]

/-- EVERY sufficiently large native cutoff contains a negative test
after ANY positive unit-diagonal Schur damping and ANY m complex jet
profiles, in addition to exact constant-density centering. The number
m is fixed; profiles and damping can depend on the cutoff. -/
theorem cofinally_negative_schur_projected {y : ℝ} (hy : y≠0) (H m : ℕ) :
    ∃ X0 : ℕ,∀ X,X0≤X → ∀ K : ℕ → ℕ → ℂ,
      (∀ n∈Finset.Icc 1 X,K n n=1) → PositiveSchur K →
      ∀ profiles : Fin m → ℕ → ℂ,
      ∃ (S : Finset ℕ) (a : ℕ → ℂ),S⊆Finset.Icc 1 X ∧
        (∀ n∈S,H<n ∧ Squarefree n) ∧ (∑ n∈S,a n)=0 ∧
        (∀ j,∑ n∈S,a n*profiles j n=0) ∧
        (∑ n∈S,∑ k∈S,a n*conj (a k)*schurEntry y K n k).re<0 := by
  obtain ⟨n,hn,hc⟩ := exists_coprime_negative_rows hy H (27*(m+1))
  have hinj : Function.Injective n := by
    intro i j he
    by_contra hij
    have h := hc hij
    change (n i).Coprime (n j) at h
    rw [he,Nat.coprime_self] at h
    have hpos := (hn j).2.1
    omega
  refine ⟨Finset.univ.sup n,?_⟩
  intro X hX K hd hK profiles
  have hns (i : Fin (27*(m+1))) : n i∈Finset.Icc 1 X :=
    Finset.mem_Icc.mpr ⟨(hn i).2.1.le,(Finset.le_sup (Finset.mem_univ i)).trans hX⟩
  let b : Fin (m+1) → Fin (27*(m+1)) → ℂ :=
    fun j i => Fin.cases 1 (fun k => profiles k (n i)) j
  obtain ⟨a,ha,hneg⟩ := exists_negative_damped_constrained
    (fun i j => K (n i) (n j)) (fun i => augmentedKernel y (n i) (n i))
    (fun i => hd (n i) (hns i)) (fun i => (hn i).2.2.2)
    (positiveSchur_indexed K hK n hinj) (by omega) b
  have hzero : (∑ i,a i)=0 := by simpa [b] using ha 0
  have hprofiles (j : Fin m) : (∑ i,a i*profiles j (n i))=0 := by
    simpa [b] using ha j.succ
  have hnative : (quadratic (fun i j => schurEntry y K (n i) (n j)) a).re<0 := by
    simpa only [quadratic,schur_matrix_eq y K n hinj hc
      (fun i => hd (n i) (hns i)),dampedMatrix] using hneg
  refine ⟨Finset.univ.image n,Function.extend n a 0,?_,?_,?_,?_,?_⟩
  · intro p hp
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_Icc.mpr ⟨(hn i).2.1.le,(Finset.le_sup hi).trans hX⟩
  · intro p hp
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hp
    exact ⟨(hn i).1,(hn i).2.2.1⟩
  · simpa only [Finset.sum_image (fun _ _ _ _ h => hinj h),hinj.extend_apply] using hzero
  · intro j
    simpa only [Finset.sum_image (fun _ _ _ _ h => hinj h),hinj.extend_apply] using hprofiles j
  · rwa [quadratic_eq_native (schurEntry y K) n hinj a] at hnative

/-- Moving damping and moving profiles of fixed finite codimension
cannot make the whole native projected space PSD cofinally. -/
theorem not_eventually_schur_projected_psd {y : ℝ} (hy : y≠0) (H m : ℕ)
    (K : ℕ → ℕ → ℕ → ℂ) (profiles : ℕ → Fin m → ℕ → ℂ)
    (hd : ∀ X,∀ n∈Finset.Icc 1 X,K X n n=1)
    (hK : ∀ X,PositiveSchur (K X)) :
    ¬∀ᶠ X : ℕ in atTop,∀ (S : Finset ℕ) (a : ℕ → ℂ),
      S⊆Finset.Icc 1 X → (∀ n∈S,H<n) → (∑ n∈S,a n)=0 →
      (∀ j,∑ n∈S,a n*profiles X j n=0) →
      0≤(∑ n∈S,∑ k∈S,a n*conj (a k)*schurEntry y (K X) n k).re := by
  intro hPSD
  obtain ⟨X0,hX0⟩ := cofinally_negative_schur_projected hy H m
  obtain ⟨X,hX,hbound⟩ := ((eventually_ge_atTop X0).and hPSD).exists
  obtain ⟨S,a,hsub,hrows,hzero,hprofiles,hneg⟩ :=
    hX0 X hX (K X) (hd X) (hK X) (profiles X)
  exact not_lt_of_ge (hbound S a hsub (fun n hn => (hrows n hn).1) hzero hprofiles) hneg

/-- Every actual zero ordinate is covered, with its analytic
multiplicity untouched and without an exposure assumption. -/
theorem not_eventually_schur_projected_psd_at_zero (rho : NontrivialZetaZero) (H m : ℕ)
    (K : ℕ → ℕ → ℕ → ℂ) (profiles : ℕ → Fin m → ℕ → ℂ)
    (hd : ∀ X,∀ n∈Finset.Icc 1 X,K X n n=1)
    (hK : ∀ X,PositiveSchur (K X)) :
    ¬∀ᶠ X : ℕ in atTop,∀ (S : Finset ℕ) (a : ℕ → ℂ),
      S⊆Finset.Icc 1 X → (∀ n∈S,H<n) → (∑ n∈S,a n)=0 →
      (∀ j,∑ n∈S,a n*profiles X j n=0) →
      0≤(∑ n∈S,∑ k∈S,a n*conj (a k)*schurEntry rho.1.im (K X) n k).re :=
  not_eventually_schur_projected_psd (NontrivialZetaZero.im_ne_zero_of_eta_mass rho)
    H m K profiles hd hK

end
end RiemannGaussian.ArithmeticOperatorSchurJetAudit
