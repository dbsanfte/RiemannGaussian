/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ArithmeticOperatorMoebiusCoprimeAudit
import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# Finite pole/density projections do not make actual coprimality PSD

The full actual Mobius divisor matrix is retained, including its native
diagonal credit and complete phase. On distinct ordinary prime rows its
off-diagonal is exactly one. After the constant density row is killed,
every sufficiently positive-phase prime row contributes a strictly
negative diagonal excess. Arbitrarily many such ACTUAL rows occur after
every head at every prescribed nonzero height.

Consequently arbitrary finitely many further linear density/jet/phase
constraints still leave a negative vector. This is a rejection of PSD on
the WHOLE finite-codimension test space, not a bound for a specially
restricted signed packet. No projected-packet source asymptotic is
inferred from the original unprojected Euler source theorem.
-/

namespace RiemannGaussian.ArithmeticOperatorPoleProjectionAudit
noncomputable section
open Complex Filter
open ArithmeticOperatorMoebiusCoprimeAudit ArithmeticOperatorGcdAudit
open SuzukiCarryCorrelation
open scoped BigOperators Classical Topology ComplexConjugate

/-- Full indexed native quadratic; neither ordered incidence is lost. -/
def rowQuadratic {ι : Type*} [Fintype ι] (y : ℝ) (n : ι → ℕ)
    (alpha : ι → ℂ) : ℂ :=
  ∑ i,∑ j,alpha i*conj (alpha j)*augmentedKernel y (n i) (n j)

private theorem prime_diagonal {p : ℕ} (hp : p.Prime) (y : ℝ) :
    augmentedKernel y p p=2*(1-primePhase y p) := by
  rw [augmentedKernel,ite_eq_left rfl,gcdKernel,Nat.gcd_self,hp.divisors,
    Finset.sum_pair hp.ne_one.symm]
  simp [column,ArithmeticOperatorMoebiusCoprimeAudit.mu,
    ArithmeticFunction.moebius_apply_prime hp,primePhase]
  ring

private theorem distinct_prime_entry {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p≠q) (y : ℝ) : augmentedKernel y p q=1 := by
  have hg := ((Nat.coprime_primes hp hq).mpr hpq).gcd_eq_one
  simp [augmentedKernel,hpq,gcdKernel,hg,column,
    ArithmeticOperatorMoebiusCoprimeAudit.mu,primePhase]

private theorem phase_re (y : ℝ) (n : ℕ) :
    (primePhase y n).re=Real.cos (y*Real.log n) := by
  simp only [primePhase,Complex.exp_re,Complex.neg_re,Complex.neg_im,
    Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,
    Complex.ofReal_re,Complex.ofReal_im,mul_zero,zero_mul,one_mul,
    zero_add,sub_zero,neg_zero,Real.exp_zero]
  rw [neg_mul,Real.cos_neg]

/-- Exact joint identity BEFORE taking a real part: the entire
off-diagonal joins to one density square, not separate allowances. -/
theorem rowQuadratic_prime_eq {ι : Type*} [Fintype ι] (y : ℝ) (n : ι → ℕ)
    (hn : ∀ i,(n i).Prime) (hinj : Function.Injective n) (alpha : ι → ℂ) :
    rowQuadratic y n alpha=(∑ i,alpha i)*conj (∑ i,alpha i)+
      ∑ i,alpha i*conj (alpha i)*(1-2*primePhase y (n i)) := by
  have he (i j : ι) : augmentedKernel y (n i) (n j)=
      1+if i=j then 1-2*primePhase y (n i) else 0 := by
    by_cases hij : i=j
    · subst j
      rw [prime_diagonal (hn i)]
      simp
      ring
    · rw [distinct_prime_entry (hn i) (hn j) (hinj.ne hij)]
      simp [hij]
  simp_rw [rowQuadratic,he,mul_add,Finset.sum_add_distrib]
  congr 1
  · simp only [mul_one,←Finset.mul_sum,←Finset.sum_mul,map_sum]
  · apply Finset.sum_congr rfl
    intro i _
    simp [mul_ite]

/-- The phase of the exact density-centered joint sum is still kept;
only now is its real part read. -/
theorem rowQuadratic_prime_re {ι : Type*} [Fintype ι] (y : ℝ) (n : ι → ℕ)
    (hn : ∀ i,(n i).Prime) (hinj : Function.Injective n) (alpha : ι → ℂ) :
    (rowQuadratic y n alpha).re=normSq (∑ i,alpha i)+
      ∑ i,normSq (alpha i)*(1-2*Real.cos (y*Real.log (n i))) := by
  rw [rowQuadratic_prime_eq y n hn hinj]
  rw [Complex.add_re,mul_conj,Complex.ofReal_re]
  rw [Complex.re_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_conj,Complex.mul_re]
  simp [phase_re]

/-- A whole mean-zero vector has a fixed negative SIGNED saving,
uniformly over its other coefficients and any additional constraints. -/
theorem centered_negative_bound {ι : Type*} [Fintype ι] (y : ℝ) (n : ι → ℕ)
    (hn : ∀ i,(n i).Prime) (hinj : Function.Injective n)
    (hphase : ∀ i,7/8≤Real.cos (y*Real.log (n i))) (alpha : ι → ℂ)
    (hzero : ∑ i,alpha i=0) :
    (rowQuadratic y n alpha).re≤-(3/4 : ℝ)*∑ i,normSq (alpha i) := by
  rw [rowQuadratic_prime_re y n hn hinj,hzero,normSq_zero,zero_add,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hp := hphase i
  nlinarith [normSq_nonneg (alpha i)]

/-- Exact positive-phase ACTUAL rows are infinite after every head.
PNT is used only to locate these rows; no signed prime estimate enters. -/
theorem positive_rows_infinite {y : ℝ} (hy : y≠0) (H : ℕ) :
    {p : ℕ | H<p ∧ p.Prime ∧ 7/8≤Real.cos (y*Real.log p)}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro a
  obtain ⟨p,hp,hP,hphase⟩ := exists_positive_prime_above hy (max H a)
  exact ⟨p,⟨(le_max_left _ _).trans_lt hp,hP,hphase⟩,(le_max_right _ _).trans_lt hp⟩

/-- Any number of distinct actual positive-phase primes can be
selected, without completing a physical sum or modifying its entries. -/
theorem exists_positive_rows {y : ℝ} (hy : y≠0) (H M : ℕ) :
    ∃ n : Fin M → ℕ,Function.Injective n ∧
      ∀ i,H<n i ∧ (n i).Prime ∧ 7/8≤Real.cos (y*Real.log (n i)) := by
  let S := {p : ℕ | H<p ∧ p.Prime ∧ 7/8≤Real.cos (y*Real.log p)}
  let e : ℕ ↪ S := Set.Infinite.natEmbedding S (positive_rows_infinite hy H)
  refine ⟨fun i => (e i.val).val,?_,fun i => (e i.val).property⟩
  intro i j hij
  exact Fin.ext (e.injective (Subtype.ext hij))

/-- Elementary finite-dimensional gate: arbitrary m further profiles,
plus the density row, leave a nonzero relation on m+2 coordinates. -/
theorem exists_centered_relation (m : ℕ) (b : Fin m → Fin (m+2) → ℂ) :
    ∃ alpha : Fin (m+2) → ℂ,(∑ i,alpha i)=0 ∧
      (∀ j,∑ i,alpha i*b j i=0) ∧ ∃ i,alpha i≠0 := by
  let v : Fin (m+2) → (Fin (m+1) → ℂ) := fun i => Fin.cases 1 (fun j => b j i)
  have hnot : ¬LinearIndependent ℂ v := by
    intro hh
    have hc := hh.fintype_card_le_finrank
    simp only [Fintype.card_fin,Module.finrank_fintype_fun_eq_card] at hc
    omega
  obtain ⟨alpha,hs,hn⟩ := Fintype.not_linearIndependent_iff.mp hnot
  refine ⟨alpha,?_,?_,hn⟩
  · have h0 := congrFun hs 0
    simpa [v,Fin.sum_univ_succ] using h0
  · intro j
    have hj := congrFun hs j.succ
    simpa [v] using hj

/-- Finite pole/density/jet restrictions do NOT make the whole actual
coprimality quadratic PSD. The profiles may be arbitrary functions of
the physical prime label, complex phase or factorial order. -/
theorem exists_negative_after_finite_projection {y : ℝ} (hy : y≠0) (H m : ℕ)
    (profiles : Fin m → ℕ → ℂ) :
    ∃ (n : Fin (m+2) → ℕ) (alpha : Fin (m+2) → ℂ),
      Function.Injective n ∧ (∀ i,H<n i ∧ (n i).Prime) ∧
      (∑ i,alpha i)=0 ∧ (∀ j,∑ i,alpha i*profiles j (n i)=0) ∧
      (rowQuadratic y n alpha).re<0 := by
  obtain ⟨n,hinj,hrows⟩ := exists_positive_rows hy H (m+2)
  obtain ⟨alpha,hzero,hprofiles,i,hne⟩ := exists_centered_relation m (fun j i => profiles j (n i))
  refine ⟨n,alpha,hinj,fun i => ⟨(hrows i).1,(hrows i).2.1⟩,hzero,hprofiles,?_⟩
  have hbound := centered_negative_bound y n (fun i => (hrows i).2.1) hinj
    (fun i => (hrows i).2.2) alpha hzero
  have hmass : 0<∑ i,normSq (alpha i) := Finset.sum_pos' (fun _ _ => normSq_nonneg _)
    ⟨i,Finset.mem_univ _,normSq_pos.mpr hne⟩
  exact hbound.trans_lt (by nlinarith)

/-- The indexed test is EXACTLY a literal native Finset quadratic.
Extending its coefficients by zero does not change any arithmetic entry. -/
theorem rowQuadratic_eq_native {ι : Type*} [Fintype ι] (y : ℝ) (n : ι → ℕ)
    (hinj : Function.Injective n) (alpha : ι → ℂ) :
    rowQuadratic y n alpha=
      ∑ m∈Finset.univ.image n,∑ k∈Finset.univ.image n,
        Function.extend n alpha 0 m*conj (Function.extend n alpha 0 k)*
          augmentedKernel y m k := by
  symm
  rw [Finset.sum_image (fun _ _ _ _ h => hinj h)]
  simp_rw [Finset.sum_image (fun _ _ _ _ h => hinj h),hinj.extend_apply]
  rfl

/-- The obstruction inhabits the ORIGINAL native physical rows with
the literal head and all finite density/jet restrictions retained. -/
theorem exists_negative_native_projected {y : ℝ} (hy : y≠0) (H m : ℕ)
    (profiles : Fin m → ℕ → ℂ) :
    ∃ (S : Finset ℕ) (alpha : ℕ → ℂ),
      (∀ n∈S,H<n ∧ n.Prime) ∧
      (∑ n∈S,alpha n)=0 ∧ (∀ j,∑ n∈S,alpha n*profiles j n=0) ∧
      (∑ n∈S,∑ k∈S,alpha n*conj (alpha k)*augmentedKernel y n k).re<0 := by
  obtain ⟨n,alpha,hinj,hrows,hzero,hprofiles,hneg⟩ :=
    exists_negative_after_finite_projection hy H m profiles
  refine ⟨Finset.univ.image n,Function.extend n alpha 0,?_,?_,?_,?_⟩
  · intro p hp
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hp
    exact hrows i
  · simpa only [Finset.sum_image (fun _ _ _ _ h => hinj h),hinj.extend_apply] using hzero
  · intro j
    simpa only [Finset.sum_image (fun _ _ _ _ h => hinj h),hinj.extend_apply] using hprofiles j
  · rwa [←rowQuadratic_eq_native y n hinj alpha]

/-- No finite linear pole/density projection rescues nonnegativity
on the WHOLE native test space beyond a head. Special nonlinearly
restricted signed packets are outside this rejection. -/
theorem not_psd_after_finite_projection {y : ℝ} (hy : y≠0) (H m : ℕ)
    (profiles : Fin m → ℕ → ℂ) :
    ¬∀ (S : Finset ℕ) (alpha : ℕ → ℂ),
      (∀ n∈S,H<n) → (∑ n∈S,alpha n)=0 →
      (∀ j,∑ n∈S,alpha n*profiles j n=0) →
      0≤(∑ n∈S,∑ k∈S,alpha n*conj (alpha k)*augmentedKernel y n k).re := by
  intro hPSD
  obtain ⟨S,alpha,hrows,hzero,hprofiles,hneg⟩ :=
    exists_negative_native_projected hy H m profiles
  exact not_lt_of_ge (hPSD S alpha (fun n hn => (hrows n hn).1) hzero hprofiles) hneg

/-- Actual zero ordinates satisfy the same negative native projection
gate. No exposure, simplicity or projected source limit is used. -/
theorem not_psd_after_finite_projection_at_zero (rho : NontrivialZetaZero) (H m : ℕ)
    (profiles : Fin m → ℕ → ℂ) :
    ¬∀ (S : Finset ℕ) (alpha : ℕ → ℂ),
      (∀ n∈S,H<n) → (∑ n∈S,alpha n)=0 →
      (∀ j,∑ n∈S,alpha n*profiles j n=0) →
      0≤(∑ n∈S,∑ k∈S,alpha n*conj (alpha k)*augmentedKernel rho.1.im n k).re :=
  not_psd_after_finite_projection (NontrivialZetaZero.im_ne_zero_of_eta_mass rho) H m profiles

/-- The negative tests lie inside EVERY sufficiently large ORIGINAL
integer cutoff. The profiles can vary with that cutoff; only their
number is fixed. Thus this is not a counterexample outside the native
mask or at a freely chosen diagnostic height. -/
theorem cofinally_negative_native_projected {y : ℝ} (hy : y≠0) (H m : ℕ) :
    ∃ X0 : ℕ,∀ X,X0≤X → ∀ profiles : Fin m → ℕ → ℂ,
      ∃ (S : Finset ℕ) (alpha : ℕ → ℂ),S⊆Finset.Icc 1 X ∧
        (∀ n∈S,H<n ∧ n.Prime) ∧
        (∑ n∈S,alpha n)=0 ∧ (∀ j,∑ n∈S,alpha n*profiles j n=0) ∧
        (∑ n∈S,∑ k∈S,alpha n*conj (alpha k)*augmentedKernel y n k).re<0 := by
  obtain ⟨n,hinj,hrows⟩ := exists_positive_rows hy H (m+2)
  refine ⟨Finset.univ.sup n,?_⟩
  intro X hX profiles
  obtain ⟨alpha,hzero,hprofiles,i,hne⟩ := exists_centered_relation m (fun j i => profiles j (n i))
  refine ⟨Finset.univ.image n,Function.extend n alpha 0,?_,?_,?_,?_,?_⟩
  · intro p hp
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_Icc.mpr ⟨(hrows i).2.1.pos,(Finset.le_sup hi).trans hX⟩
  · intro p hp
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hp
    exact ⟨(hrows i).1,(hrows i).2.1⟩
  · simpa only [Finset.sum_image (fun _ _ _ _ h => hinj h),hinj.extend_apply] using hzero
  · intro j
    simpa only [Finset.sum_image (fun _ _ _ _ h => hinj h),hinj.extend_apply] using hprofiles j
  · rw [←rowQuadratic_eq_native y n hinj alpha]
    have hbound := centered_negative_bound y n (fun i => (hrows i).2.1) hinj
      (fun i => (hrows i).2.2) alpha hzero
    have hmass : 0<∑ i,normSq (alpha i) := Finset.sum_pos' (fun _ _ => normSq_nonneg _)
      ⟨i,Finset.mem_univ _,normSq_pos.mpr hne⟩
    exact hbound.trans_lt (by nlinarith)

/-- Even moving finite jet profiles cannot make the whole native
projected space nonnegative cofinally. This is an exact PSD-premise
no-go, NOT a lower bound for the campaign's single prescribed packet. -/
theorem not_eventually_native_projected_psd {y : ℝ} (hy : y≠0) (H m : ℕ)
    (profiles : ℕ → Fin m → ℕ → ℂ) :
    ¬∀ᶠ X : ℕ in atTop,∀ (S : Finset ℕ) (alpha : ℕ → ℂ),
      S⊆Finset.Icc 1 X → (∀ n∈S,H<n) → (∑ n∈S,alpha n)=0 →
      (∀ j,∑ n∈S,alpha n*profiles X j n=0) →
      0≤(∑ n∈S,∑ k∈S,alpha n*conj (alpha k)*augmentedKernel y n k).re := by
  intro hPSD
  obtain ⟨X0,hX0⟩ := cofinally_negative_native_projected hy H m
  obtain ⟨X,hX,hbound⟩ := ((eventually_ge_atTop X0).and hPSD).exists
  obtain ⟨S,alpha,hsub,hrows,hzero,hprofiles,hneg⟩ := hX0 X hX (profiles X)
  exact not_lt_of_ge (hbound S alpha hsub (fun n hn => (hrows n hn).1) hzero hprofiles) hneg

/-- The native cofinal conclusion also holds at every actual zero
ordinate, including multiple zeros and without exposure. -/
theorem not_eventually_native_projected_psd_at_zero (rho : NontrivialZetaZero) (H m : ℕ)
    (profiles : ℕ → Fin m → ℕ → ℂ) :
    ¬∀ᶠ X : ℕ in atTop,∀ (S : Finset ℕ) (alpha : ℕ → ℂ),
      S⊆Finset.Icc 1 X → (∀ n∈S,H<n) → (∑ n∈S,alpha n)=0 →
      (∀ j,∑ n∈S,alpha n*profiles X j n=0) →
      0≤(∑ n∈S,∑ k∈S,alpha n*conj (alpha k)*augmentedKernel rho.1.im n k).re :=
  not_eventually_native_projected_psd (NontrivialZetaZero.im_ne_zero_of_eta_mass rho) H m profiles

end
end RiemannGaussian.ArithmeticOperatorPoleProjectionAudit
