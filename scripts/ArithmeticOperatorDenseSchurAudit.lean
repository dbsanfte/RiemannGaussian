/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ArithmeticOperatorSchurJetAudit
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.Linter
import Lean.Util.CollectAxioms

/-!
# Dense shared-prime grids and genuinely Hermitian Schur repairs

Keep the full actual Mobius divisor kernel and its original diagonal credit.
The phase rectangle is different from the earlier small-angle test. All
products in two adjacent genuine-prime bands are retained, including shared
prime incidences. Their exact joined matrix is a Schur matrix minus two
nonnegative incidence blocks and a diagonal penalty greater than one.

This tests a whole-space repair premise, not a prescribed RH packet. The
additional Hermitian hypothesis is explicit: real-quadratic positivity alone
does NOT license discarding an imaginary block multiplied by a complex phase.
No nonlinear hypothetical-zero source is inferred.
-/

namespace RiemannGaussian.ArithmeticOperatorDenseSchurAudit
noncomputable section
open Complex Filter
open ArithmeticOperatorMoebiusCoprimeAudit ArithmeticOperatorGcdAudit
open ArithmeticOperatorCoprimeDiagonalAudit ArithmeticOperatorSchurProjectionAudit
open ArithmeticOperatorSchurJetAudit SuzukiCarryCorrelation
open scoped BigOperators Classical Topology ComplexConjugate InnerProductSpace

/-- The exact extra diagonal after joining the two shared-prime blocks. -/
def diagonalRemainder (y : ℝ) (p q : ℕ) : ℂ :=
  1-primePhase y p-primePhase y q+2*primePhase y p*primePhase y q

private theorem gcd_prime_kernel {p : ℕ} (hp : p.Prime) (y : ℝ) :
    (∑ d∈p.divisors,column y d)=1-primePhase y p := by
  rw [hp.divisors,Finset.sum_pair hp.ne_one.symm]
  simp [column,ArithmeticOperatorMoebiusCoprimeAudit.mu,
    ArithmeticFunction.moebius_apply_prime hp,primePhase]
  ring

/-- Ordered disjoint prime bands give an injective physical integer chart. -/
theorem prime_product_injective {ι κ : Type*} (p : ι → ℕ) (q : κ → ℕ)
    (hp : ∀ i,(p i).Prime) (hq : ∀ j,(q j).Prime)
    (hi : Function.Injective p) (hj : Function.Injective q)
    (hsep : ∀ i j,p i<q j) :
    Function.Injective (fun ij : ι×κ => p ij.1*q ij.2) := by
  intro a b he
  change p a.1*q a.2=p b.1*q b.2 at he
  have hd : p a.1∣p b.1*q b.2 := by rw [←he]; exact dvd_mul_right _ _
  rcases (hp a.1).dvd_mul.mp hd with hd | hd
  · have hpp : p a.1=p b.1 := (Nat.dvd_prime (hp b.1)).mp hd |>.resolve_left (hp a.1).ne_one
    have hqq : q a.2=q b.2 := by rw [hpp] at he; exact Nat.eq_of_mul_eq_mul_left (hp b.1).pos he
    exact Prod.ext (hi hpp) (hj hqq)
  · have hbad : p a.1=q b.2 := (Nat.dvd_prime (hq b.2)).mp hd |>.resolve_left (hp a.1).ne_one
    exact False.elim ((hsep a.1 b.2).ne hbad)

/-- Every shared-prime incidence and the credited diagonal are literal. -/
theorem semiprime_entry {p q r s : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hr : r.Prime) (hs : s.Prime) (hpq : p≠q) (hrs : r≠s)
    (hps : p≠s) (hrq : r≠q) (y : ℝ) :
    augmentedKernel y (p*q) (r*s)=
      1-(if p=r then primePhase y p else 0)-
        (if q=s then primePhase y q else 0)+
        (if p=r ∧ q=s then diagonalRemainder y p q else 0) := by
  by_cases hpr : p=r
  · subst r
    by_cases hqs : q=s
    · subst s
      simp only [ite_true,and_self]
      rw [semiprime_diagonal hp hq hpq]
      unfold diagonalRemainder
      ring
    · have hg : Nat.gcd (p*q) (p*s)=p := by
        rw [Nat.gcd_mul_left,((Nat.coprime_primes hq hs).mpr hqs).gcd_eq_one,mul_one]
      have hne : p*q≠p*s := fun h => hqs (Nat.eq_of_mul_eq_mul_left hp.pos h)
      simp only [augmentedKernel,hne,ite_false,add_zero,gcdKernel,hg,hqs,and_false,
        sub_zero]
      exact gcd_prime_kernel hp y
  · by_cases hqs : q=s
    · subst s
      have hg : Nat.gcd (p*q) (r*q)=q := by
        rw [Nat.gcd_mul_right,((Nat.coprime_primes hp hr).mpr hpr).gcd_eq_one,one_mul]
      have hne : p*q≠r*q := fun h => hpr (Nat.eq_of_mul_eq_mul_right hq.pos h)
      simp only [augmentedKernel,hne,ite_false,add_zero,gcdKernel,hg,hpr,ite_true,
        false_and,sub_zero]
      exact gcd_prime_kernel hq y
    · have hc : (p*q).Coprime (r*s) :=
        (((Nat.coprime_primes hp hr).mpr hpr).mul_right
          ((Nat.coprime_primes hp hs).mpr hps)).mul_left
          (((Nat.coprime_primes hq hr).mpr hrq.symm).mul_right
            ((Nat.coprime_primes hq hs).mpr hqs))
      have hne : p*q≠r*s := by
        intro he
        have hh := hc
        rw [he,Nat.coprime_self] at hh
        nlinarith [hr.two_le,hs.two_le]
      simp [augmentedKernel,hne,gcdKernel,hc.gcd_eq_one,column,
        ArithmeticOperatorMoebiusCoprimeAudit.mu,primePhase,hpr,hqs]

/-- Diagonal term kept intact through the finite sum expansion. -/
def gridDiagonal {ι κ : Type*} (wp : ι → ℂ) (wq : κ → ℂ) (a : ι×κ) : ℂ :=
  1-wp a.1-wq a.2+2*wp a.1*wq a.2

/-- The actual full prime grid after arbitrary unit-diagonal damping. -/
def gridMatrix {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (K : (ι×κ) → (ι×κ) → ℂ) (wp : ι → ℂ) (wq : κ → ℂ)
    (a b : ι×κ) : ℂ :=
  K a b-(if a.1=b.1 then wp a.1*K a b else 0)-
    (if a.2=b.2 then wq a.2*K a b else 0)+
    if a=b then gridDiagonal wp wq a else 0

theorem gridMatrix_eq_native {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (p : ι → ℕ) (q : κ → ℕ)
    (hp : ∀ i,(p i).Prime) (hq : ∀ j,(q j).Prime)
    (hi : Function.Injective p) (hj : Function.Injective q)
    (hsep : ∀ i j,p i<q j) (y : ℝ) (K : (ι×κ) → (ι×κ) → ℂ)
    (hd : ∀ a,K a a=1) (a b : ι×κ) :
    gridMatrix K (fun i => primePhase y (p i)) (fun j => primePhase y (q j)) a b=
      K a b*augmentedKernel y (p a.1*q a.2) (p b.1*q b.2) := by
  rw [semiprime_entry (hp _) (hq _) (hp _) (hq _)
    (hsep _ _).ne (hsep _ _).ne (hsep _ _).ne (hsep _ _).ne]
  have hpiff : p a.1=p b.1 ↔ a.1=b.1 := hi.eq_iff
  have hqiff : q a.2=q b.2 ↔ a.2=b.2 := hj.eq_iff
  simp only [hpiff,hqiff,←Prod.ext_iff]
  unfold gridMatrix diagonalRemainder gridDiagonal
  by_cases ha : a=b
  · subst b
    simp [hd]
  · simp only [ha,ite_false]
    split_ifs <;> ring

/-- Hermitian symmetry makes the joined quadratic real; positivity alone
would not justify multiplication by the complex prime phase. -/
theorem quadratic_im_zero {ι : Type*} [Fintype ι]
    (K : ι → ι → ℂ) (hK : ∀ i j,conj (K i j)=K j i) (a : ι → ℂ) :
    (quadratic K a).im=0 := by
  have he : conj (quadratic K a)=quadratic K a := by
    simp only [quadratic,map_sum,map_mul,conj_conj]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hK]
    ring
  have him := congrArg Complex.im he
  simp only [Complex.conj_im] at him
  linarith

/-- Both prime marginals are joined exactly before taking real parts. -/
theorem quadratic_grid_eq {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (K : (ι×κ) → (ι×κ) → ℂ) (wp : ι → ℂ) (wq : κ → ℂ) (a : (ι×κ) → ℂ) :
    quadratic (gridMatrix K wp wq) a=quadratic K a-
      ∑ i,wp i*quadratic (fun j l => K (i,j) (i,l)) (fun j => a (i,j))-
      ∑ j,wq j*quadratic (fun i k => K (i,j) (k,j)) (fun i => a (i,j))+
      ∑ i,(normSq (a i) : ℂ)*gridDiagonal wp wq i := by
  have er : (∑ i,∑ j,a i*conj (a j)*(if i.1=j.1 then wp i.1*K i j else 0))=
      ∑ i,wp i*quadratic (fun j l => K (i,j) (i,l)) (fun j => a (i,j)) := by
    simp only [quadratic,Fintype.sum_prod_type,mul_ite,mul_zero,Finset.mul_sum]
    simp
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro l _
    ring
  have ec : (∑ i,∑ j,a i*conj (a j)*(if i.2=j.2 then wq i.2*K i j else 0))=
      ∑ j,wq j*quadratic (fun i k => K (i,j) (k,j)) (fun i => a (i,j)) := by
    simp only [quadratic,Fintype.sum_prod_type,mul_ite,mul_zero,Finset.mul_sum]
    simp
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro k _
    ring
  have ed : (∑ i,∑ j,a i*conj (a j)*(if i=j then gridDiagonal wp wq i else 0))=
      ∑ i,(normSq (a i) : ℂ)*gridDiagonal wp wq i := by
    apply Finset.sum_congr rfl
    intro i _
    simp [mul_ite,mul_conj]
  unfold quadratic gridMatrix
  simp only [mul_add,mul_sub,Finset.sum_add_distrib,Finset.sum_sub_distrib]
  rw [er,ec,ed]
  rfl

/-- A principal prime-incidence block has exactly its native quadratic. -/
theorem quadratic_row_slice {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] (K : (ι×κ) → (ι×κ) → ℂ) (a : (ι×κ) → ℂ) (i : ι) :
    quadratic K (fun b => if b.1=i then a b else 0)=
      quadratic (fun j l => K (i,j) (i,l)) (fun j => a (i,j)) := by
  simp [quadratic,Fintype.sum_prod_type,apply_ite,ite_mul]

theorem quadratic_column_slice {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] (K : (ι×κ) → (ι×κ) → ℂ) (a : (ι×κ) → ℂ) (j : κ) :
    quadratic K (fun b => if b.2=j then a b else 0)=
      quadratic (fun i k => K (i,j) (k,j)) (fun i => a (i,j)) := by
  simp [quadratic,Fintype.sum_prod_type,apply_ite,ite_mul]

/-- A genuinely Hermitian positive damping cannot use imaginary block
credits. Both incidence blocks can be subtracted after their full join. -/
theorem quadratic_grid_upper {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (K : (ι×κ) → (ι×κ) → ℂ) (wp : ι → ℂ) (wq : κ → ℂ)
    (hHerm : ∀ i j,conj (K i j)=K j i)
    (hPSD : ∀ a,0≤(quadratic K a).re)
    (hp : ∀ i,0≤(wp i).re) (hq : ∀ j,0≤(wq j).re)
    (hD : ∀ i,(gridDiagonal wp wq i).re≤-(9/8 : ℝ)) (a : (ι×κ) → ℂ) :
    (quadratic (gridMatrix K wp wq) a).re≤
      (quadratic K a).re-(9/8 : ℝ)*∑ i,normSq (a i) := by
  have hr : 0≤(∑ i,wp i*quadratic (fun j l => K (i,j) (i,l)) (fun j => a (i,j))).re := by
    rw [Complex.re_sum]
    apply Finset.sum_nonneg
    intro i _
    have hz := quadratic_im_zero (fun j l => K (i,j) (i,l))
      (fun j l => hHerm _ _) (fun j => a (i,j))
    have hb := hPSD (fun b => if b.1=i then a b else 0)
    rw [quadratic_row_slice] at hb
    simp only [Complex.mul_re,hz,mul_zero,sub_zero]
    exact mul_nonneg (hp i) hb
  have hc : 0≤(∑ j,wq j*quadratic (fun i k => K (i,j) (k,j)) (fun i => a (i,j))).re := by
    rw [Complex.re_sum]
    apply Finset.sum_nonneg
    intro j _
    have hz := quadratic_im_zero (fun i k => K (i,j) (k,j))
      (fun i k => hHerm _ _) (fun i => a (i,j))
    have hb := hPSD (fun b => if b.2=j then a b else 0)
    rw [quadratic_column_slice] at hb
    simp only [Complex.mul_re,hz,mul_zero,sub_zero]
    exact mul_nonneg (hq j) hb
  have hd : (∑ i,(normSq (a i) : ℂ)*gridDiagonal wp wq i).re≤
      -(9/8 : ℝ)*∑ i,normSq (a i) := by
    rw [Complex.re_sum,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    nlinarith [hD i,normSq_nonneg (a i)]
  rw [quadratic_grid_eq,Complex.add_re,Complex.sub_re,Complex.sub_re]
  linarith

/-- Arbitrary complex profiles on any finite literal row chart. -/
def gridProfileMap {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}
    (profiles : Fin r → ι → ℂ) : EuclideanSpace ℂ ι →ₗ[ℂ] (Fin r → ℂ) :=
  (Matrix.toLin' (Matrix.of profiles)).comp
    (WithLp.linearEquiv 2 ℂ (ι → ℂ)).toLinearMap

theorem gridProfileMap_apply {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}
    (profiles : Fin r → ι → ℂ) (x : EuclideanSpace ℂ ι) (j : Fin r) :
    gridProfileMap profiles x j=∑ i,x i*profiles j i := by
  simp [gridProfileMap,Matrix.toLin'_apply,Matrix.mulVec,dotProduct,mul_comm]

/-- A diagonal penalty 9/8 consumes at least one constraint per nine
native rows, regardless of moving profiles or Hermitian damping. -/
theorem negative_of_trace_domination {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}
    (K B : ι → ι → ℂ) (hd : ∀ i,K i i=1)
    (hPSD : ∀ a,0≤(quadratic K a).re)
    (hbound : ∀ a,(quadratic B a).re≤(quadratic K a).re-
      (9/8 : ℝ)*∑ i,normSq (a i))
    (hsize : 9*r<Fintype.card ι) (profiles : Fin r → ι → ℂ) :
    ∃ a : ι → ℂ,(∀ j,∑ i,a i*profiles j i=0) ∧ (quadratic B a).re<0 := by
  by_contra h
  push Not at h
  let V := LinearMap.ker (gridProfileMap profiles)
  have hV : ∀ x : V,(9/8 : ℝ)*‖(x : EuclideanSpace ℂ ι)‖^2≤
      (inner ℂ (x : EuclideanSpace ℂ ι) (rowOperator K x)).re := by
    intro x
    have hz (j : Fin r) : ∑ i,(x : EuclideanSpace ℂ ι) i*profiles j i=0 := by
      have hx : gridProfileMap profiles x=0 := x.property
      simpa only [gridProfileMap_apply,Pi.zero_apply] using congrFun hx j
    have hn := h (x : EuclideanSpace ℂ ι) hz
    have hb := hbound (x : EuclideanSpace ℂ ι)
    have hm : ∑ i,normSq ((x : EuclideanSpace ℂ ι) i)=‖(x : EuclideanSpace ℂ ι)‖^2 := by
      simp_rw [normSq_eq_norm_sq]
      exact (EuclideanSpace.norm_sq_eq _).symm
    rw [hm] at hb
    rw [rowOperator_inner]
    linarith
  have ht := subspace_trace_bound (rowOperator K) V (9/8 : ℝ)
    (fun x => by rw [rowOperator_inner]; exact hPSD _) hV
  rw [rowOperator_trace] at ht
  simp only [hd,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one,
    Complex.natCast_re] at ht
  have hdimen : Fintype.card ι≤r+Module.finrank ℂ V := by
    dsimp [V]
    have hh := (gridProfileMap profiles).finrank_range_add_finrank_ker
    have hr := (LinearMap.range (gridProfileMap profiles)).finrank_le
    simp only [finrank_euclideanSpace,Module.finrank_fintype_fun_eq_card,
      Fintype.card_fin] at hh hr
    omega
  have hdR : (Fintype.card ι : ℝ)≤r+(Module.finrank ℂ V : ℝ) := by exact_mod_cast hdimen
  have hsR : 9*(r : ℝ)<Fintype.card ι := by exact_mod_cast hsize
  linarith

/-- A simple rational trigonometric rectangle gives a strict penalty. -/
theorem sine_lower {a : ℝ} (ha : 0≤a) (hhi : a≤1/4) :
    (7/8 : ℝ)*a≤Real.sin a := by
  have hsq : a^2≤1/16 := by nlinarith
  have hc := mul_le_mul_of_nonneg_left hsq ha
  have hs := Real.sin_ge_sub_cube ha
  nlinarith

theorem trigonometric_diagonal_penalty {a b : ℝ}
    (ha0 : 1/8≤a) (ha1 : a≤1/4) (hb0 : 1/8≤b) (hb1 : b≤1/4) :
    1-Real.sin a-Real.sin b-2*Real.cos (a+b)≤-(9/8 : ℝ) := by
  have hsa := sine_lower (by linarith) ha1
  have hsb := sine_lower (by linarith) hb1
  have hc := Real.one_sub_sq_div_two_le_cos (x := a+b)
  have hp := mul_nonpos_of_nonneg_of_nonpos
    (show 0≤a+b-1/4 by linarith) (show a+b-1/2≤0 by linarith)
  nlinarith

/-- Shifted band starts just below a quarter turn, at the actual height. -/
def gridScale (y : ℝ) (J : ℕ) : ℝ :=
  Real.exp (((J : ℝ)*(2*Real.pi)+Real.pi/2-1/4)/|y|)

/-- Exact angular half-band width at the fixed ordinate. -/
def gridWidth (y : ℝ) : ℝ := Real.exp (1/(16*|y|))

/-- First actual prime band, with the native floor endpoints. -/
def firstPrimes (y : ℝ) (J : ℕ) : Finset ℕ :=
  PrimeWindow.primesInWindow (gridScale y J) (gridWidth y)

/-- Adjacent disjoint second band; no swapped incidence is duplicated. -/
def secondPrimes (y : ℝ) (J : ℕ) : Finset ℕ :=
  PrimeWindow.primesInWindow (gridWidth y*gridScale y J) (gridWidth y)

/-- Upper physical scale containing every product of the two bands. -/
def gridUpper (y : ℝ) (J : ℕ) : ℝ := (gridWidth y)^3*(gridScale y J)^2

/-- Original integer floor; no real-cutoff replacement is used. -/
def gridCutoff (y : ℝ) (J : ℕ) : ℕ := ⌊gridUpper y J⌋₊

theorem gridWidth_gt_one {y : ℝ} (hy : y≠0) : 1<gridWidth y :=
  Real.one_lt_exp_iff.mpr (by
    exact div_pos zero_lt_one (mul_pos (by norm_num) (abs_pos.mpr hy)))

theorem gridScale_tendsto {y : ℝ} (hy : y≠0) : Tendsto (gridScale y) atTop atTop := by
  have ht : Tendsto (fun J : ℕ => (J : ℝ)*(2*Real.pi)) atTop atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_mul_const (by positivity)
  have hs := tendsto_atTop_add_const_right atTop (Real.pi/2-1/4) ht
  apply Real.tendsto_exp_atTop.comp
    ((hs.atTop_div_const (abs_pos.mpr hy)).congr (fun J => by ring))

theorem gridCutoff_tendsto {y : ℝ} (hy : y≠0) : Tendsto (gridCutoff y) atTop atTop := by
  have hs := (tendsto_pow_atTop (α := ℝ) (by norm_num : (2 : ℕ)≠0)).comp (gridScale_tendsto hy)
  exact (tendsto_nat_floor_atTop (α := ℝ)).comp
    (hs.const_mul_atTop (pow_pos (Real.exp_pos _) 3))

theorem first_prime_bounds {y : ℝ} (hy : y≠0) {J p : ℕ}
    (hp : p∈firstPrimes y J) :
    p.Prime ∧ gridScale y J<(p : ℝ) ∧ (p : ℝ)≤gridWidth y*gridScale y J := by
  obtain ⟨hl,hu,hr⟩ := PrimeWindow.mem_primesInWindow_bounds
    (Real.exp_pos _).le (zero_lt_one.trans (gridWidth_gt_one hy)).le hp
  exact ⟨hr,hl,hu⟩

theorem second_prime_bounds {y : ℝ} (hy : y≠0) {J p : ℕ}
    (hp : p∈secondPrimes y J) :
    p.Prime ∧ gridWidth y*gridScale y J<(p : ℝ) ∧
      (p : ℝ)≤gridWidth y*(gridWidth y*gridScale y J) := by
  obtain ⟨hl,hu,hr⟩ := PrimeWindow.mem_primesInWindow_bounds
    (mul_pos (zero_lt_one.trans (gridWidth_gt_one hy)) (Real.exp_pos _)).le
    (zero_lt_one.trans (gridWidth_gt_one hy)).le hp
  exact ⟨hr,hl,hu⟩

theorem grid_geometry {y : ℝ} (hy : y≠0) {J p q : ℕ}
    (hp : p∈firstPrimes y J) (hq : q∈secondPrimes y J) :
    p.Prime ∧ q.Prime ∧ p<q ∧ gridScale y J<p ∧
      p*q∈Finset.Icc 1 (gridCutoff y J) ∧ Squarefree (p*q) := by
  obtain ⟨hpp,hpl,hpu⟩ := first_prime_bounds hy hp
  obtain ⟨hqp,hql,hqu⟩ := second_prime_bounds hy hq
  have hpq : p<q := by exact_mod_cast hpu.trans_lt hql
  have hc : p*q≤gridCutoff y J := by
    apply (Nat.le_floor_iff (by unfold gridUpper gridWidth gridScale; positivity : 0≤gridUpper y J)).mpr
    have hh := mul_le_mul hpu hqu (by exact_mod_cast hqp.pos.le)
      (by unfold gridWidth gridScale; positivity : 0≤gridWidth y*gridScale y J)
    simpa only [Nat.cast_mul] using hh.trans_eq (by unfold gridUpper; ring)
  exact ⟨hpp,hqp,hpq,hpl,
    Finset.mem_Icc.mpr ⟨by nlinarith [hpp.two_le,hqp.two_le],hc⟩,
    (Nat.squarefree_mul ((Nat.coprime_primes hpp hqp).mpr hpq.ne)).mpr
      ⟨hpp.squarefree,hqp.squarefree⟩⟩

/-- Exact complementary angle, including all period and floor conventions. -/
def gridAngle (y : ℝ) (J p : ℕ) : ℝ :=
  Real.pi/2-(|y| *Real.log p-(J : ℝ)*(2*Real.pi))

theorem grid_angle_bounds {y : ℝ} (hy : y≠0) {J p : ℕ}
    (hp : p∈firstPrimes y J ∨ p∈secondPrimes y J) :
    1/8≤gridAngle y J p ∧ gridAngle y J p≤1/4 := by
  have hA := gridWidth_gt_one hy
  have ha := abs_pos.mpr hy
  have hxp := Real.exp_pos (((J : ℝ)*(2*Real.pi)+Real.pi/2-1/4)/|y|)
  have hb : p.Prime ∧ gridScale y J<(p : ℝ) ∧
      (p : ℝ)≤gridWidth y*(gridWidth y*gridScale y J) := by
    rcases hp with hp | hp
    · obtain ⟨hP,hL,hU⟩ := first_prime_bounds hy hp
      refine ⟨hP,hL,hU.trans ?_⟩
      nlinarith [Real.exp_pos (1/(16*|y|))]
    · obtain ⟨hP,hL,hU⟩ := second_prime_bounds hy hp
      have hl : gridScale y J<gridWidth y*gridScale y J := by
        nlinarith [Real.exp_pos (((J : ℝ)*(2*Real.pi)+Real.pi/2-1/4)/|y|)]
      exact ⟨hP,hl.trans hL,hU⟩
  have hlo : ((J : ℝ)*(2*Real.pi)+Real.pi/2-1/4)/|y|<Real.log p := by
    simpa [gridScale] using Real.log_lt_log hxp hb.2.1
  have hhi : Real.log p≤1/(16*|y|)+1/(16*|y|)+
      ((J : ℝ)*(2*Real.pi)+Real.pi/2-1/4)/|y| := by
    have hh := Real.log_le_log (by exact_mod_cast hb.1.pos) hb.2.2
    rw [Real.log_mul (show gridWidth y≠0 from (Real.exp_pos _).ne') (by unfold gridWidth gridScale; positivity : gridWidth y*gridScale y J≠0),
      Real.log_mul (show gridWidth y≠0 from (Real.exp_pos _).ne') (show gridScale y J≠0 from (Real.exp_pos _).ne')] at hh
    simpa only [gridWidth,gridScale,Real.log_exp,add_assoc] using hh
  have hL := (div_lt_iff₀ ha).mp hlo
  have hU := mul_le_mul_of_nonneg_left hhi ha.le
  field_simp at hU
  unfold gridAngle
  constructor <;> nlinarith

private theorem phase_re_abs (y : ℝ) (p : ℕ) :
    (primePhase y p).re=Real.cos (|y| *Real.log p) := by
  have hh : (primePhase y p).re=Real.cos (y*Real.log p) := by
    simp only [primePhase,Complex.exp_re,Complex.neg_re,Complex.neg_im,Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,Complex.ofReal_re,Complex.ofReal_im,mul_zero,zero_mul,one_mul,zero_add,sub_zero,neg_zero,Real.exp_zero]
    rw [neg_mul,Real.cos_neg]
  rw [hh]
  rcases le_total 0 y with hy | hy
  · rw [abs_of_nonneg hy]
  · rw [abs_of_nonpos hy,neg_mul,Real.cos_neg]

theorem phase_re_gridAngle (y : ℝ) (J p : ℕ) :
    (primePhase y p).re=Real.sin (gridAngle y J p) := by
  rw [phase_re_abs]
  have he : |y| *Real.log p=(Real.pi/2-gridAngle y J p)+(J : ℝ)*(2*Real.pi) := by
    unfold gridAngle
    ring
  rw [he,Real.cos_add_nat_mul_two_pi,Real.cos_pi_div_two_sub]

theorem grid_phase_real_nonneg {y : ℝ} (hy : y≠0) {J p : ℕ}
    (hp : p∈firstPrimes y J ∨ p∈secondPrimes y J) : 0≤(primePhase y p).re := by
  obtain ⟨ha,hb⟩ := grid_angle_bounds hy hp
  rw [phase_re_gridAngle y J p]
  have hs := sine_lower (by linarith : 0≤gridAngle y J p) hb
  linarith

theorem grid_diagonal_penalty {y : ℝ} (hy : y≠0) {J p q : ℕ}
    (hp : p∈firstPrimes y J) (hq : q∈secondPrimes y J) :
    (diagonalRemainder y p q).re≤-(9/8 : ℝ) := by
  obtain ⟨hap,haq⟩ := grid_angle_bounds hy (Or.inl hp)
  obtain ⟨hbp,hbq⟩ := grid_angle_bounds hy (Or.inr hq)
  have he : (primePhase y p*primePhase y q).re=
      -Real.cos (gridAngle y J p+gridAngle y J q) := by
    rw [←ArithmeticOperatorGammaTwistAudit.primePhase_mul y
      (first_prime_bounds hy hp).1.pos (second_prime_bounds hy hq).1.pos,phase_re_abs,
      Nat.cast_mul,Real.log_mul (by exact_mod_cast (first_prime_bounds hy hp).1.ne_zero)
        (by exact_mod_cast (second_prime_bounds hy hq).1.ne_zero)]
    have hh : |y| *(Real.log p+Real.log q)=
        (Real.pi-(gridAngle y J p+gridAngle y J q))+
          ((J+J : ℕ) : ℝ)*(2*Real.pi) := by
      unfold gridAngle
      push_cast
      ring
    rw [hh,Real.cos_add_nat_mul_two_pi,Real.cos_pi_sub]
  unfold diagonalRemainder
  simp only [Complex.add_re,Complex.sub_re,Complex.one_re]
  rw [phase_re_gridAngle y J p,phase_re_gridAngle y J q]
  have he' : (2*primePhase y p*primePhase y q).re=
      -2*Real.cos (gridAngle y J p+gridAngle y J q) := by
    rw [mul_assoc,Complex.mul_re]
    change 2*(primePhase y p*primePhase y q).re-0*(primePhase y p*primePhase y q).im=_
    rw [zero_mul,sub_zero,he]
    ring
  rw [he']
  convert trigonometric_diagonal_penalty hap haq hbp hbq using 1
  ring

/-- A fixed log-bound constant, not an absolute Fourier allowance. -/
def gridLogConstant (y : ℝ) : ℝ := (2*Real.pi+Real.pi/2)/|y|

/-- Positive actual-prime population constant supplied by qualitative PNT. -/
def gridCountConstant (y : ℝ) : ℝ := (gridWidth y-1)/(2*gridLogConstant y)

theorem gridCountConstant_pos {y : ℝ} (hy : y≠0) : 0<gridCountConstant y := by
  unfold gridCountConstant gridLogConstant
  exact div_pos (by linarith [gridWidth_gt_one hy])
    (mul_pos (by norm_num) (div_pos (by positivity) (abs_pos.mpr hy)))

theorem grid_prime_log_upper {y : ℝ} (hy : y≠0) {J p : ℕ}
    (hp : p∈firstPrimes y J ∨ p∈secondPrimes y J) :
    Real.log p≤gridLogConstant y*((J : ℝ)+1) := by
  have ha := (grid_angle_bounds hy hp).1
  have hpos := abs_pos.mpr hy
  unfold gridLogConstant
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hpos).mpr
  unfold gridAngle at ha
  nlinarith [Real.pi_pos,Nat.cast_nonneg (α := ℝ) J]

/-- PNT is used solely to count the actual native counterexample rows. -/
theorem eventually_grid_prime_mass {y : ℝ} (hy : y≠0) :
    ∀ᶠ J : ℕ in atTop,
      (gridWidth y-1)/2*gridScale y J≤∑ p∈firstPrimes y J,Real.log p ∧
      (gridWidth y-1)/2*gridScale y J≤∑ q∈secondPrimes y J,Real.log q := by
  have hA := gridWidth_gt_one hy
  have hx := gridScale_tendsto hy
  have ht := (PrimeWindow.theta_interval_div_tendsto (zero_lt_one.trans hA)).comp hx
  have ht' := (PrimeWindow.theta_interval_div_tendsto (zero_lt_one.trans hA)).comp
    (hx.const_mul_atTop (zero_lt_one.trans hA))
  have he := ht.eventually (eventually_gt_nhds (by linarith : (gridWidth y-1)/2<gridWidth y-1))
  have he' := ht'.eventually (eventually_gt_nhds (by linarith : (gridWidth y-1)/2<gridWidth y-1))
  filter_upwards [he,he'] with J h h'
  have hp : 0<gridScale y J := Real.exp_pos _
  have hAp : 0<gridWidth y*gridScale y J := mul_pos (zero_lt_one.trans hA) hp
  have hh := (lt_div_iff₀ hp).mp h
  have hh' := (lt_div_iff₀ hAp).mp h'
  rw [←PrimeWindow.sum_log_primesInWindow hp.le hA.le] at hh
  rw [←PrimeWindow.sum_log_primesInWindow hAp.le hA.le] at hh'
  refine ⟨hh.le,?_⟩
  have hlo : (gridWidth y-1)/2*gridScale y J≤
      (gridWidth y-1)/2*(gridWidth y*gridScale y J) :=
    mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hp.le hA.le) (by linarith)
  exact hlo.trans hh'.le

theorem eventually_grid_prime_counts {y : ℝ} (hy : y≠0) :
    ∀ᶠ J : ℕ in atTop,
      gridCountConstant y*gridScale y J/((J : ℝ)+1)≤(firstPrimes y J).card ∧
      gridCountConstant y*gridScale y J/((J : ℝ)+1)≤(secondPrimes y J).card := by
  filter_upwards [eventually_grid_prime_mass hy] with J hJ
  have hlog : 0<gridLogConstant y := by
    unfold gridLogConstant
    exact div_pos (by positivity) (abs_pos.mpr hy)
  have bound (P : Finset ℕ) (hm : (gridWidth y-1)/2*gridScale y J≤∑ p∈P,Real.log p)
      (hP : ∀ p∈P,p∈firstPrimes y J ∨ p∈secondPrimes y J) :
      gridCountConstant y*gridScale y J/((J : ℝ)+1)≤P.card := by
    have hu : (∑ p∈P,Real.log p)≤(P.card : ℝ)*(gridLogConstant y*((J : ℝ)+1)) := by
      calc
        _ ≤ ∑ _p∈P,gridLogConstant y*((J : ℝ)+1) :=
          Finset.sum_le_sum (fun p hp => grid_prime_log_upper hy (hP p hp))
        _ = _ := by simp
    have hh := hm.trans hu
    apply (div_le_iff₀ (by positivity : (0 : ℝ)<(J : ℝ)+1)).mpr
    unfold gridCountConstant
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by positivity : (0 : ℝ)<2*gridLogConstant y)).mpr
    nlinarith
  exact ⟨bound _ hJ.1 (fun _ hp => Or.inl hp),bound _ hJ.2 (fun _ hp => Or.inr hp)⟩

/-- All pairs are used: the row count is quadratic in the prime-band count. -/
theorem eventually_grid_card_lower {y : ℝ} (hy : y≠0) :
    ∀ᶠ J : ℕ in atTop,
      (gridCountConstant y)^2*(gridScale y J)^2/((J : ℝ)+1)^2≤
        ((firstPrimes y J).card*(secondPrimes y J).card : ℕ) := by
  filter_upwards [eventually_grid_prime_counts hy] with J hJ
  have hn : 0≤gridCountConstant y*gridScale y J/((J : ℝ)+1) := by
    exact div_nonneg (mul_nonneg (gridCountConstant_pos hy).le (Real.exp_pos _).le) (by positivity)
  have hh := mul_le_mul hJ.1 hJ.2 hn (Nat.cast_nonneg _)
  calc
    _ = (gridCountConstant y*gridScale y J/((J : ℝ)+1))*
        (gridCountConstant y*gridScale y J/((J : ℝ)+1)) := by
      field_simp
    _ ≤ (firstPrimes y J).card*(secondPrimes y J).card := hh
    _ = _ := by norm_cast

/-- The dense-row count beats every power-sublinear projection budget. -/
theorem grid_card_scale_div_power_tendsto {y beta : ℝ} (hy : y≠0) (hbeta : beta<1) :
    Tendsto (fun J : ℕ =>
      ((gridCountConstant y)^2*(gridScale y J)^2/((J : ℝ)+1)^2)/(gridUpper y J)^beta)
      atTop atTop := by
  let b := (2-2*beta)*(2*Real.pi)/|y|
  let e := (2-2*beta)*(Real.pi/2-1/4)/|y|-3*beta/(16*|y|)-b
  have hb : 0<b := div_pos (mul_pos (by linarith) (by positivity)) (abs_pos.mpr hy)
  have hJt : Tendsto (fun J : ℕ => (J : ℝ)+1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 (tendsto_natCast_atTop_atTop (R := ℝ))
  have ht := (tendsto_exp_mul_div_rpow_atTop (2 : ℝ) b hb).comp hJt
  have hc : 0<(gridCountConstant y)^2*Real.exp e :=
    mul_pos (sq_pos_of_pos (gridCountConstant_pos hy)) (Real.exp_pos _)
  apply (ht.const_mul_atTop hc).congr
  intro J
  dsimp
  simp only [Real.rpow_two]
  have hpow : (gridUpper y J)^beta=
      Real.exp ((3/(16*|y|)+2*((J : ℝ)*(2*Real.pi)+Real.pi/2-1/4)/|y|)*beta) := by
    rw [Real.rpow_def_of_pos (by unfold gridUpper gridWidth gridScale; positivity)]
    congr 1
    have hA0 : 0<gridWidth y := Real.exp_pos _
    have hx0 : 0<gridScale y J := Real.exp_pos _
    rw [gridUpper,Real.log_mul (pow_pos hA0 _).ne' (pow_pos hx0 _).ne',
      Real.log_pow,Real.log_pow]
    simp only [gridWidth,gridScale,Real.log_exp]
    ring
  rw [hpow]
  have hxpow : (gridScale y J)^2=
      Real.exp (2*((J : ℝ)*(2*Real.pi)+Real.pi/2-1/4)/|y|) := by
    rw [gridScale,←Real.exp_nat_mul]
    congr 1
    ring
  rw [hxpow]
  have he : e+b*((J : ℝ)+1)=
      2*((J : ℝ)*(2*Real.pi)+Real.pi/2-1/4)/|y|-
        (3/(16*|y|)+2*((J : ℝ)*(2*Real.pi)+Real.pi/2-1/4)/|y|)*beta := by
    dsimp [b,e]
    ring
  calc
    _ = (gridCountConstant y)^2*(Real.exp e*Real.exp (b*((J : ℝ)+1)))/((J : ℝ)+1)^2 := by
      ring
    _ = (gridCountConstant y)^2*Real.exp
        (2*((J : ℝ)*(2*Real.pi)+Real.pi/2-1/4)/|y|-
          (3/(16*|y|)+2*((J : ℝ)*(2*Real.pi)+Real.pi/2-1/4)/|y|)*beta)/((J : ℝ)+1)^2 := by
      rw [←Real.exp_add,he]
    _ = _ := by rw [Real.exp_sub]; field_simp

theorem eventually_grid_size_of_power_budget {y beta C : ℝ} (hy : y≠0)
    (hb0 : 0≤beta) (hb1 : beta<1) (r : ℕ → ℕ)
    (hr : ∀ᶠ X : ℕ in atTop,((r X+1 : ℕ) : ℝ)≤C*(X : ℝ)^beta) :
    ∀ᶠ J : ℕ in atTop,
      9*(r (gridCutoff y J)+1)<(firstPrimes y J).card*(secondPrimes y J).card := by
  have hbig := (grid_card_scale_div_power_tendsto hy hb1).eventually (eventually_gt_atTop (9*C))
  have hbudget := (gridCutoff_tendsto hy).eventually hr
  filter_upwards [hbig,hbudget,eventually_grid_card_lower hy] with J hbig hbudget hcount
  have hU : 0<gridUpper y J := by unfold gridUpper gridWidth gridScale; positivity
  have hXR : 0≤(gridCutoff y J : ℝ) := Nat.cast_nonneg _
  have hle : (gridCutoff y J : ℝ)≤gridUpper y J := Nat.floor_le hU.le
  have hp := Real.rpow_le_rpow hXR hle hb0
  have hC : 0<C := by
    by_contra hh
    have hlo : 0<((r (gridCutoff y J)+1 : ℕ) : ℝ) := by positivity
    have hbad : C*(gridCutoff y J : ℝ)^beta≤0 := mul_nonpos_of_nonpos_of_nonneg
      (le_of_not_gt hh) (Real.rpow_nonneg hXR beta)
    linarith
  have hb := hbudget.trans (mul_le_mul_of_nonneg_left hp hC.le)
  have hh := (lt_div_iff₀ (Real.rpow_pos_of_pos hU beta)).mp hbig
  have hs : 9*((r (gridCutoff y J)+1 : ℕ) : ℝ)<
      ((firstPrimes y J).card*(secondPrimes y J).card : ℕ) := by nlinarith
  exact_mod_cast hs

/-- This is an additional genuine Hermitian condition, not a consequence
of the older real-quadratic `PositiveSchur` definition. -/
def HermitianSchur (K : ℕ → ℕ → ℂ) : Prop :=
  ∀ n m,conj (K n m)=K m n

/-- Dense native prime rows defeat the repair after density centering and
arbitrary additional profiles. No prime incidence is averaged or removed. -/
theorem negative_native_grid {y : ℝ} (hy : y≠0) {J H m : ℕ}
    (hhead : (H : ℝ)<gridScale y J)
    (hsize : 9*(m+1)<(firstPrimes y J).card*(secondPrimes y J).card)
    (K : ℕ → ℕ → ℂ) (hd : ∀ n∈Finset.Icc 1 (gridCutoff y J),K n n=1)
    (hHerm : HermitianSchur K) (hPSD : PositiveSchur K)
    (profiles : Fin m → ℕ → ℂ) :
    ∃ (S : Finset ℕ) (a : ℕ → ℂ),S⊆Finset.Icc 1 (gridCutoff y J) ∧
      (∀ n∈S,H<n ∧ Squarefree n) ∧ (∑ n∈S,a n)=0 ∧
      (∀ j,∑ n∈S,a n*profiles j n=0) ∧
      (∑ n∈S,∑ k∈S,a n*conj (a k)*schurEntry y K n k).re<0 := by
  let P := ↥(firstPrimes y J)
  let Q := ↥(secondPrimes y J)
  let p : P → ℕ := fun i => i.val
  let q : Q → ℕ := fun j => j.val
  have hp (i : P) : (p i).Prime := (first_prime_bounds hy i.property).1
  have hq (j : Q) : (q j).Prime := (second_prime_bounds hy j.property).1
  have hsep (i : P) (j : Q) : p i<q j := (grid_geometry hy i.property j.property).2.2.1
  let n : P×Q → ℕ := fun ij => p ij.1*q ij.2
  have hinj : Function.Injective n := prime_product_injective p q hp hq
    (fun _ _ h => Subtype.ext h) (fun _ _ h => Subtype.ext h) hsep
  have hn (i : P×Q) : n i∈Finset.Icc 1 (gridCutoff y J) ∧ H<n i ∧ Squarefree (n i) := by
    have hg := grid_geometry hy i.1.property i.2.property
    have hbig : H<p i.1 := by exact_mod_cast hhead.trans hg.2.2.2.1
    exact ⟨hg.2.2.2.2.1,hbig.trans_le (Nat.le_mul_of_pos_right _ (hq i.2).pos),hg.2.2.2.2.2⟩
  let KK : (P×Q) → (P×Q) → ℂ := fun i j => K (n i) (n j)
  let wp : P → ℂ := fun i => primePhase y (p i)
  let wq : Q → ℂ := fun j => primePhase y (q j)
  have hKK : ∀ a,0≤(quadratic KK a).re := positiveSchur_indexed K hPSD n hinj
  have hsym : ∀ i j,conj (KK i j)=KK j i := fun i j => hHerm _ _
  have hdiag : ∀ i,KK i i=1 := fun i => hd _ (hn i).1
  have hwp : ∀ i,0≤(wp i).re := fun i => grid_phase_real_nonneg hy (Or.inl i.property)
  have hwq : ∀ j,0≤(wq j).re := fun j => grid_phase_real_nonneg hy (Or.inr j.property)
  have hD : ∀ i,(gridDiagonal wp wq i).re≤-(9/8 : ℝ) := by
    intro i
    exact grid_diagonal_penalty hy i.1.property i.2.property
  let b : Fin (m+1) → P×Q → ℂ := fun j i => Fin.cases 1 (fun k => profiles k (n i)) j
  have hs : 9*(m+1)<Fintype.card (P×Q) := by
    simpa only [Fintype.card_prod,Fintype.card_coe,P,Q] using hsize
  obtain ⟨a,ha,hneg⟩ := negative_of_trace_domination KK (gridMatrix KK wp wq)
    hdiag hKK (quadratic_grid_upper KK wp wq hsym hKK hwp hwq hD) hs b
  have hzero : (∑ i,a i)=0 := by simpa [b] using ha 0
  have hprof (j : Fin m) : (∑ i,a i*profiles j (n i))=0 := by simpa [b] using ha j.succ
  have he : gridMatrix KK wp wq=(fun i j => schurEntry y K (n i) (n j)) := by
    funext i j
    exact gridMatrix_eq_native p q hp hq (fun _ _ h => Subtype.ext h)
      (fun _ _ h => Subtype.ext h) hsep y KK hdiag i j
  rw [he,quadratic_eq_native (schurEntry y K) n hinj a] at hneg
  refine ⟨Finset.univ.image n,Function.extend n a 0,?_,?_,?_,?_,hneg⟩
  · intro k hk
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hk
    exact (hn i).1
  · intro k hk
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hk
    exact (hn i).2
  · simpa only [Finset.sum_image (fun _ _ _ _ hh => hinj hh),hinj.extend_apply] using hzero
  · intro j
    simpa only [Finset.sum_image (fun _ _ _ _ hh => hinj hh),hinj.extend_apply] using hprof j

/-- Every fixed power-sublinear profile count fails cofinally, even when
the profiles and the genuine Hermitian PSD damping vary with the cutoff. -/
theorem eventually_negative_power_budget {y beta C : ℝ} (hy : y≠0)
    (hb0 : 0≤beta) (hb1 : beta<1) (H : ℕ) (r : ℕ → ℕ)
    (hr : ∀ᶠ X : ℕ in atTop,((r X+1 : ℕ) : ℝ)≤C*(X : ℝ)^beta) :
    ∀ᶠ J : ℕ in atTop,∀ K : ℕ → ℕ → ℂ,
      (∀ n∈Finset.Icc 1 (gridCutoff y J),K n n=1) →
      HermitianSchur K → PositiveSchur K →
      ∀ profiles : Fin (r (gridCutoff y J)) → ℕ → ℂ,
      ∃ (S : Finset ℕ) (a : ℕ → ℂ),S⊆Finset.Icc 1 (gridCutoff y J) ∧
        (∀ n∈S,H<n ∧ Squarefree n) ∧ (∑ n∈S,a n)=0 ∧
        (∀ j,∑ n∈S,a n*profiles j n=0) ∧
        (∑ n∈S,∑ k∈S,a n*conj (a k)*schurEntry y K n k).re<0 := by
  filter_upwards [eventually_grid_size_of_power_budget hy hb0 hb1 r hr,
    (gridScale_tendsto hy).eventually (eventually_gt_atTop (H : ℝ))] with J hs hhead
  intro K hd hHerm hPSD profiles
  exact negative_native_grid hy hhead hs K hd hHerm hPSD profiles

/-- Terminal scoped no-go at the actual native integer cutoffs. -/
theorem not_eventually_power_budget_projected_psd {y beta C : ℝ} (hy : y≠0)
    (hb0 : 0≤beta) (hb1 : beta<1) (H : ℕ) (r : ℕ → ℕ)
    (hr : ∀ᶠ X : ℕ in atTop,((r X+1 : ℕ) : ℝ)≤C*(X : ℝ)^beta)
    (K : ℕ → ℕ → ℕ → ℂ) (profiles : (X : ℕ) → Fin (r X) → ℕ → ℂ)
    (hd : ∀ X,∀ n∈Finset.Icc 1 X,K X n n=1)
    (hHerm : ∀ X,HermitianSchur (K X)) (hPSD : ∀ X,PositiveSchur (K X)) :
    ¬∀ᶠ X : ℕ in atTop,∀ (S : Finset ℕ) (a : ℕ → ℂ),
      S⊆Finset.Icc 1 X → (∀ n∈S,H<n) → (∑ n∈S,a n)=0 →
      (∀ j,∑ n∈S,a n*profiles X j n=0) →
      0≤(∑ n∈S,∑ k∈S,a n*conj (a k)*schurEntry y (K X) n k).re := by
  intro h
  have he := (gridCutoff_tendsto hy).eventually h
  obtain ⟨J,hJ,hbound⟩ := ((eventually_negative_power_budget hy hb0 hb1 H r hr).and he).exists
  obtain ⟨S,a,hsub,hrows,hzero,hprof,hneg⟩ := hJ (K _) (hd _) (hHerm _) (hPSD _) (profiles _)
  exact not_lt_of_ge (hbound S a hsub (fun n hn => (hrows n hn).1) hzero hprof) hneg

/-- Every actual zero's source-power projection budget is covered, with
its ordinate and multiplicity unchanged and no exposure hypothesis. -/
theorem no_source_power_budget_repair_at_zero (rho : NontrivialZetaZero) (C : ℝ)
    (H : ℕ) (r : ℕ → ℕ)
    (hr : ∀ᶠ X : ℕ in atTop,((r X+1 : ℕ) : ℝ)≤C*(X : ℝ)^rho.1.re)
    (K : ℕ → ℕ → ℕ → ℂ) (profiles : (X : ℕ) → Fin (r X) → ℕ → ℂ)
    (hd : ∀ X,∀ n∈Finset.Icc 1 X,K X n n=1)
    (hHerm : ∀ X,HermitianSchur (K X)) (hPSD : ∀ X,PositiveSchur (K X)) :
    ¬∀ᶠ X : ℕ in atTop,∀ (S : Finset ℕ) (a : ℕ → ℂ),
      S⊆Finset.Icc 1 X → (∀ n∈S,H<n) → (∑ n∈S,a n)=0 →
      (∀ j,∑ n∈S,a n*profiles X j n=0) →
      0≤(∑ n∈S,∑ k∈S,a n*conj (a k)*schurEntry rho.1.im (K X) n k).re :=
  not_eventually_power_budget_projected_psd
    (NontrivialZetaZero.im_ne_zero_of_eta_mass rho) (NontrivialZetaZero.zero_lt_re rho).le
    (NontrivialZetaZero.re_lt_one rho) H r hr K profiles hd hHerm hPSD

end
end RiemannGaussian.ArithmeticOperatorDenseSchurAudit

#lint+ in RiemannGaussian.ArithmeticOperatorDenseSchurAudit

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut declarations : Nat := 0
  let mut theorems : Nat := 0
  let mut reports : Array Json := #[]
  for (n,ci) in env.constants.toList do
    if env.isImportedConst n then continue
    declarations := declarations+1
    if ci.isAxiom then throwError "Project-defined axiom: {n}"
    let axs ← Lean.collectAxioms n
    for ax in axs do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom in {n}: {ax}"
    if ci.isTheorem then theorems := theorems+1
    reports := reports.push (Json.mkObj [("declaration",toJson n.toString),
      ("isTheorem",toJson ci.isTheorem),("axioms",toJson (axs.map Name.toString))])
  unless declarations>0 do throwError "Empty dense-Schur audit."
  logInfo m!"Dense-Schur audit: {declarations} declarations, {theorems} theorems; only standard axioms."
  IO.FS.createDirAll ".lake/arithmetic-operator-dense-schur"
  IO.FS.writeFile ".lake/arithmetic-operator-dense-schur/axioms.json"
    (Json.mkObj [("scope",toJson "actual dense semiprime grid refutes genuinely Hermitian unit-diagonal PSD repair with every power-sublinear profile budget; prescribed packet source not inferred"),
      ("onlyStandardAxioms",toJson true),("namespaceLinters",toJson (15:Nat)),
      ("allLocalDeclarationsByModuleProvenance",toJson true),
      ("declarations",toJson declarations),("theoremsIncludingGeneratedHelpers",toJson theorems),
      ("declarationAxioms",Json.arr reports)]).pretty
