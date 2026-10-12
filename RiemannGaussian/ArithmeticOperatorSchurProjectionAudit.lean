/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ArithmeticOperatorCoprimeDiagonalAudit
import RiemannGaussian.ArithmeticOperatorPoleProjectionAudit

/-!
# PSD Schur damping combined with density centering still fails

Twenty-seven pairwise coprime ACTUAL squarefree semiprime rows have
native real diagonals at most -1/25 and off-diagonals exactly one.
After ANY unit-diagonal positive Schur damping, summing all antisymmetric
two-row tests gives a negative trace. Each test already kills the density
row. The damping can depend on the physical cutoff and need not be
stationary, Gaussian or real. Only its constant-vector PSD test is used.

This refutes the whole density-centered PSD premise, not a prescribed
signed packet or the Gaussian/Weil endpoint. No bulk source asymptotic is
inferred; every actual zero ordinate is covered without exposure.
-/

namespace RiemannGaussian.ArithmeticOperatorSchurProjectionAudit
noncomputable section
open Complex Filter
open ArithmeticOperatorMoebiusCoprimeAudit ArithmeticOperatorGcdAudit
open scoped BigOperators Classical Topology ComplexConjugate

/-- Exact two-coordinate density-annihilating test of a complex matrix. -/
def pairDifference {ι : Type*} (B : ι → ι → ℂ) (i j : ι) : ℂ :=
  B i i+B j j-B i j-B j i

/-- Every pair and both ordered incidences join before taking a sign. -/
theorem sum_pairDifference_eq {ι : Type*} [Fintype ι] (B : ι → ι → ℂ) :
    (∑ i,∑ j,pairDifference B i j)=
      2*((Fintype.card ι : ℂ)*(∑ i,B i i)-(∑ i,∑ j,B i j)) := by
  have ht : (∑ i,∑ j,B j i)=∑ i,∑ j,B i j := Finset.sum_comm
  simp only [pairDifference,Finset.sum_add_distrib,Finset.sum_sub_distrib,
    Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  rw [ht,←Finset.mul_sum]
  ring

/-- Native actual kernel with an arbitrary coupled Schur factor. -/
def schurEntry (y : ℝ) (K : ℕ → ℕ → ℂ) (n m : ℕ) : ℂ :=
  K n m*augmentedKernel y n m

/-- Whole free Schur PSD premise. This is imposed on the damping,
not on the phased actual arithmetic matrix it is meant to repair. -/
def PositiveSchur (K : ℕ → ℕ → ℂ) : Prop :=
  ∀ (S : Finset ℕ) (a : ℕ → ℂ),
    0≤(∑ n∈S,∑ m∈S,a n*conj (a m)*K n m).re

private theorem coprime_entry {n m : ℕ} (hnm : n.Coprime m) (hne : n≠m)
    (y : ℝ) : augmentedKernel y n m=1 := by
  simp [augmentedKernel,hne,gcdKernel,hnm.gcd_eq_one,column,
    ArithmeticOperatorMoebiusCoprimeAudit.mu,SuzukiCarryCorrelation.primePhase]

/-- Exact native prime-power/divisor matrix; only genuinely coprime
rows are specialized, with no replacement of a literal cutoff. -/
theorem schur_matrix_eq {ι : Type*} [DecidableEq ι]
    (y : ℝ) (K : ℕ → ℕ → ℂ) (n : ι → ℕ)
    (hinj : Function.Injective n) (hc : Pairwise (fun i j => (n i).Coprime (n j)))
    (hd : ∀ i,K (n i) (n i)=1) (i j : ι) :
    schurEntry y K (n i) (n j)=K (n i) (n j)+
      if i=j then augmentedKernel y (n i) (n i)-1 else 0 := by
  by_cases hij : i=j
  · subst j
    simp [schurEntry,hd]
  · simp [schurEntry,coprime_entry (hc hij) (hinj.ne hij),hij]

/-- The exact finite trace becomes negative after joining all pairs.
Only the damping's constant-vector test is required; full PSD is stronger. -/
theorem sum_pairs_negative (y : ℝ) (K : ℕ → ℕ → ℂ) (n : Fin 27 → ℕ)
    (hinj : Function.Injective n) (hc : Pairwise (fun i j => (n i).Coprime (n j)))
    (hd : ∀ i,K (n i) (n i)=1)
    (hdiag : ∀ i,(augmentedKernel y (n i) (n i)).re≤-(1/25 : ℝ))
    (hPSD : 0≤(∑ i,∑ j,K (n i) (n j)).re) :
    (∑ i,∑ j,pairDifference (fun i j => schurEntry y K (n i) (n j)) i j).re≤
      -(54/25 : ℝ) := by
  have hsum : (∑ i,∑ j,schurEntry y K (n i) (n j))=
      (∑ i,∑ j,K (n i) (n j))+
        ∑ i,(augmentedKernel y (n i) (n i)-1) := by
    simp_rw [schur_matrix_eq y K n hinj hc hd,Finset.sum_add_distrib]
    simp
  have htr : (∑ i,schurEntry y K (n i) (n i))=
      ∑ i,augmentedKernel y (n i) (n i) := by simp [schurEntry,hd]
  have hbound : (∑ i,(augmentedKernel y (n i) (n i)).re)≤-(27/25 : ℝ) := by
    calc
      _ ≤ ∑ _ : Fin 27,-(1/25 : ℝ) := Finset.sum_le_sum (fun i _ => hdiag i)
      _ = _ := by norm_num
  rw [sum_pairDifference_eq,hsum,htr]
  simp only [Complex.mul_re,Complex.natCast_re,Complex.natCast_im,
    Complex.sub_re,Complex.add_re,Complex.re_sum,Complex.one_re,
    zero_mul,sub_zero,Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul]
  norm_num at hPSD ⊢
  linarith

/-- There are arbitrarily large finite families of mutually coprime
negative ACTUAL squarefree semiprime rows beyond every head. -/
theorem exists_coprime_negative_rows {y : ℝ} (hy : y≠0) (H M : ℕ) :
    ∃ n : Fin M → ℕ,
      (∀ i,H<n i ∧ 1<n i ∧ Squarefree (n i) ∧
        (augmentedKernel y (n i) (n i)).re≤-(1/25 : ℝ)) ∧
      Pairwise (fun i j => (n i).Coprime (n j)) := by
  induction M with
  | zero => exact ⟨Fin.elim0,by simp,by simp [Pairwise]⟩
  | succ M ih =>
    obtain ⟨n,hn,hc⟩ := ih
    let B := max H (Finset.univ.sup n)
    obtain ⟨p,q,hpB,hpq,hp,hq,hsq,hdiag⟩ :=
      ArithmeticOperatorCoprimeDiagonalAudit.exists_negative_semiprime_diagonal hy B
    have hsmall (i : Fin M) : n i<p :=
      (Finset.le_sup (Finset.mem_univ i)).trans_lt ((le_max_right _ _).trans_lt hpB)
    have hcop (i : Fin M) : (p*q).Coprime (n i) := by
      apply Nat.Coprime.mul_left
      · exact hp.coprime_iff_not_dvd.mpr
          (Nat.not_dvd_of_pos_of_lt (Nat.zero_lt_one.trans (hn i).2.1) (hsmall i))
      · exact hq.coprime_iff_not_dvd.mpr
          (Nat.not_dvd_of_pos_of_lt (Nat.zero_lt_one.trans (hn i).2.1) ((hsmall i).trans hpq))
    refine ⟨Fin.cons (p*q) n,?_,?_⟩
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp only [Fin.cons_zero]
        have hpp : p≤p*q := Nat.le_mul_of_pos_right _ hq.pos
        exact ⟨((le_max_left _ _).trans_lt hpB).trans_le hpp,
          hp.one_lt.trans_le hpp,hsq,hdiag⟩
      · simpa only [Fin.cons_succ] using hn j
    · intro i
      refine Fin.cases ?_ (fun i' => ?_) i
      · intro j
        refine Fin.cases ?_ (fun j' => ?_) j
        · intro hij; exact False.elim (hij rfl)
        · intro _; simpa only [Fin.cons_zero,Fin.cons_succ] using hcop j'
      · intro j
        refine Fin.cases ?_ (fun j' => ?_) j
        · intro _; simpa only [Fin.cons_zero,Fin.cons_succ] using (hcop i').symm
        · intro hij
          simpa only [Fin.cons_succ] using hc (fun h => hij (congrArg Fin.succ h))

/-- Exact density-centered native two-row quadratic. Both phased
incidences and the diagonal credit are retained. -/
theorem pairDifference_eq_native {p q : ℕ} (hpq : p≠q) (y : ℝ) (K : ℕ → ℕ → ℂ) :
    pairDifference (schurEntry y K) p q=
      ∑ n∈({p,q} : Finset ℕ),∑ m∈({p,q} : Finset ℕ),
        (if n=p then (1 : ℂ) else -1)*conj (if m=p then (1 : ℂ) else -1)*
          schurEntry y K n m := by
  simp [Finset.sum_pair hpq,pairDifference,Ne.symm hpq]
  ring

/-- EVERY sufficiently large native cutoff contains a density-centered
negative test after ANY PSD unit-diagonal Schur damping. The damping may
depend on that cutoff; only its positivity on the constant row is used.
This does not constrain a specially prescribed signed packet. -/
theorem cofinally_negative_schur_centered {y : ℝ} (hy : y≠0) (H : ℕ) :
    ∃ X0 : ℕ,∀ X,X0≤X → ∀ K : ℕ → ℕ → ℂ,
      (∀ n∈Finset.Icc 1 X,K n n=1) → PositiveSchur K →
      ∃ (S : Finset ℕ) (a : ℕ → ℂ),S⊆Finset.Icc 1 X ∧
        (∀ n∈S,H<n ∧ Squarefree n) ∧ (∑ n∈S,a n)=0 ∧
        (∑ n∈S,∑ m∈S,a n*conj (a m)*schurEntry y K n m).re<0 := by
  obtain ⟨n,hn,hc⟩ := exists_coprime_negative_rows hy H 27
  have hinj : Function.Injective n := by
    intro i j he
    by_contra hij
    have h := hc hij
    change (n i).Coprime (n j) at h
    rw [he,Nat.coprime_self] at h
    have hpos := (hn j).2.1
    omega
  refine ⟨Finset.univ.sup n,?_⟩
  intro X hX K hd hPSD
  have hns (i : Fin 27) : n i∈Finset.Icc 1 X :=
    Finset.mem_Icc.mpr ⟨(hn i).2.1.le,(Finset.le_sup (Finset.mem_univ i)).trans hX⟩
  have hconstant := hPSD (Finset.univ.image n) (fun _ => 1)
  simp only [map_one,mul_one,one_mul,
    Finset.sum_image (fun _ _ _ _ h => hinj h)] at hconstant
  have hsum := sum_pairs_negative y K n hinj hc (fun i => hd (n i) (hns i))
    (fun i => (hn i).2.2.2) hconstant
  have hex : ∃ i j : Fin 27,
      (pairDifference (fun i j => schurEntry y K (n i) (n j)) i j).re<0 := by
    by_contra h
    push Not at h
    have hlo : 0≤(∑ i,∑ j,pairDifference (fun i j => schurEntry y K (n i) (n j)) i j).re := by
      simp only [Complex.re_sum]
      exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => h i j))
    linarith
  obtain ⟨i,j,hneg⟩ := hex
  have hne : n i≠n j := by
    intro he
    simp [pairDifference,he] at hneg
  refine ⟨{n i,n j},fun m => if m=n i then 1 else -1,?_,?_,?_,?_⟩
  · intro m hm
    rcases Finset.mem_insert.mp hm with rfl | hm
    · exact hns i
    · simpa only [Finset.mem_singleton.mp hm] using hns j
  · intro m hm
    rcases Finset.mem_insert.mp hm with rfl | hm
    · exact ⟨(hn i).1,(hn i).2.2.1⟩
    · simpa only [Finset.mem_singleton.mp hm] using ⟨(hn j).1,(hn j).2.2.1⟩
  · simp [Finset.sum_pair hne,Ne.symm hne]
  · change (pairDifference (schurEntry y K) (n i) (n j)).re<0 at hneg
    rw [pairDifference_eq_native hne y K] at hneg
    exact hneg

/-- A moving/nonstationary/additive PSD Schur kernel cannot make the
whole density-centered native population nonnegative eventually.
Its diagonal and all literal finite-cutoff rows remain unchanged. -/
theorem not_eventually_schur_centered_psd {y : ℝ} (hy : y≠0) (H : ℕ)
    (K : ℕ → ℕ → ℕ → ℂ)
    (hd : ∀ X,∀ n∈Finset.Icc 1 X,K X n n=1)
    (hPSD : ∀ X,PositiveSchur (K X)) :
    ¬∀ᶠ X : ℕ in atTop,∀ (S : Finset ℕ) (a : ℕ → ℂ),
      S⊆Finset.Icc 1 X → (∀ n∈S,H<n) → (∑ n∈S,a n)=0 →
      0≤(∑ n∈S,∑ m∈S,a n*conj (a m)*schurEntry y (K X) n m).re := by
  intro h
  obtain ⟨X0,hX0⟩ := cofinally_negative_schur_centered hy H
  obtain ⟨X,hX,hbound⟩ := ((eventually_ge_atTop X0).and h).exists
  obtain ⟨S,a,hsub,hrows,hzero,hneg⟩ := hX0 X hX (K X) (hd X) (hPSD X)
  exact not_lt_of_ge (hbound S a hsub (fun n hn => (hrows n hn).1) hzero) hneg

/-- This failure covers every ACTUAL nontrivial-zero ordinate. Neither
exposure, simplicity nor a synthetic source model is required. -/
theorem not_eventually_schur_centered_psd_at_zero (rho : NontrivialZetaZero) (H : ℕ)
    (K : ℕ → ℕ → ℕ → ℂ)
    (hd : ∀ X,∀ n∈Finset.Icc 1 X,K X n n=1)
    (hPSD : ∀ X,PositiveSchur (K X)) :
    ¬∀ᶠ X : ℕ in atTop,∀ (S : Finset ℕ) (a : ℕ → ℂ),
      S⊆Finset.Icc 1 X → (∀ n∈S,H<n) → (∑ n∈S,a n)=0 →
      0≤(∑ n∈S,∑ m∈S,a n*conj (a m)*
        schurEntry rho.1.im (K X) n m).re :=
  not_eventually_schur_centered_psd (NontrivialZetaZero.im_ne_zero_of_eta_mass rho) H K hd hPSD

end
end RiemannGaussian.ArithmeticOperatorSchurProjectionAudit
