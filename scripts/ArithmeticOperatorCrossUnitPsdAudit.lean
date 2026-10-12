/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import scripts.ArithmeticOperatorCrossUnitCancellation
import RiemannGaussian.ArithmeticOperatorTwistedBulkAudit
import Mathlib.Tactic.Linter
import Lean.Util.CollectAxioms

/-!
# The actual height phase obstructs unrestricted shared-row positivity

The unphased finite matrix samples do not justify PSD at the actual height.
Every literal aligned square row has quadratic diagonal trace one. Keeping
the original product phase gives negative actual-prime diagonal tests beyond
every head, including every hypothetical zero height. This rejects only the
unrestricted phased PSD shortcut. Distinct-prime signed packets and their
actual nonlinear zero-source response remain open.
-/

set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
open scoped BigOperators Classical Topology
namespace RiemannGaussian.ArithmeticOperatorCrossUnitPsdAudit
open Complex Filter ArithmeticOperatorCrossUnitCancellation ArithmeticOperatorLucasUnitAudit
open ArithmeticOperatorGammaTwistAudit SuzukiCarryCorrelation ArithmeticOperatorGcdAudit

theorem quadraticColumn_square {p : ℕ} [Fact p.Prime] {a : ZMod p} (ha : a≠0) :
    quadraticColumn p a*quadraticColumn p a=1 := by
  change (quadraticChar (ZMod p) a : ℂ)*(quadraticChar (ZMod p) a : ℂ)=1
  exact_mod_cast (by simpa only [pow_two] using quadraticChar_sq_one ha)

/-- The diagonal is a true prime-square binomial row, not an imposed covariance convention. -/
theorem atom_square_row {p k : ℕ} [hp : Fact p.Prime] (hk : k<p*p) :
    atom (quadraticColumn p) (quadraticColumn p) (p*p) k=1 := by
  have he : (((p*p-1).choose k : ℕ) : ZMod p)=(-1 : ZMod p)^k := by
    simpa only [unitRow,pow_two] using unitRow_eq_sign hp.out 2 (by simpa only [pow_two] using hk)
  unfold atom
  rw [he]
  exact quadraticColumn_square (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))

/-- Entire actual quadratic diagonal, including every unit endpoint. -/
theorem quadraticTrace_diagonal {p : ℕ} (hp : p.Prime) : quadraticTrace p p=1 := by
  unfold quadraticTrace
  rw [dite_eq_left ⟨hp,hp⟩]
  let : Fact p.Prime := ⟨hp⟩
  have hs : (∑ k∈Finset.range (p*p),atom (quadraticColumn p) (quadraticColumn p) (p*p) k)=
      (p*p : ℕ) := by
    calc
      _ = ∑ _k∈Finset.range (p*p),(1 : ℂ) := Finset.sum_congr rfl
        (fun k hk => atom_square_row (Finset.mem_range.mp hk))
      _ = _ := by simp
  change (∑ k∈Finset.range (p*p),atom (quadraticColumn p) (quadraticColumn p) (p*p) k)/(p*p : ℕ)=1
  rw [hs,div_self (by exact_mod_cast Nat.mul_ne_zero hp.ne_zero hp.ne_zero)]

/-- Literal product height phase; conjugating one prime phase changes this arithmetic expression. -/
theorem primePhase_square (y : ℝ) {p : ℕ} (hp : 0<p) :
    primePhase y (p*p)=primePhase (2*y) p := by
  rw [primePhase_mul y hp hp]
  unfold primePhase
  rw [←Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The original coupled row coefficient, with both Mangoldt legs and total-label phase retained. -/
def phasedKernel (y : ℝ) (p q : ℕ) : ℂ :=
  (ArithmeticFunction.vonMangoldt p : ℂ)*(ArithmeticFunction.vonMangoldt q : ℂ)*
    primePhase y (p*q)*quadraticTrace p q

/-- Exact finite joint quadratic. This definition audits positivity; it is not a new RH carrier. -/
def phasedQuadratic (P : Finset ℕ) (y : ℝ) (g : ℕ → ℕ → ℂ) (a : ℕ → ℂ) : ℂ :=
  ∑ p∈P,∑ q∈P,a p*star (a q)*g p q*phasedKernel y p q

theorem phasedKernel_diagonal {p : ℕ} (hp : p.Prime) (y : ℝ) :
    phasedKernel y p p=(ArithmeticFunction.vonMangoldt p : ℂ)*
      gcdKernel (fun d => (ArithmeticFunction.vonMangoldt d : ℂ)*primePhase (2*y) d) p p := by
  have hg : gcdKernel (fun d => (ArithmeticFunction.vonMangoldt d : ℂ)*primePhase (2*y) d) p p=
      (ArithmeticFunction.vonMangoldt p : ℂ)*primePhase (2*y) p := by
    rw [gcdKernel,Nat.gcd_self,hp.divisors]
    simp only [Finset.sum_pair hp.ne_one.symm,ArithmeticFunction.vonMangoldt_apply_one,
      Complex.ofReal_zero,zero_mul,zero_add]
  rw [phasedKernel,quadraticTrace_diagonal hp,mul_one,primePhase_square y hp.pos,hg]
  ring

theorem phasedKernel_diagonal_re {p : ℕ} (hp : p.Prime) (y : ℝ) :
    (phasedKernel y p p).re=Real.log p^2*Real.cos ((2*y)*Real.log p) := by
  rw [phasedKernel_diagonal hp,Complex.mul_re]
  simp only [Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,
    ArithmeticFunction.vonMangoldt_apply_prime hp,
    ArithmeticOperatorTwistedBulkAudit.prime_diagonal_re hp]
  ring

/-- True negative diagonal at every fixed nonzero height, beyond every head. -/
theorem exists_negative_diagonal_above {y : ℝ} (hy : y≠0) (H : ℕ) :
    ∃ p>H,p.Prime ∧ (phasedKernel y p p).re<0 := by
  obtain ⟨p,hpH,hp,hn⟩ := ArithmeticOperatorTwistedBulkAudit.exists_negative_prime_diagonal_above
    (y := 2*y) (mul_ne_zero (by norm_num) hy) H
  refine ⟨p,hpH,hp,?_⟩
  rw [phasedKernel_diagonal hp,Complex.mul_re]
  simp only [Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  have hpos : 0<ArithmeticFunction.vonMangoldt p := by
    rw [ArithmeticFunction.vonMangoldt_apply_prime hp]
    exact Real.log_pos (by exact_mod_cast hp.one_lt)
  exact mul_neg_of_pos_of_neg hpos hn

theorem phasedQuadratic_singleton (p : ℕ) (y : ℝ) (g : ℕ → ℕ → ℂ) :
    phasedQuadratic {p} y g (fun _ => 1)=g p p*phasedKernel y p p := by
  simp only [phasedQuadratic,Finset.sum_singleton,star_one,one_mul]

/-- Moving Gaussian or any unit-diagonal Schur factor cannot fix the actual phased diagonal. -/
theorem exists_negative_quadratic_above {y : ℝ} (hy : y≠0) (H : ℕ)
    (g : ℕ → ℕ → ℂ) (hg : ∀ p,H<p → p.Prime → g p p=1) :
    ∃ P : Finset ℕ,(∀ p∈P,H<p ∧ p.Prime) ∧
      (phasedQuadratic P y g (fun _ => 1)).re<0 := by
  obtain ⟨p,hpH,hp,hn⟩ := exists_negative_diagonal_above hy H
  refine ⟨{p},?_,?_⟩
  · intro q hq
    have he : q=p := Finset.mem_singleton.mp hq
    subst q
    exact ⟨hpH,hp⟩
  · rw [phasedQuadratic_singleton,hg p hpH hp,one_mul]
    exact hn

/-- Even the necessary real quadratic inequality for unrestricted phased PSD is false. -/
theorem not_unrestricted_phased_positive {y : ℝ} (hy : y≠0) (H : ℕ)
    (g : ℕ → ℕ → ℂ) (hg : ∀ p,H<p → p.Prime → g p p=1) :
    ¬∀ P : Finset ℕ,(∀ p∈P,H<p ∧ p.Prime) →
      ∀ a : ℕ → ℂ,0≤(phasedQuadratic P y g a).re := by
  obtain ⟨P,hP,hn⟩ := exists_negative_quadratic_above hy H g hg
  intro hs
  exact not_lt_of_ge (hs P hP (fun _ => 1)) hn

/-- No exposure, simplicity or rightmost-zero assumption is used in this positivity rejection. -/
theorem negative_quadratic_at_zero_height (rho : NontrivialZetaZero) (H : ℕ)
    (g : ℕ → ℕ → ℂ) (hg : ∀ p,H<p → p.Prime → g p p=1) :
    ∃ P : Finset ℕ,(∀ p∈P,H<p ∧ p.Prime) ∧
      (phasedQuadratic P rho.1.im g (fun _ => 1)).re<0 :=
  exists_negative_quadratic_above (NontrivialZetaZero.im_ne_zero_of_eta_mass rho) H g hg

/-- Positivity of a difference-phase Gram is not positivity of the literal product-phase packet. -/
theorem productPhase_ne_differencePhase_above {y : ℝ} (hy : y≠0) (H : ℕ) :
    ∃ p>H,p.Prime ∧ primePhase y (p*p)≠primePhase y p*star (primePhase y p) := by
  obtain ⟨p,hpH,hp,hn⟩ := exists_negative_diagonal_above hy H
  refine ⟨p,hpH,hp,?_⟩
  intro he
  have hnorm : primePhase y p*star (primePhase y p)=1 := by
    change primePhase y p*(starRingEnd ℂ) (primePhase y p)=1
    rw [Complex.mul_conj,Complex.normSq_eq_norm_sq,norm_primePhase]
    norm_num
  have hnonneg : 0≤(phasedKernel y p p).re := by
    rw [phasedKernel,quadraticTrace_diagonal hp,he,hnorm,mul_one,mul_one]
    simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    exact mul_self_nonneg _
  exact not_lt_of_ge hnonneg hn

/-- Native coupled rows are symmetric, without conjugating the height phase. -/
theorem quadraticTrace_comm (p q : ℕ) : quadraticTrace p q=quadraticTrace q p := by
  by_cases hpq : p.Prime ∧ q.Prime
  · unfold quadraticTrace
    rw [dite_eq_left hpq,dite_eq_left ⟨hpq.2,hpq.1⟩]
    let : Fact p.Prime := ⟨hpq.1⟩
    let : Fact q.Prime := ⟨hpq.2⟩
    change pairTrace (quadraticColumn p) (quadraticColumn q) (p*q)=
      pairTrace (quadraticColumn q) (quadraticColumn p) (q*p)
    rw [Nat.mul_comm q p]
    unfold pairTrace
    congr 1
    exact Finset.sum_congr rfl (fun k _ => by unfold atom; ring)
  · have hqp : ¬(q.Prime ∧ p.Prime) := by tauto
    simp only [quadraticTrace,dite_eq_right hpq,dite_eq_right hqp]

theorem phasedKernel_comm (y : ℝ) (p q : ℕ) : phasedKernel y p q=phasedKernel y q p := by
  rw [phasedKernel,phasedKernel,quadraticTrace_comm p q,Nat.mul_comm q p]
  ring

/-- Complete diagonal deletion, kept distinct from source-safe diagonal repairs. -/
def offDiagonalKernel (y : ℝ) (p q : ℕ) : ℂ := if p=q then 0 else phasedKernel y p q

theorem offDiagonalKernel_self (y : ℝ) (p : ℕ) : offDiagonalKernel y p p=0 := by
  simp only [offDiagonalKernel,ite_true]

theorem offDiagonalKernel_comm (y : ℝ) (p q : ℕ) :
    offDiagonalKernel y p q=offDiagonalKernel y q p := by
  by_cases he : p=q
  · subst q
    rfl
  · simp only [offDiagonalKernel,ite_eq_right he,ite_eq_right (Ne.symm he),phasedKernel_comm y p q]

/-- Removing the diagonal changes the literal quadratic by this exact retained term. -/
theorem phasedQuadratic_diagonal_ledger (P : Finset ℕ) (y : ℝ)
    (g : ℕ → ℕ → ℂ) (a : ℕ → ℂ) :
    phasedQuadratic P y g a=
      (∑ p∈P,∑ q∈P,a p*star (a q)*g p q*offDiagonalKernel y p q)+
        ∑ p∈P,a p*star (a p)*g p p*phasedKernel y p p := by
  unfold phasedQuadratic
  calc
    _ = ∑ p∈P,∑ q∈P,
        (a p*star (a q)*g p q*offDiagonalKernel y p q+
          if p=q then a p*star (a q)*g p q*phasedKernel y p q else 0) := by
      apply Finset.sum_congr rfl
      intro p _
      apply Finset.sum_congr rfl
      intro q _
      by_cases h : p=q
      · simp only [offDiagonalKernel,ite_eq_left h,mul_zero,zero_add]
      · simp only [offDiagonalKernel,ite_eq_right h,add_zero]
    _ = _ := by
      simp only [Finset.sum_add_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.sum_ite_eq,ite_eq_left hp]

/-- Two exact signed tests: a symmetric zero-diagonal form cannot be positive unless
every permitted off-diagonal real coefficient is zero. No prime estimate is assumed. -/
theorem zero_diagonal_re_zero_of_positive (S : Set ℕ) (K : ℕ → ℕ → ℂ)
    (hdiag : ∀ p,K p p=0) (hsym : ∀ p q,K p q=K q p)
    (hpos : ∀ P : Finset ℕ,(∀ p∈P,p∈S) → ∀ a : ℕ → ℂ,
      0≤(∑ p∈P,∑ q∈P,a p*star (a q)*K p q).re)
    {p q : ℕ} (hp : p∈S) (hq : q∈S) : (K p q).re=0 := by
  by_cases he : p=q
  · subst q
    rw [hdiag]
    rfl
  have hP : ∀ n∈({p,q} : Finset ℕ),n∈S := by
    intro n hn
    rcases Finset.mem_insert.mp hn with hn|hn
    · simpa only [hn] using hp
    · simpa only [Finset.mem_singleton.mp hn] using hq
  have hplus := hpos {p,q} hP (fun _ => 1)
  have hminus := hpos {p,q} hP (fun n => if n=p then 1 else -1)
  have hplusEq : (∑ i∈({p,q} : Finset ℕ),∑ j∈({p,q} : Finset ℕ),
      (1 : ℂ)*star (1 : ℂ)*K i j)=2*K p q := by
    simp only [Finset.sum_pair he,star_one,one_mul]
    rw [hdiag,hdiag,hsym q p]
    ring
  have hminusEq : (∑ i∈({p,q} : Finset ℕ),∑ j∈({p,q} : Finset ℕ),
      (if i=p then (1 : ℂ) else -1)*star (if j=p then (1 : ℂ) else -1)*K i j)=
      -2*K p q := by
    simp only [Finset.sum_pair he,ite_true,ite_eq_right (Ne.symm he),star_one,star_neg,
      one_mul,mul_neg,neg_mul]
    rw [hdiag,hdiag,hsym q p]
    ring
  rw [hplusEq] at hplus
  rw [hminusEq] at hminus
  norm_num [Complex.mul_re] at hplus hminus
  linarith

/-- An unrestricted zero-diagonal positivity rescue annihilates the ENTIRE joined real
packet. It cannot coexist with any nonzero real source on that same population. -/
theorem offDiagonal_positive_forces_joined_real_zero (y : ℝ) (H : ℕ)
    (hpos : ∀ P : Finset ℕ,(∀ p∈P,H<p ∧ p.Prime) → ∀ a : ℕ → ℂ,
      0≤(∑ p∈P,∑ q∈P,a p*star (a q)*offDiagonalKernel y p q).re)
    (P : Finset ℕ) (hP : ∀ p∈P,H<p ∧ p.Prime) :
    (∑ p∈P,∑ q∈P,offDiagonalKernel y p q).re=0 := by
  have hz {p q : ℕ} (hp : p∈P) (hq : q∈P) : (offDiagonalKernel y p q).re=0 :=
    zero_diagonal_re_zero_of_positive {n : ℕ | H<n ∧ n.Prime} _
      (offDiagonalKernel_self y) (offDiagonalKernel_comm y) hpos (hP p hp) (hP q hq)
  simp only [Complex.re_sum]
  apply Finset.sum_eq_zero
  intro p hp
  exact Finset.sum_eq_zero (fun q hq => hz hp hq)

end RiemannGaussian.ArithmeticOperatorCrossUnitPsdAudit

#lint+ in RiemannGaussian.ArithmeticOperatorCrossUnitPsdAudit

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut declarations : Nat := 0
  let mut theorems : Nat := 0
  let mut reports : Array Json := #[]
  for (n,ci) in env.constants.toList do
    if env.isImportedConst n then continue
    declarations := declarations + 1
    if ci.isAxiom then throwError "Project-defined axiom: {n}"
    let axs ← Lean.collectAxioms n
    for ax in axs do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom in {n}: {ax}"
    if ci.isTheorem then theorems := theorems + 1
    reports := reports.push (Json.mkObj [("declaration",toJson n.toString),
      ("isTheorem",toJson ci.isTheorem),("axioms",toJson (axs.map Name.toString))])
  unless declarations > 0 do throwError "Empty cross-unit phased PSD audit."
  logInfo m!"Cross-unit phased PSD audit: {declarations} declarations, {theorems} theorems; only standard axioms."
  IO.FS.createDirAll ".lake/arithmetic-operator-cross-psd"
  IO.FS.writeFile ".lake/arithmetic-operator-cross-psd/axioms.json"
    (Json.mkObj [("scope",toJson "actual quadratic shared binomial row, complete diagonal, literal product phase and unrestricted PSD rejection"),
      ("onlyStandardAxioms",toJson true),("namespaceLinters",toJson (15:Nat)),
      ("allLocalDeclarationsByModuleProvenance",toJson true),
      ("declarations",toJson declarations),("theoremsIncludingGeneratedHelpers",toJson theorems),
      ("declarationAxioms",Json.arr reports)]).pretty
