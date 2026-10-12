/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import scripts.ArithmeticOperatorKummerParityAudit
import RiemannGaussian.ArithmeticOperatorNonlinearSourceAudit
import Mathlib.Tactic.Linter
import Lean.Util.CollectAxioms

/-!
# The simultaneous even-row prime-pair source gate

The literal common-row condition reduces EXACTLY to q and 2q-1 both
prime. Both valuations are one, and every finite mask and physical
phase survives the join. This is a sector identity, not an estimate
for its higher-power complement.

An exact density-free Mellin pole at ANY complex height does not force
this nonlinear packet to have a nonzero response. A parity concentration
retains that pole and kills EVERY affine pair, even with arbitrary
correlated masks and zero-preserving leg operations. These diagnostic
arrays obey divisor incidence, but are NOT the actual prime/Mangoldt
array and are NOT granted the literal binomial/Gamma observations.
-/

set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
open scoped BigOperators Classical Topology
namespace RiemannGaussian.ArithmeticOperatorKummerAffineSourceAudit
open Complex Filter ArithmeticOperatorKummerParityAudit
open ArithmeticOperatorNonlinearSourceAudit ArithmeticOperatorSuccessorSourceAudit
open ArithmeticOperatorGammaTwistAudit ArithmeticOperatorIncidenceFreedom
open ArithmeticOperatorKummerCutoff SuzukiCarryCorrelation

/-- Both primes refer to the SAME literal even-split common divisor.
Only this explicitly marked above-square-root sector is selected. -/
def twoLarge (n p q : ℕ) : Prop :=
  n%2=0 ∧ 4≤n ∧ p.Prime ∧ q.Prime ∧ 2<q ∧ q<p ∧
    n<p^2 ∧ n<q^2 ∧ p∣evenGcd n ∧ q∣evenGcd n

/-- Exact converse as well as necessity: no heuristic prime-pair
completion or dropped head is used in this sector. -/
theorem twoLarge_iff (n p q : ℕ) :
    twoLarge n p q ↔ q.Prime ∧ p.Prime ∧ 2<q ∧ n=2*q ∧ p=2*q-1 := by
  constructor
  · rintro ⟨hne,hn,hp,hq,hq2,hqp,hpl,hql,hpd,hqd⟩
    obtain ⟨_,hnq,hpq⟩ := two_large_incidence_ordered hp hq hq2 hqp hne hn
      hpl hql hpd hqd
    exact ⟨hq,hp,hq2,hnq,hpq⟩
  · rintro ⟨hq,hp,hq2,rfl,hp_eq⟩
    have hqp : q<p := by omega
    have hp2 : 2<p := hq2.trans hqp
    have hne : (2*q)%2=0 := by omega
    have hn : 4≤2*q := by omega
    have hpl : 2*q<p^2 := by nlinarith
    have hql : 2*q<q^2 := by nlinarith
    have hpd : p∣evenGcd (2*q) :=
      (evenGcd_large_dvd_iff hp hp2 hne hn hpl).mpr (Or.inl (by omega))
    have hqd : q∣evenGcd (2*q) :=
      (evenGcd_large_dvd_iff hq hq2 hne hn hql).mpr (Or.inr rfl)
    exact ⟨hne,hn,hp,hq,hq2,hqp,hpl,hql,hpd,hqd⟩

theorem twoLarge_valuations {n p q : ℕ} (h : twoLarge n p q) :
    (evenGcd n).factorization p=1 ∧ (evenGcd n).factorization q=1 := by
  obtain ⟨hne,hn,hp,hq,hq2,hqp,hpl,hql,hpd,hqd⟩ := h
  have hp2 := hq2.trans hqp
  have hps := (evenGcd_large_dvd_iff hp hp2 hne hn hpl).mp hpd
  have hqs := (evenGcd_large_dvd_iff hq hq2 hne hn hql).mp hqd
  exact ⟨by rw [evenGcd_large_factorization hp hp2 hne hn hpl,ite_eq_left hps],
    by rw [evenGcd_large_factorization hq hq2 hne hn hql,ite_eq_left hqs]⟩

/-- A literal local prime constraint, with the exceptional pair (5,3)
retained. This does NOT determine a nonlinear source at a zeta zero. -/
theorem affine_prime_mod_three {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hq2 : 2<q) (hpq : p=2*q-1) : q=3 ∨ q%3=1 := by
  by_cases hq3 : q=3
  · exact Or.inl hq3
  · apply Or.inr
    have hqp : q<p := by omega
    have hp3 : p≠3 := by omega
    have hnotq : ¬3∣q := by
      intro hd
      exact hq3 ((hq.dvd_iff_eq (by norm_num : (3 : ℕ)≠1)).mp hd)
    have hnotp : ¬3∣p := by
      intro hd
      exact hp3 ((hp.dvd_iff_eq (by norm_num : (3 : ℕ)≠1)).mp hd)
    have hmod0 : q%3≠0 := by
      intro h
      exact hnotq (Nat.dvd_of_mod_eq_zero h)
    have hmodlt := Nat.mod_lt q (by norm_num : (0 : ℕ)<3)
    by_contra hmod1
    have hmod2 : q%3=2 := by omega
    have he := Nat.mod_add_div q 3
    have hd : 3∣p := ⟨2*(q/3)+1,by omega⟩
    exact hnotp hd

theorem twoLarge_mod_three {n p q : ℕ} (h : twoLarge n p q) : q=3 ∨ q%3=1 := by
  obtain ⟨hq,hp,hq2,_,hpq⟩ := (twoLarge_iff n p q).mp h
  exact affine_prime_mod_three hp hq hq2 hpq

/-- Full logarithmic pair coefficient, with the actual row valuations. -/
def twoLargeCoefficient (n p q : ℕ) : ℂ :=
  if twoLarge n p q then
    ((evenGcd n).factorization p : ℂ)*((evenGcd n).factorization q : ℂ)*
      (Real.log p : ℂ)*(Real.log q : ℂ)
  else 0

theorem twoLargeCoefficient_eq (n p q : ℕ) :
    twoLargeCoefficient n p q=
      if q.Prime ∧ 2<q ∧ n=2*q ∧ p=2*q-1 ∧ p.Prime then
        (Real.log p : ℂ)*(Real.log q : ℂ) else 0 := by
  by_cases h : twoLarge n p q
  · obtain ⟨hq,hp,hq2,hn,hpq⟩ := (twoLarge_iff n p q).mp h
    obtain ⟨hv,hv'⟩ := twoLarge_valuations h
    have hh : q.Prime ∧ 2<q ∧ n=2*q ∧ p=2*q-1 ∧ p.Prime :=
      ⟨hq,hq2,hn,hpq,hp⟩
    rw [twoLargeCoefficient,ite_eq_left h,ite_eq_left hh,hv,hv']
    simp only [Nat.cast_one,one_mul]
  · have hh : ¬(q.Prime ∧ 2<q ∧ n=2*q ∧ p=2*q-1 ∧ p.Prime) := by
      rintro ⟨hq,hq2,hn,hpq,hp⟩
      exact h ((twoLarge_iff n p q).mpr ⟨hq,hp,hq2,hn,hpq⟩)
    simp only [twoLargeCoefficient,h,hh,↓reduceIte]

/-- The SAME finite label, prime, owner and phase masks on every leg. -/
def nativePacket (S P Q : Finset ℕ) (W : ℕ → ℕ → ℕ → ℂ) : ℂ :=
  ∑ q∈Q, ∑ n∈S, ∑ p∈P, twoLargeCoefficient n p q*W n p q

/-- The joined native integer packet is precisely an affine prime-pair
sum. No source for this quadratic is inferred from linear moments. -/
theorem nativePacket_eq (S P Q : Finset ℕ) (W : ℕ → ℕ → ℕ → ℂ) :
    nativePacket S P Q W=
      ∑ q∈Q, if q.Prime ∧ 2<q ∧ (2*q-1).Prime ∧ 2*q∈S ∧ 2*q-1∈P then
        (Real.log ((2*q-1 : ℕ) : ℝ) : ℂ)*(Real.log q : ℂ)*W (2*q) (2*q-1) q else 0 := by
  unfold nativePacket
  apply Finset.sum_congr rfl
  intro q _
  simp_rw [twoLargeCoefficient_eq]
  by_cases hq : q.Prime ∧ 2<q
  · by_cases hn : 2*q∈S
    · rw [Finset.sum_eq_single (2*q)]
      · by_cases hp : 2*q-1∈P
        · rw [Finset.sum_eq_single (2*q-1)]
          · simp [hq,hp,hn]
          · intro p _ hne
            simp [hne]
          · exact fun he => (he hp).elim
        · have hzero : (∑ p∈P,
              (if q.Prime ∧ 2<q ∧ 2*q=2*q ∧ p=2*q-1 ∧ p.Prime then
                (Real.log p : ℂ)*(Real.log q : ℂ) else 0)*W (2*q) p q)=0 := by
            apply Finset.sum_eq_zero
            intro p hmem
            have hne : p≠2*q-1 := by rintro rfl; exact hp hmem
            simp [hne]
          rw [hzero]
          simp [hp]
      · intro n _ hne
        apply Finset.sum_eq_zero
        intro p _
        simp [hne]
      · exact fun he => (he hn).elim
    · have hzero : (∑ n∈S, ∑ p∈P,
          (if q.Prime ∧ 2<q ∧ n=2*q ∧ p=2*q-1 ∧ p.Prime then
            (Real.log p : ℂ)*(Real.log q : ℂ) else 0)*W n p q)=0 := by
        apply Finset.sum_eq_zero
        intro n hmem
        apply Finset.sum_eq_zero
        intro p _
        have hne : n≠2*q := by rintro rfl; exact hn hmem
        simp [hne]
      rw [hzero]
      simp [hn]
  · have hzero : (∑ n∈S, ∑ p∈P,
        (if q.Prime ∧ 2<q ∧ n=2*q ∧ p=2*q-1 ∧ p.Prime then
          (Real.log p : ℂ)*(Real.log q : ℂ) else 0)*W n p q)=0 := by
      apply Finset.sum_eq_zero
      intro n _
      apply Finset.sum_eq_zero
      intro p _
      split_ifs with h
      · exact (hq ⟨h.1,h.2.1⟩).elim
      · exact zero_mul _
    rw [hzero]
    have hh : ¬(q.Prime ∧ 2<q ∧ (2*q-1).Prime ∧ 2*q∈S ∧ 2*q-1∈P) := by
      intro h
      exact hq ⟨h.1,h.2.1⟩
    simp only [hh,↓reduceIte]

/-- A diagnostic coefficient row at complex source beta+i*y, with its
zero endpoint explicitly removed. It is NOT the actual prime row. -/
def phasedRow (v : ℂ) (beta y : ℝ) (n : ℕ) : ℂ :=
  if n=0 then 0 else evenRow v beta n*primePhase (-y) n

/-- Exact continuation of the phase-twisted parity model. -/
def phasedResponse (v : ℂ) (beta y : ℝ) (s : ℂ) : ℂ :=
  evenResponse v beta (s-I*y)

/-- Exact source information at complex height, and genuine convergence
only on Re(s)>Re(rho). No continued sum is called an Euler sum. -/
def HasComplexDensityFreeSource (g : ℕ → ℂ) (rho v : ℂ) : Prop :=
  v≠0 ∧ ∃ F : ℂ → ℂ,
    (∀ s : ℂ, rho.re<s.re → LSeriesSummable g s) ∧
    (∀ s : ℂ, rho.re<s.re → LSeries g s=F s) ∧
    AnalyticAt ℂ F 1 ∧
    Tendsto (fun s : ℂ => (s-rho)*F s) (𝓝[≠] rho) (𝓝 v)

theorem phasedRow_zero (v : ℂ) (beta y : ℝ) : phasedRow v beta y 0=0 := by
  simp only [phasedRow,↓reduceIte]

theorem phasedRow_eq_phase {n : ℕ} (hn : n≠0) (v : ℂ) (beta y : ℝ) :
    phasedRow v beta y n=evenRow v beta n*primePhase (-y) n := by
  simp only [phasedRow,hn,↓reduceIte]

theorem phased_summable (v : ℂ) (beta y : ℝ) {s : ℂ} (hs : beta<s.re) :
    LSeriesSummable (phasedRow v beta y) s := by
  apply (LSeriesSummable_congr s (fun {n} hn => phasedRow_eq_phase hn v beta y)).mpr
  apply (LSeriesSummable_primePhase_iff _ (-y) s).mpr
  apply even_summable v beta
  simpa using hs

theorem phased_euler_response (v : ℂ) (beta y : ℝ) {s : ℂ} (hs : beta<s.re) :
    LSeries (phasedRow v beta y) s=phasedResponse v beta y s := by
  rw [LSeries_congr (fun {n} hn => phasedRow_eq_phase hn v beta y),LSeries_primePhase]
  unfold phasedResponse
  have he : s+I*↑(-y)=s-I*y := by push_cast; ring
  rw [he]
  exact even_euler_response v beta (by simpa using hs)

private theorem evenResponse_analyticAt (v : ℂ) (beta : ℝ) {s : ℂ}
    (hs : beta<s.re) : AnalyticAt ℂ (evenResponse v beta) s := by
  have ht : s-(beta-1 : ℝ)≠1 := by
    intro h
    have hr := congrArg Complex.re h
    simp only [sub_re,ofReal_re,one_re] at hr
    linarith
  have ha : AnalyticAt ℂ (fun z : ℂ => riemannZeta (z-(beta-1 : ℝ))) s :=
    AnalyticAt.comp (g := riemannZeta) (f := fun z : ℂ => z-(beta-1 : ℝ))
      (x := s) (analyticOn_riemannZeta _ ht) (by fun_prop)
  unfold evenResponse smoothResponse
  apply AnalyticAt.mul ?_ (analyticAt_const.mul ha)
  unfold evenFactor
  rw [show (fun z : ℂ => 2*((2 : ℝ)^(beta-1) : ℝ)/(2 : ℂ)^z)=
      fun z => 2*((2 : ℝ)^(beta-1) : ℝ)/Complex.exp (Complex.log 2*z) by
        funext z; rw [Complex.cpow_def_of_ne_zero (by norm_num)]]
  exact analyticAt_const.div (by fun_prop) (Complex.exp_ne_zero _)

theorem phased_density_analytic (v : ℂ) {beta : ℝ} (hb : beta<1) (y : ℝ) :
    AnalyticAt ℂ (phasedResponse v beta y) 1 := by
  unfold phasedResponse
  apply AnalyticAt.comp (g := evenResponse v beta) (f := fun s : ℂ => s-I*y)
  · apply evenResponse_analyticAt v beta
    simpa using hb
  · fun_prop

/-- Full complex residue, including the original ordinate. -/
theorem phased_source (v : ℂ) (beta y : ℝ) :
    Tendsto (fun s : ℂ => (s-((beta : ℂ)+I*y))*phasedResponse v beta y s)
      (𝓝[≠] ((beta : ℂ)+I*y)) (𝓝 v) := by
  have ht : Tendsto (fun s : ℂ => s-I*y)
      (𝓝[≠] ((beta : ℂ)+I*y)) (𝓝[≠] (beta : ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have h : Tendsto (fun s : ℂ => s-I*y) (𝓝 ((beta : ℂ)+I*y))
          (𝓝 (((beta : ℂ)+I*y)-I*y)) :=
        (continuous_id.sub continuous_const).tendsto _
      simpa only [add_sub_cancel_right] using h.mono_left nhdsWithin_le_nhds
    · filter_upwards [eventually_mem_nhdsWithin] with s hs
      simp only [Set.mem_compl_iff,Set.mem_singleton_iff] at hs ⊢
      intro h
      apply hs
      linear_combination h
  have h := (tendsto_even_source v beta).comp ht
  convert h using 1
  funext s
  unfold phasedResponse
  dsimp only [Function.comp_def]
  ring

theorem phased_has_source {v : ℂ} (hv : v≠0) {beta : ℝ} (hb : beta<1) (y : ℝ) :
    HasComplexDensityFreeSource (phasedRow v beta y) ((beta : ℂ)+I*y) v := by
  refine ⟨hv,phasedResponse v beta y,?_,?_,phased_density_analytic v hb y,
    phased_source v beta y⟩
  · intro s hs
    exact phased_summable v beta y (by simpa using hs)
  · intro s hs
    exact phased_euler_response v beta y (by simpa using hs)

/-- This works for an unbounded affine lag, not just a fixed or
sublinear additive lag. The q=0 head is kept separately. -/
theorem affine_pair_zero (v : ℂ) (beta y : ℝ) (q : ℕ) :
    phasedRow v beta y q*phasedRow v beta y (2*q-1)=0 := by
  by_cases hq : q=0
  · simp only [hq,phasedRow_zero,zero_mul]
  · have hodd : ¬2∣2*q-1 := by rintro ⟨k,hk⟩; omega
    have hpos : 2*q-1≠0 := by omega
    simp only [phasedRow,hpos,↓reduceIte,evenRow,hodd,↓reduceIte,zero_mul,mul_zero]

/-- All masks, phases and zero-preserving leg operations remain joined. -/
def affinePacket (S : Finset ℕ) (W : ℕ → ℂ) (mask : ℕ → Prop)
    (leg₀ leg₁ : ℂ → ℂ) (g : ℕ → ℂ) : ℂ :=
  ∑ q∈S, if mask q then W q*leg₀ (g q)*leg₁ (g (2*q-1)) else 0

theorem affinePacket_zero (v : ℂ) (beta y : ℝ) (S : Finset ℕ) (W : ℕ → ℂ)
    (mask : ℕ → Prop) (leg₀ leg₁ : ℂ → ℂ) (h₀ : leg₀ 0=0) (h₁ : leg₁ 0=0) :
    affinePacket S W mask leg₀ leg₁ (phasedRow v beta y)=0 := by
  unfold affinePacket
  apply Finset.sum_eq_zero
  intro q _
  split_ifs
  · have h := affine_pair_zero v beta y q
    rcases mul_eq_zero.mp h with h | h
    · rw [h,h₀,mul_zero,zero_mul]
    · rw [h,h₁,mul_zero]
  · rfl

theorem phased_divisor_realization (v : ℂ) (beta y : ℝ) {n : ℕ} (hn : 0<n) :
    divisorObservation (inverseRows (phasedRow v beta y)) n=phasedRow v beta y n :=
  observation_inverseRows _ hn

/-- This is a source-INFERENCE obstruction, not an impossibility
theorem for a new constraint special to actual integer primes. -/
theorem exists_invisible_affine_source {v : ℂ} (hv : v≠0) {beta : ℝ}
    (hb : beta<1) (y : ℝ) :
    ∃ g : ℕ → ℂ, HasComplexDensityFreeSource g ((beta : ℂ)+I*y) v ∧
      g 0=0 ∧
      (∀ S : Finset ℕ, ∀ W : ℕ → ℂ, ∀ mask : ℕ → Prop,
        ∀ leg₀ leg₁ : ℂ → ℂ, leg₀ 0=0 → leg₁ 0=0 →
          affinePacket S W mask leg₀ leg₁ g=0) ∧
      ∀ n>0, divisorObservation (inverseRows g) n=g n := by
  exact ⟨phasedRow v beta y,phased_has_source hv hb y,phasedRow_zero v beta y,
    affinePacket_zero v beta y,fun _ hn => phased_divisor_realization v beta y hn⟩

theorem source_alone_does_not_force_affine {v : ℂ} (hv : v≠0) {beta : ℝ}
    (hb : beta<1) (y : ℝ) :
    ¬(∀ g : ℕ → ℂ, HasComplexDensityFreeSource g ((beta : ℂ)+I*y) v →
      ∃ S : Finset ℕ, ∃ W : ℕ → ℂ, ∃ mask : ℕ → Prop,
        affinePacket S W mask id id g≠0) := by
  obtain ⟨g,hg,_,hz,_⟩ := exists_invisible_affine_source hv hb y
  intro h
  obtain ⟨S,W,mask,he⟩ := h g hg
  exact he (hz S W mask id id rfl rfl)

/-- Even the EXACT ordinary-prime residue and actual multiplicity of
an actual nontrivial zero do not supply the nonlinear pair source. -/
theorem actual_residue_does_not_force_affine (rho : NontrivialZetaZero) :
    ¬(∀ g : ℕ → ℂ,
      HasComplexDensityFreeSource g rho.1 (-(analyticZetaZeroMultiplicity rho : ℂ)) →
      ∃ S : Finset ℕ, ∃ W : ℕ → ℂ, ∃ mask : ℕ → Prop,
        affinePacket S W mask id id g≠0) := by
  have hv : -(analyticZetaZeroMultiplicity rho : ℂ)≠0 :=
    neg_ne_zero.mpr (Nat.cast_ne_zero.mpr (analyticZetaZeroMultiplicity_positive rho).ne')
  have h := source_alone_does_not_force_affine hv (NontrivialZetaZero.re_lt_one rho)
    rho.1.im
  have he : (rho.1.re : ℂ)+I*rho.1.im=rho.1 := by
    apply Complex.ext <;> simp
  simpa only [he] using h

end RiemannGaussian.ArithmeticOperatorKummerAffineSourceAudit

#lint+ in RiemannGaussian.ArithmeticOperatorKummerAffineSourceAudit

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
  unless declarations>0 do throwError "Empty affine source-gate audit."
  logInfo m!"Kummer-affine audit: {declarations} declarations, {theorems} theorems; only standard axioms."
  IO.FS.createDirAll ".lake/arithmetic-operator-kummer-affine"
  IO.FS.writeFile ".lake/arithmetic-operator-kummer-affine/axioms.json"
    (Json.mkObj [("scope",toJson "literal two-large common-row prime-pair identity and complex-height linear-source inference obstruction; actual nonlinear source open"),
      ("onlyStandardAxioms",toJson true),("namespaceLinters",toJson (15:Nat)),
      ("allLocalDeclarationsByModuleProvenance",toJson true),
      ("declarations",toJson declarations),("theoremsIncludingGeneratedHelpers",toJson theorems),
      ("declarationAxioms",Json.arr reports)]).pretty
