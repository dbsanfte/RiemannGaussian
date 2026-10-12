/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ArithmeticOperatorCharacterCofactorAudit

/-!
# Fixed nonunit CRT rows conserve the original prime source

The union of nonunit residues modulo q is kept on the literal outer
integer row, not on just its prime leg. Its complete response is the
uncoded commutator minus its actual principal-character counterpart.
At every genuine zero it retains the nonzero residue multiplied by
1 minus the finite excluded-prime factor at the matched real coordinate.
All prime powers, divided cutoffs, both phases and correlated tests remain.

The finite join is still one scalar test for arbitrary input columns.
This rejects fixed nonunit-row bookkeeping as a new signed constraint;
it is not a native-cutoff source asymptotic or a prime estimate. Individual
nonunit residues, growing moduli and correlated two-column constraints
are not identified with this union-of-residues audit.
-/

namespace RiemannGaussian.ArithmeticOperatorNonunitCrtAudit
noncomputable section
open Complex Filter
open ArithmeticOperatorGammaTwistAudit SuzukiCarryCorrelation
open scoped BigOperators Topology Classical

/-- Literal union of all nonunit outer rows. -/
def row (q : ℕ) (y : ℝ) (n : ℕ) : ℂ :=
  if n.Coprime q then 0 else twistCommutator (primePhase y) n

/-- Principal coding is exactly coprimality, including proper powers. -/
theorem principal_value (q n : ℕ) :
    (1 : DirichletCharacter ℂ q) n=if n.Coprime q then 1 else 0 := by
  by_cases h : n.Coprime q
  · rw [ite_eq_left h]
    exact MulChar.one_apply ((ZMod.isUnit_iff_coprime n q).mpr h)
  · rw [ite_eq_right h]
    exact MulChar.map_nonunit _ ((ZMod.isUnit_iff_coprime n q).not.mpr h)

/-- Exact subtraction on EVERY literal integer; no period completion. -/
theorem row_eq_principal_complement (q : ℕ) (y : ℝ) (n : ℕ) :
    row q y n=twistCommutator (primePhase y) n-
      ArithmeticOperatorCharacterCofactorAudit.row (1 : DirichletCharacter ℂ q) y n := by
  rw [row,ArithmeticOperatorCharacterCofactorAudit.row,principal_value]
  split_ifs <;> simp

/-- Continued response in the original zero coordinate. -/
def response (q : ℕ) [NeZero q] (y : ℝ) (z : ℂ) : ℂ :=
  ArithmeticOperatorTwistSourceAudit.response y z-
    ArithmeticOperatorCharacterCofactorAudit.response (1 : DirichletCharacter ℂ q) y z

private theorem commutator_summable (y : ℝ) {s : ℂ} (hs : 1<s.re) :
    LSeriesSummable (twistCommutator (primePhase y)) s := by
  have h := ArithmeticOperatorCharacterCofactorAudit.row_summable
    (1 : DirichletCharacter ℂ 1) y hs
  have he : ArithmeticOperatorCharacterCofactorAudit.row (1 : DirichletCharacter ℂ 1) y=
      twistCommutator (primePhase y) := by
    funext n
    simp [ArithmeticOperatorCharacterCofactorAudit.row,principal_value]
  rwa [he] at h

/-- Genuine convergent series, without extending Euler convergence
into the candidate-zero strip. -/
theorem euler_response (q : ℕ) [NeZero q] (y : ℝ) {s : ℂ} (hs : 1<s.re) :
    LSeries (row q y) s=response q y (s+I*y) := by
  have he : row q y=twistCommutator (primePhase y)-
      ArithmeticOperatorCharacterCofactorAudit.row (1 : DirichletCharacter ℂ q) y :=
    funext (row_eq_principal_complement q y)
  rw [he,LSeries_sub (commutator_summable y hs)
    (ArithmeticOperatorCharacterCofactorAudit.row_summable _ y hs),
    ArithmeticOperatorTwistSourceAudit.commutator_euler_response y hs,
    ArithmeticOperatorCharacterCofactorAudit.euler_response _ y hs]
  simp [response,ArithmeticOperatorTwistSourceAudit.response]

/-- The actual finite Euler factor on the matched real coordinate. -/
def realFactor (q : ℕ) (beta : ℝ) : ℝ :=
  ∏ p∈q.primeFactors,(1-(p : ℝ)^(-beta))

theorem principalFactor_real (q : ℕ) (beta : ℝ) :
    ArithmeticOperatorCharacterCofactorAudit.principalFactor q (beta : ℂ)=
      (realFactor q beta : ℂ) := by
  unfold ArithmeticOperatorCharacterCofactorAudit.principalFactor realFactor
  push_cast
  apply Finset.prod_congr rfl
  intro p _
  rw [show -(beta : ℂ)=((-beta : ℝ) : ℂ) by simp,
    ← Complex.ofReal_natCast,Complex.ofReal_cpow (Nat.cast_nonneg p)]

/-- Every nontrivial fixed modulus retains a strictly positive fraction
of the matched source; no height or common-L-zero premise is needed. -/
theorem realFactor_bounds {q : ℕ} (hq : 1<q) {beta : ℝ} (hb : 0<beta) :
    0<realFactor q beta ∧ realFactor q beta<1 := by
  have hp (p : ℕ) (h : p∈q.primeFactors) :
      0<1-(p : ℝ)^(-beta) ∧ 1-(p : ℝ)^(-beta)<1 := by
    have hprime := Nat.prime_of_mem_primeFactors h
    have hlt := Real.rpow_lt_one_of_one_lt_of_neg
      (show (1 : ℝ)<p by exact_mod_cast hprime.one_lt) (neg_neg_of_pos hb)
    have hpos := Real.rpow_pos_of_pos (show (0 : ℝ)<p by exact_mod_cast hprime.pos) (-beta)
    constructor <;> linarith
  unfold realFactor
  constructor
  · exact Finset.prod_pos (fun p h => (hp p h).1)
  · simpa only [Finset.prod_const_one] using
      (Finset.prod_lt_prod_of_nonempty₀ (fun p h => (hp p h).1)
        (fun p h => (hp p h).2) (Nat.nonempty_primeFactors.mpr hq))

/-- Exact residue at EVERY genuine zero and EVERY analytic multiplicity. -/
theorem actual_zero_source (q : ℕ) [NeZero q] (rho : NontrivialZetaZero) :
    Tendsto (fun z : ℂ => (z-rho.1)*response q rho.1.im z) (𝓝[≠] rho.1)
      (𝓝 (-(analyticZetaZeroMultiplicity rho : ℂ)*riemannZeta (rho.1.re : ℂ)*
        (1-(realFactor q rho.1.re : ℂ)))) := by
  have ht := (ArithmeticOperatorTwistSourceAudit.tendsto_commutator_source rho).sub
    (ArithmeticOperatorCharacterCofactorAudit.tendsto_principal_source (q := q) rho)
  have hr : (rho.1.re : ℂ)≠1 := by
    intro h
    have he := congrArg Complex.re h
    simp only [ofReal_re,one_re] at he
    linarith [NontrivialZetaZero.re_lt_one rho]
  have hL : (1 : DirichletCharacter ℂ q).LFunction (rho.1.re : ℂ)=
      (realFactor q rho.1.re : ℂ)*riemannZeta (rho.1.re : ℂ) := by
    change DirichletCharacter.LFunctionTrivChar q (rho.1.re : ℂ)=_
    rw [DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta (N := q) hr]
    exact congrArg (fun a : ℂ => a*riemannZeta (rho.1.re : ℂ)) (principalFactor_real q _)
  rw [hL] at ht
  convert ht using 1
  · funext z
    unfold response
    ring
  · congr 1
    ring

theorem actual_zero_source_ne_zero {q : ℕ} (hq : 1<q)
    (rho : NontrivialZetaZero) :
    -(analyticZetaZeroMultiplicity rho : ℂ)*riemannZeta (rho.1.re : ℂ)*
      (1-(realFactor q rho.1.re : ℂ))≠0 := by
  apply mul_ne_zero (ArithmeticOperatorTwistSourceAudit.commutator_source_ne_zero rho)
  have hf := (realFactor_bounds hq (NontrivialZetaZero.zero_lt_re rho)).2
  exact_mod_cast (show (1 : ℝ)-realFactor q rho.1.re≠0 by linarith)

/-- One common symbol clears both actual density locations. -/
def poleSymbol (y : ℝ) (z : ℂ) : ℂ := (z-1)^2*(z-(1+I*y))

private def principalClearing (q : ℕ) [NeZero q] (y : ℝ) (z : ℂ) : ℂ :=
  poleSymbol y z*ArithmeticOperatorCharacterCofactorAudit.response
    (1 : DirichletCharacter ℂ q) y z

private theorem principal_analytic (q : ℕ) [NeZero q] {z : ℂ} (hz : z≠1) :
    AnalyticAt ℂ (1 : DirichletCharacter ℂ q).LFunction z := by
  have hd : DifferentiableOn ℂ (1 : DirichletCharacter ℂ q).LFunction ({(1 : ℂ)}ᶜ) :=
    fun w hw => (DirichletCharacter.differentiableAt_LFunction _ w (Or.inl hw)).differentiableWithinAt
  exact hd.analyticAt (isOpen_compl_singleton.mem_nhds hz)

private theorem cleared_character_at_one (q : ℕ) [NeZero q] (y : ℝ) (hy : y≠0) :
    ∃ E : ℂ → ℂ,AnalyticAt ℂ E 1 ∧
      principalClearing q y=ᶠ[𝓝[≠] (1 : ℂ)] E := by
  let g := (1 : DirichletCharacter ℂ q).LFunction
  let U := DirichletCharacter.LFunctionTrivChar₁ q
  have hU : AnalyticAt ℂ U 1 :=
    (DirichletCharacter.differentiable_LFunctionTrivChar₁ q).analyticAt 1
  have hnU : U 1≠0 := DirichletCharacter.LFunctionTrivChar₁_apply_one_ne_zero q
  have hshift : (1-I*y : ℂ)≠1 := by
    intro h
    have hi := congrArg Complex.im h
    simp only [sub_im,one_im,mul_im,I_re,I_im,ofReal_re,ofReal_im] at hi
    apply hy
    linarith
  have hB : AnalyticAt ℂ (fun z : ℂ => g (z-I*y)) 1 :=
    AnalyticAt.comp (principal_analytic q hshift) (analyticAt_id.sub analyticAt_const)
  let E : ℂ → ℂ := fun z => (z-(1+I*y)) *
    (g (z-I*y)*((z-1)-(z-1)^2*logDeriv U z)+(z-1)*deriv U z-U z)
  have hLD : AnalyticAt ℂ (logDeriv U) 1 := hU.deriv.div hU hnU
  refine ⟨E,(analyticAt_id.sub analyticAt_const).mul (
    ((hB.mul ((analyticAt_id.sub analyticAt_const).sub
      (((analyticAt_id.sub analyticAt_const).pow 2).mul hLD))).add
        ((analyticAt_id.sub analyticAt_const).mul hU.deriv)).sub hU),?_⟩
  filter_upwards [self_mem_nhdsWithin,
    hU.continuousAt.eventually_ne hnU |>.filter_mono nhdsWithin_le_nhds]
    with z (hz : z≠1) hn
  have hv : U z=(z-1)*g z := Function.update_of_ne hz _ _
  have hd : deriv U z=(z-1)*deriv g z+g z :=
    DirichletCharacter.deriv_LFunctionTrivChar₁_apply_of_ne_one q hz
  have hng : g z≠0 := by intro hh; rw [hh,mul_zero] at hv; exact hn hv
  dsimp [principalClearing,poleSymbol,ArithmeticOperatorCharacterCofactorAudit.response,E]
  change (z-1)^2*(z-(1+I*y)) * (g (z-I*y)*(-logDeriv g z)+deriv g z)=_
  rw [logDeriv_apply,logDeriv_apply,hd,hv]
  field_simp [hng,sub_ne_zero.mpr hz]
  ring

private theorem cleared_character_at_shifted_one (q : ℕ) [NeZero q]
    (y : ℝ) (hy : y≠0) :
    ∃ E : ℂ → ℂ,AnalyticAt ℂ E (1+I*y) ∧
      principalClearing q y=ᶠ[𝓝[≠] (1+I*y : ℂ)] E := by
  let g := (1 : DirichletCharacter ℂ q).LFunction
  let U := DirichletCharacter.LFunctionTrivChar₁ q
  have hc : (1+I*y : ℂ)≠1 := by
    intro h
    have hi := congrArg Complex.im h
    simp only [add_im,one_im,mul_im,I_re,I_im,ofReal_re,ofReal_im] at hi
    apply hy
    linarith
  have hg : AnalyticAt ℂ g (1+I*y) :=
    principal_analytic q hc
  have hng : g (1+I*y)≠0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re _ (Or.inr hc) (by simp)
  have hA : AnalyticAt ℂ (fun z : ℂ => U (z-I*y)) (1+I*y) :=
    AnalyticAt.comp ((DirichletCharacter.differentiable_LFunctionTrivChar₁ q).analyticAt _)
      (analyticAt_id.sub analyticAt_const)
  let E : ℂ → ℂ := fun z => (z-1)^2 *
    (U (z-I*y)*(-logDeriv g z)+(z-(1+I*y))*deriv g z)
  refine ⟨E,((analyticAt_id.sub analyticAt_const).pow 2).mul
    ((hA.mul (hg.deriv.div hg hng).neg).add
      ((analyticAt_id.sub analyticAt_const).mul hg.deriv)),?_⟩
  filter_upwards [self_mem_nhdsWithin] with z (hz : z≠1+I*y)
  have hv : z-I*y≠1 := by intro hh; apply hz; linear_combination hh
  have he : U (z-I*y)=(z-(1+I*y))*g (z-I*y) := by
    rw [show z-(1+I*y)=z-I*y-1 by ring]
    exact Function.update_of_ne hv _ _
  dsimp [principalClearing,poleSymbol,ArithmeticOperatorCharacterCofactorAudit.response,E]
  change (z-1)^2*(z-(1+I*y))*(g (z-I*y)*(-logDeriv g z)+deriv g z)=_
  rw [he]
  ring

/-- The density/pole is removed as an actual analytic germ at BOTH
locations; this is not a native-cutoff or zero-free assertion. -/
def centeredResponse (q : ℕ) [NeZero q] (y : ℝ) (z : ℂ) : ℂ :=
  poleSymbol y z*response q y z

private theorem centered_eq (q : ℕ) [NeZero q] (y : ℝ) :
    centeredResponse q y=principalClearing 1 y-principalClearing q y := by
  funext z
  change poleSymbol y z*(ArithmeticOperatorTwistSourceAudit.response y z-
      ArithmeticOperatorCharacterCofactorAudit.response (1 : DirichletCharacter ℂ q) y z)=
    poleSymbol y z*ArithmeticOperatorCharacterCofactorAudit.response
      (1 : DirichletCharacter ℂ 1) y z-
    poleSymbol y z*ArithmeticOperatorCharacterCofactorAudit.response
      (1 : DirichletCharacter ℂ q) y z
  simp only [ArithmeticOperatorTwistSourceAudit.response,
    ArithmeticOperatorCharacterCofactorAudit.response,
    DirichletCharacter.LFunction_modOne_eq]
  ring

theorem centered_density_analytic (q : ℕ) [NeZero q] (y : ℝ) (hy : y≠0) :
    (∃ E : ℂ → ℂ,AnalyticAt ℂ E 1 ∧
      centeredResponse q y=ᶠ[𝓝[≠] (1 : ℂ)] E) ∧
    (∃ E : ℂ → ℂ,AnalyticAt ℂ E (1+I*y) ∧
      centeredResponse q y=ᶠ[𝓝[≠] (1+I*y : ℂ)] E) := by
  rw [centered_eq]
  constructor
  · obtain ⟨A,hA,hgA⟩ := cleared_character_at_one 1 y hy
    obtain ⟨B,hB,hgB⟩ := cleared_character_at_one q y hy
    exact ⟨A-B,hA.sub hB,hgA.sub hgB⟩
  · obtain ⟨A,hA,hgA⟩ := cleared_character_at_shifted_one 1 y hy
    obtain ⟨B,hB,hgB⟩ := cleared_character_at_shifted_one q y hy
    exact ⟨A-B,hA.sub hB,hgA.sub hgB⟩

theorem poleSymbol_ne_zero_at_zero (rho : NontrivialZetaZero) :
    poleSymbol rho.1.im rho.1≠0 := by
  apply mul_ne_zero (pow_ne_zero 2 (sub_ne_zero.mpr rho.2.2.2))
  apply sub_ne_zero.mpr
  intro h
  have he := congrArg Complex.re h
  simp only [add_re,one_re,mul_re,I_re,I_im,ofReal_re,ofReal_im] at he
  linarith [NontrivialZetaZero.re_lt_one rho]

theorem centered_actual_zero_source (q : ℕ) [NeZero q] (rho : NontrivialZetaZero) :
    Tendsto (fun z : ℂ => (z-rho.1)*centeredResponse q rho.1.im z) (𝓝[≠] rho.1)
      (𝓝 (poleSymbol rho.1.im rho.1 *
        (-(analyticZetaZeroMultiplicity rho : ℂ)*riemannZeta (rho.1.re : ℂ)*
          (1-(realFactor q rho.1.re : ℂ))))) := by
  have hA : AnalyticAt ℂ (poleSymbol rho.1.im) rho.1 :=
    ((analyticAt_id.sub analyticAt_const).pow 2).mul (analyticAt_id.sub analyticAt_const)
  have ht := hA.continuousAt.tendsto.mono_left nhdsWithin_le_nhds |>.mul
    (actual_zero_source q rho)
  convert ht using 1
  funext z
  unfold centeredResponse
  ring

theorem centered_actual_zero_source_ne_zero {q : ℕ} (hq : 1<q)
    (rho : NontrivialZetaZero) :
    poleSymbol rho.1.im rho.1 *
      (-(analyticZetaZeroMultiplicity rho : ℂ)*riemannZeta (rho.1.re : ℂ)*
        (1-(realFactor q rho.1.re : ℂ)))≠0 :=
  mul_ne_zero (poleSymbol_ne_zero_at_zero rho) (actual_zero_source_ne_zero hq rho)

/-- Exact strength check at the matched point. Fixed nonunit union
coding does not supply a stronger arithmetic nonvanishing constraint. -/
theorem response_removable_iff_nonvanishing {q : ℕ} [NeZero q] (hq : 1<q)
    {beta : ℝ} (hb0 : 0<beta) (hb1 : beta<1) (y : ℝ) :
    (∃ E : ℂ → ℂ,AnalyticAt ℂ E ((beta : ℂ)+I*y) ∧
      response q y=ᶠ[𝓝[≠] ((beta : ℂ)+I*y)] E) ↔
        riemannZeta ((beta : ℂ)+I*y)≠0 := by
  let z : ℂ := (beta : ℂ)+I*y
  have hRe : z.re=beta := by simp [z]
  have hz1 : z≠1 := by
    intro h
    have he := congrArg Complex.re h
    rw [hRe] at he
    simp only [one_re] at he
    linarith
  have he : z-I*y=(beta : ℂ) := by dsimp [z];ring
  have hshift : z-I*y≠1 := by
    rw [he]
    intro h
    have hh := congrArg Complex.re h
    simp only [ofReal_re,one_re] at hh
    linarith
  constructor
  · intro ⟨E,hE,hg⟩ hz
    let rho : NontrivialZetaZero := ⟨z,hz,by
      rintro ⟨n,hn⟩
      have hh := congrArg Complex.re hn
      rw [hRe] at hh
      norm_num [Complex.mul_re] at hh
      nlinarith [Nat.cast_nonneg (α := ℝ) n],hz1⟩
    have hy : rho.1.im=y := by simp [rho,z]
    have hSource := actual_zero_source q rho
    rw [hy] at hSource
    have hSub : Tendsto (fun w : ℂ => w-z) (𝓝[≠] z) (𝓝 0) := by
      simpa only [sub_self] using (show Tendsto (fun w : ℂ => w-z)
        (𝓝[≠] z) (𝓝 (z-z)) from
          (continuous_id.sub continuous_const).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    have hELimit : Tendsto E (𝓝[≠] z) (𝓝 (E z)) :=
      hE.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have hZero : Tendsto (fun w : ℂ => (w-z)*response q y w) (𝓝[≠] z) (𝓝 0) := by
      have ht := hSub.mul hELimit
      simp only [zero_mul] at ht
      exact ht.congr' (Filter.EventuallyEq.rfl.mul hg.symm)
    exact actual_zero_source_ne_zero hq rho (tendsto_nhds_unique hSource hZero)
  · intro hz
    have hA := analyticOn_riemannZeta z hz1
    have hB : AnalyticAt ℂ (fun w : ℂ => riemannZeta (w-I*y)) z :=
      AnalyticAt.comp (analyticOn_riemannZeta _ hshift) (analyticAt_id.sub analyticAt_const)
    have hC := principal_analytic q hz1
    have hD : AnalyticAt ℂ
        (fun w : ℂ => (1 : DirichletCharacter ℂ q).LFunction (w-I*y)) z :=
      AnalyticAt.comp (principal_analytic q hshift) (analyticAt_id.sub analyticAt_const)
    have hL : (1 : DirichletCharacter ℂ q).LFunction z≠0 := by
      change DirichletCharacter.LFunctionTrivChar q z≠0
      rw [DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta hz1]
      exact mul_ne_zero (ArithmeticOperatorCharacterCofactorAudit.principalFactor_ne_zero q
        (by rwa [hRe])) hz
    exact ⟨response q y,((hB.mul (hA.deriv.div hA hz).neg).add hA.deriv).sub
      ((hD.mul (hC.deriv.div hC hL).neg).add hC.deriv),Filter.EventuallyEq.rfl⟩

/-- Actual native packet, without altering its nonunit-row mask. -/
def nativePacket (q : ℕ) (y : ℝ) (X : ℕ) (test : ℕ → ℂ) : ℂ :=
  ∑ n∈Finset.Icc 1 X,test n*row q y n

/-- Arbitrary-column audit with the same outer mask and both phases. -/
def freePacket (q : ℕ) (y : ℝ) (X : ℕ) (test w : ℕ → ℂ) : ℂ :=
  ∑ n∈Finset.Icc 1 X,test n*(1-(1 : DirichletCharacter ℂ q) n)*
    ArithmeticOperatorTwistSourceAudit.defect w y n

/-- Full signed kernel, retaining the original divided cutoff. -/
def joinedKernel (q : ℕ) (y : ℝ) (X : ℕ) (test : ℕ → ℂ) (d : ℕ) : ℂ :=
  ∑ a∈Finset.Icc 1 (X/d),test (d*a)*(1-(1 : DirichletCharacter ℂ q) (d*a))*
    primePhase y d*(1-primePhase y a)

/-- Squarefreeness, period averaging or a prime density is not used in
this exact finite identity. Every proper-power column is retained. -/
theorem freePacket_eq_scalar (q : ℕ) (y : ℝ) (X : ℕ) (test w : ℕ → ℂ) :
    freePacket q y X test w=∑ d∈Finset.Icc 1 X,w d*joinedKernel q y X test d := by
  have he : freePacket q y X test w=
      ∑ n∈Finset.Icc 1 X,∑ da∈n.divisorsAntidiagonal,
        w da.1*test (da.1*da.2)*(1-(1 : DirichletCharacter ℂ q) (da.1*da.2))*
          primePhase y da.1*(1-primePhase y da.2) := by
    unfold freePacket ArithmeticOperatorTwistSourceAudit.defect
      ArithmeticOperatorCommutatorAudit.divisorConvolution
    apply Finset.sum_congr rfl
    intro n _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro da hda
    simp only [← (Nat.mem_divisorsAntidiagonal.mp hda).1]
    simp only [Nat.cast_mul]
    ring
  rw [he,sum_Icc_divisorsAntidiagonal_eq_sum_divided_prefix X
    (fun d a => w d*test (d*a)*(1-(1 : DirichletCharacter ℂ q) (d*a))*
      primePhase y d*(1-primePhase y a))]
  apply Finset.sum_congr rfl
  intro d _
  rw [joinedKernel,Finset.mul_sum]
  exact Finset.sum_congr rfl (fun _ _ => by ring)

theorem actualPacket_eq_scalar (q : ℕ) (y : ℝ) (X : ℕ) (test : ℕ → ℂ) :
    nativePacket q y X test=
      ∑ d∈Finset.Icc 1 X,(ArithmeticFunction.vonMangoldt d : ℂ)*joinedKernel q y X test d := by
  have he : nativePacket q y X test=freePacket q y X test
      (fun d => (ArithmeticFunction.vonMangoldt d : ℂ)) := by
    unfold nativePacket freePacket
    simp_rw [ArithmeticOperatorTwistSourceAudit.defect_eq_commutator,
      row_eq_principal_complement,ArithmeticOperatorCharacterCofactorAudit.row]
    exact Finset.sum_congr rfl (fun _ _ => by ring)
  rw [he,freePacket_eq_scalar]

/-- Free-column bounds require the full signed kernel to vanish.
These free controls are NOT claimed to satisfy actual Gamma data. -/
theorem bound_forall_free_inputs_iff (q : ℕ) (y : ℝ) (X : ℕ)
    (test : ℕ → ℂ) (B : ℝ) :
    (∀ w,‖freePacket q y X test w‖≤B) ↔
      0≤B ∧ ∀ d∈Finset.Icc 1 X,joinedKernel q y X test d=0 := by
  simp_rw [freePacket_eq_scalar]
  exact ArithmeticOperatorGramAudit.scalar_bound_forall_weights_iff _ _ _

end
end RiemannGaussian.ArithmeticOperatorNonunitCrtAudit
