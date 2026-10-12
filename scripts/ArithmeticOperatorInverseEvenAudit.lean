/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ArithmeticOperatorKloostermanPsdAudit
import RiemannGaussian.ArithmeticOperatorOrderedGapAudit
import Mathlib.Tactic.Linter
import Lean.Util.CollectAxioms

/-!
# Inverse-even projection: exact positivity and its retained diagonal cost

The positive inverse-even form is half the original inverse pairing PLUS
the ordinary primitive-residue Gram form. No diagonal or proper-power
denominator is deleted. The added diagonal has the genuine totient/zeta
source, even after density-pole removal; it cannot be declared a paid
analytic error. Generic involution positivity is not a new arithmetic
estimate for the surviving Kloosterman/signed packets.

The actual zero source of the COMPLETE projected nonzero-frequency
packet is deliberately not inferred from that of its diagonal debit.
-/

set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
open scoped BigOperators Classical Topology ComplexConjugate
namespace RiemannGaussian.ArithmeticOperatorInverseEvenAudit
open Complex Filter ArithmeticOperatorKloostermanPsdAudit

section Involution
variable {ι : Type*} [Fintype ι]

/-- Finite energy, without any assumption about primes or integer data. -/
def finiteEnergy (f : ι → ℂ) : ℂ := ∑ a, f a*conj (f a)

/-- The complete pairing for an arbitrary finite involution. -/
def involutionPairing (sigma : ι → ι) (f : ι → ℂ) : ℂ :=
  ∑ a, f a*conj (f (sigma a))

/-- Symmetrization BEFORE joining the involution pairing. -/
def evenProjection (sigma : ι → ι) (f : ι → ℂ) (a : ι) : ℂ :=
  (f a+f (sigma a))/2

omit [Fintype ι] in
theorem evenProjection_invariant (sigma : ι → ι)
    (hs : Function.Involutive sigma) (f : ι → ℂ) (a : ι) :
    evenProjection sigma f (sigma a)=evenProjection sigma f a := by
  simp only [evenProjection,hs a]
  ring

omit [Fintype ι] in
theorem evenProjection_idempotent (sigma : ι → ι)
    (hs : Function.Involutive sigma) (f : ι → ℂ) :
    evenProjection sigma (evenProjection sigma f)=evenProjection sigma f := by
  funext a
  rw [evenProjection,evenProjection_invariant sigma hs]
  ring

theorem finiteEnergy_nonneg (f : ι → ℂ) : 0≤(finiteEnergy f).re := by
  simp only [finiteEnergy,Complex.re_sum]
  exact Finset.sum_nonneg (fun a _ => by
    rw [mul_conj,Complex.ofReal_re]
    exact normSq_nonneg _)

theorem involutionPairing_reindex (sigma : ι → ι)
    (hs : Function.Involutive sigma) (f : ι → ℂ) :
    (∑ a, f (sigma a)*conj (f a))=involutionPairing sigma f := by
  exact Fintype.sum_equiv (hs.toPerm sigma) _ _ (fun a => by
    change f (sigma a)*conj (f a)=f (sigma a)*conj (f (sigma (sigma a)))
    rw [hs a])

/-- The positivity mechanism is an exact ANY-involution identity. It
cannot itself constrain actual prime weights across denominators. -/
theorem twice_evenEnergy (sigma : ι → ι)
    (hs : Function.Involutive sigma) (f : ι → ℂ) :
    2*finiteEnergy (evenProjection sigma f)=
      finiteEnergy f+involutionPairing sigma f := by
  have he : (∑ a, f (sigma a)*conj (f (sigma a)))=finiteEnergy f :=
    Fintype.sum_equiv (hs.toPerm sigma) _ _ (fun _ => rfl)
  have hx := involutionPairing_reindex sigma hs f
  have hatom (a : ι) :
      4*(evenProjection sigma f a*conj (evenProjection sigma f a))=
        f a*conj (f a)+f a*conj (f (sigma a))+
          f (sigma a)*conj (f a)+f (sigma a)*conj (f (sigma a)) := by
    simp only [evenProjection,map_div₀,map_add,map_ofNat]
    ring
  have ht : 4*finiteEnergy (evenProjection sigma f)=
      finiteEnergy f+involutionPairing sigma f+involutionPairing sigma f+
        finiteEnergy f := by
    simp only [finiteEnergy,Finset.mul_sum]
    rw [Finset.sum_congr rfl (fun a _ => hatom a)]
    simp only [Finset.sum_add_distrib]
    rw [he,hx]
    rfl
  linear_combination ht/2

theorem evenPairing_eq_energy (sigma : ι → ι)
    (hs : Function.Involutive sigma) (f : ι → ℂ) :
    involutionPairing sigma (evenProjection sigma f)=
      finiteEnergy (evenProjection sigma f) := by
  simp only [involutionPairing,finiteEnergy,evenProjection_invariant sigma hs]

end Involution

variable {q : ℕ} [NeZero q]

/-- Actual inverse-even unit amplitudes; every unit of every modulus,
including proper prime powers and the modulus-one endpoint, is kept. -/
def inverseEven (f : (ZMod q)ˣ → ℂ) : (ZMod q)ˣ → ℂ :=
  evenProjection Inv.inv f

omit [NeZero q] in
theorem inverseEven_invariant (f : (ZMod q)ˣ → ℂ) (a : (ZMod q)ˣ) :
    inverseEven f a⁻¹=inverseEven f a :=
  evenProjection_invariant Inv.inv inv_inv f a

theorem inverseEven_positive (f : (ZMod q)ˣ → ℂ) :
    0≤(inverseQuadratic (inverseEven f)).re := by
  change 0≤(involutionPairing Inv.inv (evenProjection Inv.inv f)).re
  rw [evenPairing_eq_energy Inv.inv inv_inv]
  exact finiteEnergy_nonneg _

/-- The ORIGINAL inverse correlation survives with coefficient one
half. The other half is a full retained Gram term, not a small error. -/
theorem inverseEven_exact_ledger (f : (ZMod q)ˣ → ℂ) :
    inverseQuadratic (inverseEven f)=
      (finiteEnergy f+inverseQuadratic f)/2 := by
  change involutionPairing Inv.inv (evenProjection Inv.inv f)=
    (finiteEnergy f+involutionPairing Inv.inv f)/2
  rw [evenPairing_eq_energy Inv.inv inv_inv]
  have h := twice_evenEnergy Inv.inv inv_inv f
  linear_combination h/2

/-- The added Fourier Gram row has the SAME two frequency indices. -/
def unitGram (m n : ZMod q) : ℂ :=
  ∑ a : (ZMod q)ˣ,
    ZMod.stdAddChar (m*(a : ZMod q))*conj (ZMod.stdAddChar (n*(a : ZMod q)))

/-- Complete frequency quadratic of the added primitive-residue Gram. -/
def unitGramQuadratic (alpha : ZMod q → ℂ) : ℂ :=
  ∑ m, ∑ n, alpha m*conj (alpha n)*unitGram m n

theorem unitGramQuadratic_eq_energy (alpha : ZMod q → ℂ) :
    unitGramQuadratic alpha=finiteEnergy
      (fun a : (ZMod q)ˣ => amplitude alpha (a : ZMod q)) := by
  classical
  unfold unitGramQuadratic unitGram finiteEnergy amplitude
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Eq.trans (Finset.sum_congr rfl (fun _ _ => Finset.sum_comm))
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp only [map_sum,map_mul,Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  apply Finset.sum_congr rfl
  intro n _
  ring

theorem inverseEven_fourier_ledger (alpha : ZMod q → ℂ) :
    inverseQuadratic (inverseEven
      (fun a : (ZMod q)ˣ => amplitude alpha (a : ZMod q)))=
      (unitGramQuadratic alpha+quadratic alpha)/2 := by
  rw [inverseEven_exact_ledger,unitGramQuadratic_eq_energy,quadratic_eq_inverse]

/-- Each diagonal is the complete native primitive count, not just
ordinary prime moduli. This is the exact repair cost being added. -/
theorem unitGram_diagonal (m : ZMod q) : unitGram m m=(q.totient : ℂ) := by
  classical
  have hc (x : ZMod q) : ZMod.stdAddChar x*conj (ZMod.stdAddChar x)=1 := by
    simp only [ZMod.stdAddChar_apply]
    rw [mul_conj,Circle.normSq_coe]
    rfl
  simp only [unitGram,hc,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one]
  rw [ZMod.card_units_eq_totient]

/-- Arbitrary original complex frequency coefficients retain an
EXPLICIT complete primitive-count diagonal debit. -/
theorem unitGram_diagonal_debit (alpha : ZMod q → ℂ) :
    (∑ m, alpha m*conj (alpha m)*unitGram m m)=
      (q.totient : ℂ)*finiteEnergy alpha := by
  simp only [unitGram_diagonal,finiteEnergy,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  ring

/-- Even after joining moduli, the new Gram term is only a scalar
test for arbitrary outer arrays. No actual Mobius data are granted to
those controls. -/
theorem freeGram_bound_iff (D : Finset ℕ) (E : ℕ → ℂ) (B : ℝ) :
    (∀ w : ℕ → ℂ,‖∑ d∈D,w d*E d‖≤B) ↔
      0≤B ∧ ∀ d∈D,E d=0 :=
  ArithmeticOperatorGramAudit.scalar_bound_forall_weights_iff D E B

/-- Actual diagonal Euler response, including every nonsquarefree and
proper-power denominator. Euler convergence is only asserted Re(s)>2. -/
def repairResponse (s : ℂ) : ℂ := (1/2 : ℂ)*ArithmeticOperatorOrderedGapAudit.countResponse s

theorem repair_euler_response (y : ℝ) {s : ℂ} (hs : 2<s.re) :
    LSeries (fun n => (1/2 : ℂ)*(n.totient : ℂ)*SuzukiCarryCorrelation.primePhase y n) s=
      repairResponse (s+I*y) := by
  have he : (fun n => (1/2 : ℂ)*(n.totient : ℂ)*SuzukiCarryCorrelation.primePhase y n)=
      (1/2 : ℂ) • ArithmeticOperatorOrderedGapAudit.increment y := by
    funext n
    simp only [Pi.smul_apply,smul_eq_mul]
    rw [ArithmeticOperatorOrderedGapAudit.increment_eq]
    ring
  rw [he,LSeries_smul,ArithmeticOperatorOrderedGapAudit.increment_euler_response y hs]
  rfl

/-- Every actual zero multiplicity is present in the added diagonal
cost. This does NOT identify the source of the WHOLE projected packet. -/
theorem repair_actual_zero_source (rho : NontrivialZetaZero) :
    ∃ v : ℂ,v≠0 ∧ Tendsto
      (fun s : ℂ => (s-rho.1)^(analyticZetaZeroMultiplicity rho)*repairResponse s)
      (𝓝[≠] rho.1) (𝓝 v) := by
  obtain ⟨v,hv,ht⟩ := ArithmeticOperatorOrderedGapAudit.actual_zero_source rho
  refine ⟨(1/2 : ℂ)*v,mul_ne_zero (by norm_num) hv,?_⟩
  convert ht.const_mul (1/2 : ℂ) using 1
  funext s
  unfold repairResponse
  ring

/-- Exact removal of the two-dimensional density pole of the repair. -/
def centeredRepairResponse (s : ℂ) : ℂ := (s-2)*repairResponse s

theorem repair_density_analytic :
    ∃ E : ℂ → ℂ,AnalyticAt ℂ E 2 ∧
      centeredRepairResponse=ᶠ[𝓝[≠] (2 : ℂ)] E := by
  obtain ⟨E,hE,he⟩ := ArithmeticOperatorOrderedGapAudit.centered_density_analytic
  refine ⟨fun s => (1/2 : ℂ)*E s,analyticAt_const.mul hE,?_⟩
  filter_upwards [he] with s hs
  unfold centeredRepairResponse repairResponse
  rw [←hs]
  unfold ArithmeticOperatorOrderedGapAudit.centeredCountResponse
  ring

theorem centered_repair_actual_zero_source (rho : NontrivialZetaZero) :
    ∃ v : ℂ,v≠0 ∧ Tendsto
      (fun s : ℂ => (s-rho.1)^(analyticZetaZeroMultiplicity rho)*centeredRepairResponse s)
      (𝓝[≠] rho.1) (𝓝 v) := by
  obtain ⟨v,hv,ht⟩ := ArithmeticOperatorOrderedGapAudit.centered_actual_zero_source rho
  refine ⟨(1/2 : ℂ)*v,mul_ne_zero (by norm_num) hv,?_⟩
  convert ht.const_mul (1/2 : ℂ) using 1
  funext s
  unfold centeredRepairResponse repairResponse ArithmeticOperatorOrderedGapAudit.centeredCountResponse
  ring

/-- Declaring the repair analytic through the zero region after pole
removal is EXACTLY an existing zero-free-strength premise. -/
theorem centered_repair_removable_iff {s : ℂ} (hs0 : 0<s.re) (hs1 : s.re<1) :
    (∃ E : ℂ → ℂ,AnalyticAt ℂ E s ∧ E=ᶠ[𝓝[≠] s] centeredRepairResponse) ↔
      riemannZeta s≠0 := by
  rw [←ArithmeticOperatorOrderedGapAudit.centered_removable_iff hs0 hs1]
  constructor
  · rintro ⟨E,hE,he⟩
    refine ⟨fun z => 2*E z,analyticAt_const.mul hE,?_⟩
    filter_upwards [he] with z hz
    rw [hz]
    unfold centeredRepairResponse repairResponse ArithmeticOperatorOrderedGapAudit.centeredCountResponse
    ring
  · rintro ⟨E,hE,he⟩
    refine ⟨fun z => (1/2 : ℂ)*E z,analyticAt_const.mul hE,?_⟩
    filter_upwards [he] with z hz
    rw [hz]
    unfold centeredRepairResponse repairResponse ArithmeticOperatorOrderedGapAudit.centeredCountResponse
    ring

/-- Even the most basic discrete density-centered diagonal payment
is NOT globally source-small. All phases and denominator powers stay. -/
def repairError (c y : ℝ) (N : ℕ) : ℂ :=
  (1/2 : ℂ)*ArithmeticOperatorPrimitiveCountAudit.error c y N

theorem not_eventually_repair_subsource {c : ℝ} (hc : c≤2/3) (y : ℝ)
    {beta : ℝ} (hb : beta<1) (C : ℝ) :
    ¬∀ᶠ N : ℕ in atTop,‖repairError c y N‖≤C*(N : ℝ)^beta := by
  intro h
  apply ArithmeticOperatorPrimitiveCountAudit.not_eventually_subsource_bound hc y hb (2*C)
  filter_upwards [h] with N hN
  have hn : ‖repairError c y N‖=(1/2 : ℝ)*
      ‖ArithmeticOperatorPrimitiveCountAudit.error c y N‖ := by
    simp only [repairError,norm_mul]
    norm_num
  rw [hn] at hN
  linarith

end RiemannGaussian.ArithmeticOperatorInverseEvenAudit

#lint+ in RiemannGaussian.ArithmeticOperatorInverseEvenAudit

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
  unless declarations>0 do throwError "Empty inverse-even projection audit."
  logInfo m!"Inverse-even projection audit: {declarations} declarations, {theorems} theorems; only standard axioms."
  IO.FS.createDirAll ".lake/arithmetic-operator-inverse-even"
  IO.FS.writeFile ".lake/arithmetic-operator-inverse-even/axioms.json"
    (Json.mkObj [("scope",toJson "all actual modular units, exact inverse-even Gram repair, retained totient diagonal source and arbitrary-array collapse"),
      ("onlyStandardAxioms",toJson true),("namespaceLinters",toJson (15:Nat)),
      ("allLocalDeclarationsByModuleProvenance",toJson true),
      ("declarations",toJson declarations),("theoremsIncludingGeneratedHelpers",toJson theorems),
      ("declarationAxioms",Json.arr reports)]).pretty
