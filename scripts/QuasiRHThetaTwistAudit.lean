/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import QuasiRHPattersonModelLocalAudit
import OAI.NumberTheory.DirichletL.GaussSum.CompletedExpansion
import OAI.NumberTheory.DirichletL.Moments.Canonical
import Mathlib.Tactic.Linter
import Lean.Util.CollectAxioms

/-!
# Actual principal unit weight and model-subtracted native Gauss coefficient

The reindexed inverse-character twist times the inverse Kubota multiplier
is principal on units, including at zero additive frequency. The native CRT
character instantiation retains its true quotient ring. On actual squarefree
prime products, the corrected cubic coefficient times the sextic Gauss root
is Mobius. Its SAME-WEIGHT Patterson residual is exactly Mobius times
`1-c*pattersonRatio`, with all angular, ramified-ray and modulus-four factors.
No analytic twisted Voronoi formula, source transfer, or estimate is asserted.
-/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 0
noncomputable section
open scoped BigOperators Classical

namespace OpenAIReview.ThetaTwist
open OAI ActualEisensteinCubic CompletedGauss FiniteGaussPhase QuadraticGaussRay
open CanonicalRowCompletion
open OAI.SevenEighths.CenteredMomentCanonical
open OpenAIReview.PattersonModelLocal
local notation "O" => ActualEisensteinCubic.O

/-- The literal additive sum over every unit, with no nonunit substitution. -/
def unitRamanujan {R : Type*} [CommRing R] [Fintype Rˣ]
    (ψ : AddChar R ℂ) (a : R) : ℂ := ∑ d : Rˣ,ψ (a*d)

/-- The two inverse-character factors cancel on actual units. This is the
reindexed coefficient weight for twist +1 and Kubota multiplier -1. -/
theorem inverse_twist_unit_principal {R : Type*} [CommRing R]
    (χ : MulChar R ℂ) (d : Rˣ) :
    star (χ ((d⁻¹ : Rˣ) : R))*star (χ (d : R))=1 := by
  rw [← star_mul,← map_mul]
  simp

/-- At every additive frequency, including zero and nonunits, the actual
inverse-twist unit sum is the principal Ramanujan sum. -/
theorem inverse_twist_sum_eq_ramanujan {R : Type*} [CommRing R] [Fintype Rˣ]
    (χ : MulChar R ℂ) (ψ : AddChar R ℂ) (a : R) :
    (∑ d : Rˣ,star (χ ((d⁻¹ : Rˣ) : R))*star (χ (d : R))*ψ (a*d))=
      unitRamanujan ψ a := by
  simp only [inverse_twist_unit_principal,one_mul,unitRamanujan]

/-- The zero frequency has the complete unit mass, not mean zero. -/
theorem unitRamanujan_zero {R : Type*} [CommRing R] [Fintype Rˣ]
    (ψ : AddChar R ℂ) : unitRamanujan ψ 0=Fintype.card Rˣ := by
  simp [unitRamanujan]

/-- A literal unit group is nonempty, so the principal zero mass is nonzero. -/
theorem unitRamanujan_zero_ne_zero {R : Type*} [CommRing R] [Fintype Rˣ]
    (ψ : AddChar R ℂ) : unitRamanujan ψ 0≠0 := by
  rw [unitRamanujan_zero]
  exact_mod_cast Fintype.card_ne_zero

/-- Actual canonical CRT characters, with all prime-power exponents and their
quotient ring retained, instantiate the principal unit calculation. -/
theorem native_crt_twist_principal
    {ι : Type*} [Fintype ι] (P : ι → Ideal O) [∀ i,(P i).IsMaximal]
    (hg : ∀ i,OAI.ConcretePrimeRowBridge.goodLambda∉P i)
    (c : ι → ℕ) (hc : ∀ i,1≤c i)
    (hcop : Pairwise (Function.onFun IsCoprime P))
    [Fintype (O⧸∏ i,P i^c i)ˣ]
    (ψ : AddChar (O⧸∏ i,P i^c i) ℂ) (a : O⧸∏ i,P i^c i) :
    (∑ d : (O⧸∏ i,P i^c i)ˣ,
      star (canonicalCRTCharacter P hg c hc hcop ((d⁻¹ : (O⧸∏ i,P i^c i)ˣ) : _))*
      star (canonicalCRTCharacter P hg c hc hcop (d : _))*ψ (a*d))=
      unitRamanujan ψ a :=
  inverse_twist_sum_eq_ramanujan _ ψ a

/-- The actual corrected squarefree spectral coefficient. -/
def nativeCoefficient (n : O) : ℂ :=
  squarefreeGaussCoefficient (Ideal.span {n})*
    star (fixedGQuotientValue (Ideal.Quotient.mk (Ideal.span {(4:O)}) n))

/-- The Patterson replacement changes only gaussTwo, retaining the angular,
ramified-ray and modulus-four factors. The fixed global scalar is separate. -/
def modelCoefficient (n : O) : ℂ :=
  star (angularFactor n)*nativeRay (Ideal.span {n})*
    (Real.rpow (Ideal.absNorm (Ideal.span {n}) : ℝ) (-(1/6:ℝ)) : ℂ)*
      star (fixedGQuotientValue (Ideal.Quotient.mk (Ideal.span {(4:O)}) n))

/-- The literal same-weight residual before a character or scalar is removed. -/
def residualCoefficient (n : O) (c : ℂ) : ℂ :=
  nativeCoefficient n-c*modelCoefficient n

/-- The existing actual Patterson ratio multiplies precisely this same
native coefficient, rather than a changed character population. -/
theorem ratio_mul_native (n : O)
    (hI : OAI.SevenEighths.CubicSieve.Admissible (Ideal.span {n}))
    (hn : n≠0) (hprimary : lambda^2∣n-1) :
    pattersonRatio (Ideal.span {n}) hI*nativeCoefficient n=modelCoefficient n := by
  have hang : star (angularFactor (primaryGenerator (Ideal.span {n})))=
      star (angularFactor n) :=
    congrArg (fun a : O=>star (angularFactor a)) (primaryGenerator_span n hn hprimary)
  rw [nativeCoefficient,squarefreeGaussCoefficient_eq _ hI.1 hI.2,hang]
  calc
    _=star (angularFactor n)*
        (pattersonRatio (Ideal.span {n}) hI*gaussTwo (Ideal.span {n}) hI.2)*
          star (fixedGQuotientValue (Ideal.Quotient.mk (Ideal.span {(4:O)}) n)) := by ring
    _=modelCoefficient n := by rw [pattersonRatio_mul_gaussTwo];unfold modelCoefficient;ring

/-- Native Gauss cancellation uses the actual ideal Mobius value and fixed
modulus-four correction. It introduces no free phase or new source theorem. -/
theorem native_mul_gauss
    {ι : Type*} [Fintype ι] (p : ι → O) (hp : ∀ i,p i≠0)
    [∀ i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hgood : ∀ i,lambda∉Ideal.span {p i})
    (hchar : ∀ i,ringChar (O⧸Ideal.span {p i})≠2)
    (hprimary : ∀ i,lambda^2∣p i-1) :
    nativeCoefficient (∏ i,p i)*canonicalProductGauss p hp hcop hgood (fun _=>1)=
      (UniqueFactorizationMonoid.moebius (Ideal.span {∏ i,p i}) : ℂ) := by
  have hc:=canonicalProductCoefficient_mul_gauss_one p hp hcop hgood hchar hprimary
  have hg : canonicalProductG p hp hcop hgood*
      star (canonicalProductG p hp hcop hgood)=1 := by
    rw [← starRingEnd_apply,Complex.mul_conj',
      norm_canonicalProductG p hp hcop hgood hchar hprimary]
    norm_num
  unfold nativeCoefficient
  rw [squarefreeGaussCoefficient_eq_canonicalProductCoefficient p hp hcop hgood hprimary,
    ← canonicalProductG_eq_fixed_quotient p hp hcop hgood hchar hprimary]
  calc
    _=(canonicalProductCoefficient p hp hcop hgood*
        canonicalProductGauss p hp hcop hgood (fun _=>1))*
          star (canonicalProductG p hp hcop hgood) := by ring
    _=_ := by rw [hc,mul_assoc,hg,mul_one]

/-- The model-subtracted pole coefficient keeps the ACTUAL Patterson ratio.
No scalar model cancellation of the Mobius coefficient is inferred. -/
theorem residual_mul_gauss
    {ι : Type*} [Fintype ι] (p : ι → O) (hp : ∀ i,p i≠0)
    [∀ i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hgood : ∀ i,lambda∉Ideal.span {p i})
    (hchar : ∀ i,ringChar (O⧸Ideal.span {p i})≠2)
    (hprimary : ∀ i,lambda^2∣p i-1)
    (hI : OAI.SevenEighths.CubicSieve.Admissible (Ideal.span {∏ i,p i})) (c : ℂ) :
    residualCoefficient (∏ i,p i) c*canonicalProductGauss p hp hcop hgood (fun _=>1)=
      (UniqueFactorizationMonoid.moebius (Ideal.span {∏ i,p i}) : ℂ)*
        (1-c*pattersonRatio (Ideal.span {∏ i,p i}) hI) := by
  have hn : (∏ i,p i)≠0:=Finset.prod_ne_zero_iff.mpr (fun i _=>hp i)
  have hpr : lambda^2∣(∏ i,p i)-1 := by
    simpa using OAI.CubicEisenstein.primary_finset_product Finset.univ p (fun i _=>hprimary i)
  unfold residualCoefficient
  rw [← ratio_mul_native _ hI hn hpr]
  calc
    _=(nativeCoefficient (∏ i,p i)*canonicalProductGauss p hp hcop hgood (fun _=>1))*
        (1-c*pattersonRatio (Ideal.span {∏ i,p i}) hI) := by ring
    _=_ := by rw [native_mul_gauss p hp hcop hgood hchar hprimary]

/-- The model correction is small in norm, but is not erased. This finite
bound does not assert a pole or give an arithmetic sum estimate. -/
theorem residual_ratio_norm_lower (I : Ideal O)
    (hI : OAI.SevenEighths.CubicSieve.Admissible I) (c : ℂ) :
    1-‖c‖*(Ideal.absNorm I : ℝ)^(-(1/6:ℝ))≤‖1-c*pattersonRatio I hI‖ := by
  simpa only [norm_one,norm_mul,pattersonRatio_norm] using
    norm_sub_norm_le (1:ℂ) (c*pattersonRatio I hI)

/-- A divisor in the same half-open norm dyad is the whole actual ideal.
Thus the top divisor block has no cofactor averaging. -/
theorem divisor_eq_of_norm_lt_two_mul (D I : Ideal O) (hD : D≠0) (hI : I≠0)
    (hdiv : D∣I) (hnorm : Ideal.absNorm I<2*Ideal.absNorm D) : D=I := by
  obtain ⟨B,rfl⟩:=hdiv
  have hB : B≠0 := by intro hz;apply hI;rw [hz,mul_zero]
  have hDN : 0<Ideal.absNorm D :=
    Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hD)
  have hBN : 0<Ideal.absNorm B :=
    Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hB)
  have hBN1 : Ideal.absNorm B=1 := by
    rw [map_mul] at hnorm
    by_contra hh
    have ht : 2≤Ideal.absNorm B := by omega
    nlinarith
  have hb:=Ideal.absNorm_eq_one_iff.mp hBN1
  simp [hb]

end OpenAIReview.ThetaTwist

#lint+ in OpenAIReview.ThetaTwist

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
  unless declarations>0 do throwError "Empty theta twist audit."
  logInfo m!"Theta twist audit: {declarations} declarations, {theorems} theorems; only standard axioms."
  IO.FS.createDirAll ".lake/arithmetic-operator-theta-covariance-gate"
  IO.FS.writeFile ".lake/arithmetic-operator-theta-covariance-gate/axioms.json"
    (Json.mkObj [("scope",toJson "literal principal unit sum and model-subtracted native Gauss coefficient; no analytic twisted Voronoi/source transfer or RH estimate"),
      ("onlyStandardAxioms",toJson true),("namespaceLinters",toJson (15:Nat)),
      ("allLocalDeclarationsByModuleProvenance",toJson true),
      ("declarations",toJson declarations),("theoremsIncludingGeneratedHelpers",toJson theorems),
      ("declarationAxioms",Json.arr reports)]).pretty
