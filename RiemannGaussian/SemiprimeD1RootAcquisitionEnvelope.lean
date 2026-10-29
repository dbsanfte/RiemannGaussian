/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1RootAcquisitionResources
import RiemannGaussian.SemiprimeReportPolynomialGrowth

/-! # Original root acquisition: fixed polynomial times the actual scope table
The exponential stays2^scopeBound(ell). A coarse scalar preprocessing envelope
is never substituted into that exponent. This is a retained-report bound.
-/
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace RiemannGaussian.SemiprimeD1RootAcquisitionEnvelope
open SemiprimePublicAcquiredExecution SemiprimeMacroParameters
open SemiprimeD1RootStateResources SemiprimeD1RootAcquisitionResources
open SemiprimeReportPolynomialGrowth

/-- Fixed scalar/list preprocessing polynomial, before every original family. -/
def scalarPolynomial (S : ℕ) : ℕ :=
  SemiprimePaidFiniteEnumerations.incidenceBudget S (2*S)+10*S+
    3*(S+1)^2+3*(S+1)^2+S*(3*(S+1)^2+3*S+6)+
    S*((16*S+87)*4+10*S+11)+5*(S+S+1)+10*(2*S+S+S+1)^3

/-- Fixed per-assignment table construction/copy polynomial. -/
def tablePolynomial (S : ℕ) : ℕ :=
  S*(1048576*(64*S+2)^10+3*S+12)+(S+S)*(18+4*S)

/-- Fixed combined polynomial, used with the ORIGINAL scope exponential. -/
def polynomial (S : ℕ) : ℕ := scalarPolynomial S+tablePolynomial S

/-- A direct arithmetic majorant preserves the actual exponential. -/
theorem budget_le (N P S : ℕ) (hell : bitLength N ≤ S) (hn : wireCount N ≤ S)
    (hF : factorCount N ≤ S) (hD : scopeBound (bitLength N) ≤ S) (hP : P ≤ S) :
    budget N P ≤ polynomial S*2^(scopeBound (bitLength N)) := by
  have hraw : budget N P ≤ scalarPolynomial S+tablePolynomial S*2^(scopeBound (bitLength N)) := by
    unfold budget SemiprimeD1RootTensorTablesBounds.budget SemiprimeD1RootTensorTablesBounds.factorBudget
      SemiprimeD1RootTensorTablesBounds.ownerBudget SemiprimeD1RootTensorTablesBounds.scope
      SemiprimeD1RootTensorTablesBounds.checkerBudget copyBudget
    calc
      _  ≤  SemiprimePaidFiniteEnumerations.incidenceBudget S (2*S)+10*S+
        3*(S+1)^2+3*(S+1)^2+
        S*(3*(S+1)^2+3*S+6+(1048576*(64*S+2)^10+3*S+12)*2^(scopeBound (bitLength N)))+
        S*((16*S+87)*4+5*(2*S)+11)+5*(S+S+1)+
        (S+S)*((18+4*S)*2^(scopeBound (bitLength N)))+10*(2*S+S+S+1)^3 := by
          unfold SemiprimePaidFiniteEnumerations.incidenceBudget
          gcongr
      _ = _ := by unfold scalarPolynomial tablePolynomial;ring
  have hpow : 1 ≤ (2:ℕ)^(scopeBound (bitLength N)):=Nat.one_le_pow _ _ (by decide)
  have hscalar:=Nat.mul_le_mul_left (scalarPolynomial S) hpow
  unfold polynomial
  nlinarith

/-- Monotonicity is proved from this concrete fixed arithmetic expression. -/
theorem polynomial_mono {S T : ℕ} (h : S ≤ T) : polynomial S ≤ polynomial T := by
  unfold polynomial scalarPolynomial tablePolynomial SemiprimePaidFiniteEnumerations.incidenceBudget
  gcongr

/-- Fixed scalar envelope from original input length and actual prefix length. -/
def scalarSize (ell P : ℕ) : ℕ :=
  SemiprimeD1PublicPackingReady.scale ell+
    SemiprimePublicBudgetDimensions.scopeEnvelope (SemiprimeD1PublicPackingReady.scale ell)+ell+P+1

/-- Original fields all fit the acquired scalar envelope. -/
theorem original_fields (N : ℕ) (hN : 0<N) (fixed : List (Fin (wireCount N)×Bool)) :
    bitLength N ≤ scalarSize (bitLength N) fixed.length ∧
    wireCount N ≤ scalarSize (bitLength N) fixed.length ∧
    factorCount N ≤ scalarSize (bitLength N) fixed.length ∧
    scopeBound (bitLength N) ≤ scalarSize (bitLength N) fixed.length ∧
    fixed.length ≤ scalarSize (bitLength N) fixed.length := by
  have hm:=root_edges_le_scale N hN fixed
  rw [root_edges] at hm
  have hn : wireCount N ≤ SemiprimeD1PublicPackingReady.scale (bitLength N):=by omega
  have hF:=(SemiprimePublicBudgetDimensions.factorCount_le N hN).trans hn
  have hD:=SemiprimePublicBudgetDimensions.scope_le N hN
  have hs : SemiprimePublicBudgetDimensions.scopeEnvelope (wireCount N) ≤
      SemiprimePublicBudgetDimensions.scopeEnvelope (SemiprimeD1PublicPackingReady.scale (bitLength N)) := by
    unfold SemiprimePublicBudgetDimensions.scopeEnvelope
    gcongr
  unfold scalarSize
  omega

/-- CLOSED actual source+copy root report for every positive N and original prefix. -/
theorem original_clock (N : ℕ) (hN : 0<N) (fixed : List (Fin (wireCount N)×Bool)) :
    (SemiprimeD1RootNetwork.acquirePositive N hN fixed).clock ≤
      polynomial (scalarSize (bitLength N) fixed.length)*2^(scopeBound (bitLength N)) := by
  have h:=original_fields N hN fixed
  exact (SemiprimeD1RootAcquisitionResources.acquirePositive_clock N hN fixed).trans
    (budget_le N fixed.length _ h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2)

/-- Original query prefixes have length at most the actual wire count. -/
def queryScalarSize (ell : ℕ) : ℕ :=
  2*SemiprimeD1PublicPackingReady.scale ell+
    SemiprimePublicBudgetDimensions.scopeEnvelope (SemiprimeD1PublicPackingReady.scale ell)+ell+1

/-- The entire non-exponential original query factor is one FIXED monomial. -/
theorem query_polynomial_monomial : ∃C k : ℕ,∀ell,polynomial (queryScalarSize ell) ≤ C*(ell+1)^k := by
  change Bound (fun ell=>polynomial (queryScalarSize ell))
  unfold polynomial scalarPolynomial tablePolynomial queryScalarSize
    SemiprimeD1PublicPackingReady.scale SemiprimePublicBudgetDimensions.scopeEnvelope
    SemiprimePaidFiniteEnumerations.incidenceBudget
  boundArithmetic

/-- Uniform constants precede the whole original-input query family. The only
exponential is the actually materialized original macro scope. -/
theorem exists_query_clock : ∃C k : ℕ,∀ (N : ℕ) (hN : 0<N)
    (fixed : List (Fin (wireCount N)×Bool)), fixed.length ≤ wireCount N →
    (SemiprimeD1RootNetwork.acquirePositive N hN fixed).clock ≤
      C*(bitLength N+1)^k*2^(scopeBound (bitLength N)) := by
  obtain ⟨C,k,hpoly⟩:=query_polynomial_monomial
  refine ⟨C,k,?_⟩
  intro N hN fixed hf
  have hm:=root_edges_le_scale N hN fixed
  rw [root_edges] at hm
  have hs : scalarSize (bitLength N) fixed.length ≤ queryScalarSize (bitLength N) := by
    unfold scalarSize queryScalarSize
    omega
  exact (original_clock N hN fixed).trans (Nat.mul_le_mul_right _
    ((polynomial_mono hs).trans (hpoly (bitLength N))))

end RiemannGaussian.SemiprimeD1RootAcquisitionEnvelope
