/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1RootTapeAcquisitionBounds
import RiemannGaussian.SemiprimeD1RootAcquisitionEnvelope

/-! # Original-input bound for the executed tape root
Full table serialization and scanning add a second literal scope exponential.
Scalar preprocessing is kept polynomial in original input length. No changed
memory-access clock is obtained from value equality with the old root program.
-/
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1RootTapeAcquisitionEnvelope
open SemiprimePublicAcquiredExecution SemiprimeMacroParameters
open SemiprimeD1RootStateResources SemiprimeD1RootTapeAcquisitionBounds
open SemiprimeD1RootAcquisitionEnvelope (scalarSize queryScalarSize original_fields)
open SemiprimeReportPolynomialGrowth

/-- Fixed scalar polynomial before retaining both actual scope factors. -/
def polynomial (S : ℕ) : ℕ :=
  SemiprimeD1RootAcquisitionEnvelope.polynomial S+2*S*(72*(S+2)+11)

/-- Every source report and tape recopy remains in the numeric envelope. -/
theorem budget_le (N P S : ℕ) (hell:bitLength N ≤ S) (hn:wireCount N ≤ S)
    (hF:factorCount N ≤ S) (hD:scopeBound (bitLength N) ≤ S) (hP:P ≤ S) :
    budget N P ≤ polynomial S*2^(2*scopeBound (bitLength N)) := by
  let D:=scopeBound (bitLength N)
  let R:=2^D
  have hR:1 ≤ R:=Nat.one_le_two_pow
  have hOld:=SemiprimeD1RootAcquisitionEnvelope.budget_le N P S hell hn hF hD hP
  have hsource:SemiprimeD1RootTensorTablesBounds.budget N P+
      10*(2*wireCount N+factorCount N+wireCount N+1)^3 ≤
        SemiprimeD1RootAcquisitionEnvelope.polynomial S*R:=by
    apply le_trans _ hOld
    unfold SemiprimeD1RootAcquisitionResources.budget
    omega
  have hcopy:copyBudget D ≤ (72*(S+2)+11)*R^2:=by
    unfold copyBudget
    change (72*(D+2)*R+11)*R ≤ (72*(S+2)+11)*R^2
    have hDR:D ≤ S:=hD
    have hmul:11*R ≤ 11*R^2:=by nlinarith
    calc
      _  ≤  (72*(S+2)*R+11)*R := by gcongr
      _  ≤  _ := by nlinarith
  have hcounts:(wireCount N+factorCount N)*copyBudget D ≤
      (2*S)*((72*(S+2)+11)*R^2):=
    Nat.mul_le_mul (by omega) hcopy
  have hR2:R ≤ R^2:=by nlinarith
  have hbase:=Nat.mul_le_mul_left (SemiprimeD1RootAcquisitionEnvelope.polynomial S) hR2
  have he:2^(2*D)=R^2:=by dsimp only [R];rw [Nat.mul_comm 2 D,pow_mul]
  change budget N P ≤ polynomial S*2^(2*D)
  rw [he]
  unfold budget polynomial
  change SemiprimeD1RootTensorTablesBounds.budget N P+
    (wireCount N+factorCount N)*copyBudget D+
    10*(2*wireCount N+factorCount N+wireCount N+1)^3 ≤ _
  nlinarith

/-- Concrete scalar polynomial monotonicity. -/
theorem polynomial_mono {S T:ℕ} (h:S ≤ T) : polynomial S ≤ polynomial T := by
  unfold polynomial
  exact Nat.add_le_add (SemiprimeD1RootAcquisitionEnvelope.polynomial_mono h) (by gcongr)

/-- CLOSED original N/prefix root, including actual source production once. -/
theorem original_clock (N:ℕ) (hN:0<N) (fixed:List (Fin (wireCount N)×Bool)) :
    (SemiprimeD1RootTapeNetwork.acquirePositive N hN fixed).clock ≤
      polynomial (scalarSize (bitLength N) fixed.length)*2^(2*scopeBound (bitLength N)) := by
  have h:=original_fields N hN fixed
  exact (SemiprimeD1RootTapeAcquisitionBounds.acquirePositive_clock N hN fixed).trans
    (budget_le N fixed.length _ h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2)

/-- Fixed monomial coefficient and exponent precede all original inputs. -/
theorem query_polynomial_monomial : ∃C k:ℕ,∀ell,
    polynomial (queryScalarSize ell) ≤ C*(ell+1)^k := by
  change Bound (fun ell=>polynomial (queryScalarSize ell))
  unfold polynomial SemiprimeD1RootAcquisitionEnvelope.polynomial
    SemiprimeD1RootAcquisitionEnvelope.scalarPolynomial
    SemiprimeD1RootAcquisitionEnvelope.tablePolynomial queryScalarSize
    SemiprimeD1PublicPackingReady.scale SemiprimePublicBudgetDimensions.scopeEnvelope
    SemiprimePaidFiniteEnumerations.incidenceBudget
  boundArithmetic

/-- Whole-family actual tape-root acquisition cost. Both materialized scope
factors remain; neither is replaced by the original wire count or scalar cap. -/
theorem exists_query_clock : ∃C k:ℕ,∀(N:ℕ)(hN:0<N)
    (fixed:List (Fin (wireCount N)×Bool)),fixed.length ≤ wireCount N→
    (SemiprimeD1RootTapeNetwork.acquirePositive N hN fixed).clock ≤
      C*(bitLength N+1)^k*2^(2*scopeBound (bitLength N)) := by
  obtain ⟨C,k,hpoly⟩:=query_polynomial_monomial
  refine ⟨C,k,?_⟩
  intro N hN fixed hf
  have hm:=root_edges_le_scale N hN fixed
  rw [root_edges] at hm
  have hs:scalarSize (bitLength N) fixed.length ≤ queryScalarSize (bitLength N):=by
    unfold scalarSize queryScalarSize
    omega
  exact (original_clock N hN fixed).trans (Nat.mul_le_mul_right _
    ((polynomial_mono hs).trans (hpoly (bitLength N))))

end RiemannGaussian.SemiprimeD1RootTapeAcquisitionEnvelope
