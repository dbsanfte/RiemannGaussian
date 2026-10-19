/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import OAI.NumberTheory.DirichletL.CubicSieve.GaussNorm
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Tactic.Linter
import Lean.Util.CollectAxioms

/-!
# The actual signed native unit sum, before divisorwise estimates

The displayed sum is literally ThetaTwist.unitRamanujan applied to the native
primitive trace. It is not defined as an assumed divisor sum. Its CRT product
retains every zero/nonunit numerator. Actual ideal Mobius cancels each local
minus one away from the numerator. No annular mean or theta covariance bound
is inferred from this identity.
-/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
open scoped BigOperators Classical
namespace OpenAIReview.JoinedRamanujan
open OAI ActualEisensteinCubic CompletedGauss ConcreteTraceCRT CanonicalRowCompletion
  OAI.SevenEighths.CubicSieve
local notation "O" => ActualEisensteinCubic.O

/-- Exact CRT evaluation of a literal additive unit sum with primitive trace. -/
theorem primitive_unit_sum_product {ι T : Type*} [Fintype ι]
    (R : ι → Type*) [CommRing T] [∀ i, Field (R i)]
    [Fintype T] [∀ i, Fintype (R i)]
    (e : T ≃+* ∀ i, R i) (ψ : AddChar T ℂ) (hp : ψ.IsPrimitive) (a : T) :
    (∑ d : Tˣ, ψ (a*d)) =
      ∏ i, if e a i=0 then (Fintype.card (R i)ˣ : ℂ) else -1 := by
  let u := (Units.mapEquiv e.toMulEquiv).trans (MulEquiv.piUnits (M:=R))
  calc
    _ = ∑ d : Tˣ, ∏ i, IdealGaussCRT.coordinateAddChar R e ψ i
        (e a i*(u d i : R i)) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [IdealGaussCRT.addChar_finite_crt_factor R e ψ (a*d)]
      apply Finset.prod_congr rfl
      intro i hi
      rw [map_mul]
      rfl
    _ = ∑ d : ∀ i, (R i)ˣ, ∏ i, IdealGaussCRT.coordinateAddChar R e ψ i
        (e a i*(d i : R i)) :=
      Equiv.sum_comp u.toEquiv (fun d : ∀ i, (R i)ˣ =>
        ∏ i, IdealGaussCRT.coordinateAddChar R e ψ i (e a i*(d i : R i)))
    _ = _ := by
      rw [← Fintype.prod_sum (fun i (d : (R i)ˣ) =>
        IdealGaussCRT.coordinateAddChar R e ψ i (e a i*(d : R i)))]
      apply Finset.prod_congr rfl
      intro i hi
      have hn : IdealGaussCRT.coordinateAddChar R e ψ i≠1 := by
        simpa only [AddChar.mulShift_one] using
          (IdealGaussCRT.coordinateAddChar_isPrimitive R e ψ hp i) (a:=1) one_ne_zero
      exact ShortDraftLocal.additive_unit_sum _ hn _

/-- Literal native primitive-trace unit sum on an actual admissible squarefree
ideal, multiplied by its prescribed native Mobius coefficient. -/
theorem native_signed_unit_sum (I : Ideal O) (hI : Admissible I) (n : O) :
    let c := primaryGenerator I
    let hc := hI.2
    let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
    let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
    (UniqueFactorizationMonoid.moebius I : ℂ) *
      (∑ d : (O ⧸ Ideal.span {c})ˣ,
        CubicEisenstein.quotientTrace c hc
          (Ideal.Quotient.mk (Ideal.span {c}) n*(d : O ⧸ Ideal.span {c}))) =
      ∏ P : PrimeIndex I, if n∈P.val then 1-(Ideal.absNorm P.val : ℂ) else 1 := by
  dsimp only
  let : Finite (O ⧸ Ideal.span {primaryGenerator I}) := finite_quotient_span hI.2
  let : Fintype (O ⧸ Ideal.span {primaryGenerator I}) := Fintype.ofFinite _
  let (P : PrimeIndex I) : Fintype (O ⧸ P.val) := Fintype.ofFinite _
  let (P : PrimeIndex I) : Field (O ⧸ P.val) := Ideal.Quotient.field _
  let e : (O ⧸ Ideal.span {primaryGenerator I}) ≃+* ∀ P : PrimeIndex I, O ⧸ P.val :=
    (Ideal.quotEquivOfEq ((primaryGenerator_spec I hI.2).1.trans (primeIndex_product I hI).symm)).trans
      (IdealGaussCRT.quotientProdEquivPi (fun P : PrimeIndex I=>P.val) (primeIndex_pairwise_coprime I))
  have htrace : (CubicEisenstein.quotientTrace (primaryGenerator I) hI.2).IsPrimitive :=
    GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive _ _
  have he := primitive_unit_sum_product (fun P : PrimeIndex I=>O ⧸ P.val) e
    (CubicEisenstein.quotientTrace (primaryGenerator I) hI.2) htrace (Ideal.Quotient.mk _ n)
  have hmu : (UniqueFactorizationMonoid.moebius I : ℂ)=
      (-1 : ℂ)^(Fintype.card (PrimeIndex I)) := by
    have hp (P : PrimeIndex I) : Prime P.val :=
      UniqueFactorizationMonoid.prime_of_normalized_factor P.val (Multiset.mem_toFinset.mp P.property)
    have hm := prime_product_moebius
      (fun P : PrimeIndex I=>P.val) hp Subtype.val_injective Finset.univ
    simpa only [Finset.card_univ,primeIndex_product I hI] using hm
  have hconst : (-1 : ℂ)^Fintype.card (PrimeIndex I)=∏ _P : PrimeIndex I, (-1 : ℂ) := by simp
  rw [he,hmu,hconst,← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro P hP
  have hcoord : e (Ideal.Quotient.mk _ n) P=Ideal.Quotient.mk P.val n := by
    simp only [e,RingEquiv.trans_apply,Ideal.quotEquivOfEq_mk,IdealGaussCRT.quotientProdEquivPi_mk]
  have hcard : (Fintype.card (O ⧸ P.val)ˣ : ℂ)=(Ideal.absNorm P.val : ℂ)-1 := by
    rw [← Nat.card_eq_fintype_card,Nat.card_units,
      Nat.cast_sub (Nat.card_pos : 0<Nat.card (O ⧸ P.val)),Nat.cast_one]
    rfl
  rw [hcoord]
  by_cases hn : n∈P.val
  · rw [ite_eq_left (Ideal.Quotient.eq_zero_iff_mem.mpr hn),ite_eq_left hn,hcard]
    ring
  · rw [ite_eq_right (fun h=>hn (Ideal.Quotient.eq_zero_iff_mem.mp h)),ite_eq_right hn]
    norm_num

/-- Away from the numerator's prime support, the whole prescribed Mobius
times native Ramanujan coefficient is exactly one. All outside phases stay. -/
theorem native_signed_unit_sum_coprime (I : Ideal O) (hI : Admissible I) (n : O)
    (hcop : IsCoprime I (Ideal.span {n})) :
    let c := primaryGenerator I
    let hc := hI.2
    let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
    let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
    (UniqueFactorizationMonoid.moebius I : ℂ) *
      (∑ d : (O ⧸ Ideal.span {c})ˣ,
        CubicEisenstein.quotientTrace c hc
          (Ideal.Quotient.mk (Ideal.span {c}) n*(d : O ⧸ Ideal.span {c}))) = 1 := by
  dsimp only
  rw [native_signed_unit_sum I hI n]
  apply Finset.prod_eq_one
  intro P hP
  have hPI : P.val∣I := Ideal.dvd_iff_le.mpr (primeIndex_le I (primaryGenerator_ne_zero_ideal I hI.2) P)
  have hn : n∉P.val := (SixthPowerAverage.prime_coprime_span_iff P.val n).mp
    (hcop.of_isCoprime_of_dvd_left hPI)
  rw [ite_eq_right hn]

/-- A larger-norm prime ideal cannot divide any nonzero ideal in the cutoff. -/
theorem prime_norm_gt_coprime (I P : Ideal O) (hI : I≠0) [P.IsMaximal]
    (hN : Ideal.absNorm I<Ideal.absNorm P) : IsCoprime I P := by
  rw [isCoprime_comm,Ideal.isCoprime_iff_codisjoint,codisjoint_iff]
  by_contra hh
  have he : P=P⊔I := (inferInstance : P.IsMaximal).eq_of_le hh le_sup_left
  have hle : I≤P := le_sup_right.trans_eq he.symm
  have hd := Ideal.absNorm_dvd_absNorm_of_le hle
  have hpos : 0<Ideal.absNorm I := Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  exact (not_le_of_gt hN) (Nat.le_of_dvd hpos hd)

/-- For a prime numerator larger than the I cutoff, the actual joined finite
coefficient is one. This is not a lower bound for the remaining theta pairing. -/
theorem native_signed_unit_sum_large_prime (I : Ideal O) (hI : Admissible I) (n : O)
    [(Ideal.span {n} : Ideal O).IsMaximal]
    (hN : Ideal.absNorm I<Ideal.absNorm (Ideal.span {n})) :
    let c := primaryGenerator I
    let hc := hI.2
    let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
    let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
    (UniqueFactorizationMonoid.moebius I : ℂ) *
      (∑ d : (O ⧸ Ideal.span {c})ˣ,
        CubicEisenstein.quotientTrace c hc
          (Ideal.Quotient.mk (Ideal.span {c}) n*(d : O ⧸ Ideal.span {c}))) = 1 := by
  exact native_signed_unit_sum_coprime I hI n
    (prime_norm_gt_coprime I (Ideal.span {n}) (primaryGenerator_ne_zero_ideal I hI.2) hN)

end OpenAIReview.JoinedRamanujan

#lint+ in OpenAIReview.JoinedRamanujan

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
  unless declarations>0 do throwError "Empty native joined Ramanujan audit."
  logInfo m!"Joined Ramanujan audit: {declarations} declarations, {theorems} theorems; only standard axioms."
  IO.FS.createDirAll ".lake/arithmetic-operator-native-ramanujan-gate"
  IO.FS.writeFile ".lake/arithmetic-operator-native-ramanujan-gate/axioms.json"
    (Json.mkObj [("scope",toJson "actual native primitive-trace unit sum, signed squarefree prime product, exact coprime/large-prime coefficient one; no divisor surrogate or annular/theta/source estimate"),
      ("onlyStandardAxioms",toJson true),("namespaceLinters",toJson (15:Nat)),
      ("allLocalDeclarationsByModuleProvenance",toJson true),("declarations",toJson declarations),
      ("theoremsIncludingGeneratedHelpers",toJson theorems),("declarationAxioms",Json.arr reports)]).pretty
