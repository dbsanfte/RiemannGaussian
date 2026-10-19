/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import QuasiRHFiniteSquareGaussAudit
import OAI.NumberTheory.DirichletL.Detector.HighRowsSharpScalar
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicative
import Mathlib.Tactic.Linter
import Lean.Util.CollectAxioms

/-! Actual all-nonunit square-argument Gauss transport across distinct primes.
No theta/residue or physical energy/source claim is asserted. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 0
noncomputable section
open scoped Classical BigOperators
namespace OpenAIReview.AllSquareGaussBridge
open OAI OAI.ActualEisensteinCubic OAI.CompletedGauss
open OAI.SevenEighths OAI.SevenEighths.ProbePhysical OAI.SevenEighths.ProbePrimePower
open OAI.CanonicalQuadraticSieve OAI.ConcretePrimeRowBridge OAI.CanonicalRowCompletion
open OAI.SevenEighths.CenteredMomentUnequal OAI.SevenEighths.CenteredMomentSupportedCorrelation
open OpenAIReview.FiniteSquareGauss
local notation "O" => OAI.ActualEisensteinCubic.O

/-- Field Gauss transport is valid also when the varying square is a nonunit. -/
theorem primeGauss_square_ratio (p : O) (hp : p ≠ 0)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (hχ : χ ≠ 1) (w u : O) :
    primeGauss p hp χ (w*u^2) =
      ((χ (Ideal.Quotient.mk _ u))^2)⁻¹ * primeGauss p hp χ w := by
  let : Field (O ⧸ Ideal.span {p}) := Ideal.Quotient.field _
  let : Finite (O ⧸ Ideal.span {p}) := ConcreteTraceCRT.finite_quotient_span hp
  let : Fintype (O ⧸ Ideal.span {p}) := Fintype.ofFinite _
  let ψ := CubicEisenstein.quotientTrace p hp
  have he := ShortDraftLocal.gaussSum_mulShift_any χ
    (ψ.mulShift (Ideal.Quotient.mk _ w)) hχ (Ideal.Quotient.mk _ u ^ 2)
  simp only [MulChar.inv_apply_eq_inv', map_pow] at he
  simpa only [primeGauss, tsum_fintype, gaussSum, AddChar.mulShift_apply,
    map_mul, map_pow, inv_pow, mul_assoc, mul_comm, mul_left_comm, ψ] using he

/-- Nonprincipal physical prime powers retain the exact square character at
ALL varying u; no unit condition on u or baseline w is imposed. -/
theorem nonprincipal_square_ratio (p : O) (hp : Prime p)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : goodLambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (n : ℕ) (hn : ¬6∣n+1) (w u : O) :
    sexticGauss (p^(n+1)) (pow_ne_zero _ hp.ne_zero) (p^n*w*u^2) =
      ((actualSextic (Ideal.span {p}) hg^(n+1)) (Ideal.Quotient.mk _ u)^2)⁻¹ *
        sexticGauss (p^(n+1)) (pow_ne_zero _ hp.ne_zero) (p^n*w) := by
  have hχ : actualSextic (Ideal.span {p}) hg^(n+1) ≠ 1 :=
    fun h => hn ((actualSextic_pow_eq_one_iff _ hg hc _).mp h)
  rw [sexticGauss_prime_power p hp hg, sexticGauss_prime_power p hp hg,
    show p^n*w*u^2=p^n*(w*u^2) by ring,
    primePowerGauss_lift, primePowerGauss_lift, primeGauss_square_ratio p hp.ne_zero _ hχ]
  ring

/-- Principal physical sixth powers are constant on the ENTIRE high-valuation
numerator family, including u=0 and p dividing u. There is no H-unit mask. -/
theorem principal_high_square_constant (p : O) (hp : Prime p)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : goodLambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (n : ℕ) (hn : 6∣n+1) (w u : O) :
    sexticGauss (p^(n+1)) (pow_ne_zero _ hp.ne_zero) (p^(n+1)*w*u^2) =
      (Ideal.absNorm (Ideal.span {p}) : ℂ)^n *
        ((Ideal.absNorm (Ideal.span {p}) : ℂ)-1) := by
  rw [sexticGauss_prime_power p hp hg, (actualSextic_pow_eq_one_iff _ hg hc _).mpr hn]
  have he : p^(n+1)*w*u^2 = p^n*(p*(w*u^2)) := by rw [pow_succ]; ring
  rw [he, primePowerGauss_principal]
  · rw [ite_eq_left (dvd_mul_right p _)]
    have hcard : (Nat.card (O ⧸ Ideal.span {p})ˣ : ℂ)=
        (Ideal.absNorm (Ideal.span {p}) : ℂ)-1 := by
      rw [Nat.card_units, Nat.cast_sub (Nat.card_pos : 0 < Nat.card (O ⧸ Ideal.span {p})), Nat.cast_one]
      rfl
    rw [hcard]
  · have ht := GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive p hp.ne_zero
    simpa [CubicEisenstein.quotientTrace] using ht (a:=1) one_ne_zero

/-- Inverse square-character values equal their conjugates also at zero. -/
theorem inverse_square_character (p : O) (hp : p≠0)
    (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (u : O) :
    ((χ (Ideal.Quotient.mk _ u))^2)⁻¹=star ((χ (Ideal.Quotient.mk _ u))^2) := by
  let : Finite (O ⧸ Ideal.span {p}) := ConcreteTraceCRT.finite_quotient_span hp
  have he := MulChar.star_apply' (χ^2) (Ideal.Quotient.mk (Ideal.span {p}) u)
  simpa only [MulChar.pow_apply' _ (by decide : (2:ℕ)≠0), MulChar.inv_apply_eq_inv'] using he.symm

/-- The actual sextic character has period six as a CHARACTER, including zero. -/
theorem sextic_character_period (p : O) [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : goodLambda∉Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p})≠2) (h r : ℕ) :
    actualSextic (Ideal.span {p}) hg^(6*h+r)=actualSextic (Ideal.span {p}) hg^r := by
  rw [pow_add, pow_mul, (actualSextic_pow_eq_one_iff _ hg hc 6).mpr dvd_rfl,
    one_pow, one_mul]

/-- At physical class one, the ratio is the conjugate NATIVE cubic row. -/
theorem square_character_one (p : O) (hp : p≠0)
    [(Ideal.span {p} : Ideal O).IsMaximal] (hg : goodLambda∉Ideal.span {p}) (u : O) :
    ((actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ u))^2)⁻¹=
      star (CubicSieve.cubicRow (Ideal.span {p}) u) := by
  rw [inverse_square_character p hp,
    ←idealRowHom_prime u (Ideal.span {p}) hg, idealRowHom_square]
  rfl

/-- At physical class three, the ratio is the actual unit mask. -/
theorem square_character_three (p : O) (hp : p≠0)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hs : Supported (Ideal.span {p})) (hg : goodLambda∉Ideal.span {p}) (u : O) :
    (((actualSextic (Ideal.span {p}) hg^3) (Ideal.Quotient.mk _ u))^2)⁻¹=
      coprimalityMask u p := by
  rw [inverse_square_character p hp, MulChar.pow_apply' _ (by decide : (3:ℕ)≠0), ←pow_mul]
  norm_num only [show (3:ℕ)*2=6 by decide]
  rw [←idealRowHom_prime u (Ideal.span {p}) hg,
    ←idealRowHom_argument_pow u 6 _ hs, idealRowHom_sixth_eq_mask u p hs]
  change star (if IsCoprime u p then (1:ℂ) else 0) = if IsCoprime u p then 1 else 0
  split_ifs <;> simp only [star_one, star_zero]

/-- At physical class five, the ratio is the NATIVE cubic row, not its conjugate. -/
theorem square_character_five (p : O) (hp : p≠0)
    [(Ideal.span {p} : Ideal O).IsMaximal] (hg : goodLambda∉Ideal.span {p})
    (hc : ringChar (O ⧸ Ideal.span {p})≠2) (u : O) :
    (((actualSextic (Ideal.span {p}) hg^5) (Ideal.Quotient.mk _ u))^2)⁻¹=
      CubicSieve.cubicRow (Ideal.span {p}) u := by
  have h10 : actualSextic (Ideal.span {p}) hg^10=actualSextic (Ideal.span {p}) hg^4 := by
    simpa using sextic_character_period p hg hc 1 4
  have hx := congrArg (fun χ : MulChar (O ⧸ Ideal.span {p}) ℂ =>
    χ (Ideal.Quotient.mk _ u)) h10
  simp only [MulChar.pow_apply' _ (by decide : (10:ℕ)≠0),
    MulChar.pow_apply' _ (by decide : (4:ℕ)≠0)] at hx
  rw [inverse_square_character p hp, MulChar.pow_apply' _ (by decide : (5:ℕ)≠0), ←pow_mul]
  norm_num only [show (5:ℕ)*2=10 by decide]
  rw [hx, ←idealRowHom_prime u (Ideal.span {p}) hg,
    show idealRowHom u (Ideal.span {p})^4=(idealRowHom u (Ideal.span {p})^2)^2 by ring,
    idealRowHom_square]
  change star (CubicSieve.cubicRow (Ideal.span {p}) u^2)=_
  rw [CubicSieve.cubicRow_square_eq_star, star_star]

/-- Actual all-nonunit transport for physical exponent 6h+1. -/
theorem class_one_transport (p : O) (hp : Prime p)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : goodLambda∉Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p})≠2)
    (h : ℕ) (w u : O) :
    sexticGauss (p^(6*h+1)) (pow_ne_zero _ hp.ne_zero) (p^(6*h)*w*u^2)=
      sexticGauss (p^(6*h+1)) (pow_ne_zero _ hp.ne_zero) (p^(6*h)*w)*
        star (CubicSieve.cubicRow (Ideal.span {p}) u) := by
  rw [nonprincipal_square_ratio p hp hg hc (6*h) (by omega),
    sextic_character_period p hg hc h 1, pow_one, square_character_one p hp.ne_zero hg]
  ring

/-- Actual all-nonunit transport for physical exponent 6h+3. -/
theorem class_three_transport (p : O) (hp : Prime p)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hs : Supported (Ideal.span {p})) (hg : goodLambda∉Ideal.span {p})
    (hc : ringChar (O ⧸ Ideal.span {p})≠2) (h : ℕ) (w u : O) :
    sexticGauss (p^(6*h+3)) (pow_ne_zero _ hp.ne_zero) (p^(6*h+2)*w*u^2)=
      sexticGauss (p^(6*h+3)) (pow_ne_zero _ hp.ne_zero) (p^(6*h+2)*w)*
        coprimalityMask u p := by
  have he := nonprincipal_square_ratio p hp hg hc (6*h+2) (by omega) w u
  rw [show 6*h+2+1=6*h+3 by omega, sextic_character_period p hg hc h 3,
    square_character_three p hp.ne_zero hs hg] at he
  exact he.trans (mul_comm _ _)

/-- Actual all-nonunit transport for physical exponent 6h+5. -/
theorem class_five_transport (p : O) (hp : Prime p)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : goodLambda∉Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p})≠2)
    (h : ℕ) (w u : O) :
    sexticGauss (p^(6*h+5)) (pow_ne_zero _ hp.ne_zero) (p^(6*h+4)*w*u^2)=
      sexticGauss (p^(6*h+5)) (pow_ne_zero _ hp.ne_zero) (p^(6*h+4)*w)*
        CubicSieve.cubicRow (Ideal.span {p}) u := by
  have he := nonprincipal_square_ratio p hp hg hc (6*h+4) (by omega) w u
  rw [show 6*h+4+1=6*h+5 by omega, sextic_character_period p hg hc h 5,
    square_character_five p hp.ne_zero hg hc] at he
  exact he.trans (mul_comm _ _)

/-- The principal class has no restriction on the varying square argument. -/
theorem class_zero_transport (p : O) (hp : Prime p)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : goodLambda∉Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p})≠2)
    (h : ℕ) (w u : O) :
    sexticGauss (p^(6*h)) (pow_ne_zero _ hp.ne_zero) (p^(6*h)*w*u^2)=
      sexticGauss (p^(6*h)) (pow_ne_zero _ hp.ne_zero) (p^(6*h)*w) := by
  cases h with
  | zero => simp only [Nat.mul_zero, pow_zero, sexticGauss_one]
  | succ h =>
    have hk : 6*(h+1)=(6*h+5)+1 := by omega
    rw [hk, principal_high_square_constant p hp hg hc (6*h+5) (by omega),
      show p^(6*h+5+1)*w=(p^(6*h+5+1)*w)*1^2 by ring,
      principal_high_square_constant p hp hg hc (6*h+5) (by omega)]

/-- A finite product of actual supported moduli remains supported. -/
theorem supported_finset_product {ι : Type*} (S : Finset ι) (c : ι→O)
    (hc : ∀i, Supported (Ideal.span {c i})) :
    Supported (Ideal.span {∏i∈S,c i}) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, Ideal.span_singleton_one]
    rw [←Ideal.one_eq_top]
    refine ⟨one_ne_zero, ?_⟩
    intro P hP
    simp only [UniqueFactorizationMonoid.normalizedFactors_one, Multiset.notMem_zero] at hP
  | @insert i S hi ih =>
    rw [Finset.prod_insert hi]
    exact supported_mul_elements (c i) _ (hc i) ih

/-- CRT assembles exact local square transport across DISTINCT coprime moduli.
This helper is instantiated below with the proved actual prime-power laws. -/
theorem gauss_product_transport {ι : Type*} (S : Finset ι) (c t : ι→O)
    (hc : ∀i, Supported (Ideal.span {c i}))
    (hcop : Pairwise (fun i j => IsCoprime (c i) (c j))) (r : ι→O→ℂ)
    (hloc : ∀i w u,
      sexticGauss (c i) (supportedElement_ne_zero _ (hc i)) ((t i)^2*w*u^2)=
        sexticGauss (c i) (supportedElement_ne_zero _ (hc i)) ((t i)^2*w)*r i u) :
    ∀w u, sexticGauss (∏i∈S,c i)
        (supportedElement_ne_zero _ (supported_finset_product S c hc)) ((∏i∈S,t i)^2*w*u^2)=
      sexticGauss (∏i∈S,c i)
        (supportedElement_ne_zero _ (supported_finset_product S c hc)) ((∏i∈S,t i)^2*w)*
          ∏i∈S,r i u := by
  classical
  induction S using Finset.induction_on with
  | empty => intro w u; simp only [Finset.prod_empty, sexticGauss_one, mul_one]
  | @insert i S hi ih =>
    intro w u
    have hs := supported_finset_product S c hc
    have hcs : IsCoprime (c i) (∏j∈S,c j) := IsCoprime.prod_right (fun j hj =>
      hcop (fun he => hi (he ▸ hj)))
    have hl : sexticGauss (c i) (supportedElement_ne_zero _ (hc i))
        (((t i)*(∏j∈S,t j))^2*w*u^2)=
      sexticGauss (c i) (supportedElement_ne_zero _ (hc i))
        (((t i)*(∏j∈S,t j))^2*w)*r i u := by
      rw [show ((t i)*(∏j∈S,t j))^2*w*u^2=(t i)^2*((∏j∈S,t j)^2*w)*u^2 by ring,
        show ((t i)*(∏j∈S,t j))^2*w=(t i)^2*((∏j∈S,t j)^2*w) by ring]
      exact hloc i _ _
    have hr : sexticGauss (∏j∈S,c j) (supportedElement_ne_zero _ hs)
        (((t i)*(∏j∈S,t j))^2*w*u^2)=
      sexticGauss (∏j∈S,c j) (supportedElement_ne_zero _ hs)
        (((t i)*(∏j∈S,t j))^2*w)*(∏j∈S,r j u) := by
      rw [show ((t i)*(∏j∈S,t j))^2*w*u^2=(∏j∈S,t j)^2*((t i)^2*w)*u^2 by ring,
        show ((t i)*(∏j∈S,t j))^2*w=(∏j∈S,t j)^2*((t i)^2*w) by ring]
      exact ih _ _
    simp only [Finset.prod_insert hi]
    rw [sexticGauss_coprime_product _ _ (hc i) hs hcs,
      sexticGauss_coprime_product _ _ (hc i) hs hcs, hl, hr]
    ring

/-- Actual remaining local factor in the four admissible physical classes. -/
def primeSquareFactor (p : O) (r : ℕ) (u : O) : ℂ :=
  if r=1 then star (CubicSieve.cubicRow (Ideal.span {p}) u)
  else if r=3 then coprimalityMask u p
  else if r=5 then CubicSieve.cubicRow (Ideal.span {p}) u else 1

/-- Every admissible local prime power obeys the exact all-nonunit law.
The h exponent is unrestricted and therefore includes H-overlap. -/
theorem admissible_prime_transport (p : O) (hp : Prime p)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hs : Supported (Ideal.span {p})) (hg : goodLambda∉Ideal.span {p})
    (hc : ringChar (O ⧸ Ideal.span {p})≠2) (h r : ℕ)
    (hr : r=0 ∨ r=1 ∨ r=3 ∨ r=5) (w u : O) :
    sexticGauss (p^(6*h+r)) (pow_ne_zero _ hp.ne_zero) ((p^(3*h+r/2))^2*w*u^2)=
      sexticGauss (p^(6*h+r)) (pow_ne_zero _ hp.ne_zero) ((p^(3*h+r/2))^2*w)*
        primeSquareFactor p r u := by
  have he : (p^(3*h+r/2))^2=p^(6*h+2*(r/2)) := by
    rw [←pow_mul]
    congr 1
    omega
  rw [he]
  rcases hr with rfl | rfl | rfl | rfl
  · simpa only [primeSquareFactor, Nat.reduceEqDiff, ite_false, Nat.zero_div,
      Nat.mul_zero, Nat.add_zero, mul_one] using class_zero_transport p hp hg hc h w u
  · simpa only [primeSquareFactor, ite_true, Nat.reduceDiv, Nat.mul_zero, Nat.add_zero]
      using class_one_transport p hp hg hc h w u
  · simpa only [primeSquareFactor, Nat.reduceEqDiff, ite_false, ite_true, Nat.reduceDiv,
      Nat.reduceMul] using class_three_transport p hp hs hg hc h w u
  · simpa only [primeSquareFactor, Nat.reduceEqDiff, ite_false, ite_true, Nat.reduceDiv,
      Nat.reduceMul] using class_five_transport p hp hg hc h w u

/-- GLOBAL actual Gauss transport across a common finite good-prime algebra.
Every phase is fixed by the proved native local law, not a supplied phase vector. -/
theorem all_square_prime_product_transport {ι : Type*} (S : Finset ι)
    (p : ι→O) (hp : ∀i, Prime (p i))
    (hs : ∀i, Supported (Ideal.span {p i}))
    (hcop : Pairwise (fun i j => IsCoprime (p i) (p j)))
    (h r : ι→ℕ) (hr : ∀i, r i=0 ∨ r i=1 ∨ r i=3 ∨ r i=5) (w u : O) :
    sexticGauss (∏i∈S,(p i)^(6*h i+r i))
        (supportedElement_ne_zero _ (supported_finset_product S _
          (fun i => supported_power (p i) (hs i) _)))
        ((∏i∈S,(p i)^(3*h i+r i/2))^2*w*u^2)=
      sexticGauss (∏i∈S,(p i)^(6*h i+r i))
        (supportedElement_ne_zero _ (supported_finset_product S _
          (fun i => supported_power (p i) (hs i) _)))
        ((∏i∈S,(p i)^(3*h i+r i/2))^2*w)*
          ∏i∈S,primeSquareFactor (p i) (r i) u := by
  apply gauss_product_transport S (fun i => (p i)^(6*h i+r i))
    (fun i => (p i)^(3*h i+r i/2))
    (fun i => supported_power (p i) (hs i) _) (fun i j hij => (hcop hij).pow_left.pow_right)
    (fun i => primeSquareFactor (p i) (r i))
  intro i w u
  let : (Ideal.span {p i} : Ideal O).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible (hp i).irreducible
  obtain ⟨hg,hc⟩ := supported_prime_data (p i) (hp i) (hs i)
  exact admissible_prime_transport (p i) (hp i) (hs i) hg hc (h i) (r i) (hr i) w u

/-- The native cubic row at the unit ideal is one. -/
theorem cubicRow_one (u : O) : CubicSieve.cubicRow (Ideal.span {(1:O)}) u=1 := by
  rw [CubicSieve.cubicRow, ←idealRowHom_square, Ideal.span_singleton_one, ←Ideal.one_eq_top, map_one]
  norm_num

/-- Native cubic rows multiply over the actual finite product of generators. -/
theorem cubicRow_finset_product {ι : Type*} (S : Finset ι) (a : ι→O) (u : O) :
    CubicSieve.cubicRow (Ideal.span {∏i∈S,a i}) u=
      ∏i∈S,CubicSieve.cubicRow (Ideal.span {a i}) u := by
  classical
  induction S using Finset.induction_on with
  | empty => simp only [Finset.prod_empty, cubicRow_one]
  | @insert i S hi ih =>
    rw [Finset.prod_insert hi, ←Ideal.span_singleton_mul_span_singleton,
      CubicSieve.cubicRow_mul, ih, Finset.prod_insert hi]

/-- The actual local factor splits into b-character, e-character and d-mask. -/
theorem primeSquareFactor_eq (p : O) (r : ℕ) (u : O) :
    primeSquareFactor p r u=
      star (CubicSieve.cubicRow (Ideal.span {if r=1 then p else 1}) u)*
        CubicSieve.cubicRow (Ideal.span {if r=5 then p else 1}) u*
        coprimalityMask u (if r=3 then p else 1) := by
  unfold primeSquareFactor
  by_cases h1 : r=1
  · subst r; simp only [ite_true, Nat.reduceEqDiff, ite_false, cubicRow_one, map_one, mul_one]
  · by_cases h3 : r=3
    · subst r; simp only [Nat.reduceEqDiff, ite_false, ite_true, cubicRow_one, star_one, one_mul]
    · by_cases h5 : r=5
      · subst r; simp only [Nat.reduceEqDiff, ite_false, ite_true, cubicRow_one, star_one, one_mul, map_one, mul_one]
      · simp only [h1, h3, h5, ite_false, cubicRow_one, star_one, map_one, mul_one]

/-- GLOBAL factor is the prescribed pair of native cubic rows and exact mask. -/
theorem primeSquareFactor_product {ι : Type*} (S : Finset ι) (p : ι→O) (r : ι→ℕ) (u : O) :
    (∏i∈S,primeSquareFactor (p i) (r i) u)=
      star (CubicSieve.cubicRow (Ideal.span {∏i∈S,if r i=1 then p i else 1}) u)*
        CubicSieve.cubicRow (Ideal.span {∏i∈S,if r i=5 then p i else 1}) u*
        coprimalityMask u (∏i∈S,if r i=3 then p i else 1) := by
  simp_rw [primeSquareFactor_eq]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib,
    cubicRow_finset_product, cubicRow_finset_product, map_prod, star_prod]

/-- Explicit native GLOBAL character/mask identity on the full prime product. -/
theorem all_square_cubic_transport {ι : Type*} (S : Finset ι)
    (p : ι→O) (hp : ∀i, Prime (p i))
    (hs : ∀i, Supported (Ideal.span {p i}))
    (hcop : Pairwise (fun i j => IsCoprime (p i) (p j)))
    (h r : ι→ℕ) (hr : ∀i, r i=0 ∨ r i=1 ∨ r i=3 ∨ r i=5) (w u : O) :
    sexticGauss (∏i∈S,(p i)^(6*h i+r i))
        (supportedElement_ne_zero _ (supported_finset_product S _
          (fun i => supported_power (p i) (hs i) _)))
        ((∏i∈S,(p i)^(3*h i+r i/2))^2*w*u^2)=
      sexticGauss (∏i∈S,(p i)^(6*h i+r i))
        (supportedElement_ne_zero _ (supported_finset_product S _
          (fun i => supported_power (p i) (hs i) _)))
        ((∏i∈S,(p i)^(3*h i+r i/2))^2*w)*
        (star (CubicSieve.cubicRow (Ideal.span {∏i∈S,if r i=1 then p i else 1}) u)*
          CubicSieve.cubicRow (Ideal.span {∏i∈S,if r i=5 then p i else 1}) u*
          coprimalityMask u (∏i∈S,if r i=3 then p i else 1)) := by
  rw [all_square_prime_product_transport S p hp hs hcop h r hr w u, primeSquareFactor_product]

/-- Literal physical product is H⁶*b*d³*e⁵; H may share primes with all slots. -/
theorem physical_product_normal_form {ι : Type*} (S : Finset ι) (p : ι→O) (h r : ι→ℕ)
    (hr : ∀i, r i=0 ∨ r i=1 ∨ r i=3 ∨ r i=5) :
    (∏i∈S,(p i)^(6*h i+r i))=
      (∏i∈S,(p i)^(h i))^6*(∏i∈S,if r i=1 then p i else 1)*
        (∏i∈S,if r i=3 then p i else 1)^3*(∏i∈S,if r i=5 then p i else 1)^5 := by
  classical
  calc
    _ = ∏i∈S, ((p i)^(h i))^6*(if r i=1 then p i else 1)*
        (if r i=3 then p i else 1)^3*(if r i=5 then p i else 1)^5 := by
      apply Finset.prod_congr rfl
      intro i _
      have hh : ((p i)^(h i))^6=(p i)^(6*h i) := by rw [←pow_mul]; congr 1; omega
      rw [hh]
      rcases hr i with hr | hr | hr | hr <;> rw [hr] <;>
        simp only [Nat.reduceEqDiff, ite_true, ite_false, Nat.add_zero, one_pow,
          mul_one, pow_add, pow_one]
    _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib,
        Finset.prod_mul_distrib, Finset.prod_pow, Finset.prod_pow, Finset.prod_pow]

/-- Literal root product is H³*d*e², retaining every H overlap. -/
theorem root_product_normal_form {ι : Type*} (S : Finset ι) (p : ι→O) (h r : ι→ℕ)
    (hr : ∀i, r i=0 ∨ r i=1 ∨ r i=3 ∨ r i=5) :
    (∏i∈S,(p i)^(3*h i+r i/2))=
      (∏i∈S,(p i)^(h i))^3*(∏i∈S,if r i=3 then p i else 1)*
        (∏i∈S,if r i=5 then p i else 1)^2 := by
  classical
  calc
    _ = ∏i∈S, ((p i)^(h i))^3*(if r i=3 then p i else 1)*
        (if r i=5 then p i else 1)^2 := by
      apply Finset.prod_congr rfl
      intro i _
      have hh : ((p i)^(h i))^3=(p i)^(3*h i) := by rw [←pow_mul]; congr 1; omega
      rw [hh]
      rcases hr i with hr | hr | hr | hr <;> rw [hr] <;>
        simp only [Nat.reduceEqDiff, ite_true, ite_false, Nat.reduceDiv, Nat.zero_div,
          Nat.add_zero, one_pow, mul_one, pow_add, pow_one]
    _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib,
        Finset.prod_pow, Finset.prod_pow]

/-- Nonzero actual full Gauss sum forces every coprime physical component
Gauss sum to be nonzero at the SAME numerator. -/
theorem gauss_product_component_nonzero {ι : Type*} (S : Finset ι) (c : ι→O)
    (hc : ∀i, Supported (Ideal.span {c i}))
    (hcop : Pairwise (fun i j => IsCoprime (c i) (c j)))
    (z : O) (i : ι) (hi : i∈S)
    (hG : sexticGauss (∏j∈S,c j)
      (supportedElement_ne_zero _ (supported_finset_product S c hc)) z≠0) :
    sexticGauss (c i) (supportedElement_ne_zero _ (hc i)) z≠0 := by
  classical
  have hs := supported_finset_product (S.erase i) c hc
  have hcp : IsCoprime (c i) (∏j∈S.erase i,c j) := IsCoprime.prod_right (fun j hj =>
    hcop (Finset.ne_of_mem_erase hj).symm)
  have hn : sexticGauss ((c i)*(∏j∈S.erase i,c j))
      (mul_ne_zero (supportedElement_ne_zero _ (hc i)) (supportedElement_ne_zero _ hs)) z≠0 := by
    simpa only [Finset.mul_prod_erase S c hi] using hG
  rw [sexticGauss_coprime_product _ _ (hc i) hs hcp] at hn
  intro hz
  exact hn (by rw [hz, mul_zero, zero_mul])

/-- ACTUAL nonzero Gauss support at any square numerator, expressed by the
literal prime multiplicity of the root. Principal sixth powers keep inequality. -/
theorem nonzero_square_prime_power_support (p : O) (hp : Prime p)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hs : Supported (Ideal.span {p})) (hg : goodLambda∉Ideal.span {p})
    (hc : ringChar (O ⧸ Ideal.span {p})≠2)
    (k : ℕ) (x ζ : O) (hx : x≠0) (hζ : IsUnit ζ)
    (hG : sexticGauss (p^k) (pow_ne_zero _ hp.ne_zero) (ζ*x^2)≠0) :
    if 6∣k then k≤2*multiplicity p x else k=2*multiplicity p x+1 := by
  cases k with
  | zero => simp only [dvd_zero, ite_true, zero_le]
  | succ n =>
    obtain ⟨v, hv, hpv⟩ := (FiniteMultiplicity.of_prime_left hp hx).exists_eq_pow_mul_and_not_dvd
    have hpζ : ¬p∣ζ := fun h => hp.not_isUnit (isUnit_of_dvd_unit h hζ)
    have hunit : ¬p∣ζ*v^2 := by
      intro h
      rcases hp.dvd_mul.mp h with h | h
      · exact hpζ h
      · exact hpv (hp.dvd_of_dvd_pow h)
    have harg : ζ*x^2=(ζ*v^2)*p^(2*multiplicity p x) := by
      conv_lhs => rw [hv, mul_pow, ←pow_mul]
      rw [show 2*multiplicity p x=multiplicity p x*2 by omega]
      ring
    rw [harg] at hG
    have hb := gauss_prime_power_unit_support p hp hs hg hc n (2*multiplicity p x)
      (ζ*v^2) hunit hG
    by_cases hd : 6∣n+1
    · rw [ite_eq_left hd] at hb ⊢
      omega
    · rw [ite_eq_right hd] at hb ⊢
      omega

/-- A nonzero actual physical prime power at a square has only classes0,1,3,5. -/
theorem nonzero_square_prime_power_classes (p : O) (hp : Prime p)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hs : Supported (Ideal.span {p})) (hg : goodLambda∉Ideal.span {p})
    (hc : ringChar (O ⧸ Ideal.span {p})≠2)
    (k : ℕ) (x ζ : O) (hx : x≠0) (hζ : IsUnit ζ)
    (hG : sexticGauss (p^k) (pow_ne_zero _ hp.ne_zero) (ζ*x^2)≠0) :
    k%6=0 ∨ k%6=1 ∨ k%6=3 ∨ k%6=5 := by
  have hb := nonzero_square_prime_power_support p hp hs hg hc k x ζ hx hζ hG
  by_cases hd : 6∣k
  · exact Or.inl (Nat.mod_eq_zero_of_dvd hd)
  · rw [ite_eq_right hd] at hb
    omega

/-- Actual global nonzero square support on an arbitrary common physical
prime family, ready for the canonical ideal partition. -/
theorem nonzero_square_prime_product_support {ι : Type*} (S : Finset ι)
    (p : ι→O) (hp : ∀i, Prime (p i))
    (hs : ∀i, Supported (Ideal.span {p i}))
    (hcop : Pairwise (fun i j => IsCoprime (p i) (p j))) (k : ι→ℕ)
    (x ζ : O) (hx : x≠0) (hζ : IsUnit ζ)
    (hG : sexticGauss (∏i∈S,(p i)^(k i))
      (supportedElement_ne_zero _ (supported_finset_product S _
        (fun i => supported_power (p i) (hs i) _))) (ζ*x^2)≠0) :
    ∀i∈S, if 6∣k i then k i≤2*multiplicity (p i) x else k i=2*multiplicity (p i) x+1 := by
  intro i hi
  have hgi := gauss_product_component_nonzero S (fun j => (p j)^(k j))
    (fun j => supported_power (p j) (hs j) _) (fun j l hjl => (hcop hjl).pow_left.pow_right)
    (ζ*x^2) i hi hG
  let : (Ideal.span {p i} : Ideal O).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (hp i).irreducible
  obtain ⟨hg,hc⟩ := supported_prime_data (p i) (hp i) (hs i)
  exact nonzero_square_prime_power_support (p i) (hp i) (hs i) hg hc (k i) x ζ hx hζ hgi

end OpenAIReview.AllSquareGaussBridge
#lint+ in OpenAIReview.AllSquareGaussBridge

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut declarations : Nat := 0
  let mut theorems : Nat := 0
  let mut details : Array Json := #[]
  for (n, ci) in env.constants.toList do
    if env.isImportedConst n then continue
    declarations := declarations + 1
    if ci.isAxiom then throwError "Project-defined axiom: {n}"
    let axs ← Lean.collectAxioms n
    for ax in axs do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom in {n}: {ax}"
    if ci.isTheorem then theorems := theorems + 1
    details := details.push (Json.mkObj [("declaration", toJson n.toString),
      ("isTheorem", toJson ci.isTheorem), ("axioms", toJson (axs.map Name.toString))])
  unless declarations > 0 do throwError "Empty all-square actual Gauss audit."
  logInfo m!"All-square actual Gauss audit: {declarations} declarations, {theorems} theorems; only standard axioms."
  IO.FS.createDirAll ".lake/arithmetic-operator-all-square-gauss-bridge"
  IO.FS.writeFile ".lake/arithmetic-operator-all-square-gauss-bridge/axioms.json"
    (Json.mkObj [("scope", toJson "actual GLOBAL all-nonunit sextic Gauss transport, native cubic factors, principal H branch, finite CRT product and square support; no norm/source estimate"),
      ("namespaceLinters", toJson (15 : Nat)), ("onlyStandardAxioms", toJson true),
      ("allLocalModuleProvenance", toJson true), ("declarations", toJson declarations),
      ("theoremsIncludingHelpers", toJson theorems), ("details", Json.arr details)]).pretty
