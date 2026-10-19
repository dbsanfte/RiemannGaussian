/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import OAI.NumberTheory.DirichletL.Detector.HighRowsSharpScalar
import OAI.NumberTheory.DirichletL.Moments.AmplificationLocal
import OAI.NumberTheory.DirichletL.Detector.PhysicalCRT
import OAI.NumberTheory.DirichletL.Detector.LocalUnitFrequency
import OAI.NumberTheory.DirichletL.Detector.PhysicalNorms
import OAI.NumberTheory.DirichletL.Detector.RadialIdentity
import OAI.NumberTheory.DirichletL.Moments.GaussEnergy
import Mathlib.Tactic.Linter
import Lean.Util.CollectAxioms

/-! Actual square-numerator Gauss norm estimates, including principal
sixth-power physical moduli. No freely supplied Gauss phase is used. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 0
noncomputable section
open scoped Classical BigOperators
namespace OpenAIReview.SquareGaussNorm
open OAI OAI.ActualEisensteinCubic OAI.CompletedGauss
open OAI.SevenEighths OAI.SevenEighths.ProbePhysical
open OAI.SevenEighths.ProbePrimePower OAI.CanonicalQuadraticSieve
open OAI.SevenEighths.CenteredMomentUnequal
open OAI.SevenEighths.CenteredMomentAmplification
open OAI.SevenEighths.CenteredMomentAmplificationLocal
open OAI.SevenEighths.CenteredMomentSupportedCorrelation
open OAI.ConcretePrimeRowBridge OAI.CanonicalRowCompletion
local notation "O" => OAI.ActualEisensteinCubic.O

/-- All nonprincipal powers of the actual sextic character have the exact
prime Gauss norm, independently of their unreduced exponent. -/
theorem primeGauss_power_norm (p : O) (hp : Prime p)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : goodLambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (k : ℕ) (hk : ¬ 6 ∣ k) :
    ‖primeGauss p hp.ne_zero (actualSextic (Ideal.span {p}) hg ^ k) 1‖ =
      Real.sqrt (Ideal.absNorm (Ideal.span {p}) : ℝ) := by
  have he : actualSextic (Ideal.span {p}) hg ^ k =
      actualSextic (Ideal.span {p}) hg ^ (k % 6) := by
    rw [← CenteredMomentCanonical.actualSextic_order_six (Ideal.span {p}) hg hc,
      pow_mod_orderOf]
  rw [he]
  exact primeGauss_actual_pow_norm p hp hg hc (k%6)
    (fun he => hk (Nat.dvd_of_mod_eq_zero he)) (Nat.mod_lt _ (by norm_num))

/-- The principal Ramanujan boundary is impossible at an even numerator
valuation when the physical exponent is divisible by six. -/
theorem principal_square_boundary (n v : ℕ) (hn : 6 ∣ n+1) :
    n ≤ 2*v ↔ n+1 ≤ 2*v := by omega

/-- The literal local Gauss norm squared is bounded by q^(physical+root²).
The statement includes every physical exponent and every root valuation. -/
theorem local_square_norm_sq (p : O) (hp : Prime p)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : goodLambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (n v : ℕ) :
    ‖sexticGauss (p^(n+1)) (pow_ne_zero _ hp.ne_zero) (p^(2*v))‖^2 ≤
      (Ideal.absNorm (Ideal.span {p}) : ℝ)^(n+1+2*v) := by
  let q : ℝ := Ideal.absNorm (Ideal.span {p})
  have hq : 1 ≤ q := by
    dsimp [q]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero))
  have hq0 : 0 ≤ q := by linarith
  have hpows (k : ℕ) : ‖(Ideal.absNorm (Ideal.span {p}) : ℂ)^k‖ = q^k := by
    rw [norm_pow, Complex.norm_natCast]
  rw [sexticGauss_prime_power p hp hg,
    actualSextic_primePowerGauss_at_pow p hp hg hc]
  change _ ≤ q^(n+1+2*v)
  by_cases hd : 6 ∣ n+1
  · rw [ite_eq_left hd]
    by_cases hv : n+1 ≤ 2*v
    · rw [ite_eq_left hv, ite_eq_left (by omega : n ≤ 2*v)]
      have hdiff : ‖(Ideal.absNorm (Ideal.span {p}) : ℂ)^(n+1) -
          (Ideal.absNorm (Ideal.span {p}) : ℂ)^n‖ ≤ q^(n+1) := by
        change ‖(q:ℂ)^(n+1)-(q:ℂ)^n‖ ≤ _
        rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_sub,
          Complex.norm_real, Real.norm_eq_abs]
        rw [abs_of_nonneg (sub_nonneg.mpr (pow_le_pow_right₀ hq (by omega : n ≤ n+1)))]
        exact sub_le_self _ (pow_nonneg hq0 n)
      exact (pow_le_pow_left₀ (norm_nonneg _) hdiff 2).trans (by
        rw [← pow_mul]
        exact pow_le_pow_right₀ hq (by omega))
    · rw [ite_eq_right hv, ite_eq_right
        (fun h => hv ((principal_square_boundary n v hd).mp h))]
      simp only [sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0)]
      exact pow_nonneg hq0 _
  · rw [ite_eq_right hd]
    by_cases hn : 2*v=n
    · rw [ite_eq_left hn, norm_mul, hpows,
        primeGauss_power_norm p hp hg hc (n+1) hd, mul_pow,
        Real.sq_sqrt hq0, ← pow_mul, ← pow_succ]
      apply le_of_eq
      congr 1
      omega
    · rw [ite_eq_right hn, norm_zero]
      simpa only [zero_pow (by decide : 2 ≠ 0)] using pow_nonneg hq0 (n+1+2*v)

/-- A coprime numerator multiplier does not worsen the local square bound. -/
theorem local_square_unit_norm_sq (p : O) (hp : Prime p)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hs : Supported (Ideal.span {p})) (hg : goodLambda ∉ Ideal.span {p})
    (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (n v : ℕ) (w : O) (hw : ¬p ∣ w) :
    ‖sexticGauss (p^(n+1)) (pow_ne_zero _ hp.ne_zero) (w*p^(2*v))‖^2 ≤
      (Ideal.absNorm (Ideal.span {p}) : ℝ)^(n+1+2*v) := by
  rw [gauss_unit_scale_norm _ (supported_power p hs (n+1)) w _
    ((hp.irreducible.coprime_iff_not_dvd.mpr hw).symm.pow_right)]
  exact local_square_norm_sq p hp hg hc n v

/-- CRT does not enlarge the product of the actual local Gauss norms. -/
theorem gauss_coprime_norm_sq (a b : O) (ha : Supported (Ideal.span {a}))
    (hb : Supported (Ideal.span {b})) (hab : IsCoprime a b) (m : O) :
    ‖sexticGauss (a*b) (mul_ne_zero (supportedElement_ne_zero _ ha)
      (supportedElement_ne_zero _ hb)) m‖^2 ≤
      ‖sexticGauss a (supportedElement_ne_zero _ ha) m‖^2 *
        ‖sexticGauss b (supportedElement_ne_zero _ hb) m‖^2 := by
  rw [sexticGauss_coprime_product a b ha hb hab]
  simp only [norm_mul, mul_pow]
  have h1 := pow_le_pow_left₀ (norm_nonneg _) (idealRowHom_norm b (Ideal.span {a})) 2
  have h2 := pow_le_pow_left₀ (norm_nonneg _) (idealRowHom_norm a (Ideal.span {b})) 2
  norm_num only [one_pow] at h1 h2
  calc
    _ ≤ 1*1*‖sexticGauss a (supportedElement_ne_zero _ ha) m‖^2 *
        ‖sexticGauss b (supportedElement_ne_zero _ hb) m‖^2 := by gcongr
    _ = _ := by ring

/-- Actual supported moduli are closed under finite products. -/
theorem supported_product {ι : Type*} (S : Finset ι) (c : ι → O)
    (hc : ∀ i, Supported (Ideal.span {c i})) :
    Supported (Ideal.span {∏ i ∈ S, c i}) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, Ideal.span_singleton_one]
    rw [← Ideal.one_eq_top]
    refine ⟨one_ne_zero, ?_⟩
    intro P hP
    simp only [UniqueFactorizationMonoid.normalizedFactors_one, Multiset.notMem_zero] at hP
  | @insert i S hi ih =>
    rw [Finset.prod_insert hi]
    exact supported_mul_elements (c i) _ (hc i) ih

/-- The full actual norm is bounded by the product over distinct prime-power
moduli. Local factors are evaluated at the SAME original numerator. -/
theorem gauss_product_norm_sq {ι : Type*} (S : Finset ι) (c : ι → O)
    (hc : ∀ i, Supported (Ideal.span {c i}))
    (hcop : Pairwise (fun i j => IsCoprime (c i) (c j))) (m : O) :
    ‖sexticGauss (∏ i ∈ S, c i)
      (supportedElement_ne_zero _ (supported_product S c hc)) m‖^2 ≤
        ∏ i ∈ S, ‖sexticGauss (c i) (supportedElement_ne_zero _ (hc i)) m‖^2 := by
  classical
  induction S using Finset.induction_on with
  | empty => simp only [Finset.prod_empty, sexticGauss_one, norm_one, one_pow, le_refl]
  | @insert i S hi ih =>
    have hcs : IsCoprime (c i) (∏ j ∈ S, c j) :=
      IsCoprime.prod_right (fun j hj => hcop (fun he => hi (he ▸ hj)))
    simpa only [Finset.prod_insert hi] using
      (gauss_coprime_norm_sq (c i) _ (hc i) (supported_product S c hc) hcs m).trans
        (mul_le_mul_of_nonneg_left ih (sq_nonneg _))

/-- A prime is coprime to the product of all other prime-power factors. -/
theorem prime_not_dvd_other_product {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (p : ι → O) (hp : ∀ i, Prime (p i))
    (hcop : Pairwise (fun i j => IsCoprime (p i) (p j))) (v : ι → ℕ) (i : ι) :
    ¬ p i ∣ ∏ j ∈ S.erase i, (p j)^(v j) := by
  apply (hp i).irreducible.coprime_iff_not_dvd.mp
  exact IsCoprime.prod_right (fun j hj =>
    (hcop (Finset.mem_erase.mp hj).1.symm).pow_right)

/-- Exact element norm of the common actual prime-power product. -/
theorem elementNorm_prime_product {ι : Type*} (S : Finset ι)
    (p : ι → O) (k : ι → ℕ) :
    elementNorm (∏ i ∈ S, (p i)^(k i)) =
      ∏ i ∈ S, (Ideal.absNorm (Ideal.span {p i}) : ℝ)^(k i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp only [Finset.prod_empty, elementNorm_one]
  | @insert i S hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi, elementNorm_mul,
      elementNorm_pow, ih]
    rfl

/-- Actual full prime-power modulus square-numerator bound. Physical orders
are arbitrary, including forbidden classes (whose actual Gauss factors vanish).
There is no squarefree, canonical-residue or H-coprimality assumption. -/
theorem prime_product_square_raw_norm_sq {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (p : ι → O) (hp : ∀ i, Prime (p i))
    (hs : ∀ i, Supported (Ideal.span {p i}))
    (hcop : Pairwise (fun i j => IsCoprime (p i) (p j)))
    (k v : ι → ℕ) (w : O) (hw : ∀ i ∈ S, ¬ p i ∣ w) :
    ‖sexticGauss (∏ i ∈ S, (p i)^(k i))
      (supportedElement_ne_zero _ (supported_product S _
        (fun i => supported_power (p i) (hs i) (k i))))
      (w*(∏ i ∈ S, (p i)^(v i))^2)‖^2 ≤
      elementNorm (∏ i ∈ S, (p i)^(k i)) *
        elementNorm (∏ i ∈ S, (p i)^(v i))^2 := by
  have hprod := gauss_product_norm_sq S (fun i => (p i)^(k i))
    (fun i => supported_power (p i) (hs i) (k i))
    (fun i j hij => (hcop hij).pow_left.pow_right)
    (w*(∏ i ∈ S, (p i)^(v i))^2)
  have hlocal (i : ι) (hi : i ∈ S) :
      ‖sexticGauss ((p i)^(k i)) (pow_ne_zero _ (hp i).ne_zero)
        (w*(∏ j ∈ S, (p j)^(v j))^2)‖^2 ≤
        (Ideal.absNorm (Ideal.span {p i}) : ℝ)^(k i+2*v i) := by
    have hq : (1:ℝ) ≤ Ideal.absNorm (Ideal.span {p i}) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr
        (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr (hp i).ne_zero))
    rcases Nat.eq_zero_or_pos (k i) with hk | hk
    · simp only [hk, pow_zero, sexticGauss_one, norm_one, one_pow, zero_add]
      exact one_le_pow₀ hq
    · obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
      let : (Ideal.span {p i} : Ideal O).IsMaximal :=
        PrincipalIdealRing.isMaximal_of_irreducible (hp i).irreducible
      obtain ⟨hg,hc⟩ := supported_prime_data (p i) (hp i) (hs i)
      let other := ∏ j ∈ S.erase i, (p j)^(v j)
      have ho : ¬ p i ∣ other := prime_not_dvd_other_product S p hp hcop v i
      have hmul : ¬ p i ∣ w*other^2 := by
        intro h
        rcases (hp i).dvd_mul.mp h with h | h
        · exact hw i hi h
        · exact ho ((hp i).dvd_of_dvd_pow h)
      have hroot : (∏ j ∈ S, (p j)^(v j)) = (p i)^(v i)*other :=
        (Finset.mul_prod_erase S (fun j => (p j)^(v j)) hi).symm
      have hm : w*(∏ j ∈ S, (p j)^(v j))^2 =
          (w*other^2)*(p i)^(2*v i) := by rw [hroot]; ring
      rw [hn, hm]
      exact local_square_unit_norm_sq (p i) (hp i) (hs i) hg hc n (v i) _ hmul
  calc
    _ ≤ ∏ i ∈ S, ‖sexticGauss ((p i)^(k i)) (pow_ne_zero _ (hp i).ne_zero)
        (w*(∏ j ∈ S, (p j)^(v j))^2)‖^2 := hprod
    _ ≤ ∏ i ∈ S, (Ideal.absNorm (Ideal.span {p i}) : ℝ)^(k i+2*v i) :=
      Finset.prod_le_prod₀ (fun _ _ => sq_nonneg _) hlocal
    _ = _ := by
      have he (i : ι) : (Ideal.absNorm (Ideal.span {p i}) : ℝ)^(k i+2*v i) =
          (Ideal.absNorm (Ideal.span {p i}) : ℝ)^(k i) *
            ((Ideal.absNorm (Ideal.span {p i}) : ℝ)^(v i))^2 := by
        rw [pow_add, show 2*v i=v i*2 by omega, pow_mul]
      simp_rw [he]
      rw [Finset.prod_mul_distrib, Finset.prod_pow,
        elementNorm_prime_product, elementNorm_prime_product]

/-- The normalized actual Gauss value at a square baseline is bounded by
the root norm, uniformly in ALL physical prime-power orders. -/
theorem prime_product_square_norm {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (p : ι → O) (hp : ∀ i, Prime (p i))
    (hs : ∀ i, Supported (Ideal.span {p i}))
    (hcop : Pairwise (fun i j => IsCoprime (p i) (p j)))
    (k v : ι → ℕ) (w : O) (hw : ∀ i ∈ S, ¬ p i ∣ w) :
    ‖CenteredMomentGaussEnergy.gaussRow (∏ i ∈ S, (p i)^(k i))
      (supported_product S _ (fun i => supported_power (p i) (hs i) (k i)))
      (w*(∏ i ∈ S, (p i)^(v i))^2)‖ ≤
        elementNorm (∏ i ∈ S, (p i)^(v i)) := by
  have he := prime_product_square_raw_norm_sq S p hp hs hcop k v w hw
  have hc : 0 < elementNorm (∏ i ∈ S, (p i)^(k i)) :=
    elementNorm_pos _ (supportedElement_ne_zero _
      (supported_product S _ (fun i => supported_power (p i) (hs i) (k i))))
  have ht : 0 ≤ elementNorm (∏ i ∈ S, (p i)^(v i)) := by
    unfold elementNorm
    positivity
  rw [CenteredMomentGaussEnergy.gaussRow, norm_div, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  apply (div_le_iff₀ (Real.sqrt_pos.mpr hc)).mpr
  have hsqrt := Real.sq_sqrt hc.le
  have hnon := norm_nonneg
    (sexticGauss (∏ i ∈ S, (p i)^(k i))
      (supportedElement_ne_zero _ (supported_product S _
        (fun i => supported_power (p i) (hs i) (k i))))
      (w*(∏ i ∈ S, (p i)^(v i))^2))
  have hnon2 := mul_nonneg ht (Real.sqrt_nonneg (elementNorm (∏ i ∈ S, (p i)^(k i))))
  nlinarith

end OpenAIReview.SquareGaussNorm
#lint+ in OpenAIReview.SquareGaussNorm

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
  unless declarations > 0 do throwError "Empty actual square Gauss norm audit."
  logInfo m!"Square Gauss norm: {declarations} declarations, {theorems} theorems; only standard axioms."
  IO.FS.createDirAll ".lake/arithmetic-operator-square-gauss-norm"
  IO.FS.writeFile ".lake/arithmetic-operator-square-gauss-norm/axioms.json"
    (Json.mkObj [("scope", toJson "actual all-prime-power square Gauss norm bound; no supplied Gauss norm or phase; no source or zero-free claim"),
      ("namespaceLinters", toJson (15 : Nat)), ("onlyStandardAxioms", toJson true),
      ("allLocalModuleProvenance", toJson true),
      ("declarations", toJson declarations), ("theoremsIncludingHelpers", toJson theorems),
      ("details", Json.arr details)]).pretty
