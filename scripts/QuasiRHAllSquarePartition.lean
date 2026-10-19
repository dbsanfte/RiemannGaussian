/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import OAI.NumberTheory.DirichletL.CubicSieve.Gcd
import Mathlib.RingTheory.UniqueFactorizationDomain.Finsupp
import Mathlib.Tactic.Linter
import Lean.Util.CollectAxioms

/-!
Canonical prime-power partition of actual Eisenstein ideals. No residue,
source assignment or global energy estimate is asserted.
-/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
noncomputable section
open scoped Classical BigOperators
namespace OpenAIReview.AllSquarePartition
open OAI UniqueFactorizationMonoid
local notation "O" => OAI.ActualEisensteinCubic.O
local notation "Id" => Ideal O

/-- Literal prime multiplicity in the ideal factorization. -/
def val (I P : Id) : ℕ := factorization I P

/-- Prime support of an actual ideal. -/
def support (I : Id) : Finset Id := (normalizedFactors I).toFinset

/-- Apply a natural exponent function prime by prime to an actual ideal. -/
def block (I : Id) (f : ℕ → ℕ) : Id := ∏ P ∈ support I, P ^ f (val I P)

lemma support_prime {I P : Id} (hP : P ∈ support I) : Prime P :=
  prime_of_normalized_factor P (Multiset.mem_toFinset.mp hP)

lemma val_eq_count (I P : Id) : val I P = (normalizedFactors I).count P :=
  factorization_eq_count

lemma val_zero_of_not_mem {I P : Id} (hP : P ∉ support I) : val I P = 0 := by
  rw [val_eq_count]
  exact Multiset.count_eq_zero.mpr (fun h => hP (Multiset.mem_toFinset.mpr h))

lemma block_ne_zero (I : Id) (f : ℕ → ℕ) : block I f ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro P hP
  exact pow_ne_zero _ (support_prime hP).ne_zero

lemma val_mul {I J : Id} (hI : I ≠ 0) (hJ : J ≠ 0) (P : Id) :
    val (I*J) P = val I P + val J P := by
  simp [val, factorization_mul hI hJ]

lemma val_pow (I P : Id) (n : ℕ) : val (I^n) P = n * val I P := by
  simp [val, factorization_pow]

lemma val_prime_pow (P Q : Id) (hp : Prime P) (n : ℕ) :
    val (P^n) Q = if P=Q then n else 0 := by
  rw [val_eq_count, hp.irreducible.normalizedFactors_pow]
  simp only [normalize_eq, Multiset.count_replicate]

lemma val_prod (s : Finset Id) (f : Id → Id) (hn : ∀ P ∈ s, f P ≠ 0) (Q : Id) :
    val (∏ P ∈ s, f P) Q = ∑ P ∈ s, val (f P) Q := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, Finset.sum_empty]
    change factorization (1 : Id) Q = 0
    simp only [factorization_one, Finsupp.zero_apply]
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, val_mul (hn a (Finset.mem_insert_self _ _))
      (Finset.prod_ne_zero_iff.mpr (fun P hP => hn P (Finset.mem_insert_of_mem hP))),
      Finset.sum_insert ha, ih (fun P hP => hn P (Finset.mem_insert_of_mem hP))]

lemma val_block (I : Id) (f : ℕ → ℕ) (hf : f 0=0) (P : Id) :
    val (block I f) P = f (val I P) := by
  rw [block, val_prod _ _ (fun Q hQ => pow_ne_zero _ (support_prime hQ).ne_zero)]
  have he (Q : Id) (hQ : Q ∈ support I) :
      val (Q ^ f (val I Q)) P = if Q=P then f (val I Q) else 0 :=
    val_prime_pow Q P (support_prime hQ) _
  simp_rw [Finset.sum_congr rfl he]
  by_cases hp : P ∈ support I
  · simp [hp]
  · simp [hp, val_zero_of_not_mem hp, hf]

lemma eq_of_val_eq {I J : Id} (hI : I ≠ 0) (hJ : J ≠ 0)
    (hv : ∀ P, val I P = val J P) : I=J := by
  apply associated_iff_eq.mp
  apply associated_of_factorization_eq I J hI hJ
  ext P
  exact hv P

lemma dvd_of_val_le {I J : Id} (hI : I ≠ 0) (hJ : J ≠ 0)
    (hv : ∀ P, val I P ≤ val J P) : I ∣ J := by
  apply (dvd_iff_normalizedFactors_le_normalizedFactors hI hJ).mpr
  rw [Multiset.le_iff_count]
  intro P
  simpa only [← val_eq_count] using hv P

lemma block_dvd {I : Id} (hI : I ≠ 0) (f : ℕ → ℕ) (hf : f 0=0)
    (hle : ∀ n, f n ≤ n) : block I f ∣ I := by
  apply dvd_of_val_le (block_ne_zero I f) hI
  intro P
  rw [val_block I f hf]
  exact hle _

/-- The full sixth-power component of the physical ideal. -/
def H6 (I : Id) : Id := block I (fun n => n/6)
/-- Physical exponent-one residue component. -/
def b6 (I : Id) : Id := block I (fun n => if n%6=1 then 1 else 0)
/-- Physical exponent-three residue component. -/
def d6 (I : Id) : Id := block I (fun n => if n%6=3 then 1 else 0)
/-- Physical exponent-five residue component. -/
def e6 (I : Id) : Id := block I (fun n => if n%6=5 then 1 else 0)
/-- The actual root divisor dictated by a physical ideal. -/
def rootPart (I : Id) : Id := H6 I ^ 3 * d6 I * e6 I ^ 2
/-- Remaining physical factor, independent of the squarefree exponent-one part. -/
def V6 (I : Id) : Id := H6 I ^ 6 * d6 I ^ 3 * e6 I ^ 5

lemma H6_ne_zero (I : Id) : H6 I ≠ 0 := block_ne_zero _ _
lemma b6_ne_zero (I : Id) : b6 I ≠ 0 := block_ne_zero _ _
lemma d6_ne_zero (I : Id) : d6 I ≠ 0 := block_ne_zero _ _
lemma e6_ne_zero (I : Id) : e6 I ≠ 0 := block_ne_zero _ _

@[simp] lemma val_H6 (I P : Id) : val (H6 I) P = val I P / 6 :=
  val_block I _ (by decide) P
@[simp] lemma val_b6 (I P : Id) : val (b6 I) P = if val I P % 6=1 then 1 else 0 :=
  val_block I _ (by decide) P
@[simp] lemma val_d6 (I P : Id) : val (d6 I) P = if val I P % 6=3 then 1 else 0 :=
  val_block I _ (by decide) P
@[simp] lemma val_e6 (I P : Id) : val (e6 I) P = if val I P % 6=5 then 1 else 0 :=
  val_block I _ (by decide) P

lemma squarefree_of_val_le_one {I : Id} (hI : I ≠ 0) (hv : ∀ P, val I P ≤ 1) :
    Squarefree I := by
  rw [squarefree_iff_nodup_normalizedFactors hI, Multiset.nodup_iff_count_le_one]
  intro P
  simpa only [← val_eq_count] using hv P

lemma b6_squarefree (I : Id) : Squarefree (b6 I) := by
  apply squarefree_of_val_le_one (b6_ne_zero I)
  intro P
  rw [val_b6]
  split_ifs <;> omega

lemma d6_squarefree (I : Id) : Squarefree (d6 I) := by
  apply squarefree_of_val_le_one (d6_ne_zero I)
  intro P
  rw [val_d6]
  split_ifs <;> omega

lemma e6_squarefree (I : Id) : Squarefree (e6 I) := by
  apply squarefree_of_val_le_one (e6_ne_zero I)
  intro P
  rw [val_e6]
  split_ifs <;> omega

lemma coprime_of_val_disjoint {I J : Id} (hI : I ≠ 0) (hJ : J ≠ 0)
    (hv : ∀ P, val I P = 0 ∨ val J P = 0) : IsCoprime I J := by
  apply Ideal.isCoprime_iff_gcd.mpr
  apply IsUnit.eq_one
  rw [gcd_isUnit_iff_isRelPrime, isRelPrime_iff_no_prime_factors hI]
  intro P hPI hPJ hp
  have hi : 0 < val I P := by
    rw [val_eq_count, Multiset.count_pos]
    exact (mem_normalizedFactors_iff hI).mpr ⟨hp,hPI⟩
  have hj : 0 < val J P := by
    rw [val_eq_count, Multiset.count_pos]
    exact (mem_normalizedFactors_iff hJ).mpr ⟨hp,hPJ⟩
  rcases hv P with h | h <;> omega

lemma b6_coprime_d6 (I : Id) : IsCoprime (b6 I) (d6 I) := by
  apply coprime_of_val_disjoint (b6_ne_zero I) (d6_ne_zero I)
  intro P
  rw [val_b6, val_d6]
  split_ifs <;> omega

lemma b6_coprime_e6 (I : Id) : IsCoprime (b6 I) (e6 I) := by
  apply coprime_of_val_disjoint (b6_ne_zero I) (e6_ne_zero I)
  intro P
  rw [val_b6, val_e6]
  split_ifs <;> omega

lemma d6_coprime_e6 (I : Id) : IsCoprime (d6 I) (e6 I) := by
  apply coprime_of_val_disjoint (d6_ne_zero I) (e6_ne_zero I)
  intro P
  rw [val_d6, val_e6]
  split_ifs <;> omega

/-- The physical residues permitted by an actual square numerator. -/
def Allowed (I : Id) : Prop := ∀ P, val I P % 6=0 ∨ val I P % 6=1 ∨
  val I P % 6=3 ∨ val I P % 6=5

lemma physical_eq {I : Id} (hI : I ≠ 0) (ha : Allowed I) :
    I=H6 I^6*b6 I*d6 I^3*e6 I^5 := by
  have hH := pow_ne_zero 6 (H6_ne_zero I)
  have hD := pow_ne_zero 3 (d6_ne_zero I)
  have hE := pow_ne_zero 5 (e6_ne_zero I)
  have hHb := mul_ne_zero hH (b6_ne_zero I)
  have hHbD := mul_ne_zero hHb hD
  apply eq_of_val_eq hI (mul_ne_zero hHbD hE)
  intro P
  have hm := ha P
  rw [val_mul hHbD hE, val_mul hHb hD, val_mul hH (b6_ne_zero I),
    val_pow, val_pow, val_pow, val_H6, val_b6, val_d6, val_e6]
  split_ifs <;> omega

lemma H6_dvd {I : Id} (hI : I ≠ 0) : H6 I ∣ I :=
  block_dvd hI _ (by decide) (fun _ => Nat.div_le_self _ _)
lemma b6_dvd {I : Id} (hI : I ≠ 0) : b6 I ∣ I := by
  apply block_dvd hI _ (by decide)
  intro n
  split_ifs <;> omega
lemma d6_dvd {I : Id} (hI : I ≠ 0) : d6 I ∣ I := by
  apply block_dvd hI _ (by decide)
  intro n
  split_ifs <;> omega
lemma e6_dvd {I : Id} (hI : I ≠ 0) : e6 I ∣ I := by
  apply block_dvd hI _ (by decide)
  intro n
  split_ifs <;> omega

lemma supported_of_dvd {I J : Id} (hI : OAI.CanonicalQuadraticSieve.Supported I)
    (hJ : J ∣ I) : OAI.CanonicalQuadraticSieve.Supported J := by
  obtain ⟨K,rfl⟩ := hJ
  exact (OAI.CanonicalQuadraticSieve.supported_mul_iff J K).mp hI |>.1

lemma H6_supported {I : Id} (hI : OAI.CanonicalQuadraticSieve.Supported I) :
    OAI.CanonicalQuadraticSieve.Supported (H6 I) := supported_of_dvd hI (H6_dvd hI.1)
lemma b6_supported {I : Id} (hI : OAI.CanonicalQuadraticSieve.Supported I) :
    OAI.CanonicalQuadraticSieve.Supported (b6 I) := supported_of_dvd hI (b6_dvd hI.1)
lemma d6_supported {I : Id} (hI : OAI.CanonicalQuadraticSieve.Supported I) :
    OAI.CanonicalQuadraticSieve.Supported (d6 I) := supported_of_dvd hI (d6_dvd hI.1)
lemma e6_supported {I : Id} (hI : OAI.CanonicalQuadraticSieve.Supported I) :
    OAI.CanonicalQuadraticSieve.Supported (e6 I) := supported_of_dvd hI (e6_dvd hI.1)

lemma rootPart_ne_zero (I : Id) : rootPart I ≠ 0 :=
  mul_ne_zero (mul_ne_zero (pow_ne_zero _ (H6_ne_zero I)) (d6_ne_zero I))
    (pow_ne_zero _ (e6_ne_zero I))

lemma val_rootPart (I P : Id) : val (rootPart I) P =
    3*(val I P/6)+(if val I P%6=3 then 1 else 0)+
      2*(if val I P%6=5 then 1 else 0) := by
  rw [rootPart, val_mul (mul_ne_zero (pow_ne_zero _ (H6_ne_zero I)) (d6_ne_zero I))
    (pow_ne_zero _ (e6_ne_zero I)), val_mul (pow_ne_zero _ (H6_ne_zero I)) (d6_ne_zero I),
    val_pow, val_pow, val_H6, val_d6, val_e6]

lemma V6_eq (I : Id) : V6 I = rootPart I ^ 2 * d6 I * e6 I := by
  simp only [V6, rootPart, mul_pow, ← pow_mul]
  ring

lemma physical_eq_rootPart {I : Id} (hI : I ≠ 0) (ha : Allowed I) :
    I=rootPart I^2*d6 I*e6 I*b6 I := by
  calc
    I = H6 I^6*b6 I*d6 I^3*e6 I^5 := physical_eq hI ha
    _ = V6 I*b6 I := by unfold V6; ring
    _ = rootPart I^2*d6 I*e6 I*b6 I := by rw [V6_eq]

lemma V6_absNorm (I : Id) : Ideal.absNorm (V6 I) =
    Ideal.absNorm (rootPart I)^2 * Ideal.absNorm (d6 I) * Ideal.absNorm (e6 I) := by
  rw [V6_eq]
  simp only [map_mul, map_pow]

/-- Canonical cube part of an actual root divisor. -/
def H3 (T : Id) : Id := block T (fun n => n/3)
/-- Canonical exponent-one residue part of an actual root divisor. -/
def d3 (T : Id) : Id := block T (fun n => if n%3=1 then 1 else 0)
/-- Canonical exponent-two residue part of an actual root divisor. -/
def e3 (T : Id) : Id := block T (fun n => if n%3=2 then 1 else 0)

lemma H3_ne_zero (T : Id) : H3 T ≠ 0 := block_ne_zero _ _
lemma d3_ne_zero (T : Id) : d3 T ≠ 0 := block_ne_zero _ _
lemma e3_ne_zero (T : Id) : e3 T ≠ 0 := block_ne_zero _ _
@[simp] lemma val_H3 (I P : Id) : val (H3 I) P = val I P / 3 :=
  val_block I _ (by decide) P
@[simp] lemma val_d3 (I P : Id) : val (d3 I) P = if val I P%3=1 then 1 else 0 :=
  val_block I _ (by decide) P
@[simp] lemma val_e3 (I P : Id) : val (e3 I) P = if val I P%3=2 then 1 else 0 :=
  val_block I _ (by decide) P

lemma H3_rootPart (I : Id) : H3 (rootPart I)=H6 I := by
  apply eq_of_val_eq (H3_ne_zero _) (H6_ne_zero _)
  intro P
  rw [val_H3, val_rootPart, val_H6]
  split_ifs <;> omega

lemma d3_rootPart (I : Id) : d3 (rootPart I)=d6 I := by
  apply eq_of_val_eq (d3_ne_zero _) (d6_ne_zero _)
  intro P
  rw [val_d3, val_rootPart, val_d6]
  split_ifs <;> omega

lemma e3_rootPart (I : Id) : e3 (rootPart I)=e6 I := by
  apply eq_of_val_eq (e3_ne_zero _) (e6_ne_zero _)
  intro P
  rw [val_e3, val_rootPart, val_e6]
  split_ifs <;> omega

lemma rootPart_components_unique {I J : Id} (he : rootPart I=rootPart J) :
    H6 I=H6 J ∧ d6 I=d6 J ∧ e6 I=e6 J := by
  refine ⟨?_,?_,?_⟩
  · rw [← H3_rootPart I, ← H3_rootPart J, he]
  · rw [← d3_rootPart I, ← d3_rootPart J, he]
  · rw [← e3_rootPart I, ← e3_rootPart J, he]

lemma root_eq {T : Id} (hT : T ≠ 0) : T=H3 T^3*d3 T*e3 T^2 := by
  have hH := pow_ne_zero 3 (H3_ne_zero T)
  have hE := pow_ne_zero 2 (e3_ne_zero T)
  apply eq_of_val_eq hT (mul_ne_zero (mul_ne_zero hH (d3_ne_zero T)) hE)
  intro P
  rw [val_mul (mul_ne_zero hH (d3_ne_zero T)) hE, val_mul hH (d3_ne_zero T),
    val_pow, val_pow, val_H3, val_d3, val_e3]
  split_ifs <;> omega

lemma rootPart_dvd {I : Id} (hI : I ≠ 0) : rootPart I ∣ I := by
  apply dvd_of_val_le (rootPart_ne_zero _) hI
  intro P
  rw [val_rootPart]
  split_ifs <;> omega

lemma rootPart_supported {I : Id} (hI : OAI.CanonicalQuadraticSieve.Supported I) :
    OAI.CanonicalQuadraticSieve.Supported (rootPart I) :=
  supported_of_dvd hI (rootPart_dvd hI.1)

/-- Literal valuation constraints supplied by nonzero local square Gauss rows. -/
def SquareSupport (I X : Id) : Prop := ∀ P,
  if val I P%6=0 then val I P ≤ 2*val X P else val I P=2*val X P+1

lemma allowed_of_squareSupport {I X : Id} (hs : SquareSupport I X) : Allowed I := by
  intro P
  have hh := hs P
  by_cases hc : val I P%6=0
  · exact Or.inl hc
  · rw [ite_eq_right hc] at hh
    omega

lemma rootPart_dvd_of_squareSupport {I X : Id} (hX : X ≠ 0)
    (hs : SquareSupport I X) : rootPart I ∣ X := by
  apply dvd_of_val_le (rootPart_ne_zero I) hX
  intro P
  have hh := hs P
  rw [val_rootPart]
  split_ifs at * <;> omega

/-- The actual finite family of prime ideals of a physical modulus. -/
abbrev PrimeOf (I : Id) := {P // P ∈ support I}

/-- Literal native primary prime, without a choice of associate. -/
def primeElement (I : Id) (P : PrimeOf I) : O := CompletedGauss.primaryPrime P.val

lemma primaryGenerator_product {I : Id} (hI : I ≠ 0) :
    CompletedGauss.primaryGenerator I =
      ∏ P ∈ support I, CompletedGauss.primaryPrime P ^ val I P := by
  simp only [CompletedGauss.primaryGenerator, ite_eq_right hI]
  simpa only [support, val_eq_count] using
    Finset.prod_multiset_map_count (normalizedFactors I) CompletedGauss.primaryPrime

lemma primaryGenerator_family {I : Id} (hI : I ≠ 0) :
    CompletedGauss.primaryGenerator I = ∏ P : PrimeOf I, primeElement I P ^ val I P := by
  rw [primaryGenerator_product hI]
  exact (Finset.prod_coe_sort (support I) (fun P => CompletedGauss.primaryPrime P ^ val I P)).symm

lemma primeElement_spec {I : Id} (hI : CanonicalQuadraticSieve.Supported I) (P : PrimeOf I) :
    P.val.IsMaximal ∧ ActualEisensteinCubic.lambda ∉ P.val ∧
      Ideal.span {primeElement I P} = P.val ∧
      ActualEisensteinCubic.lambda ^ 2 ∣ primeElement I P - 1 := by
  apply CompletedGauss.primaryPrime_spec
  exact CompletedGauss.primaryPrime_factor_ne_zero I P
    (CanonicalQuadraticSieve.supported_primaryGenerator_ne_zero I hI)
    (Multiset.mem_toFinset.mp P.property)

lemma primeElement_ne_zero {I : Id} (hI : CanonicalQuadraticSieve.Supported I) (P : PrimeOf I) :
    primeElement I P ≠ 0 :=
  CompletedGauss.primaryPrime_factor_ne_zero I P
    (CanonicalQuadraticSieve.supported_primaryGenerator_ne_zero I hI)
    (Multiset.mem_toFinset.mp P.property)

lemma primeElement_prime {I : Id} (hI : CanonicalQuadraticSieve.Supported I) (P : PrimeOf I) :
    Prime (primeElement I P) := by
  have hs := primeElement_spec hI P
  let : P.val.IsMaximal := hs.1
  apply (Ideal.span_singleton_prime (primeElement_ne_zero hI P)).mp
  rw [hs.2.2.1]
  infer_instance

lemma primeElement_coprime {I : Id} (hI : CanonicalQuadraticSieve.Supported I) :
    Pairwise (fun P Q : PrimeOf I => IsCoprime (primeElement I P) (primeElement I Q)) := by
  intro P Q hne
  have hp := primeElement_spec hI P
  have hq := primeElement_spec hI Q
  let : P.val.IsMaximal := hp.1
  let : Q.val.IsMaximal := hq.1
  apply (Ideal.isCoprime_span_singleton_iff _ _).mp
  rw [hp.2.2.1, hq.2.2.1]
  exact Ideal.isCoprime_of_isMaximal (fun he => hne (Subtype.ext he))

lemma primeElement_odd {I : Id} (hI : CanonicalQuadraticSieve.Supported I) (P : PrimeOf I) :
    ringChar (O ⧸ P.val) ≠ 2 :=
  (hI.2 P.val (Multiset.mem_toFinset.mp P.property)).2

lemma val_pos_of_mem {I P : Id} (hP : P ∈ support I) : 0 < val I P := by
  rw [val_eq_count]
  exact Multiset.count_pos.mpr (Multiset.mem_toFinset.mp hP)

lemma squareSupport_of_family {I X : Id}
    (hs : ∀ P : PrimeOf I, if val I P%6=0 then val I P ≤ 2*val X P
      else val I P=2*val X P+1) : SquareSupport I X := by
  intro P
  by_cases hp : P ∈ support I
  · exact hs ⟨P,hp⟩
  · rw [val_zero_of_not_mem hp]
    simp only [Nat.zero_mod, ite_true, Nat.zero_le]

lemma physical_absNorm {I : Id} (hI : I ≠ 0) (ha : Allowed I) :
    Ideal.absNorm I = Ideal.absNorm (rootPart I)^2 *
      Ideal.absNorm (d6 I) * Ideal.absNorm (e6 I) * Ideal.absNorm (b6 I) := by
  conv_lhs => rw [physical_eq_rootPart hI ha]
  simp only [map_mul, map_pow]

lemma val_span_primeElement {I : Id} (hI : CanonicalQuadraticSieve.Supported I)
    (P : PrimeOf I) {x : O} (hx : x ≠ 0) :
    val (Ideal.span {x}) P = multiplicity (primeElement I P) x := by
  let : StrongNormalizationMonoid O := UniqueFactorizationMonoid.strongNormalizationMonoid
  rw [val_eq_count, ← (primeElement_spec hI P).2.2.1]
  rw [Ideal.count_span_normalizedFactors_eq hx (primeElement_prime hI P),
    multiplicity_eq_count_normalizedFactors (primeElement_prime hI P).irreducible hx]

lemma primeElement_supported {I : Id} (hI : CanonicalQuadraticSieve.Supported I)
    (P : PrimeOf I) : CanonicalQuadraticSieve.Supported (Ideal.span {primeElement I P}) := by
  rw [(primeElement_spec hI P).2.2.1]
  apply supported_of_dvd hI
  exact dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp P.property)

lemma primaryGenerator_block (I : Id) (f : ℕ → ℕ) :
    CompletedGauss.primaryGenerator (block I f) =
      ∏ P ∈ support I, CompletedGauss.primaryGenerator P ^ f (val I P) := by
  exact map_prod CompletedGauss.primaryGeneratorHom _ _ |>.trans
    (Finset.prod_congr rfl (fun P _ => map_pow CompletedGauss.primaryGeneratorHom P _))

lemma physical_eq_canonical {I : Id} (hI : I ≠ 0) (ha : Allowed I) :
    I = rootPart I ^ 2 * d3 (rootPart I) * e3 (rootPart I) * b6 I := by
  rw [d3_rootPart, e3_rootPart]
  exact physical_eq_rootPart hI ha

/-- A physical ideal is recovered from its divisor index and squarefree column. -/
lemma partition_injective {I J : Id} (hI : I ≠ 0) (hJ : J ≠ 0)
    (ha : Allowed I) (hb : Allowed J)
    (ht : rootPart I = rootPart J) (hc : b6 I = b6 J) : I = J := by
  calc
    I = rootPart I ^ 2 * d3 (rootPart I) * e3 (rootPart I) * b6 I :=
      physical_eq_canonical hI ha
    _ = rootPart J ^ 2 * d3 (rootPart J) * e3 (rootPart J) * b6 J := by rw [ht,hc]
    _ = J := (physical_eq_canonical hJ hb).symm

lemma canonical_reindex {I X : Id} (hI : CanonicalQuadraticSieve.Supported I)
    (hX : X ≠ 0) (hs : SquareSupport I X) :
    rootPart I ∣ X ∧ CanonicalQuadraticSieve.Supported (rootPart I) ∧
      Squarefree (b6 I) ∧ IsCoprime (b6 I) (d3 (rootPart I) * e3 (rootPart I)) ∧
      I = rootPart I ^ 2 * d3 (rootPart I) * e3 (rootPart I) * b6 I := by
  refine ⟨rootPart_dvd_of_squareSupport hX hs, rootPart_supported hI,
    b6_squarefree I, ?_, physical_eq_canonical hI.1 (allowed_of_squareSupport hs)⟩
  rw [d3_rootPart,e3_rootPart]
  exact (b6_coprime_d6 I).mul_right (b6_coprime_e6 I)

lemma val_le_one_of_squarefree {I : Id} (hs : Squarefree I) (P : Id) : val I P ≤ 1 := by
  rw [val_eq_count]
  exact Multiset.nodup_iff_count_le_one.mp
    ((squarefree_iff_nodup_normalizedFactors hs.ne_zero).mp hs) P

lemma val_disjoint_of_coprime {I J : Id} (hc : IsCoprime I J) (P : Id) :
    val I P=0 ∨ val J P=0 := by
  by_cases hi : val I P=0
  · exact Or.inl hi
  by_cases hj : val J P=0
  · exact Or.inr hj
  have hPi : P ∈ normalizedFactors I := by
    exact Multiset.count_pos.mp (by rw [← val_eq_count]; omega)
  have hPj : P ∈ normalizedFactors J := by
    exact Multiset.count_pos.mp (by rw [← val_eq_count]; omega)
  exact False.elim ((prime_of_normalized_factor P hPi).not_isUnit
    (hc.isUnit_of_dvd' (dvd_of_mem_normalizedFactors hPi) (dvd_of_mem_normalizedFactors hPj)))

/-- The literal physical ideal attached to the divisor index and cubic column. -/
def physical (T B : Id) : Id := T^2*d3 T*e3 T*B

lemma physical_ne_zero {T B : Id} (hT : T ≠ 0) (hB : B ≠ 0) : physical T B ≠ 0 :=
  mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hT) (d3_ne_zero T)) (e3_ne_zero T)) hB

lemma val_physical {T B : Id} (hT : T ≠ 0) (hB : B ≠ 0) (P : Id) :
    val (physical T B) P = 2*val T P + (if val T P%3=1 then 1 else 0) +
      (if val T P%3=2 then 1 else 0) + val B P := by
  rw [physical, val_mul
    (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hT) (d3_ne_zero T)) (e3_ne_zero T)) hB,
    val_mul (mul_ne_zero (pow_ne_zero 2 hT) (d3_ne_zero T)) (e3_ne_zero T),
    val_mul (pow_ne_zero 2 hT) (d3_ne_zero T), val_pow, val_d3, val_e3]

lemma physical_val_constraints {T B : Id} (_hT : T ≠ 0) (hB : Squarefree B)
    (hc : IsCoprime B (d3 T*e3 T)) (P : Id) :
    val B P ≤ 1 ∧ ((val T P%3=1 ∨ val T P%3=2) → val B P=0) := by
  refine ⟨val_le_one_of_squarefree hB P, ?_⟩
  intro hm
  rcases val_disjoint_of_coprime hc P with hh | hh
  · exact hh
  · rw [val_mul (d3_ne_zero T) (e3_ne_zero T), val_d3, val_e3] at hh
    rcases hm with hm | hm <;> norm_num [hm] at hh

lemma physical_allowed {T B : Id} (hT : T ≠ 0) (hB : Squarefree B)
    (hc : IsCoprime B (d3 T*e3 T)) : Allowed (physical T B) := by
  intro P
  have hv := physical_val_constraints hT hB hc P
  rw [val_physical hT hB.ne_zero]
  split_ifs <;> omega

lemma rootPart_physical {T B : Id} (hT : T ≠ 0) (hB : Squarefree B)
    (hc : IsCoprime B (d3 T*e3 T)) : rootPart (physical T B)=T := by
  apply eq_of_val_eq (rootPart_ne_zero _) hT
  intro P
  have hv := physical_val_constraints hT hB hc P
  rw [val_rootPart, val_physical hT hB.ne_zero]
  split_ifs <;> omega

lemma b6_physical {T B : Id} (hT : T ≠ 0) (hB : Squarefree B)
    (hc : IsCoprime B (d3 T*e3 T)) : b6 (physical T B)=B := by
  apply eq_of_val_eq (b6_ne_zero _) hB.ne_zero
  intro P
  have hv := physical_val_constraints hT hB hc P
  rw [val_b6, val_physical hT hB.ne_zero]
  split_ifs <;> omega

lemma primaryGenerator_prime {P : Id} (hp : Prime P) :
    CompletedGauss.primaryGenerator P = CompletedGauss.primaryPrime P := by
  simp only [CompletedGauss.primaryGenerator, ite_eq_right hp.ne_zero,
    normalizedFactors_irreducible hp.irreducible, normalize_eq, Multiset.map_singleton,
    Multiset.prod_singleton]

lemma primaryGenerator_block_family (I : Id) (f : ℕ → ℕ) :
    CompletedGauss.primaryGenerator (block I f) =
      ∏ P : PrimeOf I, primeElement I P ^ f (val I P) := by
  calc
    _ = ∏ P ∈ support I, CompletedGauss.primaryGenerator P ^ f (val I P) :=
      primaryGenerator_block I f
    _ = ∏ P ∈ support I, CompletedGauss.primaryPrime P ^ f (val I P) := by
      apply Finset.prod_congr rfl
      intro P hp
      rw [primaryGenerator_prime (support_prime hp)]
    _ = _ := (Finset.prod_coe_sort (support I)
      (fun P : Id => CompletedGauss.primaryPrime P ^ f (val I P))).symm

lemma primaryGenerator_rootPart_family (I : Id) :
    CompletedGauss.primaryGenerator (rootPart I) =
      ∏ P : PrimeOf I, primeElement I P ^ (3*(val I P/6) +
        (if val I P%6=3 then 1 else 0) + 2*(if val I P%6=5 then 1 else 0)) := by
  change CompletedGauss.primaryGenerator (H6 I^3*d6 I*e6 I^2) = _
  simp only [CompletedGauss.primaryGenerator_mul,
    show ∀ J n, CompletedGauss.primaryGenerator (J^n) =
      CompletedGauss.primaryGenerator J ^ n from fun J n =>
        map_pow CompletedGauss.primaryGeneratorHom J n,
    H6, d6, e6, primaryGenerator_block_family, ← Finset.prod_pow,
    ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro P _
  rw [pow_add, pow_add, ← pow_mul, ← pow_mul]
  ring_nf

lemma d3_squarefree (T : Id) : Squarefree (d3 T) := by
  apply squarefree_of_val_le_one (d3_ne_zero T)
  intro P
  rw [val_d3]
  split_ifs <;> omega

lemma e3_squarefree (T : Id) : Squarefree (e3 T) := by
  apply squarefree_of_val_le_one (e3_ne_zero T)
  intro P
  rw [val_e3]
  split_ifs <;> omega

lemma d3_coprime_e3 (T : Id) : IsCoprime (d3 T) (e3 T) := by
  apply coprime_of_val_disjoint (d3_ne_zero T) (e3_ne_zero T)
  intro P
  rw [val_d3,val_e3]
  split_ifs <;> omega

lemma d3_supported {T : Id} (hT : CanonicalQuadraticSieve.Supported T) :
    CanonicalQuadraticSieve.Supported (d3 T) := by
  apply supported_of_dvd hT
  exact block_dvd hT.1 _ (by decide) (by intro n; split_ifs <;> omega)

lemma e3_supported {T : Id} (hT : CanonicalQuadraticSieve.Supported T) :
    CanonicalQuadraticSieve.Supported (e3 T) := by
  apply supported_of_dvd hT
  exact block_dvd hT.1 _ (by decide) (by intro n; split_ifs <;> omega)

lemma physical_supported {T B : Id} (hT : CanonicalQuadraticSieve.Supported T)
    (hB : CanonicalQuadraticSieve.Supported B) : CanonicalQuadraticSieve.Supported (physical T B) := by
  apply (CanonicalQuadraticSieve.supported_mul_iff _ _).mpr
  refine ⟨?_,hB⟩
  apply (CanonicalQuadraticSieve.supported_mul_iff _ _).mpr
  refine ⟨?_,e3_supported hT⟩
  apply (CanonicalQuadraticSieve.supported_mul_iff _ _).mpr
  refine ⟨?_,d3_supported hT⟩
  exact (CanonicalQuadraticSieve.supported_sq_iff T).mpr hT

end OpenAIReview.AllSquarePartition
#lint+ in OpenAIReview.AllSquarePartition

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
  unless declarations > 0 do throwError "Empty canonical all-square partition audit."
  logInfo m!"Canonical all-square partition: {declarations} declarations, {theorems} theorems; only standard axioms."
  IO.FS.createDirAll ".lake/arithmetic-operator-all-square-partition"
  IO.FS.writeFile ".lake/arithmetic-operator-all-square-partition/axioms.json"
    (Json.mkObj [("scope", toJson "pure canonical actual ideal partition, inverse coverage, exact primary generators and multiplicities; actual Gauss support is a separate integration obligation"),
      ("namespaceLinters", toJson (15 : Nat)), ("onlyStandardAxioms", toJson true),
      ("allLocalModuleProvenance", toJson true), ("declarations", toJson declarations),
      ("theoremsIncludingHelpers", toJson theorems), ("details", Json.arr details)]).pretty
