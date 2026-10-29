/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeCardinalHeight

/-!
# Executed scalar Hermite evaluation and prefix heights

Finite array evaluation and node accumulation are executed by explicit rational
loops. Bounds cover each intermediate accumulator, not just a final polynomial.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeHermiteArrayHeight
open scoped BigOperators
open Polynomial
open RiemannGaussian.SemiprimeJetArray
open RiemannGaussian.SemiprimeJetRecurrence
open RiemannGaussian.SemiprimeJetArrayHeight
open RiemannGaussian.SemiprimeHermiteRecovery
open RiemannGaussian.SemiprimeCardinalHeight

/-- Scalar evaluation accumulator and its currently cached integer power. -/
structure EvalReport where
  /-- Accumulated scalar value. -/
  value : ℚ
  /-- Cached argument power. -/
  power : ℚ
  /-- Exact rational multiply/add count. -/
  arithmetic : ℕ
  /-- Exact coefficient-array read count. -/
  reads : ℕ

/-- Executed ascending-power scalar evaluation; no rational exponentiation is hidden. -/
def evalPrefix (a : Array ℚ) (x : ℤ) : ℕ → EvalReport
  | 0 => ⟨0, 1, 0, 0⟩
  | len + 1 =>
      let old := evalPrefix a x len
      ⟨old.value + coefficient a len * old.power, old.power * (x : ℚ),
        old.arithmetic + 3, old.reads + 1⟩

theorem evalPrefix_power (a : Array ℚ) (x : ℤ) (len : ℕ) :
    (evalPrefix a x len).power = (x : ℚ) ^ len := by
  induction len with
  | zero => simp [evalPrefix]
  | succ len ih => simp only [evalPrefix, ih, pow_succ]

theorem evalPrefix_value (a : Array ℚ) (x : ℤ) (len : ℕ) :
    (evalPrefix a x len).value = ∑ i ∈ Finset.range len, coefficient a i * (x : ℚ) ^ i := by
  induction len with
  | zero => simp [evalPrefix]
  | succ len ih => simp only [evalPrefix, ih, evalPrefix_power, Finset.sum_range_succ]

theorem evalPrefix_work (a : Array ℚ) (x : ℤ) (len : ℕ) :
    (evalPrefix a x len).arithmetic = 3 * len ∧ (evalPrefix a x len).reads = len := by
  induction len with
  | zero => simp [evalPrefix]
  | succ len ih => simp only [evalPrefix]; omega

theorem evalPrefix_polynomial (a : Array ℚ) (x : ℤ) :
    (evalPrefix a x a.size).value = (asPolynomial a).eval (x : ℚ) := by
  rw [evalPrefix_value, asPolynomial]
  simp [SemiprimeJetRecurrence.jetPolynomial, Polynomial.eval_finsetSum]

theorem representation_zero (d : ℕ) : Representation 0 d 0 := by
  exact ⟨0, by simp, by simp⟩

theorem representation_integer (x : ℤ) : Representation (x : ℚ) 1 x.natAbs := by
  exact ⟨x, by simp, le_refl _⟩

theorem representation_integer_mul {q : ℚ} {d B T : ℕ}
    (hq : Representation q d B) (x : ℤ) (hx : x.natAbs ≤ T) :
    Representation (q * (x : ℚ)) d (B * T) := by
  have h := representation_mul hq (representation_mono (representation_integer x) hx)
  simpa only [Nat.mul_one] using h

/-- Every multiply-add accumulator has the SAME input denominator. -/
theorem evalPrefix_representation (a : Array ℚ) (x : ℤ) (d B T J len : ℕ)
    (hx : x.natAbs ≤ T) (hlen : len ≤ J)
    (ha : ∀ i < J, Representation (coefficient a i) d B) :
    Representation (evalPrefix a x len).value d (len * B * (T + 1) ^ J) := by
  rw [evalPrefix_value]
  have h := representation_sum (Finset.range len)
    (fun i => coefficient a i * (x : ℚ) ^ i) d (B * (T + 1) ^ J) (by
      intro i hi
      have hi' := Finset.mem_range.mp hi
      have ht : (x ^ i).natAbs ≤ (T + 1) ^ J := by
        rw [Int.natAbs_pow]
        calc
          _ ≤ (T + 1) ^ i := Nat.pow_le_pow_left (by omega) _
          _ ≤ (T + 1) ^ J := Nat.pow_le_pow_right (by omega) (by omega)
      simpa only [Int.cast_pow] using representation_integer_mul (ha i (by omega)) (x ^ i) ht)
  simpa only [Finset.card_range, Nat.mul_assoc] using h

/-- All partial convolution sums, using common input denominators. -/
theorem dotPrefix_common_representation (a b : Array ℚ) (d e B C n len : ℕ)
    (ha : ∀ i < len, Representation (coefficient a (i + 1)) d B)
    (hb : ∀ i < len, Representation (coefficient b (n - i)) e C) :
    Representation (dotPrefix a b n len).value (d * e) (len * B * C) := by
  rw [dotPrefix_value]
  have h := representation_sum (Finset.range len)
    (fun i => coefficient a (i + 1) * coefficient b (n - i)) (d * e) (B * C) (by
      intro i hi
      have hi' := Finset.mem_range.mp hi
      exact representation_mul (ha i hi') (hb i hi'))
  simpa only [Finset.card_range, Nat.mul_assoc] using h

/-- The actual cached quotient has common coefficient representations, prior to reduction. -/
theorem quotient_representation (H L : Array ℚ) (dH dL BH BL J : ℕ)
    (hdL : 0 < dL) (hL0 : coefficient L 0 = 1)
    (hH : ∀ i < J, Representation (coefficient H i) dH BH)
    (hL : ∀ i < J, Representation (coefficient L i) dL BL) (k : ℕ) (hk : k < J) :
    Representation (coefficient (quotient H L J).coefficients k)
      (dH * dL ^ J) (J * BH * inverseBase J dL BL ^ J) := by
  exact multiply_representation H (inverse L J).coefficients dH (dL ^ J) BH
    (inverseBase J dL BL ^ J) J hH
    (fun i hi => cached_inverse_common_representation L dL BL J hdL hL0 hL i hi) k hk

/-- Every scalar-evaluation prefix after the executed cached quotient. -/
theorem quotient_evalPrefix_representation (H L : Array ℚ) (x : ℤ)
    (dH dL BH BL J T len : ℕ) (hdL : 0 < dL) (hL0 : coefficient L 0 = 1)
    (hH : ∀ i < J, Representation (coefficient H i) dH BH)
    (hL : ∀ i < J, Representation (coefficient L i) dL BL)
    (hx : x.natAbs ≤ T) (hlen : len ≤ J) :
    Representation (evalPrefix (quotient H L J).coefficients x len).value
      (dH * dL ^ J) (len * (J * BH * inverseBase J dL BL ^ J) * (T + 1) ^ J) :=
  evalPrefix_representation _ _ _ _ _ _ _ hx hlen
    (fun k hk => quotient_representation H L dH dL BH BL J hdL hL0 hH hL k hk)

/-- Actual node sum, retaining an observable prefix accumulator and operation count. -/
def nodePrefix (node : ℕ → ℚ) : ℕ → DotReport
  | 0 => ⟨0, 0, 0⟩
  | len + 1 =>
      let old := nodePrefix node len
      ⟨old.value + node len, old.arithmetic + 1, old.reads + 1⟩

theorem nodePrefix_value (node : ℕ → ℚ) (len : ℕ) :
    (nodePrefix node len).value = ∑ i ∈ Finset.range len, node i := by
  induction len with
  | zero => simp [nodePrefix]
  | succ len ih => simp [nodePrefix, Finset.sum_range_succ, ih]

theorem nodePrefix_work (node : ℕ → ℚ) (len : ℕ) :
    (nodePrefix node len).arithmetic = len ∧ (nodePrefix node len).reads = len := by
  induction len with
  | zero => simp [nodePrefix]
  | succ len ih => simp [nodePrefix, ih]

theorem nodePrefix_representation (node : ℕ → ℚ) (d B len : ℕ)
    (hnode : ∀ i < len, Representation (node i) d B) :
    Representation (nodePrefix node len).value d (len * B) := by
  rw [nodePrefix_value]
  simpa only [Finset.card_range] using representation_sum (Finset.range len) node d B
    (fun i hi => hnode i (Finset.mem_range.mp hi))

/-- One literal affine-factor coefficient array. -/
def affineArray (c : ℚ) : Array ℚ := #[1, c]

/-- Executed truncated product of a supplied finite affine-factor list. -/
def buildAffine (J : ℕ) : List ℚ → InverseReport
  | [] => ⟨#[1], 0, 0⟩
  | c :: cs =>
      let old := buildAffine J cs
      let next := multiply old.coefficients (affineArray c) J
      ⟨next.coefficients, old.arithmetic + next.arithmetic, old.reads + next.reads⟩

theorem affineArray_polynomial (c : ℚ) : asPolynomial (affineArray c) = 1 + C c * X := by
  simp [asPolynomial, affineArray, SemiprimeJetRecurrence.jetPolynomial, coefficient,
    Finset.sum_range_succ, C_mul_X_eq_monomial]

theorem unitArray_polynomial : asPolynomial #[1] = (1 : Polynomial ℚ) := by
  simp [asPolynomial, SemiprimeJetRecurrence.jetPolynomial, coefficient]

theorem truncate_mul_left (p q : Polynomial ℚ) (J : ℕ) :
    ((p %ₘ X ^ J) * q) %ₘ X ^ J = (p * q) %ₘ X ^ J := by
  apply modByMonic_eq_of_dvd_sub (monic_X.pow J)
  simpa only [sub_mul] using (dvd_modByMonic_sub p (X ^ J)).mul_right q

/-- Exact semantic meaning of the executed affine builder, with finite truncation retained. -/
theorem buildAffine_polynomial (J : ℕ) (hJ : 0 < J) (cs : List ℚ) :
    asPolynomial (buildAffine J cs).coefficients =
      (cs.map (fun c => 1 + C c * X)).prod %ₘ X ^ J := by
  induction cs with
  | nil =>
    simp only [buildAffine, unitArray_polynomial, List.map_nil, List.prod_nil]
    symm
    apply (modByMonic_eq_self_iff (monic_X.pow J)).mpr
    simp only [degree_one, degree_X_pow]
    exact_mod_cast hJ
  | cons c cs ih =>
    change asPolynomial (multiply (buildAffine J cs).coefficients (affineArray c) J).coefficients = _
    rw [multiply_asPolynomial, ih, affineArray_polynomial, truncate_mul_left]
    simp only [List.map_cons, List.prod_cons]
    congr 1
    ring

theorem buildAffine_work (J : ℕ) (cs : List ℚ) :
    (buildAffine J cs).arithmetic = cs.length * (J * (J + 1)) ∧
      (buildAffine J cs).reads = cs.length * (J * (J + 1)) := by
  induction cs with
  | nil => simp [buildAffine]
  | cons c cs ih =>
    simp only [buildAffine, multiply_work, List.length_cons, ih.1, ih.2]
    constructor <;> ring

/-- Exact factor list for the actual normalized cardinal jet. Self-node factors
are explicitly one, so no zero reciprocal is used as an inverse. -/
def cardinalSlopes (Q J t : ℕ) : List ℚ :=
  (List.range Q).flatMap (fun s => List.replicate J
    (if s = t then 0 else (((t : ℚ) + 1) - ((s : ℚ) + 1))⁻¹))

/-- Actual finite-array cardinal supplier. -/
def cardinalJet (Q J t : ℕ) : InverseReport :=
  let out := buildAffine J (cardinalSlopes Q J t)
  ⟨out.coefficients, out.arithmetic + 4 * Q, out.reads⟩

theorem cardinalSlopes_length (Q J t : ℕ) : (cardinalSlopes Q J t).length = Q * J := by
  have h : ∀ ls : List ℕ, (ls.flatMap (fun s => List.replicate J
      (if s = t then (0 : ℚ) else (((t : ℚ) + 1) - ((s : ℚ) + 1))⁻¹))).length = ls.length * J := by
    intro ls
    induction ls with
    | nil => simp
    | cons s ls ih => simp only [List.flatMap_cons, List.length_append, List.length_replicate,
        List.length_cons, ih]; ring
  exact (h (List.range Q)).trans (by simp)

theorem cardinalSlopes_product_range (Q J t : ℕ) :
    ((cardinalSlopes Q J t).map (fun c => (1 : Polynomial ℚ) + C c * X)).prod =
      ∏ s ∈ Finset.range Q, (1 + C (if s = t then 0 else
        (((t : ℚ) + 1) - ((s : ℚ) + 1))⁻¹) * X) ^ J := by
  let f : ℕ → ℚ := fun s => if s = t then 0 else (((t : ℚ) + 1) - ((s : ℚ) + 1))⁻¹
  have h : ∀ ls : List ℕ,
      ((ls.flatMap (fun s => List.replicate J (f s))).map (fun c => (1 : Polynomial ℚ) + C c * X)).prod =
      (ls.map (fun s => ((1 : Polynomial ℚ) + C (f s) * X) ^ J)).prod := by
    intro ls
    induction ls with
    | nil => simp
    | cons s ls ih => simp [List.flatMap_cons, List.map_append, List.prod_append, ih]
  rw [cardinalSlopes]
  change ((List.range Q |>.flatMap (fun s => List.replicate J (f s))).map
    (fun c => (1 : Polynomial ℚ) + C c * X)).prod = _
  rw [h, ← List.prod_toFinset _ List.nodup_range]
  simp only [List.toFinset_range, f]

theorem cardinalSlopes_product (Q J : ℕ) (t : Fin Q) :
    ((cardinalSlopes Q J t.val).map (fun c => (1 : Polynomial ℚ) + C c * X)).prod =
      taylor ((t.val : ℚ) + 1) (cardinalFactor (samplePoints Q) J ((t.val : ℚ) + 1)) := by
  classical
  rw [cardinalSlopes_product_range, ← Fin.prod_univ_eq_prod_range]
  let x : ℚ := (t.val : ℚ) + 1
  let g : ℚ → Polynomial ℚ := fun y => if y = x then 1 else (1 + C ((x - y)⁻¹) * X) ^ J
  have hx : x ∈ samplePoints Q := Finset.mem_image.mpr ⟨t, Finset.mem_univ _, rfl⟩
  have hm : (∏ y ∈ samplePoints Q, g y) =
      ∏ i : Fin Q, (1 + C (if i.val = t.val then 0 else
        (((t.val : ℚ) + 1) - ((i.val : ℚ) + 1))⁻¹) * X) ^ J := by
    unfold samplePoints
    rw [Finset.prod_image]
    · apply Finset.prod_congr rfl
      intro i _
      by_cases hi : i.val = t.val
      · simp [g, x, hi]
      · have hie : (i.val : ℚ) + 1 ≠ (t.val : ℚ) + 1 := by
          intro he
          exact hi (by exact_mod_cast add_right_cancel he)
        simp [g, x, hi, hie]
    · intro i _ j _ hij
      apply Fin.ext
      exact_mod_cast add_right_cancel hij
  rw [← hm]
  rw [← Finset.prod_erase_mul _ _ hx]
  have hg : g x = 1 := by simp [g]
  rw [hg, mul_one, taylor_cardinal_product]
  apply Finset.prod_congr rfl
  intro y hy
  have hne : y ≠ x := Finset.ne_of_mem_erase hy
  simp only [g, ite_eq_right hne]
  congr 1
  ring

/-- The intrinsic cardinal supplier is the actual first-J Taylor packet. -/
theorem cardinalJet_polynomial (Q J : ℕ) (hJ : 0 < J) (t : Fin Q) :
    asPolynomial (cardinalJet Q J t.val).coefficients =
      taylor ((t.val : ℚ) + 1) (cardinalFactor (samplePoints Q) J ((t.val : ℚ) + 1)) %ₘ X ^ J := by
  rw [cardinalJet, buildAffine_polynomial J hJ, cardinalSlopes_product]

theorem cardinalJet_coefficient (Q J : ℕ) (hJ : 0 < J) (t : Fin Q) (k : ℕ) (hk : k < J) :
    coefficient (cardinalJet Q J t.val).coefficients k =
      (taylor ((t.val : ℚ) + 1) (cardinalFactor (samplePoints Q) J ((t.val : ℚ) + 1))).coeff k := by
  rw [← asPolynomial_coeff, cardinalJet_polynomial Q J hJ t, coeff_mod_X_pow, ite_eq_left hk]

/-- Executed scalar product of the SAME finite affine factors used by cardinalJet. -/
def affineValue (x : ℤ) : List ℚ → DotReport
  | [] => ⟨1, 0, 0⟩
  | c :: cs =>
      let old := affineValue x cs
      ⟨old.value * (1 + c * (x : ℚ)), old.arithmetic + 3, old.reads + 1⟩

theorem affineValue_value (x : ℤ) (cs : List ℚ) :
    (affineValue x cs).value = ((cs.map (fun c => (1 : Polynomial ℚ) + C c * X)).prod).eval (x : ℚ) := by
  induction cs with
  | nil => simp [affineValue]
  | cons c cs ih => simp only [affineValue, List.map_cons, List.prod_cons, eval_mul,
      eval_add, eval_one, eval_C, eval_X, ih]; ring

theorem affineValue_work (x : ℤ) (cs : List ℚ) :
    (affineValue x cs).arithmetic = 3 * cs.length ∧ (affineValue x cs).reads = cs.length := by
  induction cs with
  | nil => simp [affineValue]
  | cons c cs ih => simp [affineValue, ih]; omega

/-- Executable cardinal factor at zero, without computing polynomial coefficients. -/
def cardinalZero (Q J t : ℕ) : DotReport :=
  let out := affineValue (-(t + 1 : ℕ)) (cardinalSlopes Q J t)
  ⟨out.value, out.arithmetic + 4 * Q, out.reads⟩

theorem cardinalZero_value (Q J : ℕ) (t : Fin Q) :
    (cardinalZero Q J t.val).value = (cardinalFactor (samplePoints Q) J ((t.val : ℚ) + 1)).eval 0 := by
  rw [cardinalZero, affineValue_value, cardinalSlopes_product, taylor_eval]
  have he : ((-((t.val + 1 : ℕ) : ℤ) : ℤ) : ℚ) + ((t.val : ℚ) + 1) = 0 := by push_cast; ring
  rw [he]

theorem cardinalJet_intrinsic_representation (Q J : ℕ) (hJ : 0 < J) (t : Fin Q)
    (k : ℕ) (hk : k < J) :
    Representation (coefficient (cardinalJet Q J t.val).coefficients k)
      (cardinalDenominator Q J) (cardinalDenominator Q J * 2 ^ (Q * J)) := by
  rw [cardinalJet_coefficient Q J hJ t k hk]
  exact taylor_cardinal_representation (Finset.mem_image.mpr ⟨t, Finset.mem_univ _, rfl⟩) k

theorem cardinalJet_constant (Q J : ℕ) (hJ : 0 < J) (t : Fin Q) :
    coefficient (cardinalJet Q J t.val).coefficients 0 = 1 := by
  rw [cardinalJet_coefficient Q J hJ t 0 hJ, taylor_cardinal_constant]

theorem representation_one (d : ℕ) (hd : 0 < d) : Representation 1 d d := by
  refine ⟨d, ?_, by simp⟩
  have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hd
  simp [hdq]

theorem representation_add_one {q : ℚ} {d B : ℕ} (hq : Representation q d B) (hd : 0 < d) :
    Representation (1 + q) d (d + B) := representation_add (representation_one d hd) hq

/-- Every scalar-product prefix in cardinalZero retains a known power denominator. -/
theorem affineValue_representation (x : ℤ) (cs : List ℚ) (d T : ℕ) (hd : 0 < d)
    (hx : x.natAbs ≤ T) (hc : ∀ c ∈ cs, Representation c d d) :
    Representation (affineValue x cs).value (d ^ cs.length) ((d * (T + 1)) ^ cs.length) := by
  induction cs with
  | nil => simpa [affineValue] using representation_one 1 (by decide)
  | cons c cs ih =>
    have ho := ih (fun z hz => hc z (List.mem_cons_of_mem c hz))
    have ht := representation_add_one (representation_integer_mul (hc c (List.mem_cons_self)) x hx) hd
    have ht' : Representation (1 + c * (x : ℚ)) d (d * (T + 1)) := by
      apply representation_mono ht
      nlinarith
    have hm := representation_mul ho ht'
    simpa only [affineValue, List.length_cons, pow_succ] using hm

/-- Uniform executed node report, charging cardinal construction, quotient and scalar evaluation. -/
def hermiteNode (H : Array ℚ) (Q J : ℕ) (t : Fin Q) : DotReport :=
  let L := cardinalJet Q J t.val
  let c := cardinalZero Q J t.val
  let q := quotient H L.coefficients J
  let e := evalPrefix q.coefficients (-(t.val + 1 : ℕ)) J
  ⟨c.value * e.value, L.arithmetic + c.arithmetic + q.arithmetic + e.arithmetic + 1,
    L.reads + c.reads + q.reads + e.reads⟩

theorem denominator_truncate (H L : Polynomial ℚ) (J : ℕ) (hJ : 0 < J) (hL : L.coeff 0 = 1) :
    localQuotient H (L %ₘ X ^ J) J = localQuotient H L J := by
  have hL' : (L %ₘ X ^ J).coeff 0 = 1 := by rw [coeff_mod_X_pow, ite_eq_left hJ, hL]
  rw [← recurrence_localQuotient H (L %ₘ X ^ J) J hL']
  exact packet_recurrence_localQuotient H L J hJ hL

/-- Literal scalar node value equals its actual finite Hermite summand. -/
theorem hermiteNode_value (H : Array ℚ) (Q J : ℕ) (hJ : 0 < J) (t : Fin Q) :
    (hermiteNode H Q J t).value =
      (cardinalFactor (samplePoints Q) J ((t.val : ℚ) + 1)).eval 0 *
        (localQuotient (asPolynomial H)
          (taylor ((t.val : ℚ) + 1) (cardinalFactor (samplePoints Q) J ((t.val : ℚ) + 1))) J).eval
          (-((t.val : ℚ) + 1)) := by
  change (cardinalZero Q J t.val).value *
    (evalPrefix (quotient H (cardinalJet Q J t.val).coefficients J).coefficients
      (-(t.val + 1 : ℕ)) J).value = _
  rw [cardinalZero_value]
  congr 1
  have hs : (quotient H (cardinalJet Q J t.val).coefficients J).coefficients.size = J := by
    simp only [quotient, multiply_size]
  have he := evalPrefix_polynomial (quotient H (cardinalJet Q J t.val).coefficients J).coefficients
    (-(t.val + 1 : ℕ))
  rw [hs] at he
  rw [he, quotient_correct _ _ J (cardinalJet_constant Q J hJ t),
    cardinalJet_polynomial Q J hJ t,
    denominator_truncate _ _ J hJ (taylor_cardinal_constant Q J ((t.val : ℚ) + 1))]
  congr 1
  push_cast
  ring

theorem representation_of_clears_abs {q : ℚ} {d B : ℕ} (hd : 0 < d)
    (hc : SemiprimeSourceRowHeight.Clears d (C q)) (hb : |q| ≤ B) :
    Representation q d (d * B) := by
  obtain ⟨P, hP⟩ := hc
  change P.map (Int.castRingHom ℚ) = _ at hP
  have he := congrArg (fun p : Polynomial ℚ => p.coeff 0) hP
  simp only [coeff_map, coeff_C_mul, coeff_C_zero] at he
  change ((P.coeff 0 : ℤ) : ℚ) = _ at he
  have hdq : (0 : ℚ) < d := by exact_mod_cast hd
  refine ⟨P.coeff 0, ?_, ?_⟩
  · apply (eq_div_iff (ne_of_gt hdq)).mpr
    simpa only [mul_comm] using he.symm
  · have hh : |((P.coeff 0 : ℤ) : ℚ)| ≤ ((d * B : ℕ) : ℚ) := by
      rw [he, abs_mul, abs_of_nonneg hdq.le]
      exact_mod_cast mul_le_mul_of_nonneg_left hb hdq.le
    have hz : |P.coeff 0| ≤ ((d * B : ℕ) : ℤ) := by exact_mod_cast hh
    rw [← Int.natCast_natAbs] at hz
    exact_mod_cast hz

theorem cardinalSlopes_representation (Q J : ℕ) (t : Fin Q) (c : ℚ)
    (hc : c ∈ cardinalSlopes Q J t.val) : Representation c Q.factorial Q.factorial := by
  obtain ⟨s, hs, hc⟩ := List.mem_flatMap.mp hc
  have hsQ := List.mem_range.mp hs
  obtain ⟨_, he⟩ := List.mem_replicate.mp hc
  subst c
  by_cases hst : s = t.val
  · simp only [hst]
    exact representation_mono (representation_zero Q.factorial) (by omega)
  · simp only [ite_eq_right hst]
    have ht : (t.val : ℚ) + 1 ∈ samplePoints Q :=
      Finset.mem_image.mpr ⟨t, Finset.mem_univ _, rfl⟩
    have hs' : (s : ℚ) + 1 ∈ samplePoints Q :=
      Finset.mem_image.mpr ⟨⟨s, hsQ⟩, Finset.mem_univ _, rfl⟩
    have hne : (s : ℚ) + 1 ≠ (t.val : ℚ) + 1 := by
      intro h
      exact hst (by exact_mod_cast add_right_cancel h)
    simpa only [Nat.mul_one] using representation_of_clears_abs (Nat.factorial_pos Q)
      (sample_inverse_clears ht hs' hne) (sample_inverse_abs ht hs' hne)

theorem cardinalZero_representation (Q J : ℕ) (t : Fin Q) :
    Representation (cardinalZero Q J t.val).value (cardinalDenominator Q J)
      ((Q.factorial * (Q + 1)) ^ (Q * J)) := by
  have hx : (-((t.val + 1 : ℕ) : ℤ)).natAbs ≤ Q := by
    simp only [Int.natAbs_neg, Int.natAbs_natCast]
    omega
  have h := affineValue_representation (-((t.val + 1 : ℕ) : ℤ))
    (cardinalSlopes Q J t.val) Q.factorial Q (Nat.factorial_pos Q) hx
    (fun c hc => cardinalSlopes_representation Q J t c hc)
  simpa only [cardinalZero, cardinalDenominator, cardinalSlopes_length] using h

/-- One denominator and one height cover EVERY node, while the prefix length is observable. -/
def hermiteDenominator (Q J dH : ℕ) : ℕ :=
  cardinalDenominator Q J * (dH * cardinalDenominator Q J ^ J)

/-- Explicit common numerator budget for one fully evaluated scalar node. -/
def hermiteNodeBound (Q J BH : ℕ) : ℕ :=
  ((Q.factorial * (Q + 1)) ^ (Q * J)) *
    (J * (J * BH * inverseBase J (cardinalDenominator Q J)
      (cardinalDenominator Q J * 2 ^ (Q * J)) ^ J) * (Q + 1) ^ J)

/-- Actual node output height from intrinsic cardinal inputs and one H packet bound. -/
theorem hermiteNode_representation (H : Array ℚ) (Q J dH BH : ℕ)
    (hJ : 0 < J) (t : Fin Q)
    (hH : ∀ k < J, Representation (coefficient H k) dH BH) :
    Representation (hermiteNode H Q J t).value (hermiteDenominator Q J dH)
      (hermiteNodeBound Q J BH) := by
  have hx : (-((t.val + 1 : ℕ) : ℤ)).natAbs ≤ Q := by
    simp only [Int.natAbs_neg, Int.natAbs_natCast]
    omega
  have he := quotient_evalPrefix_representation H (cardinalJet Q J t.val).coefficients
    (-((t.val + 1 : ℕ) : ℤ)) dH (cardinalDenominator Q J) BH
    (cardinalDenominator Q J * 2 ^ (Q * J)) J Q J (cardinalDenominator_pos Q J)
    (cardinalJet_constant Q J hJ t) hH
    (fun k hk => cardinalJet_intrinsic_representation Q J hJ t k hk) hx (le_refl _)
  exact representation_mul (cardinalZero_representation Q J t) he

/-- Report-aware executed node summation; callback work is charged, not treated as a free read. -/
def sumReports (node : ℕ → DotReport) : ℕ → DotReport
  | 0 => ⟨0, 0, 0⟩
  | len + 1 =>
      let old := sumReports node len
      let next := node len
      ⟨old.value + next.value, old.arithmetic + next.arithmetic + 1, old.reads + next.reads⟩

theorem sumReports_value (node : ℕ → DotReport) (len : ℕ) :
    (sumReports node len).value = ∑ i ∈ Finset.range len, (node i).value := by
  induction len with
  | zero => simp [sumReports]
  | succ len ih => simp [sumReports, Finset.sum_range_succ, ih]

theorem sumReports_work (node : ℕ → DotReport) (len : ℕ) :
    (sumReports node len).arithmetic = (∑ i ∈ Finset.range len, (node i).arithmetic) + len ∧
      (sumReports node len).reads = ∑ i ∈ Finset.range len, (node i).reads := by
  induction len with
  | zero => simp [sumReports]
  | succ len ih => simp [sumReports, Finset.sum_range_succ, ih]; omega

theorem sumReports_representation (node : ℕ → DotReport) (d B len : ℕ)
    (hnode : ∀ i < len, Representation (node i).value d B) :
    Representation (sumReports node len).value d (len * B) := by
  rw [sumReports_value]
  simpa only [Finset.card_range] using representation_sum (Finset.range len)
    (fun i => (node i).value) d B (fun i hi => hnode i (Finset.mem_range.mp hi))

/-- One intrinsic Hermite-node call for an integer loop index. -/
def indexedNode {Q : ℕ} (H : Fin Q → Array ℚ) (J : ℕ) (i : ℕ) : DotReport :=
  if hi : i < Q then hermiteNode (H ⟨i, hi⟩) Q J ⟨i, hi⟩ else ⟨0, 0, 0⟩

/-- The actual finite Hermite evaluation, including intrinsic cardinal suppliers. -/
def hermite (Q J : ℕ) (H : Fin Q → Array ℚ) : DotReport :=
  sumReports (indexedNode H J) Q

/-- Every node-sum accumulator has ONE denominator shared by all nodes. -/
theorem hermite_prefix_representation (Q J dH BH len : ℕ) (hJ : 0 < J)
    (H : Fin Q → Array ℚ) (hlen : len ≤ Q)
    (hH : ∀ t k, k < J → Representation (coefficient (H t) k) dH BH) :
    Representation (sumReports (indexedNode H J) len).value (hermiteDenominator Q J dH)
      (len * hermiteNodeBound Q J BH) := by
  apply sumReports_representation
  intro i hi
  have hiQ : i < Q := lt_of_lt_of_le hi hlen
  simp only [indexedNode, dite_eq_left hiQ]
  exact hermiteNode_representation (H ⟨i, hiQ⟩) Q J dH BH hJ ⟨i, hiQ⟩ (hH ⟨i, hiQ⟩)

theorem hermite_representation (Q J dH BH : ℕ) (hJ : 0 < J)
    (H : Fin Q → Array ℚ)
    (hH : ∀ t k, k < J → Representation (coefficient (H t) k) dH BH) :
    Representation (hermite Q J H).value (hermiteDenominator Q J dH)
      (Q * hermiteNodeBound Q J BH) :=
  hermite_prefix_representation Q J dH BH Q hJ H (le_refl _) hH

theorem hermite_value_sum (Q J : ℕ) (H : Fin Q → Array ℚ) :
    (hermite Q J H).value = ∑ t : Fin Q, (hermiteNode (H t) Q J t).value := by
  rw [hermite, sumReports_value, Finset.sum_fin_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  simp only [indexedNode]
  split_ifs <;> rfl

/-- Exact scalar Hermite recovery from actual finite Taylor packets. The cardinal
inputs are built internally; only the independently supplied H frontend remains. -/
theorem hermite_correct (Q J : ℕ) (hJ : 0 < J) (P : Polynomial ℚ)
    (hP : P.natDegree < Q * J) (H : Fin Q → Array ℚ)
    (hH : ∀ t, asPolynomial (H t) = taylor ((t.val : ℚ) + 1) P %ₘ X ^ J) :
    (hermite Q J H).value = P.eval 0 := by
  rw [hermite_value_sum]
  have he := explicit_hermite_at_zero (samplePoints Q) J hJ P
    (by simpa only [samplePoints_card] using hP)
  let f : ℚ → ℚ := fun x => (cardinalFactor (samplePoints Q) J x).eval 0 *
    (localQuotient (taylor x P %ₘ X ^ J) (taylor x (cardinalFactor (samplePoints Q) J x)) J).eval (-x)
  have hs : (∑ x ∈ samplePoints Q, f x) = ∑ t : Fin Q, f ((t.val : ℚ) + 1) := by
    rw [samplePoints, Finset.sum_image]
    intro i _ j _ hij
    apply Fin.ext
    exact_mod_cast add_right_cancel hij
  change P.eval 0 = ∑ x ∈ samplePoints Q, f x at he
  rw [hs] at he
  rw [he]
  apply Finset.sum_congr rfl
  intro t _
  rw [hermiteNode_value _ Q J hJ t, hH t]


theorem cardinalJet_work (Q J t : ℕ) :
    (cardinalJet Q J t).arithmetic = Q * J * (J * (J + 1)) + 4 * Q ∧
      (cardinalJet Q J t).reads = Q * J * (J * (J + 1)) := by
  simp only [cardinalJet, buildAffine_work, cardinalSlopes_length]
  trivial

theorem cardinalZero_work (Q J t : ℕ) :
    (cardinalZero Q J t).arithmetic = 3 * (Q * J) + 4 * Q ∧
      (cardinalZero Q J t).reads = Q * J := by
  simp only [cardinalZero, affineValue_work, cardinalSlopes_length]
  trivial

/-- A finite polynomial arithmetic/access budget, including both slope-list suppliers. -/
def nodeWork (Q J : ℕ) : ℕ := Q * J * (J * (J + 1)) + 3 * (Q * J) + 8 * Q +
  3 * J ^ 2 + 4 * J + 2

theorem hermiteNode_work (H : Array ℚ) (Q J : ℕ) (t : Fin Q) :
    (hermiteNode H Q J t).arithmetic ≤ nodeWork Q J ∧
      (hermiteNode H Q J t).reads ≤ nodeWork Q J := by
  have hL := cardinalJet_work Q J t.val
  have hc := cardinalZero_work Q J t.val
  have hq := quotient_work H (cardinalJet Q J t.val).coefficients J
  have he := evalPrefix_work (quotient H (cardinalJet Q J t.val).coefficients J).coefficients
    (-((t.val + 1 : ℕ) : ℤ)) J
  change (cardinalJet Q J t.val).arithmetic + (cardinalZero Q J t.val).arithmetic +
      (quotient H (cardinalJet Q J t.val).coefficients J).arithmetic +
      (evalPrefix (quotient H (cardinalJet Q J t.val).coefficients J).coefficients
        (-((t.val + 1 : ℕ) : ℤ)) J).arithmetic + 1 ≤ _ ∧ _
  dsimp only [hermiteNode, nodeWork]
  constructor <;> omega

theorem hermite_work (Q J : ℕ) (H : Fin Q → Array ℚ) :
    (hermite Q J H).arithmetic ≤ Q * (nodeWork Q J + 1) ∧
      (hermite Q J H).reads ≤ Q * nodeWork Q J := by
  have hs := sumReports_work (indexedNode H J) Q
  have ha : (∑ i ∈ Finset.range Q, (indexedNode H J i).arithmetic) ≤ Q * nodeWork Q J := by
    calc
      _ ≤ ∑ _i ∈ Finset.range Q, nodeWork Q J := by
        apply Finset.sum_le_sum
        intro i hi
        have hiQ := Finset.mem_range.mp hi
        simp only [indexedNode, dite_eq_left hiQ]
        exact (hermiteNode_work _ Q J ⟨i, hiQ⟩).1
      _ = _ := by simp
  have hr : (∑ i ∈ Finset.range Q, (indexedNode H J i).reads) ≤ Q * nodeWork Q J := by
    calc
      _ ≤ ∑ _i ∈ Finset.range Q, nodeWork Q J := by
        apply Finset.sum_le_sum
        intro i hi
        have hiQ := Finset.mem_range.mp hi
        simp only [indexedNode, dite_eq_left hiQ]
        exact (hermiteNode_work _ Q J ⟨i, hiQ⟩).2
      _ = _ := by simp
  change (sumReports (indexedNode H J) Q).arithmetic ≤ _ ∧
    (sumReports (indexedNode H J) Q).reads ≤ _
  rw [hs.1, hs.2]
  constructor <;> nlinarith

/-- Lift power denominators to one fixed public denominator without reducing fractions. -/
theorem representation_power_extend {q : ℚ} (d B n N : ℕ) (hd : 0 < d)
    (hdB : d ≤ B) (hn : n ≤ N) (hq : Representation q (d ^ n) (B ^ n)) :
    Representation q (d ^ N) (B ^ N) := by
  obtain ⟨z, hz, hb⟩ := hq
  refine ⟨z * (d : ℤ) ^ (N - n), ?_, ?_⟩
  · rw [hz]
    have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hd
    have hp : (d : ℚ) ^ N = (d : ℚ) ^ n * (d : ℚ) ^ (N - n) := by
      rw [← pow_add, Nat.add_sub_cancel' hn]
    push_cast
    rw [hp]
    field_simp
  · rw [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast]
    calc
      _ ≤ B ^ n * B ^ (N - n) := by gcongr
      _ = B ^ N := by rw [← pow_add, Nat.add_sub_cancel' hn]

theorem affineArray_representation (c : ℚ) (d : ℕ) (hd : 0 < d)
    (hc : Representation c d d) (k : ℕ) : Representation (coefficient (affineArray c) k) d d := by
  rcases k with _ | k
  · simpa [coefficient, affineArray] using representation_one d hd
  rcases k with _ | k
  · simpa [coefficient, affineArray] using hc
  · rw [coefficient_zero (by change 2 ≤ k + 2; omega)]
    exact representation_mono (representation_zero d) (by omega)

/-- Every recursive array constructed by the intrinsic cardinal builder has a
known power denominator and explicit numerator bound. -/
theorem buildAffine_representation (J d : ℕ) (hd : 0 < d) (cs : List ℚ)
    (hc : ∀ c ∈ cs, Representation c d d) (k : ℕ) (hk : k < J) :
    Representation (coefficient (buildAffine J cs).coefficients k)
      (d ^ cs.length) ((J * d) ^ cs.length) := by
  induction cs generalizing k with
  | nil =>
    change Representation (coefficient #[1] k) 1 1
    rcases k with _ | k
    · simpa [coefficient] using representation_one 1 (by decide)
    · rw [coefficient_zero (by simp)]
      exact representation_mono (representation_zero 1) (by decide)
  | cons c cs ih =>
    have h := multiply_representation (buildAffine J cs).coefficients (affineArray c)
      (d ^ cs.length) d ((J * d) ^ cs.length) d J
      (fun i hi => ih (fun z hz => hc z (List.mem_cons_of_mem c hz)) i hi)
      (fun i _ => affineArray_representation c d hd (hc c List.mem_cons_self) i) k hk
    simpa only [buildAffine, List.length_cons, pow_succ, Nat.mul_assoc, Nat.mul_left_comm,
      Nat.mul_comm] using h

/-- Uniform bound for EVERY recursive suffix array, using the final node denominator. -/
theorem cardinalJet_suffix_representation (Q J : ℕ) (hJ : 0 < J) (t : Fin Q) (s k : ℕ)
    (hk : k < J) :
    Representation (coefficient (buildAffine J ((cardinalSlopes Q J t.val).drop s)).coefficients k)
      (cardinalDenominator Q J) ((J * Q.factorial) ^ (Q * J)) := by
  apply representation_power_extend Q.factorial (J * Q.factorial)
    ((cardinalSlopes Q J t.val).drop s).length (Q * J) (Nat.factorial_pos Q)
  · nlinarith
  · rw [List.length_drop, cardinalSlopes_length]
    omega
  · apply buildAffine_representation J Q.factorial (Nat.factorial_pos Q)
    · intro c hc
      exact cardinalSlopes_representation Q J t c (List.mem_of_mem_drop hc)
    · exact hk

/-- Uniform bound for EVERY scalar cardinal-product suffix accumulator. -/
theorem cardinalZero_suffix_representation (Q J : ℕ) (t : Fin Q) (s : ℕ) :
    Representation (affineValue (-((t.val + 1 : ℕ) : ℤ))
      ((cardinalSlopes Q J t.val).drop s)).value (cardinalDenominator Q J)
      ((Q.factorial * (Q + 1)) ^ (Q * J)) := by
  apply representation_power_extend Q.factorial (Q.factorial * (Q + 1))
    ((cardinalSlopes Q J t.val).drop s).length (Q * J) (Nat.factorial_pos Q)
  · nlinarith
  · rw [List.length_drop, cardinalSlopes_length]
    omega
  · apply affineValue_representation _ _ _ Q (Nat.factorial_pos Q)
    · simp only [Int.natAbs_neg, Int.natAbs_natCast]
      omega
    · intro c hc
      exact cardinalSlopes_representation Q J t c (List.mem_of_mem_drop hc)

/-- Every partial multiply accumulator after cached inversion shares the quotient denominator. -/
theorem quotient_dotPrefix_representation (H L : Array ℚ) (dH dL BH BL J n len : ℕ)
    (hdL : 0 < dL) (hL0 : coefficient L 0 = 1)
    (hH : ∀ i < J, Representation (coefficient H i) dH BH)
    (hL : ∀ i < J, Representation (coefficient L i) dL BL)
    (hn : n < J) (hlen : len ≤ n) :
    Representation (dotPrefix H (inverse L J).coefficients (n - 1) len).value
      (dH * dL ^ J) (len * BH * inverseBase J dL BL ^ J) := by
  apply dotPrefix_common_representation
  · intro i hi
    exact hH (i + 1) (by omega)
  · intro i hi
    exact cached_inverse_common_representation L dL BL J hdL hL0 hL (n - 1 - i) (by omega)

/-- Cached powers in scalar evaluation are integral at EVERY prefix. -/
theorem evalPrefix_power_representation (a : Array ℚ) (x : ℤ) (T len : ℕ)
    (hx : x.natAbs ≤ T) : Representation (evalPrefix a x len).power 1 (T ^ len) := by
  rw [evalPrefix_power]
  have h := representation_integer (x ^ len)
  apply representation_mono (by simpa only [Int.cast_pow] using h)
  rw [Int.natAbs_pow]
  exact Nat.pow_le_pow_left hx _

/-- Actual cardinal common-denominator exponent. -/
def cardinalBits (Q J : ℕ) : ℕ := Nat.clog 2 Q * Q * (Q * J)
/-- A literal height exponent for the cached normalized inverse base. -/
def inverseBits (Q J : ℕ) : ℕ := cardinalBits Q J + Q * J + Nat.clog 2 (J + 1) + 3
/-- Height exponent for the scalar cardinal-at-zero product. -/
def cardinalZeroBits (Q J : ℕ) : ℕ := (Nat.clog 2 Q * Q + Nat.clog 2 (Q + 1)) * (Q * J)
/-- Common final denominator exponent when the supplied H denominator is at most 2^b. -/
def hermiteDenominatorBits (Q J b : ℕ) : ℕ := b + cardinalBits Q J * (J + 1)
/-- Explicit polynomial expression bounding all final node-sum numerators. -/
def hermiteNumeratorBits (Q J b : ℕ) : ℕ :=
  Nat.clog 2 (Q + 1) + cardinalZeroBits Q J + 2 * Nat.clog 2 (J + 1) + b +
    inverseBits Q J * J + Nat.clog 2 (Q + 1) * J

theorem factorial_dyadic (Q : ℕ) : Q.factorial ≤ 2 ^ (Nat.clog 2 Q * Q) := by
  calc
    _ ≤ Q ^ Q := Nat.factorial_le_pow Q
    _ ≤ (2 ^ Nat.clog 2 Q) ^ Q := Nat.pow_le_pow_left (Nat.le_pow_clog (by decide) Q) Q
    _ = _ := by rw [← pow_mul]

theorem cardinalDenominator_dyadic (Q J : ℕ) :
    cardinalDenominator Q J ≤ 2 ^ cardinalBits Q J := cardinalDenominator_le_power Q J

theorem inverseBase_dyadic (Q J : ℕ) :
    inverseBase J (cardinalDenominator Q J) (cardinalDenominator Q J * 2 ^ (Q * J)) ≤
      2 ^ inverseBits Q J := by
  let e := cardinalBits Q J + Q * J
  let j := Nat.clog 2 (J + 1)
  have hd := cardinalDenominator_dyadic Q J
  have hd' : cardinalDenominator Q J ≤ 2 ^ e :=
    hd.trans (Nat.pow_le_pow_right (by decide) (by dsimp [e]; omega))
  have hB : cardinalDenominator Q J * 2 ^ (Q * J) ≤ 2 ^ e := by
    dsimp [e]
    rw [pow_add]
    exact Nat.mul_le_mul_right _ hd
  have hj : J ≤ 2 ^ j := (Nat.le_succ J).trans (Nat.le_pow_clog (by decide) _)
  have h1 : 1 ≤ 2 ^ e := Nat.one_le_pow _ _ (by decide)
  have hi : cardinalDenominator Q J + cardinalDenominator Q J * 2 ^ (Q * J) + 1 ≤
      2 ^ (e + 2) := by
    rw [pow_add]
    norm_num
    nlinarith
  have hm := Nat.mul_le_mul hj hi
  have heq : 2 ^ j * 2 ^ (e + 2) = 2 ^ (j + e + 2) := by simp only [pow_add, Nat.mul_assoc]
  rw [heq] at hm
  have hpos : 1 ≤ 2 ^ (j + e + 2) := Nat.one_le_pow _ _ (by decide)
  unfold inverseBase
  have hstep : J * (cardinalDenominator Q J + cardinalDenominator Q J * 2 ^ (Q * J) + 1) + 1 ≤
      2 ^ (j + e + 3) := by
    rw [show j + e + 3 = (j + e + 2) + 1 by omega, pow_succ]
    nlinarith
  convert hstep using 1
  unfold inverseBits e j
  congr 1
  omega

theorem cardinalZeroBound_dyadic (Q J : ℕ) :
    (Q.factorial * (Q + 1)) ^ (Q * J) ≤ 2 ^ cardinalZeroBits Q J := by
  calc
    _ ≤ (2 ^ (Nat.clog 2 Q * Q) * 2 ^ Nat.clog 2 (Q + 1)) ^ (Q * J) := by
      gcongr
      · exact factorial_dyadic Q
      · exact Nat.le_pow_clog (by decide) _
    _ = _ := by rw [← pow_add, ← pow_mul]; rfl

/-- Concrete polynomial-bit denominator bound for the actual scalar evaluator. -/
theorem hermiteDenominator_dyadic (Q J dH b : ℕ) (hdH : dH ≤ 2 ^ b) :
    hermiteDenominator Q J dH ≤ 2 ^ hermiteDenominatorBits Q J b := by
  unfold hermiteDenominator
  calc
    _ ≤ 2 ^ cardinalBits Q J * (2 ^ b * (2 ^ cardinalBits Q J) ^ J) := by
      gcongr
      · exact cardinalDenominator_dyadic Q J
      · exact cardinalDenominator_dyadic Q J
    _ = _ := by rw [← pow_mul, ← pow_add, ← pow_add]; congr 1; unfold hermiteDenominatorBits; ring

/-- Concrete polynomial-bit numerator bound, with no H-packet value identity assumed. -/
theorem hermiteNodeBound_dyadic (Q J BH b : ℕ) (hBH : BH ≤ 2 ^ b) :
    Q * hermiteNodeBound Q J BH ≤ 2 ^ hermiteNumeratorBits Q J b := by
  let q := Nat.clog 2 (Q + 1)
  let j := Nat.clog 2 (J + 1)
  have hq : Q ≤ 2 ^ q := (Nat.le_succ Q).trans (Nat.le_pow_clog (by decide) _)
  have hj : J ≤ 2 ^ j := (Nat.le_succ J).trans (Nat.le_pow_clog (by decide) _)
  have hq1 : Q + 1 ≤ 2 ^ q := Nat.le_pow_clog (by decide) _
  have hi := inverseBase_dyadic Q J
  have hc := cardinalZeroBound_dyadic Q J
  unfold hermiteNodeBound
  calc
    _ ≤ 2 ^ q * (2 ^ cardinalZeroBits Q J *
        (2 ^ j * (2 ^ j * 2 ^ b * (2 ^ inverseBits Q J) ^ J) * (2 ^ q) ^ J)) := by
      gcongr
    _ = _ := by
      rw [← pow_mul, ← pow_mul]
      simp only [← pow_add]
      congr 1
      unfold hermiteNumeratorBits q j
      ring

/-- Reduced output integer lengths follow from the explicit common representations. -/
theorem hermite_output_dyadic (Q J dH BH b : ℕ) (hJ : 0 < J) (hdH : 0 < dH)
    (hdHbits : dH ≤ 2 ^ b) (hBHbits : BH ≤ 2 ^ b) (H : Fin Q → Array ℚ)
    (hH : ∀ t k, k < J → Representation (coefficient (H t) k) dH BH) :
    (hermite Q J H).value.den ≤ 2 ^ hermiteDenominatorBits Q J b ∧
      (hermite Q J H).value.num.natAbs ≤ 2 ^ hermiteNumeratorBits Q J b := by
  have hrep := hermite_representation Q J dH BH hJ H hH
  have hd : 0 < hermiteDenominator Q J dH := by
    unfold hermiteDenominator
    exact Nat.mul_pos (cardinalDenominator_pos Q J) (Nat.mul_pos hdH (Nat.pow_pos (cardinalDenominator_pos Q J)))
  have hr := representation_reduced_bound hd hrep
  exact ⟨hr.1.trans (hermiteDenominator_dyadic Q J dH b hdHbits),
    hr.2.trans (hermiteNodeBound_dyadic Q J BH b hBHbits)⟩

/-- Every partial convolution while building an affine packet has the same
height scale as the completed next array. -/
theorem buildAffine_dotPrefix_representation (J d : ℕ) (hd : 0 < d)
    (cs : List ℚ) (hc : ∀ c ∈ cs, Representation c d d) (c : ℚ) (hcc : Representation c d d)
    (n len : ℕ) (hn : n < J) (hlen : len ≤ n) :
    Representation (dotPrefix (buildAffine J cs).coefficients (affineArray c) (n - 1) len).value
      (d ^ (cs.length + 1)) ((J * d) ^ (cs.length + 1)) := by
  have h := dotPrefix_common_representation (buildAffine J cs).coefficients (affineArray c)
    (d ^ cs.length) d ((J * d) ^ cs.length) d (n - 1) len
    (fun i hi => buildAffine_representation J d hd cs hc (i + 1) (by omega))
    (fun i _ => affineArray_representation c d hd hcc (n - 1 - i))
  rw [pow_succ, pow_succ]
  apply representation_mono h
  have hl : len ≤ J := by omega
  calc
    len * (J * d) ^ cs.length * d ≤ J * (J * d) ^ cs.length * d :=
      Nat.mul_le_mul_right d (Nat.mul_le_mul_right _ hl)
    _ = (J * d) ^ cs.length * (J * d) := by ring

/-- Normalized inverse recurrence partial sums are represented before rational reduction. -/
theorem inverse_dotPrefix_representation (a : Array ℚ) (d B J n len : ℕ) (hd : 0 < d)
    (ha0 : coefficient a 0 = 1) (ha : ∀ i < J, Representation (coefficient a i) d B)
    (hn : n + 1 < J) (hlen : len ≤ n + 1) :
    Representation (dotPrefix a (inverse a (n + 1)).coefficients n len).value
      (d ^ J) (inverseBase J d B ^ J) := by
  have hdH : d ≤ inverseBase J d B := by unfold inverseBase; nlinarith
  have h := dotPrefix_representation a (inverse a (n + 1)).coefficients d B
    (inverseBase J d B) n len hd hdH hlen (fun i hi => ha (i + 1) (by omega)) (by
      intro i hi
      rw [inverse_coefficient a (n + 1) (n - i) (by omega)]
      exact inverseCoeff_representation (coefficient a) d B J hd ha0 ha (n - i) (by omega))
  have hb : len * B ≤ inverseBase J d B := by unfold inverseBase; nlinarith
  have h' : Representation (dotPrefix a (inverse a (n + 1)).coefficients n len).value
      (d ^ (n + 1)) (inverseBase J d B ^ (n + 1)) := by
    apply representation_mono h
    simpa only [pow_succ, Nat.mul_comm] using Nat.mul_le_mul_right (inverseBase J d B ^ n) hb
  exact representation_power_extend d (inverseBase J d B) (n + 1) J hd hdH (by omega) h'

/-- Binary lengths of EVERY node-sum prefix, not solely the completed sum. -/
theorem hermite_prefix_dyadic (Q J dH BH b len : ℕ) (hJ : 0 < J) (hdH : 0 < dH)
    (hdHbits : dH ≤ 2 ^ b) (hBHbits : BH ≤ 2 ^ b) (H : Fin Q → Array ℚ)
    (hlen : len ≤ Q)
    (hH : ∀ t k, k < J → Representation (coefficient (H t) k) dH BH) :
    (sumReports (indexedNode H J) len).value.den ≤ 2 ^ hermiteDenominatorBits Q J b ∧
      (sumReports (indexedNode H J) len).value.num.natAbs ≤ 2 ^ hermiteNumeratorBits Q J b := by
  have hrep := hermite_prefix_representation Q J dH BH len hJ H hlen hH
  have hd : 0 < hermiteDenominator Q J dH := by
    unfold hermiteDenominator
    exact Nat.mul_pos (cardinalDenominator_pos Q J) (Nat.mul_pos hdH (Nat.pow_pos (cardinalDenominator_pos Q J)))
  have hr := representation_reduced_bound hd hrep
  refine ⟨hr.1.trans (hermiteDenominator_dyadic Q J dH b hdHbits), hr.2.trans ?_⟩
  exact (Nat.mul_le_mul_right (hermiteNodeBound Q J BH) hlen).trans
    (hermiteNodeBound_dyadic Q J BH b hBHbits)

theorem clog_two_succ_of_dyadic {v e : ℕ} (h : v ≤ 2 ^ e) : Nat.clog 2 (v + 1) ≤ e + 1 := by
  apply Nat.clog_le_of_le_pow
  have hp : 1 ≤ 2 ^ e := Nat.one_le_pow _ _ (by decide)
  rw [pow_succ]
  omega

theorem hermite_prefix_bit_lengths (Q J dH BH b len : ℕ) (hJ : 0 < J) (hdH : 0 < dH)
    (hdHbits : dH ≤ 2 ^ b) (hBHbits : BH ≤ 2 ^ b) (H : Fin Q → Array ℚ)
    (hlen : len ≤ Q)
    (hH : ∀ t k, k < J → Representation (coefficient (H t) k) dH BH) :
    Nat.clog 2 ((sumReports (indexedNode H J) len).value.den + 1) ≤ hermiteDenominatorBits Q J b + 1 ∧
      Nat.clog 2 ((sumReports (indexedNode H J) len).value.num.natAbs + 1) ≤ hermiteNumeratorBits Q J b + 1 := by
  have h := hermite_prefix_dyadic Q J dH BH b len hJ hdH hdHbits hBHbits H hlen hH
  exact ⟨clog_two_succ_of_dyadic h.1, clog_two_succ_of_dyadic h.2⟩

theorem clog_two_le_self (v : ℕ) : Nat.clog 2 v ≤ v :=
  Nat.clog_le_of_le_pow (Nat.le_of_lt v.lt_two_pow_self)

/-- The displayed output/prefix bit budgets are genuinely polynomial in the
public dimensions and the common input bit budget. -/
theorem hermite_bits_polynomial (Q J b : ℕ) :
    hermiteDenominatorBits Q J b ≤ b + 16 * (Q + J + 1) ^ 5 ∧
      hermiteNumeratorBits Q J b ≤ b + 16 * (Q + J + 1) ^ 5 := by
  let S := Q + J + 1
  have hS : 1 ≤ S := by dsimp [S]; omega
  have hQ : Q ≤ S := by dsimp [S]; omega
  have hJ : J ≤ S := by dsimp [S]; omega
  have hJ1 : J + 1 ≤ S := by dsimp [S]; omega
  have hc : Nat.clog 2 Q ≤ S := (clog_two_le_self Q).trans hQ
  have hq : Nat.clog 2 (Q + 1) ≤ S := (clog_two_le_self _).trans (by dsimp [S]; omega)
  have hj : Nat.clog 2 (J + 1) ≤ S := (clog_two_le_self _).trans hJ1
  have h2 : Q * J ≤ S ^ 2 := by calc
    _ ≤ S * S := Nat.mul_le_mul hQ hJ
    _ = _ := by ring
  have hcard : cardinalBits Q J ≤ S ^ 4 := by
    unfold cardinalBits
    calc
      _ ≤ S * S * (S * S) := by gcongr
      _ = _ := by ring
  have hS2 : S ≤ S ^ 2 := by simpa using Nat.pow_le_pow_right (by omega : 0 < S) (show 1 ≤ 2 by decide)
  have hS4 : S ≤ S ^ 4 := by simpa using Nat.pow_le_pow_right (by omega : 0 < S) (show 1 ≤ 4 by decide)
  have h24 : S ^ 2 ≤ S ^ 4 := Nat.pow_le_pow_right (by omega) (by decide)
  have h14 : 1 ≤ S ^ 4 := Nat.one_le_pow _ _ (by omega)
  have hinv : inverseBits Q J ≤ 6 * S ^ 4 := by
    unfold inverseBits
    nlinarith
  have hz : cardinalZeroBits Q J ≤ 2 * S ^ 4 := by
    unfold cardinalZeroBits
    calc
      _ ≤ (S * S + S) * (S * S) := by gcongr
      _ ≤ (2 * (S * S)) * (S * S) := by
        exact Nat.mul_le_mul_right _ (by nlinarith [hS2])
      _ = _ := by ring
  have hS5 : S ≤ S ^ 5 := by simpa using Nat.pow_le_pow_right (by omega : 0 < S) (show 1 ≤ 5 by decide)
  have h25 : S ^ 2 ≤ S ^ 5 := Nat.pow_le_pow_right (by omega) (by decide)
  have h45 : S ^ 4 ≤ S ^ 5 := Nat.pow_le_pow_right (by omega) (by decide)
  constructor
  · unfold hermiteDenominatorBits
    have hh := Nat.mul_le_mul hcard hJ1
    have he : S ^ 4 * S = S ^ 5 := by ring
    rw [he] at hh
    dsimp [S] at hh
    nlinarith
  · have hh : hermiteNumeratorBits Q J b ≤
        S + 2 * S ^ 4 + 2 * S + b + (6 * S ^ 4) * S + S * S := by
      unfold hermiteNumeratorBits
      gcongr
    have he : (6 * S ^ 4) * S = 6 * S ^ 5 := by ring
    rw [he] at hh
    change hermiteNumeratorBits Q J b ≤ b + 16 * S ^ 5
    nlinarith

end RiemannGaussian.SemiprimeHermiteArrayHeight

