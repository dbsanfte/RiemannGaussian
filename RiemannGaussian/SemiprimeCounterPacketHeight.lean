/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeCounterCompose
import RiemannGaussian.SemiprimeTaylorHeight
import RiemannGaussian.SemiprimeStreamingTensorHeight
import RiemannGaussian.SemiprimeCounterEnumeration

/-!
# Fixed-denominator heights of actual corrected counter packets

Integer numerator packets are constructed from native source rows. Products use
one denominator power per incidence; partial finite sums keep that denominator.
-/
set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace RiemannGaussian.SemiprimeCounterPacketHeight
open scoped BigOperators
open Polynomial
open SemiprimeBooleanDiagonal SemiprimeCounterNative SemiprimeCounterCompose
open SemiprimeCounterFiltration SemiprimeStreamingTensor
open SemiprimeSourceRowHeight SemiprimeTaylorHeight SemiprimeJetArrayHeight SemiprimeHermiteRecovery SemiprimeJetRecurrence
open SemiprimeStreamingTensorHeight
attribute [local instance] Classical.propDecidable

/-- A scalar base and the actual positive-degree correction coefficients. -/
def packet {C : Type*} [Semiring C] (base : C) (R : ℕ) (coeff : ℕ → C) : Polynomial C :=
  Polynomial.C base + ∑ k ∈ Finset.range R, monomial (k+1) (coeff k)

/-- Every coefficient is either the base or one positive-degree coefficient. -/
theorem packet_coeff {C : Type*} [Semiring C] (base : C) (R : ℕ) (coeff : ℕ → C) (k : ℕ) :
    (packet base R coeff).coeff k =
      if k=0 then base else if k-1<R then coeff (k-1) else 0 := by
  cases k with
  | zero => simp [packet]
  | succ k => simp [packet, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]

/-- Common scaling commutes with the finite corrected-packet frontend. -/
theorem packet_scale {C : Type*} [CommSemiring C] (d base : C) (R : ℕ) (coeff : ℕ → C) :
    Polynomial.C d * packet base R coeff = packet (d*base) R (fun k => d*coeff k) := by
  ext k
  rw [Polynomial.coeff_C_mul, packet_coeff, packet_coeff]
  split_ifs <;> simp

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E]

/-- Literal corrected port used by fibrePacket, before truncation. -/
def correctedPort (rows : V → Polynomial ℚ) (t : ℚ) (R : ℕ) (x U : Finset V) : Polynomial ℚ :=
  packet (∑ v, (rows v).eval t * indicator x v) R
    (fun k => ∑ v, (taylor t (rows v)).coeff (k+1) * indicator U v)

/-- Integer corrected port with the same independent Boolean base and correction. -/
def inputNumerator (P : V → Polynomial ℤ) (t : ℤ) (R : ℕ) (x U : Finset V) : Polynomial ℤ :=
  packet (∑ v, (taylor t (P v)).coeff 0 * indicator x v) R
    (fun k => ∑ v, (taylor t (P v)).coeff (k+1) * indicator U v)

omit [Fintype E] in
/-- Native corrected ports are exactly the literal frontend of fibrePacket. -/
theorem correctedPort_native (arity : E → ℕ)
    (rows : (e : E) → Fin (arity e) → V → Polynomial ℚ)
    (t : ℚ) (R : ℕ) (x U : Finset V) (e : E) (i : Fin (arity e)) :
    correctedPort (rows e i) t R x U =
      C (∑ v, (rows e i v).eval t * indicator x v) + nativeCorrection arity rows t R U e i := rfl

/-- The actual integer input has one shared row denominator, not a new one per sum. -/
theorem inputNumerator_map (P : V → Polynomial ℤ) (rows : V → Polynomial ℚ)
    (d : ℕ) (hP : ∀ v, (P v).map (Int.castRingHom ℚ) = C (d : ℚ) * rows v)
    (t : ℤ) (R : ℕ) (x U : Finset V) :
    (inputNumerator P t R x U).map (Int.castRingHom ℚ) =
      C (d : ℚ) * correctedPort rows (t : ℚ) R x U := by
  have hc (v : V) (k : ℕ) :
      (((taylor t (P v)).coeff k : ℤ) : ℚ) = (d : ℚ) * (taylor (t : ℚ) (rows v)).coeff k := by
    have h := congrArg (fun p : Polynomial ℚ => p.coeff k) (map_taylor_cleared (P v) (rows v) d (hP v) t)
    simp only [Polynomial.coeff_map, Polynomial.coeff_C_mul] at h
    change (((taylor t (P v)).coeff k : ℤ) : ℚ) = _ at h
    exact h
  have hm (S : Finset V) (k : ℕ) :
      ((∑ v, (taylor t (P v)).coeff k * (indicator S v : ℤ) : ℤ) : ℚ) =
        (d : ℚ) * ∑ v, (taylor (t : ℚ) (rows v)).coeff k * indicator S v := by
    simp only [Int.cast_sum, Int.cast_mul, hc, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    simp only [indicator]
    split_ifs <;> simp
  unfold correctedPort
  rw [packet_scale]
  simp only [inputNumerator, packet, Polynomial.map_add,
    Polynomial.map_sum, Polynomial.map_C, Polynomial.map_monomial]
  congr 1
  · congr 1
    change ((∑ v, (taylor t (P v)).coeff 0 * (indicator x v : ℤ) : ℤ) : ℚ) = _
    simpa only [taylor_coeff_zero] using hm x 0
  · apply Finset.sum_congr rfl
    intro k _
    congr 1
    change ((∑ v, (taylor t (P v)).coeff (k+1) * (indicator U v : ℤ) : ℤ) : ℚ) = _
    exact hm U (k+1)

/-- A Boolean-weighted coefficient sum costs a factor card V, not extra denominators. -/
theorem abs_indicator_sum_le (f : V → ℤ) (S : Finset V) (B : ℕ)
    (hf : ∀ v, |f v| ≤ (B : ℤ)) :
    |∑ v, f v * (indicator S v : ℤ)| ≤ (Fintype.card V * B : ℕ) := by
  calc
    _ ≤ ∑ v, |f v * (indicator S v : ℤ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _v : V, (B : ℤ) := by
      apply Finset.sum_le_sum
      intro v _
      simp only [indicator]
      split_ifs
      · simpa using hf v
      · simp
    _ = _ := by simp

/-- Every corrected input coefficient, including the independent constant, is bounded. -/
theorem inputNumerator_bound (P : V → Polynomial ℤ) (t : ℤ) (R B T : ℕ)
    (hp : ∀ v, (P v).natDegree ≤ R) (hb : ∀ v k, |(P v).coeff k| ≤ (B : ℤ))
    (ht : |t| ≤ (T : ℤ)) (x U : Finset V) (k : ℕ) :
    |(inputNumerator P t R x U).coeff k| ≤
      (Fintype.card V * shiftBound R B T : ℕ) := by
  rw [inputNumerator, packet_coeff]
  split_ifs
  · exact abs_indicator_sum_le _ x _ (fun v => integer_taylor_bound (P v) R B T (hp v) (hb v) t ht 0)
  · exact abs_indicator_sum_le _ U _ (fun v => integer_taylor_bound (P v) R B T (hp v) (hb v) t ht _)
  · positivity

/-- Actual native rows supply every integer numerator premise of the port bound. -/
theorem builtLayout_correctedPort_representation
    {I F : Type} [Fintype I] [DecidableEq I] [DecidableEq F]
    {r Q : ℕ} (owner : I → V) (factor : I → F)
    (en : SemiprimeSourceLayout.Enumerations I V F r Q) (ε : ℚ) (R B T : ℕ)
    (howner : ∀ v, (Finset.univ.filter (fun i => owner i = v)).card ≤ B)
    (hQ : 1 ≤ Q) (hAQ : OAI.Algorithms.SubexponentialSAT.Subexp.TailInterval.intervalStart r Q R ≤ Q)
    (i : I) (t : ℤ) (ht : |t| ≤ (T : ℤ)) (x U : Finset V) :
    ∃ P : Polynomial ℤ,
      P.map (Int.castRingHom ℚ) = C (rowDenominator Q R : ℚ) *
        correctedPort ((SemiprimeSourceLayout.builtLayout owner factor en ε R).row i) (t : ℚ) R x U ∧
      ∀ k, |P.coeff k| ≤ (Fintype.card V * shiftBound R (B*2^rowNumeratorExponent Q R) T : ℕ) := by
  choose P hP hp hb using fun v => builtLayout_row_representation owner factor en ε R B howner hQ hAQ i v
  refine ⟨inputNumerator P t R x U, inputNumerator_map P _ _ hP t R x U, ?_⟩
  exact inputNumerator_bound P t R _ T hp hb ht x U

/-- Actual local factor product on independent Boolean base/correction subsets. -/
def nativeTerm (arity : E → ℕ)
    (T : (e : E) → (Fin (arity e) → Bool) → ℤ)
    (rows : (e : E) → Fin (arity e) → V → Polynomial ℚ)
    (t : ℚ) (R : ℕ) (x : E → Finset V) (U : Finset V) : Polynomial ℚ :=
  ∏ e, evaluate (arity e) (fun a => C (T e a : ℚ))
    (fun i => correctedPort (rows e i) t R (x e) U)

/-- Literal integer product of the actual streamed local numerator recursions. -/
def termNumerator (arity : E → ℕ)
    (T : (e : E) → (Fin (arity e) → Bool) → ℤ)
    (P : (e : E) → Fin (arity e) → V → Polynomial ℤ)
    (d : ℕ) (t : ℤ) (R : ℕ) (x : E → Finset V) (U : Finset V) : Polynomial ℤ :=
  ∏ e, polynomialNumerator (d : ℤ) (arity e) (T e)
    (fun i => inputNumerator (P e i) t R (x e) U)

/-- Each complete term has exactly the total-incidence denominator power. -/
theorem termNumerator_map (arity : E → ℕ)
    (T : (e : E) → (Fin (arity e) → Bool) → ℤ)
    (P : (e : E) → Fin (arity e) → V → Polynomial ℤ)
    (rows : (e : E) → Fin (arity e) → V → Polynomial ℚ)
    (d : ℕ) (hd : 0 < d)
    (hP : ∀ e i v, (P e i v).map (Int.castRingHom ℚ) = C (d : ℚ) * rows e i v)
    (t : ℤ) (R : ℕ) (x : E → Finset V) (U : Finset V) :
    (termNumerator arity T P d t R x U).map (Int.castRingHom ℚ) =
      C ((d : ℚ)^(∑ e, arity e)) * nativeTerm arity T rows (t : ℚ) R x U := by
  have hdZ : (d : ℤ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hd
  have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hd
  have hlocal (e : E) :
      (polynomialNumerator (d : ℤ) (arity e) (T e)
        (fun i => inputNumerator (P e i) t R (x e) U)).map (Int.castRingHom ℚ) =
      C ((d : ℚ)^arity e) * evaluate (arity e) (fun a => C (T e a : ℚ))
        (fun i => correctedPort (rows e i) (t : ℚ) R (x e) U) := by
    rw [polynomialNumerator_map (d : ℤ) hdZ]
    simp only [Int.cast_natCast]
    congr 1
    congr 1
    funext i
    rw [inputNumerator_map (P e i) (rows e i) d (hP e i)]
    rw [← mul_assoc, ← C_mul, inv_mul_cancel₀ hdq, C_1, one_mul]
  simp only [termNumerator, Polynomial.map_prod, hlocal, nativeTerm,
    Finset.prod_mul_distrib, ← map_prod, Finset.prod_pow_eq_pow_sum]

/-- Uniform full-term coefficient envelope, before any assignment/support sums. -/
def termBound (arity : E → ℕ) (d R B T J : ℕ) : ℕ :=
  J^Fintype.card E * (J*(d+2*(Fintype.card V*shiftBound R B T)))^(∑ e, arity e)

/-- Native corrected factors have bounded integer coefficients at every retained index. -/
theorem termNumerator_bound (arity : E → ℕ)
    (Tentry : (e : E) → (Fin (arity e) → Bool) → ℤ)
    (P : (e : E) → Fin (arity e) → V → Polynomial ℤ)
    (d tR B T J : ℕ) (t : ℤ) (hJ : 1 ≤ J)
    (hentry : ∀ e a, |Tentry e a| ≤ 1)
    (hp : ∀ e i v, (P e i v).natDegree ≤ tR)
    (hb : ∀ e i v k, |(P e i v).coeff k| ≤ (B : ℤ))
    (ht : |t| ≤ (T : ℤ)) (x : E → Finset V) (U : Finset V) (k : ℕ) (hk : k < J) :
    |(termNumerator arity Tentry P d t tR x U).coeff k| ≤
      (termBound (V := V) arity d tR B T J : ℤ) := by
  have hbase : 0 ≤ (J : ℤ)*((d : ℤ)+2*(Fintype.card V*shiftBound tR B T : ℕ)) := by positivity
  have h := abs_coeff_prod_le Finset.univ
    (fun e => polynomialNumerator (d : ℤ) (arity e) (Tentry e)
      (fun i => inputNumerator (P e i) t tR (x e) U)) J hJ
    (fun e => ((J : ℤ)*((d : ℤ)+2*(Fintype.card V*shiftBound tR B T : ℕ)))^arity e)
    (fun e => pow_nonneg hbase _) (by
      intro e _
      have hi := abs_coeff_polynomialNumerator_le (d : ℤ) (arity e) J (Tentry e)
        (fun i => inputNumerator (P e i) t tR (x e) U)
        (Fintype.card V*shiftBound tR B T : ℕ) (by positivity) (hentry e)
        (fun i k _ => inputNumerator_bound (P e i) t tR B T (hp e i) (hb e i) ht (x e) U k)
      simpa only [Int.abs_natCast] using hi) k hk
  simpa only [termNumerator, termBound, Finset.card_univ, Finset.prod_pow_eq_pow_sum,
    Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_ofNat] using h

/-- Any partial finite signed sum retains the SAME full incidence denominator. -/
theorem signed_terms_representation {X : Type*} (s : Finset X) (arity : E → ℕ)
    (Tentry : (e : E) → (Fin (arity e) → Bool) → ℤ)
    (P : (e : E) → Fin (arity e) → V → Polynomial ℤ)
    (rows : (e : E) → Fin (arity e) → V → Polynomial ℚ)
    (d R B T J : ℕ) (hd : 0 < d) (hJ : 1 ≤ J)
    (hP : ∀ e i v, (P e i v).map (Int.castRingHom ℚ) = C (d : ℚ)*rows e i v)
    (hp : ∀ e i v, (P e i v).natDegree ≤ R)
    (hb : ∀ e i v k, |(P e i v).coeff k| ≤ (B : ℤ))
    (hentry : ∀ e a, |Tentry e a| ≤ 1)
    (t : ℤ) (ht : |t| ≤ (T : ℤ)) (base : X → E → Finset V) (correction : X → Finset V)
    (weight : X → ℤ) (hw : ∀ a ∈ s, |weight a| ≤ 1) (k : ℕ) (hk : k < J) :
    Representation ((∑ a ∈ s, C (weight a : ℚ) *
      nativeTerm arity Tentry rows (t : ℚ) R (base a) (correction a)).coeff k)
      (d^(∑ e, arity e)) (s.card*termBound (V := V) arity d R B T J) := by
  classical
  let N : Polynomial ℤ := ∑ a ∈ s, C (weight a) *
    termNumerator arity Tentry P d t R (base a) (correction a)
  have hmap : N.map (Int.castRingHom ℚ) = C ((d : ℚ)^(∑ e, arity e)) *
      ∑ a ∈ s, C (weight a : ℚ) * nativeTerm arity Tentry rows (t : ℚ) R (base a) (correction a) := by
    simp only [N, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C,
      termNumerator_map arity Tentry P rows d hd hP, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    change C (weight a : ℚ) * (C ((d : ℚ)^_) * _) = _
    ring
  refine ⟨N.coeff k, ?_, ?_⟩
  · have he := congrArg (fun p : Polynomial ℚ => p.coeff k) hmap
    simp only [Polynomial.coeff_map, Polynomial.coeff_C_mul] at he
    change ((N.coeff k : ℤ) : ℚ) = _ at he
    apply (eq_div_iff (by exact_mod_cast Nat.ne_of_gt (pow_pos hd _))).mpr
    simpa only [Nat.cast_pow, mul_comm] using he.symm
  · have hbound (a : X) (ha : a ∈ s) :
        |(C (weight a) * termNumerator arity Tentry P d t R (base a) (correction a)).coeff k| ≤
          (termBound (V := V) arity d R B T J : ℤ) := by
      rw [Polynomial.coeff_C_mul, abs_mul]
      exact (mul_le_mul_of_nonneg_right (hw a ha) (abs_nonneg _)).trans
        (by simpa only [one_mul] using termNumerator_bound arity Tentry P d R B T J t hJ hentry hp hb ht _ _ k hk)
    have hsum : |N.coeff k| ≤ (s.card*termBound (V := V) arity d R B T J : ℕ) := by
      simp only [N, Polynomial.finsetSum_coeff]
      calc
        _ ≤ ∑ a ∈ s, |(C (weight a)*termNumerator arity Tentry P d t R (base a) (correction a)).coeff k| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _a ∈ s, (termBound (V := V) arity d R B T J : ℤ) := Finset.sum_le_sum hbound
        _ = _ := by simp
    have hnat : ((N.coeff k).natAbs : ℤ) ≤ (s.card*termBound (V := V) arity d R B T J : ℕ) := by
      simpa only [Int.natCast_natAbs] using hsum
    exact_mod_cast hnat

/-- Supplying the constant-one tensor masks inactive factors without changing scopes. -/
theorem evaluate_one (w : ℕ) {C : Type*} [CommRing C] (ports : Fin w → C) :
    evaluate w (fun _ => (1 : C)) ports = 1 := by
  induction w with
  | zero => rfl
  | succ w ih => simp only [evaluate, ih]; ring

/-- Partial factor products can use the original arities and denominator padding. -/
theorem masked_nativeTerm [DecidableEq E] (selected : Finset E) (arity : E → ℕ)
    (Tentry : (e : E) → (Fin (arity e) → Bool) → ℤ)
    (rows : (e : E) → Fin (arity e) → V → Polynomial ℚ)
    (t : ℚ) (R : ℕ) (x : E → Finset V) (U : Finset V) :
    nativeTerm arity (fun e a => if e ∈ selected then Tentry e a else 1) rows t R x U =
      ∏ e ∈ selected, evaluate (arity e) (fun a => C (Tentry e a : ℚ))
        (fun i => correctedPort (rows e i) t R (x e) U) := by
  unfold nativeTerm
  rw [← Finset.prod_subset (Finset.subset_univ selected) (by
    intro e _ he
    simp only [he, ite_false, Int.cast_one, C_1, evaluate_one])]
  apply Finset.prod_congr rfl
  intro e he
  simp only [he, ite_true]

/-- The actual native row family, indexed by the original factor incidences. -/
def builtRows [DecidableEq E] (arity : E → ℕ)
    {r Q : ℕ} (owner : ((e : E) × Fin (arity e)) → V)
    (en : SemiprimeSourceLayout.Enumerations ((e : E) × Fin (arity e)) V E r Q)
    (ε : ℚ) (R : ℕ) : (e : E) → Fin (arity e) → V → Polynomial ℚ :=
  fun e i v => (SemiprimeSourceLayout.builtLayout owner Sigma.fst en ε R).row ⟨e,i⟩ v

/-- No supplied row-height premise: any partial signed corrected-factor sum
inherits heights from the actual searched source constructor. -/
theorem built_signed_terms_representation {X : Type*} [DecidableEq E]
    (s : Finset X) (arity : E → ℕ)
    (Tentry : (e : E) → (Fin (arity e) → Bool) → ℤ)
    {r Q : ℕ} (owner : ((e : E) × Fin (arity e)) → V)
    (en : SemiprimeSourceLayout.Enumerations ((e : E) × Fin (arity e)) V E r Q)
    (ε : ℚ) (R B T J : ℕ) (hJ : 1 ≤ J)
    (howner : ∀ v, (Finset.univ.filter (fun i => owner i = v)).card ≤ B)
    (hQ : 1 ≤ Q) (hAQ : OAI.Algorithms.SubexponentialSAT.Subexp.TailInterval.intervalStart r Q R ≤ Q)
    (hentry : ∀ e a, |Tentry e a| ≤ 1)
    (t : ℤ) (ht : |t| ≤ (T : ℤ)) (base : X → E → Finset V) (correction : X → Finset V)
    (weight : X → ℤ) (hw : ∀ a ∈ s, |weight a| ≤ 1) (k : ℕ) (hk : k < J) :
    Representation ((∑ a ∈ s, C (weight a : ℚ) * nativeTerm arity Tentry
      (builtRows arity owner en ε R) (t : ℚ) R (base a) (correction a)).coeff k)
      ((rowDenominator Q R)^(∑ e, arity e))
      (s.card*termBound (V := V) arity (rowDenominator Q R) R
        (B*2^rowNumeratorExponent Q R) T J) := by
  choose P hP hp hb using fun (i : (e : E) × Fin (arity e)) (v : V) =>
    builtLayout_row_representation owner Sigma.fst en ε R B howner hQ hAQ i v
  exact signed_terms_representation s arity Tentry (fun e i v => P ⟨e,i⟩ v) _
    (rowDenominator Q R) R (B*2^rowNumeratorExponent Q R) T J (rowDenominator_pos Q R) hJ
    (fun e i v => hP ⟨e,i⟩ v) (fun e i v => hp ⟨e,i⟩ v) (fun e i v k => hb ⟨e,i⟩ v k)
    hentry t ht base correction weight hw k hk

/-- Original signed support/assignment leaf weight, including empty or omitted fibres. -/
def rawWeight (J : ℕ) (a : (Finset V × Finset V) × Finset V) : ℤ :=
  if a.1.1.card ≤ J-1 ∧ a.1.2 ⊆ a.1.1 ∧ a.1.1 ⊆ a.2 then
    (-1)^(a.1.1.card-a.1.2.card) else 0

omit [Fintype V] in
theorem rawWeight_abs (J : ℕ) (a : (Finset V × Finset V) × Finset V) :
    |rawWeight J a| ≤ 1 := by
  unfold rawWeight
  split_ifs <;> simp

/-- The actual separated fibres equal native corrected products at Boolean bases. -/
theorem fibrePacket_nativeTerm (arity : E → ℕ)
    (Tentry : (e : E) → (Fin (arity e) → Bool) → ℤ)
    (rows : (e : E) → Fin (arity e) → V → Polynomial ℚ) (t : ℚ) (R : ℕ)
    (d : NodeCertificate arity (fun e i v => (rows e i v).eval t)) (S U : Finset V) :
    fibrePacket arity (fun e a => (Tentry e a : ℚ)) (fun e i v => (rows e i v).eval t) d
      (nativeCorrection arity rows t R U) S =
      ∑ x : Finset V, if S ⊆ x then nativeTerm arity Tentry rows t R (fun _ => x) U else 0 := by
  rw [fibrePacket_eq]
  rfl

/-- Exact logical leaf expansion of rawPacket; this identity does not bound
intermediate separated sums by relying on cancellation. -/
theorem rawPacket_expansion (arity : E → ℕ)
    (Tentry : (e : E) → (Fin (arity e) → Bool) → ℤ)
    (rows : (e : E) → Fin (arity e) → V → Polynomial ℚ) (t : ℚ) (R J : ℕ)
    (d : NodeCertificate arity (fun e i v => (rows e i v).eval t)) :
    rawPacket arity (fun e a => (Tentry e a : ℚ)) rows t R J d =
      ∑ a : (Finset V × Finset V) × Finset V, C (rawWeight J a : ℚ) *
        nativeTerm arity Tentry rows t R (fun _ => a.2) a.1.2 := by
  classical
  have hpow (S : Finset V) : S.powerset = Finset.univ.filter (fun U => U ⊆ S) := by
    ext U
    simp
  simp only [rawPacket, fibrePacket_nativeTerm, hpow, Finset.sum_filter,
    Fintype.sum_prod_type, Finset.subset_univ, ite_true]
  apply Finset.sum_congr rfl
  intro S _
  by_cases hS : S.card ≤ J-1
  · simp only [hS, ite_true]
    apply Finset.sum_congr rfl
    intro U _
    by_cases hU : U ⊆ S
    · simp only [hU, ite_true, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : S ⊆ x
      · simp [rawWeight, hS, hU, hx]
      · simp [rawWeight, hS, hU, hx]
    · simp [rawWeight, hS, hU]
  · simp [rawWeight, hS]

/-- A coarse public logical leaf bound sufficient for bit height, not runtime. -/
def rawIndexCount : ℕ := (2^Fintype.card V * 2^Fintype.card V) * 2^Fintype.card V

/-- Uniform native raw/node numerator envelope; exponential counts occur only
inside the integer magnitude, hence add linearly to its logarithmic height. -/
def rawBound (arity : E → ℕ) (Q R B T J : ℕ) : ℕ :=
  rawIndexCount (V := V) * termBound (V := V) arity (rowDenominator Q R) R
    (B*2^rowNumeratorExponent Q R) T J

/-- Actual separated raw packets inherit a common denominator and explicit
numerator bound from native rows, with no desired output-height premise. -/
theorem built_rawPacket_representation [DecidableEq E] (arity : E → ℕ)
    (Tentry : (e : E) → (Fin (arity e) → Bool) → ℤ)
    {r Q : ℕ} (owner : ((e : E) × Fin (arity e)) → V)
    (en : SemiprimeSourceLayout.Enumerations ((e : E) × Fin (arity e)) V E r Q)
    (ε : ℚ) (R B T J : ℕ) (hJ : 1 ≤ J)
    (howner : ∀ v, (Finset.univ.filter (fun i => owner i = v)).card ≤ B)
    (hQ : 1 ≤ Q) (hAQ : OAI.Algorithms.SubexponentialSAT.Subexp.TailInterval.intervalStart r Q R ≤ Q)
    (hentry : ∀ e a, |Tentry e a| ≤ 1)
    (t : ℤ) (ht : |t| ≤ (T : ℤ))
    (d : NodeCertificate arity (fun e i v => ((builtRows arity owner en ε R) e i v).eval (t : ℚ)))
    (k : ℕ) (hk : k < J) :
    Representation ((rawPacket arity (fun e a => (Tentry e a : ℚ))
      (builtRows arity owner en ε R) (t : ℚ) R J d).coeff k)
      ((rowDenominator Q R)^(∑ e, arity e)) (rawBound (V := V) arity Q R B T J) := by
  rw [rawPacket_expansion]
  have h := built_signed_terms_representation (V := V)
    (Finset.univ : Finset ((Finset V × Finset V) × Finset V)) arity Tentry owner en ε R B T J hJ
    howner hQ hAQ hentry t ht (fun a _ => a.2) (fun a => a.1.2) (rawWeight J)
    (fun a _ => rawWeight_abs J a) k hk
  simpa only [Finset.card_univ, Fintype.card_prod, Fintype.card_finset, rawBound, rawIndexCount] using h

/-- The retained actual node packet has the same common denominator and envelope. -/
theorem built_nodePacket_representation [DecidableEq E] (arity : E → ℕ)
    (Tentry : (e : E) → (Fin (arity e) → Bool) → ℤ)
    {r Q : ℕ} (owner : ((e : E) × Fin (arity e)) → V)
    (en : SemiprimeSourceLayout.Enumerations ((e : E) × Fin (arity e)) V E r Q)
    (ε : ℚ) (R B T J : ℕ) (hJ : 1 ≤ J)
    (howner : ∀ v, (Finset.univ.filter (fun i => owner i = v)).card ≤ B)
    (hQ : 1 ≤ Q) (hAQ : OAI.Algorithms.SubexponentialSAT.Subexp.TailInterval.intervalStart r Q R ≤ Q)
    (hentry : ∀ e a, |Tentry e a| ≤ 1)
    (t : ℤ) (ht : |t| ≤ (T : ℤ))
    (d : NodeCertificate arity (fun e i v => ((builtRows arity owner en ε R) e i v).eval (t : ℚ)))
    (k : ℕ) (hk : k < J) :
    Representation ((nodePacket arity (fun e a => (Tentry e a : ℚ))
      (builtRows arity owner en ε R) (t : ℚ) R J d).coeff k)
      ((rowDenominator Q R)^(∑ e, arity e)) (rawBound (V := V) arity Q R B T J) := by
  rw [nodePacket, coeff_mod_X_pow, ite_eq_left hk]
  exact built_rawPacket_representation arity Tentry owner en ε R B T J hJ howner hQ hAQ hentry t ht d k hk

/-- The actual global Taylor coefficients inherit those same packet heights. -/
theorem built_globalTaylor_representation [DecidableEq E] (arity : E → ℕ)
    (Tentry : (e : E) → (Fin (arity e) → Bool) → ℤ)
    {r Q : ℕ} (owner : ((e : E) × Fin (arity e)) → V)
    (en : SemiprimeSourceLayout.Enumerations ((e : E) × Fin (arity e)) V E r Q)
    (ε : ℚ) (R B T J : ℕ) (hJ : 1 ≤ J)
    (howner : ∀ v, (Finset.univ.filter (fun i => owner i = v)).card ≤ B)
    (hQ : 1 ≤ Q) (hAQ : OAI.Algorithms.SubexponentialSAT.Subexp.TailInterval.intervalStart r Q R ≤ Q)
    (hentry : ∀ e a, |Tentry e a| ≤ 1)
    (t : ℤ) (ht : |t| ≤ (T : ℤ))
    (d : NodeCertificate arity (fun e i v => ((builtRows arity owner en ε R) e i v).eval (t : ℚ)))
    (k : ℕ) (hk : k < J) :
    Representation ((taylor (t : ℚ) (globalPolynomial arity (fun e a => (Tentry e a : ℚ))
      (builtRows arity owner en ε R))).coeff k)
      ((rowDenominator Q R)^(∑ e, arity e)) (rawBound (V := V) arity Q R B T J) := by
  rw [← rawPacket_coeff arity (fun e a => (Tentry e a : ℚ)) (builtRows arity owner en ε R)
    (t : ℚ) R J d (fun e i v => SemiprimeSourceLayout.builtLayout_degree owner Sigma.fst en ε R ⟨e,i⟩ v) k hk]
  exact built_rawPacket_representation arity Tentry owner en ε R B T J hJ howner hQ hAQ hentry t ht d k hk

/-- A group value is literally a selected corrected-factor product at a Boolean base. -/
theorem groupValue_corrected_product (arity : E → ℕ)
    (Tentry : (e : E) → (Fin (arity e) → Bool) → ℤ)
    (rows : (e : E) → Fin (arity e) → V → Polynomial ℚ) (t : ℚ) (R : ℕ)
    (d : NodeCertificate arity (fun e i v => (rows e i v).eval t))
    (g : d.Group) (x U : Finset V) :
    SemiprimeCounterSeparation.groupValue arity (fun e a => (Tentry e a : ℚ)) d.assigned
      (groupedRows arity (fun e i v => (rows e i v).eval t) d)
      (nativeCorrection arity rows t R U) g (splitAssignment d.grouping x) =
      ∏ e ∈ Finset.univ.filter (fun e => d.assigned e=g),
        evaluate (arity e) (fun a => C (Tentry e a : ℚ))
          (fun i => correctedPort (rows e i) t R x U) := by
  simp only [SemiprimeCounterSeparation.groupValue, SemiprimeCounterSeparation.factorValue,
    basePort_split]
  rw [Finset.prod_subtype (p := fun e : E => d.assigned e=g)
    (Finset.univ.filter (fun e => d.assigned e=g)) (by intro e; simp)]
  rfl

/-- Arbitrary actual Boolean representatives/updates admit the same native base
bound; no agreement between different groups' representatives is required. -/
theorem groupValue_boolean_base (arity : E → ℕ)
    (Tentry : (e : E) → (Fin (arity e) → Bool) → ℤ)
    (rows : (e : E) → Fin (arity e) → V → Polynomial ℚ) (t : ℚ) (R : ℕ)
    (d : NodeCertificate arity (fun e i v => (rows e i v).eval t)) (g : d.Group)
    (a : (g : d.Group) → d.Local g → Bool) (U : Finset V) :
    ∃ x : Finset V,
      SemiprimeCounterSeparation.groupValue arity (fun e b => (Tentry e b : ℚ)) d.assigned
        (groupedRows arity (fun e i v => (rows e i v).eval t) d)
        (nativeCorrection arity rows t R U) g a =
      ∏ e ∈ Finset.univ.filter (fun e => d.assigned e=g),
        evaluate (arity e) (fun b => C (Tentry e b : ℚ))
          (fun i => correctedPort (rows e i) t R x U) := by
  let x := (splitAssignment d.grouping).symm a
  refine ⟨x, ?_⟩
  have h := groupValue_corrected_product arity Tentry rows t R d g x U
  simpa only [x, Equiv.apply_symm_apply] using h

/-- Any partial group/factor sum has the padded original incidence denominator,
including arbitrary Boolean representatives and independent corrected subsets. -/
theorem built_masked_terms_representation {X : Type*} [DecidableEq E]
    (s : Finset X) (selected : Finset E) (arity : E → ℕ)
    (Tentry : (e : E) → (Fin (arity e) → Bool) → ℤ)
    {r Q : ℕ} (owner : ((e : E) × Fin (arity e)) → V)
    (en : SemiprimeSourceLayout.Enumerations ((e : E) × Fin (arity e)) V E r Q)
    (ε : ℚ) (R B T J : ℕ) (hJ : 1 ≤ J)
    (howner : ∀ v, (Finset.univ.filter (fun i => owner i = v)).card ≤ B)
    (hQ : 1 ≤ Q) (hAQ : OAI.Algorithms.SubexponentialSAT.Subexp.TailInterval.intervalStart r Q R ≤ Q)
    (hentry : ∀ e a, |Tentry e a| ≤ 1)
    (t : ℤ) (ht : |t| ≤ (T : ℤ)) (base : X → E → Finset V) (correction : X → Finset V)
    (weight : X → ℤ) (hw : ∀ a ∈ s, |weight a| ≤ 1) (k : ℕ) (hk : k < J) :
    Representation ((∑ a ∈ s, C (weight a : ℚ) *
      ∏ e ∈ selected, evaluate (arity e) (fun b => C (Tentry e b : ℚ))
        (fun i => correctedPort ((builtRows arity owner en ε R) e i) (t : ℚ) R (base a e) (correction a))).coeff k)
      ((rowDenominator Q R)^(∑ e, arity e))
      (s.card*termBound (V := V) arity (rowDenominator Q R) R
        (B*2^rowNumeratorExponent Q R) T J) := by
  have hmask : ∀ e a, |(if e ∈ selected then Tentry e a else 1 : ℤ)| ≤ 1 := by
    intro e a
    split_ifs
    · exact hentry e a
    · norm_num
  have h := built_signed_terms_representation s arity
    (fun e a => if e ∈ selected then Tentry e a else 1) owner en ε R B T J hJ
    howner hQ hAQ hmask t ht base correction weight hw k hk
  simpa only [masked_nativeTerm] using h

/-- Explicit dyadic numerator envelope for actual packets. -/
def rawNumeratorExponent (arity : E → ℕ) (Q R B T J : ℕ) : ℕ :=
  3*Fintype.card V + Nat.clog 2 (J+1)*Fintype.card E +
    Nat.clog 2 (J*(rowDenominator Q R+2*(Fintype.card V*
      shiftBound R (B*2^rowNumeratorExponent Q R) T))+1)*(∑ e, arity e)

omit [DecidableEq V] in
/-- The numerator bound has polynomial logarithmic size in the displayed dimensions. -/
theorem rawBound_le_power (arity : E → ℕ) (Q R B T J : ℕ) :
    rawBound (V := V) arity Q R B T J ≤ 2^rawNumeratorExponent (V := V) arity Q R B T J := by
  let C := J*(rowDenominator Q R+2*(Fintype.card V*shiftBound R (B*2^rowNumeratorExponent Q R) T))
  have hJ : J ≤ 2^Nat.clog 2 (J+1) := (Nat.le_succ J).trans (Nat.le_pow_clog (by decide) _)
  have hC : C ≤ 2^Nat.clog 2 (C+1) := (Nat.le_succ C).trans (Nat.le_pow_clog (by decide) _)
  have hraw : rawIndexCount (V := V) = 2^(3*Fintype.card V) := by
    unfold rawIndexCount
    rw [← pow_add, ← pow_add]
    congr 1
    omega
  unfold rawBound termBound
  rw [hraw]
  calc
    _ ≤ 2^(3*Fintype.card V) *
        (2^Nat.clog 2 (J+1))^Fintype.card E * (2^Nat.clog 2 (C+1))^(∑ e, arity e) := by
      change 2^(3*Fintype.card V) * (J^Fintype.card E * C^(∑ e, arity e)) ≤ _
      rw [mul_assoc]
      exact Nat.mul_le_mul_left _ (Nat.mul_le_mul
        (Nat.pow_le_pow_left hJ _) (Nat.pow_le_pow_left hC _))
    _ = _ := by
      rw [← pow_mul, ← pow_mul, ← pow_add, ← pow_add]
      rfl

/-- Full incidence denominator powers also have an explicit polynomial bit envelope. -/
theorem packetDenominator_le_power (arity : E → ℕ) (Q R : ℕ) :
    (rowDenominator Q R)^(∑ e, arity e) ≤
      2^((R+Nat.clog 2 Q*Q*(Q+1))*(∑ e, arity e)) := by
  exact (Nat.pow_le_pow_left (rowDenominator_le_power Q R) _).trans_eq (by rw [← pow_mul])

end RiemannGaussian.SemiprimeCounterPacketHeight

#print axioms RiemannGaussian.SemiprimeCounterPacketHeight.built_nodePacket_representation
#print axioms RiemannGaussian.SemiprimeCounterPacketHeight.built_masked_terms_representation
#print axioms RiemannGaussian.SemiprimeCounterPacketHeight.rawBound_le_power
