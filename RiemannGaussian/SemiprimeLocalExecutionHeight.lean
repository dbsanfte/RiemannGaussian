/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeLocalArrayFrontend
import RiemannGaussian.SemiprimeTaylorHeight

/-!
# Heights of the executed local source interpreter

Bounds below concern the actual Horner buffers, corrected-input prefixes and
local tensor branches. Integer source nodes preserve the source denominator.
No coefficient of a requested shifted polynomial is supplied as runtime advice.
-/
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace RiemannGaussian.SemiprimeLocalExecutionHeight
open scoped BigOperators
open Polynomial SemiprimeJetArray SemiprimeJetArrayHeight SemiprimeArrayOps
open SemiprimeLocalArrayFrontend SemiprimeHermiteArrayHeight

/-- One shared denominator and numerator envelope for every retained array entry. -/
def ArrayBound (a : Array ℚ) (J d B : ℕ) : Prop :=
  ∀ i, i < J → Representation (coefficient a i) d B

/-- A coefficient envelope for a source Horner suffix of the indicated length. -/
def hornerBound (J B T len : ℕ) : ℕ := B * (1 + J * (T+1))^len

/-- Increasing a numerator envelope preserves a retained-array bound. -/
theorem arrayBound_mono {a : Array ℚ} {J d B C : ℕ}
    (h : ArrayBound a J d B) (hBC : B ≤ C) : ArrayBound a J d C :=
  fun i hi => representation_mono (h i hi) hBC

/-- The zero-filled actual buffer has every common denominator. -/
theorem zero_bound (J d B : ℕ) : ArrayBound (zeroJet J).coefficients J d B := by
  intro i hi
  rw [zeroJet_coefficient]
  exact representation_mono (representation_zero d) (Nat.zero_le _)

/-- Every multiply-add prefix of an ordinary convolution retains the product denominator. -/
theorem convolution_prefix (a b : Array ℚ) (J d e B C k len : ℕ)
    (ha : ArrayBound a J d B) (hb : ArrayBound b J e C)
    (hk : k < J) (hlen : len ≤ k) :
    Representation (dotPrefix a b (k-1) len).value (d*e) (len*B*C) := by
  rw [dotPrefix_value]
  have hs := representation_sum (Finset.range len)
    (fun i => coefficient a (i+1)*coefficient b (k-1-i)) (d*e) (B*C) (by
      intro i hi
      have hi' := Finset.mem_range.mp hi
      exact representation_mul (ha (i+1) (by omega)) (hb (k-1-i) (by omega)))
  simpa only [Finset.card_range, Nat.mul_assoc] using hs

/-- Every individual product used by a convolution has a bounded numerator. -/
theorem convolution_term (a b : Array ℚ) (J d e B C k i : ℕ)
    (ha : ArrayBound a J d B) (hb : ArrayBound b J e C)
    (hk : k < J) (hi : i ≤ k) :
    Representation (coefficient a i*coefficient b (k-i)) (d*e) (B*C) :=
  representation_mul (ha i (by omega)) (hb (k-i) (by omega))

/-- The affine multiplier used by the literal Horner loop has integer coefficients. -/
theorem shift_linear_bound (t : ℤ) (J T : ℕ) (ht : t.natAbs ≤ T) :
    ArrayBound #[(t : ℚ),1] J 1 (T+1) := by
  intro i _
  cases i with
  | zero =>
    change Representation (t : ℚ) 1 (T+1)
    exact representation_mono (representation_integer t) (by omega)
  | succ i =>
    cases i with
    | zero =>
      change Representation (1 : ℚ) 1 (T+1)
      exact representation_mono (representation_one 1 (by decide)) (by omega)
    | succ i =>
      rw [coefficient_zero (by simp)]
      exact representation_mono (representation_zero 1) (Nat.zero_le _)

/-- The constant-coefficient buffer actually scaled at a Horner step. -/
theorem horner_constant_bound (a : Array ℚ) (start J d B : ℕ)
    (ha : Representation (coefficient a start) d B) :
    ArrayBound (scaleJet (oneJet J).coefficients (coefficient a start) J).coefficients J d B := by
  intro i hi
  rw [scaleJet_coefficient _ _ J i hi, oneJet_coefficient J i hi]
  split_ifs
  · simpa only [mul_one] using ha
  · rw [mul_zero]
    exact representation_mono (representation_zero d) (Nat.zero_le _)

/-- Every actual Horner suffix is bounded directly from its source coefficients. -/
theorem shiftFrom_bound (a : Array ℚ) (t : ℤ) (J d B T start len : ℕ)
    (ht : t.natAbs ≤ T)
    (ha : ∀ i, start ≤ i → i < start+len → Representation (coefficient a i) d B) :
    ArrayBound (shiftFrom a (t : ℚ) J start len).coefficients J d
      (hornerBound J B T len) := by
  induction len generalizing start with
  | zero => exact zero_bound _ _ _
  | succ len ih =>
    have hold := ih (start+1) (fun i h₁ h₂ => ha i (by omega) (by omega))
    have hlinear := shift_linear_bound t J T ht
    have hp := multiply_representation
      (shiftFrom a (t : ℚ) J (start+1) len).coefficients #[(t : ℚ),1]
      d 1 (hornerBound J B T len) (T+1) J hold hlinear
    have hc (i : ℕ) (hi : i < J) :
        Representation (coefficient (scaleJet (oneJet J).coefficients
          (coefficient a start) J).coefficients i) d B := by
      rw [scaleJet_coefficient _ _ J i hi, oneJet_coefficient J i hi]
      split_ifs
      · simpa only [mul_one] using ha start (by omega) (by omega)
      · rw [mul_zero]
        exact representation_mono (representation_zero d) (Nat.zero_le _)
    intro i hi
    change Representation (coefficient (addJet
      (scaleJet (oneJet J).coefficients (coefficient a start) J).coefficients
      (multiply (shiftFrom a (t : ℚ) J (start+1) len).coefficients #[(t : ℚ),1] J).coefficients J).coefficients i) _ _
    have hsum := addJet_representation _ _ J d B
      (J*hornerBound J B T len*(T+1)) hc (fun k hk => by
        simpa only [Nat.mul_one] using hp k hk) i hi
    apply representation_mono hsum
    have hpow : 1 ≤ (1+J*(T+1))^len := Nat.one_le_pow _ _ (by omega)
    have hB : B ≤ hornerBound J B T len := by
      unfold hornerBound
      nlinarith
    unfold hornerBound at hB ⊢
    rw [pow_succ]
    nlinarith

/-- The suffix bound also covers every partial multiplication accumulator in Horner. -/
theorem shiftFrom_product_prefix (a : Array ℚ) (t : ℤ)
    (J d B T start len k p : ℕ) (ht : t.natAbs ≤ T)
    (ha : ∀ i, start ≤ i → i < start+len → Representation (coefficient a i) d B)
    (hk : k < J) (hp : p ≤ k) :
    Representation (dotPrefix (shiftFrom a (t : ℚ) J start len).coefficients
      #[(t : ℚ),1] (k-1) p).value d (p*hornerBound J B T len*(T+1)) := by
  simpa only [Nat.mul_one] using convolution_prefix _ _ J d 1
    (hornerBound J B T len) (T+1) k p
    (shiftFrom_bound a t J d B T start len ht ha) (shift_linear_bound t J T ht) hk hp

/-- A completed shifted row is obtained from the same source bound. -/
theorem shiftRow_bound (a : Array ℚ) (t : ℤ) (R J d B T : ℕ)
    (ht : t.natAbs ≤ T) (ha : ∀ i ≤ R, Representation (coefficient a i) d B) :
    ArrayBound (shiftRow a (t : ℚ) R J).coefficients J d (hornerBound J B T (R+1)) :=
  shiftFrom_bound a t J d B T 0 (R+1) ht (fun i _ hi => ha i (by omega))

/-- Boolean masking retains rather than increases a coefficient's numerator. -/
theorem maskShift_bound (a : Array ℚ) (base correction : Bool) (J d B : ℕ)
    (ha : ArrayBound a J d B) :
    ArrayBound (maskShift a base correction J).coefficients J d B := by
  intro i hi
  rw [maskShift_coefficient _ _ _ J i hi]
  split_ifs <;> first | exact ha _ (by omega) |
    exact representation_mono (representation_zero d) (Nat.zero_le _)

/-- Every prefix of the actual corrected-input sum uses the source denominator. -/
theorem acquireCorrected_bound (source : ℕ → Array ℚ) (t : ℤ)
    (R J d B T n : ℕ) (base correction : ℕ → Bool) (ht : t.natAbs ≤ T)
    (hs : ∀ v < n, ∀ i ≤ R, Representation (coefficient (source v) i) d B) :
    ArrayBound (acquireCorrected source (t : ℚ) R J base correction n).coefficients
      J d (n*hornerBound J B T (R+1)) := by
  induction n with
  | zero => exact zero_bound _ _ _
  | succ n ih =>
    have hold := ih (fun v hv => hs v (by omega))
    have hrow := shiftRow_bound (source n) t R J d B T ht (hs n (by omega))
    have hmask := maskShift_bound _ (base n) (correction n) J d _ hrow
    intro i hi
    change Representation (coefficient (addJet
      (acquireCorrected source (t : ℚ) R J base correction n).coefficients
      (maskShift (shiftRow (source n) (t : ℚ) R J).coefficients (base n) (correction n) J).coefficients J).coefficients i) _ _
    convert addJet_representation _ _ J d _ _ hold hmask i hi using 1
    ring

/-- The actual Horner multiplication buffer is bounded before the final coefficient addition. -/
theorem shiftFrom_product_bound (a : Array ℚ) (t : ℤ) (J d B T start len : ℕ)
    (ht : t.natAbs ≤ T)
    (ha : ∀ i, start ≤ i → i < start+len → Representation (coefficient a i) d B) :
    ArrayBound (multiply (shiftFrom a (t : ℚ) J start len).coefficients
      #[(t : ℚ),1] J).coefficients J d (J*hornerBound J B T len*(T+1)) := by
  intro i hi
  simpa only [Nat.mul_one] using multiply_representation _ _ d 1
    (hornerBound J B T len) (T+1) J
    (shiftFrom_bound a t J d B T start len ht ha) (shift_linear_bound t J T ht) i hi

/-- The scalar products preceding each Horner multiply-add are bounded too. -/
theorem shiftFrom_product_term (a : Array ℚ) (t : ℤ)
    (J d B T start len k i : ℕ) (ht : t.natAbs ≤ T)
    (ha : ∀ v, start ≤ v → v < start+len → Representation (coefficient a v) d B)
    (hk : k < J) (hi : i ≤ k) :
    Representation (coefficient (shiftFrom a (t : ℚ) J start len).coefficients i *
      coefficient #[(t : ℚ),1] (k-i)) d (hornerBound J B T len*(T+1)) := by
  simpa only [Nat.mul_one] using convolution_term _ _ J d 1
    (hornerBound J B T len) (T+1) k i
    (shiftFrom_bound a t J d B T start len ht ha) (shift_linear_bound t J T ht) hk hi

/-- Fin-indexed source acquisition has the same literal prefix height. -/
theorem acquireCorrectedFin_bound {n : ℕ} (source : Fin n → Array ℚ) (t : ℤ)
    (R J d B T : ℕ) (base correction : Fin n → Bool) (ht : t.natAbs ≤ T)
    (hs : ∀ v i, i ≤ R → Representation (coefficient (source v) i) d B) :
    ArrayBound (acquireCorrectedFin source (t : ℚ) R J base correction).coefficients
      J d (n*hornerBound J B T (R+1)) := by
  unfold acquireCorrectedFin
  apply acquireCorrected_bound
  · exact ht
  · intro v hv i hi
    simp only [dite_eq_left hv]
    exact hs ⟨v,hv⟩ i hi

/-- A literal source coefficient array inherits the constructor's integer clearing bound. -/
theorem cleared_source_bound (a : Array ℚ) (p : Polynomial ℚ) (P : Polynomial ℤ)
    (d B R : ℕ) (hd : 0<d)
    (hclear : P.map (Int.castRingHom ℚ) = C (d : ℚ)*p)
    (hB : ∀ i, |P.coeff i| ≤ (B : ℤ))
    (ha : ∀ i ≤ R, coefficient a i = p.coeff i) (i : ℕ) (hi : i ≤ R) :
    Representation (coefficient a i) d B := by
  rw [ha i hi]
  refine ⟨P.coeff i, ?_, ?_⟩
  · have hc := congrArg (fun q : Polynomial ℚ => q.coeff i) hclear
    simp only [coeff_map, coeff_C_mul] at hc
    apply (eq_div_iff (by exact_mod_cast Nat.ne_of_gt hd)).mpr
    change ((P.coeff i : ℤ) : ℚ) = (d : ℚ)*p.coeff i at hc
    exact (mul_comm _ _).trans hc.symm
  · exact_mod_cast (show ((P.coeff i).natAbs : ℤ) ≤ (B : ℤ) by
      simpa only [Int.natCast_natAbs] using hB i)

/-- The actual built source row, with no supplied row-height conclusion. -/
theorem builtLayout_source_bound {I V E : Type} [Fintype I] [DecidableEq I]
    [Fintype V] [DecidableEq V] [DecidableEq E]
    {r Q : ℕ} (owner : I → V) (factor : I → E)
    (en : SemiprimeSourceLayout.Enumerations I V E r Q) (eps : ℚ) (R B : ℕ)
    (howner : ∀ v, (Finset.univ.filter (fun i => owner i=v)).card ≤ B)
    (hQ : 1≤Q) (hAQ : OAI.Algorithms.SubexponentialSAT.Subexp.TailInterval.intervalStart r Q R ≤ Q)
    (i : I) (v : V) (a : Array ℚ)
    (ha : ∀ k ≤ R, coefficient a k = ((SemiprimeSourceLayout.builtLayout owner factor en eps R).row i v).coeff k)
    (k : ℕ) (hk : k ≤ R) :
    Representation (coefficient a k) (SemiprimeSourceRowHeight.rowDenominator Q R)
      (B*2^SemiprimeSourceRowHeight.rowNumeratorExponent Q R) := by
  obtain ⟨P,hP,_hdeg,hb⟩ := SemiprimeSourceRowHeight.builtLayout_row_representation
    owner factor en eps R B howner hQ hAQ i v
  exact cleared_source_bound a _ P _ _ R
    (SemiprimeSourceRowHeight.rowDenominator_pos Q R) hP hb ha k hk

/-- All actual arithmetic buffers at one nonleaf local tensor node. -/
structure LocalStepSafe (J w d B : ℕ) (T : (Fin (w+1) → Bool) → EntryReport)
    (inputs : Fin (w+1) → Array ℚ) : Prop where
  /-- Negating the selected port preserves its height. -/
  neg : ArrayBound (scaleJet (inputs 0) (-1) J).coefficients J d B
  /-- The false branch multiplier is the actual one-minus-port array. -/
  no : ArrayBound (addJet (oneJet J).coefficients
    (scaleJet (inputs 0) (-1) J).coefficients J).coefficients J d (d+B)
  /-- Every partial false-branch convolution accumulator is bounded. -/
  leftPrefix : ∀ k < J, ∀ p ≤ k, Representation (dotPrefix
    (addJet (oneJet J).coefficients (scaleJet (inputs 0) (-1) J).coefficients J).coefficients
    (localEvaluate J w (fun eta => T (Fin.cons false eta)) (fun i => inputs i.succ)).coefficients
    (k-1) p).value (d*d^w) (p*(d+B)*localBase J d B^w)
  /-- Every partial true-branch convolution accumulator is bounded. -/
  rightPrefix : ∀ k < J, ∀ p ≤ k, Representation (dotPrefix (inputs 0)
    (localEvaluate J w (fun eta => T (Fin.cons true eta)) (fun i => inputs i.succ)).coefficients
    (k-1) p).value (d*d^w) (p*B*localBase J d B^w)
  /-- Individual false-branch scalar products before addition are bounded. -/
  leftTerm : ∀ k < J, ∀ i ≤ k, Representation
    (coefficient (addJet (oneJet J).coefficients
      (scaleJet (inputs 0) (-1) J).coefficients J).coefficients i *
      coefficient (localEvaluate J w (fun eta => T (Fin.cons false eta))
        (fun v => inputs v.succ)).coefficients (k-i)) (d*d^w) ((d+B)*localBase J d B^w)
  /-- Individual true-branch scalar products before addition are bounded. -/
  rightTerm : ∀ k < J, ∀ i ≤ k, Representation (coefficient (inputs 0) i *
      coefficient (localEvaluate J w (fun eta => T (Fin.cons true eta))
        (fun v => inputs v.succ)).coefficients (k-i)) (d*d^w) (B*localBase J d B^w)
  /-- Every retained false-branch convolution coefficient is bounded. -/
  left : ArrayBound (multiply
    (addJet (oneJet J).coefficients (scaleJet (inputs 0) (-1) J).coefficients J).coefficients
    (localEvaluate J w (fun eta => T (Fin.cons false eta)) (fun i => inputs i.succ)).coefficients J).coefficients
    J (d*d^w) (J*(d+B)*localBase J d B^w)
  /-- Every retained true-branch convolution coefficient is bounded. -/
  right : ArrayBound (multiply (inputs 0)
    (localEvaluate J w (fun eta => T (Fin.cons true eta)) (fun i => inputs i.succ)).coefficients J).coefficients
    J (d*d^w) (J*B*localBase J d B^w)
  /-- The actual completed node has the derived common power denominator. -/
  out : ArrayBound (localEvaluate J (w+1) T inputs).coefficients J (d^(w+1)) (localBase J d B^(w+1))

/-- A proof tree recording bounds for every actually visited local recursive branch. -/
inductive LocalTrace (J d B : ℕ) : (w : ℕ) → ((Fin w → Bool) → EntryReport) →
    (Fin w → Array ℚ) → Prop
  | leaf (T : (Fin 0 → Bool) → EntryReport) (inputs : Fin 0 → Array ℚ)
      (hout : ArrayBound (localEvaluate J 0 T inputs).coefficients J 1 1) : LocalTrace J d B 0 T inputs
  | step (w : ℕ) (T : (Fin (w+1) → Bool) → EntryReport) (inputs : Fin (w+1) → Array ℚ)
      (lo : LocalTrace J d B w (fun eta => T (Fin.cons false eta)) (fun i => inputs i.succ))
      (hi : LocalTrace J d B w (fun eta => T (Fin.cons true eta)) (fun i => inputs i.succ))
      (buffers : LocalStepSafe J w d B T inputs) : LocalTrace J d B (w+1) T inputs

/-- All branches, all convolution prefixes and all node outputs follow from source-port heights. -/
theorem localEvaluate_trace (J w d B : ℕ) (hd : 0<d)
    (T : (Fin w → Bool) → EntryReport) (inputs : Fin w → Array ℚ)
    (hT : ∀ eta, (T eta).value.natAbs ≤ 1) (hinputs : ∀ v, ArrayBound (inputs v) J d B) :
    LocalTrace J d B w T inputs := by
  induction w with
  | zero =>
    apply LocalTrace.leaf
    simpa only [ArrayBound, pow_zero] using localEvaluate_representation J 0 d B hd T inputs hT hinputs
  | succ w ih =>
    have hlo := ih (fun eta => T (Fin.cons false eta)) (fun i => inputs i.succ)
      (fun eta => hT (Fin.cons false eta)) (fun i => hinputs i.succ)
    have hhi := ih (fun eta => T (Fin.cons true eta)) (fun i => inputs i.succ)
      (fun eta => hT (Fin.cons true eta)) (fun i => hinputs i.succ)
    apply LocalTrace.step w T inputs hlo hhi
    have hl : ArrayBound
        (localEvaluate J w (fun eta => T (Fin.cons false eta)) (fun i => inputs i.succ)).coefficients
        J (d^w) (localBase J d B^w) :=
      localEvaluate_representation J w d B hd _ _ (fun eta => hT (Fin.cons false eta)) (fun i => hinputs i.succ)
    have hh : ArrayBound
        (localEvaluate J w (fun eta => T (Fin.cons true eta)) (fun i => inputs i.succ)).coefficients
        J (d^w) (localBase J d B^w) :=
      localEvaluate_representation J w d B hd _ _ (fun eta => hT (Fin.cons true eta)) (fun i => hinputs i.succ)
    have hn : ArrayBound (scaleJet (inputs 0) (-1) J).coefficients J d B := by
      intro i hi
      rw [scaleJet_coefficient _ _ J i hi, neg_one_mul]
      exact representation_neg (hinputs 0 i hi)
    have hno : ArrayBound (addJet (oneJet J).coefficients
        (scaleJet (inputs 0) (-1) J).coefficients J).coefficients J d (d+B) :=
      addJet_representation _ _ J d d B (oneJet_representation J d hd) hn
    exact ⟨hn,hno,
      fun k hk p hp => convolution_prefix _ _ J d (d^w) (d+B) _ k p hno hl hk hp,
      fun k hk p hp => convolution_prefix _ _ J d (d^w) B _ k p (hinputs 0) hh hk hp,
      fun k hk i hi => convolution_term _ _ J d (d^w) (d+B) _ k i hno hl hk hi,
      fun k hk i hi => convolution_term _ _ J d (d^w) B _ k i (hinputs 0) hh hk hi,
      multiply_representation _ _ d (d^w) (d+B) _ J hno hl,
      multiply_representation _ _ d (d^w) B _ J (hinputs 0) hh,
      localEvaluate_representation J (w+1) d B hd T inputs hT hinputs⟩

/-- Source coefficients suffice to bound the actual cached input array's whole tensor trace. -/
theorem nativeLocal_trace {n : ℕ} (w J R d B T : ℕ) (hd : 0<d)
    (t : ℤ) (ht : t.natAbs ≤ T)
    (source : Fin w → Fin n → Array ℚ) (base correction : Fin n → Bool)
    (entries : (Fin w → Bool) → EntryReport)
    (hentries : ∀ eta, (entries eta).value.natAbs ≤ 1)
    (hs : ∀ v u i, i ≤ R → Representation (coefficient (source v u) i) d B) :
    let inputs := Array.ofFn (fun v : Fin w => acquireCorrectedFin (source v)
      (t : ℚ) R J base correction)
    LocalTrace J d (n*hornerBound J B T (R+1)) w entries
      (fun v => (inputs[v.val]'(by simp [inputs])).coefficients) := by
  dsimp only
  apply localEvaluate_trace J w d _ hd entries
  · exact hentries
  · intro v
    simpa only [Array.getElem_ofFn] using
      acquireCorrectedFin_bound (source v) t R J d B T base correction ht (hs v)

end RiemannGaussian.SemiprimeLocalExecutionHeight
