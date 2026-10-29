/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeJetBits
import RiemannGaussian.SemiprimeRationalWordAcquisition
import RiemannGaussian.SemiprimeMaterializedOriginalSource
import RiemannGaussian.SemiprimeLocalExecutionHeight
import RiemannGaussian.SemiprimePaidFiniteEnumerationLists

/-! # Actual original source to cached physical rational coefficients
The original producer is called once. Its scalar work and the scalar encoding
ledger remain separate; neither is asserted to be physical source production.
-/
set_option autoImplicit false
set_option maxHeartbeats 300000
namespace RiemannGaussian.SemiprimeSourceWordAcquisition
open OAI.Algorithms.SubexponentialSAT
open MulticolorTypes Subexp.ConstructivePacking
open SemiprimeMaterializedSourceUniversal SemiprimeRationalWordAcquisition
open SemiprimeJetArrayHeight SemiprimeJetArray SemiprimeSourceRowHeight
open SemiprimeRationalBits

/-- Explicit original-row denominator exponent from the constructor height theorem. -/
def denominatorBits (Q R : ℕ) : ℕ := R+Nat.clog 2 Q*Q*(Q+1)

/-- One parameter-only width covers all original row coefficient numerators and denominators. -/
def sourceBits (B Q R : ℕ) : ℕ := B+denominatorBits Q R+rowNumeratorExponent Q R

/-- Actual common denominator fits the explicit source width. -/
theorem denominator_le (B Q R : ℕ) : rowDenominator Q R≤2^(sourceBits B Q R) := by
  apply (rowDenominator_le_power Q R).trans
  apply Nat.pow_le_pow_right (by decide)
  unfold sourceBits denominatorBits
  omega

/-- Actual common numerator bound fits without an output Fits hypothesis. -/
theorem numerator_le (B Q R : ℕ) : B*2^rowNumeratorExponent Q R≤2^(sourceBits B Q R) := by
  calc
    B*2^rowNumeratorExponent Q R ≤ 2^B*2^rowNumeratorExponent Q R :=
      Nat.mul_le_mul_right _ (Nat.le_of_lt Nat.lt_two_pow_self)
    _ = 2^(B+rowNumeratorExponent Q R) := (pow_add _ _ _).symm
    _ ≤ 2^(sourceBits B Q R) := by
      apply Nat.pow_le_pow_right (by decide)
      unfold sourceBits
      omega

/-- Paid literal original-incidence index scan and two stored array reads. -/
def readSource {I : Type} [DecidableEq I] {n : ℕ} (en : FiniteEnumeration I)
    (source : Array (Array (Array ℚ))) (i : I) (v : Fin n) : Run (Array ℚ) :=
  let index := SemiprimeMaterializedSourceWords.indexRun i en.values
  ⟨((source[index.value]?).getD #[])[v.val]?.getD #[],index.work+4⟩

/-- The executed scan is the exact original source accessor, not a different ordering. -/
theorem readSource_value {I : Type} [DecidableEq I] {n : ℕ} (en : FiniteEnumeration I)
    (source : Array (Array (Array ℚ))) (i : I) (v : Fin n) :
    (readSource en source i v).value=SemiprimeSourceArrayAcquisition.read en source i v := by
  simp only [readSource,SemiprimeMaterializedSourceWords.indexRun_value,
    LocalExpectation.indexCode,SemiprimeSourceArrayAcquisition.read,FiniteEnumeration.equivFin]
  rfl

/-- All original index scans are retained in the stored-source getter. -/
theorem readSource_work {I : Type} [DecidableEq I] {n : ℕ} (en : FiniteEnumeration I)
    (source : Array (Array (Array ℚ))) (i : I) (v : Fin n) :
    (readSource en source i v).work≤2*en.values.length+6 := by
  have h := SemiprimeMaterializedSourceWords.indexRun_work i en.values
  exact Nat.add_le_add_right h 4

variable {I E : Type} [Fintype I] [DecidableEq I] [DecidableEq E] {n r Q : ℕ}

/-- The actual acquired coefficient has the constructor's common representation. -/
theorem source_representation (owner : I → Fin n) (factor : I → E)
    (en : SemiprimeSourceLayout.Enumerations I (Fin n) E r Q) (eps : ℚ) (R B : ℕ)
    (howner : ∀ v,(Finset.univ.filter (fun i => owner i=v)).card≤B)
    (hQ : 1≤Q) (hAQ : Subexp.TailInterval.intervalStart r Q R≤Q)
    (i : I) (v : Fin n) (k : ℕ) (hk : k≤R) :
    Representation (coefficient (readSource en.incidences
      (SemiprimeMaterializedOriginalSource.acquire owner factor en eps R).value i v).value k)
      (rowDenominator Q R) (B*2^rowNumeratorExponent Q R) := by
  rw [readSource_value]
  exact SemiprimeLocalExecutionHeight.builtLayout_source_bound owner factor en eps R B howner hQ hAQ i v _
    (fun k hk => SemiprimeMaterializedOriginalSource.acquire_coefficient owner factor en eps R i v k hk) k hk

/-- One retained source row is read once, then each of its R+1 coefficients is encoded once. -/
def acquireRow (bits R : ℕ) (source : Run (Array ℚ)) : ArrayRun :=
  let out := encodeArray bits (R+1) source.value
  ⟨out.words,out.stages,source.work+out.work+1⟩

/-- Source-ready legality/value/width uses only original constructor assumptions. -/
theorem acquireRow_source (owner : I → Fin n) (factor : I → E)
    (en : SemiprimeSourceLayout.Enumerations I (Fin n) E r Q) (eps : ℚ) (R B : ℕ)
    (howner : ∀ v,(Finset.univ.filter (fun i => owner i=v)).card≤B)
    (hQ : 1≤Q) (hAQ : Subexp.TailInterval.intervalStart r Q R≤Q)
    (i : I) (v : Fin n) (k : Fin (R+1)) :
    let source := readSource en.incidences (SemiprimeMaterializedOriginalSource.acquire owner factor en eps R).value i v
    let w := (acquireRow (sourceBits B Q R) R source).words[k.val]'(by simpa only [acquireRow,encodeArray,Array.size_map,Array.size_ofFn] using k.isLt)
    w.value=coefficient source.value k.val ∧ w.Valid ∧ Width w (sourceBits B Q R+1) := by
  dsimp only [acquireRow]
  exact encodeArray_representation _ _ _ _ _ (rowDenominator_pos Q R) (numerator_le B Q R)
    (denominator_le B Q R) (fun k => source_representation owner factor en eps R B howner hQ hAQ i v k.val (by omega)) k

/-- Encode the actual original incidence/column family, retaining each row report once. -/
def encodeFamily (bits R : ℕ) (incidences : FiniteEnumeration I)
    (source : Array (Array (Array ℚ))) : Run (Array (Array (Array RationalWord))) :=
  let columns := SemiprimePaidFiniteEnumerationLists.fin n
  let rows := collect (fun i =>
    let out := collect (fun v =>
      let row := acquireRow bits R (readSource incidences source i v)
      (⟨row.words,row.work⟩ : Run (Array RationalWord))) columns.value
    (⟨out.value.toArray,out.work+out.value.length+2⟩ : Run (Array (Array RationalWord)))) incidences.values
  ⟨rows.value.toArray,columns.work+rows.work+rows.value.length+2⟩

/-- Read the physical cache by an executed original-incidence scan and two flat reads. -/
def readWords (incidences : FiniteEnumeration I) (cache : Array (Array (Array RationalWord)))
    (i : I) (v : Fin n) : Run (Array RationalWord) :=
  let index := SemiprimeMaterializedSourceWords.indexRun i incidences.values
  ⟨((cache[index.value]?).getD #[])[v.val]?.getD #[],index.work+4⟩

omit [Fintype I] in
/-- Cached row lookup is exactly its once-acquired physical row. -/
theorem encodeFamily_read (bits R : ℕ) (incidences : FiniteEnumeration I)
    (source : Array (Array (Array ℚ))) (i : I) (v : Fin n) :
    (readWords incidences (encodeFamily (n:=n) bits R incidences source).value i v).value=
      (acquireRow bits R (readSource incidences source i v)).words := by
  simp [readWords,encodeFamily,collect_value,SemiprimePaidFiniteEnumerationLists.fin_value,
    SemiprimeMaterializedSourceWords.indexRun_value,LocalExpectation.indexCode,
    List.getElem?_idxOf (incidences.complete i)]

omit [Fintype I] in
/-- Physical getter pays the actual index scan; no equivalence-inverse oracle is used. -/
theorem readWords_work (incidences : FiniteEnumeration I)
    (cache : Array (Array (Array RationalWord))) (i : I) (v : Fin n) :
    (readWords incidences cache i v).work≤2*incidences.values.length+6 := by
  exact Nat.add_le_add_right (SemiprimeMaterializedSourceWords.indexRun_work i incidences.values) 4

/-- Explicit scalar digit/cell envelope for the whole physical source cache. -/
def encodingBudget (M n bits R : ℕ) : ℕ :=
  let E := (R+1)*(8*(bits+1)+13)+12*(R+1)+5
  3*(n+1)^2+M*(n*(2*M+E+10)+5)+M+3

omit [Fintype I] in
/-- Every coefficient scan/encode and every retained row cache is paid. -/
theorem encodeFamily_work (bits R : ℕ) (incidences : FiniteEnumeration I)
    (source : Array (Array (Array ℚ))) :
    (encodeFamily (n:=n) bits R incidences source).work≤
      encodingBudget incidences.values.length n bits R := by
  let M := incidences.values.length
  let E := (R+1)*(8*(bits+1)+13)+12*(R+1)+5
  have rowWork (i : I) (v : Fin n) :
      (acquireRow bits R (readSource incidences source i v)).work≤2*M+E+7 := by
    have hr := readSource_work incidences source i v
    have he := (encodeArray_work bits (R+1) (readSource incidences source i v).value).1
    unfold acquireRow
    dsimp only
    omega
  have inner (i : I) := collect_work (fun v : Fin n =>
    let row := acquireRow bits R (readSource incidences source i v)
    (⟨row.words,row.work⟩ : Run (Array RationalWord)))
    (SemiprimePaidFiniteEnumerationLists.fin n).value (2*M+E+7) (fun v _ => rowWork i v)
  have outer := collect_work (fun i =>
    let out := collect (fun v : Fin n =>
      let row := acquireRow bits R (readSource incidences source i v)
      (⟨row.words,row.work⟩ : Run (Array RationalWord)))
      (SemiprimePaidFiniteEnumerationLists.fin n).value
    (⟨out.value.toArray,out.work+out.value.length+2⟩ : Run (Array (Array RationalWord))))
    incidences.values (n*(2*M+E+10)+3) (by
      intro i _
      have h := inner i
      simp only [SemiprimePaidFiniteEnumerationLists.fin_value,List.length_finRange] at h
      dsimp only
      simp only [collect_value,List.length_map,SemiprimePaidFiniteEnumerationLists.fin_value,List.length_finRange]
      nlinarith)
  have hf := SemiprimePaidFiniteEnumerationLists.fin_work n
  unfold encodeFamily encodingBudget
  dsimp only [M,E] at outer
  dsimp only
  simp only [collect_value,List.length_map] at outer ⊢
  have hsum := Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add hf outer) incidences.values.length) 2
  convert hsum using 1; ring

/-- Original source work and the physical-cache scalar encoding work are kept separately. -/
structure SourceRun where
  /-- Cached physical words in original incidence/column/coefficient order. -/
  words : Array (Array (Array RationalWord))
  /-- Retained actual original source producer work. -/
  sourceWork : ℕ
  /-- Retained scalar digit/cell encoding work. -/
  encodingWork : ℕ
  /-- Sum of both acquired reports and the fixed join allowance. -/
  work : ℕ

/-- Actual original source acquisition ONCE followed by physical coefficient caching. -/
def acquire (owner : I → Fin n) (factor : I → E)
    (en : SemiprimeSourceLayout.Enumerations I (Fin n) E r Q) (eps : ℚ) (R B : ℕ) : SourceRun :=
  let source := SemiprimeMaterializedOriginalSource.acquire owner factor en eps R
  let encoded := encodeFamily (n:=n) (sourceBits B Q R) R en.incidences source.value
  ⟨encoded.value,source.work,encoded.work,source.work+encoded.work+1⟩

/-- Every exported physical source cell is exact, legal and bounded from original inputs. -/
theorem acquire_read (owner : I → Fin n) (factor : I → E)
    (en : SemiprimeSourceLayout.Enumerations I (Fin n) E r Q) (eps : ℚ) (R B : ℕ)
    (howner : ∀ v,(Finset.univ.filter (fun i => owner i=v)).card≤B)
    (hQ : 1≤Q) (hAQ : Subexp.TailInterval.intervalStart r Q R≤Q)
    (i : I) (v : Fin n) (k : Fin (R+1)) :
    let row := (readWords en.incidences (acquire owner factor en eps R B).words i v).value
    ∃ hk : k.val<row.size,
      (row[k.val]'hk).value=((SemiprimeSourceLayout.builtLayout owner factor en eps R).row i v).coeff k.val ∧
      (row[k.val]'hk).Valid ∧ Width (row[k.val]'hk) (sourceBits B Q R+1) := by
  dsimp only [acquire]
  rw [encodeFamily_read]
  refine ⟨by simpa only [acquireRow,encodeArray,Array.size_map,Array.size_ofFn] using k.isLt,?_⟩
  have h := acquireRow_source owner factor en eps R B howner hQ hAQ i v k
  dsimp only at h
  have hc : coefficient (readSource en.incidences
      (SemiprimeMaterializedOriginalSource.acquire owner factor en eps R).value i v).value k.val=
      ((SemiprimeSourceLayout.builtLayout owner factor en eps R).row i v).coeff k.val := by
    exact (congrArg (fun a => coefficient a k.val) (readSource_value en.incidences
      (SemiprimeMaterializedOriginalSource.acquire owner factor en eps R).value i v)).trans
      (SemiprimeMaterializedOriginalSource.acquire_coefficient owner factor en eps R i v k.val (by omega))
  exact ⟨h.1.trans hc,h.2⟩

/-- Stored original source row; runtime users may retain `readWords.work` alongside it. -/
def acquiredRow (owner : I → Fin n) (factor : I → E)
    (en : SemiprimeSourceLayout.Enumerations I (Fin n) E r Q) (eps : ℚ) (R B : ℕ)
    (i : I) (v : Fin n) : Array RationalWord :=
  (readWords en.incidences (acquire owner factor en eps R B).words i v).value

/-- Every physical source row has exactly R+1 stored coefficients. -/
theorem acquire_row_size (owner : I → Fin n) (factor : I → E)
    (en : SemiprimeSourceLayout.Enumerations I (Fin n) E r Q) (eps : ℚ) (R B : ℕ)
    (i : I) (v : Fin n) : (acquiredRow owner factor en eps R B i v).size=R+1 := by
  unfold acquiredRow acquire
  dsimp only
  rw [encodeFamily_read]
  exact encodeArray_size _ _ _

/-- All actual physical source denominators are legal, from original source assumptions. -/
theorem acquire_row_valid (owner : I → Fin n) (factor : I → E)
    (en : SemiprimeSourceLayout.Enumerations I (Fin n) E r Q) (eps : ℚ) (R B : ℕ)
    (howner : ∀ v,(Finset.univ.filter (fun i => owner i=v)).card≤B)
    (hQ : 1≤Q) (hAQ : Subexp.TailInterval.intervalStart r Q R≤Q)
    (i : I) (v : Fin n) : SemiprimeJetBits.Valid (acquiredRow owner factor en eps R B i v) := by
  intro k hk
  have hkR : k<R+1 := by rwa [acquire_row_size] at hk
  obtain ⟨hp,h⟩ := acquire_read owner factor en eps R B howner hQ hAQ i v ⟨k,hkR⟩
  exact h.2.1

/-- All actual physical source words have the derived parameter-only width. -/
theorem acquire_row_bounded (owner : I → Fin n) (factor : I → E)
    (en : SemiprimeSourceLayout.Enumerations I (Fin n) E r Q) (eps : ℚ) (R B : ℕ)
    (howner : ∀ v,(Finset.univ.filter (fun i => owner i=v)).card≤B)
    (hQ : 1≤Q) (hAQ : Subexp.TailInterval.intervalStart r Q R≤Q)
    (i : I) (v : Fin n) :
    SemiprimeJetBits.Bounded (acquiredRow owner factor en eps R B i v) (sourceBits B Q R+1) := by
  intro k hk
  have hkR : k<R+1 := by rwa [acquire_row_size] at hk
  obtain ⟨hp,h⟩ := acquire_read owner factor en eps R B howner hQ hAQ i v ⟨k,hkR⟩
  exact h.2.2

/-- Decoded acquired coefficients are exactly the actual original layout coefficients. -/
theorem acquire_coefficient (owner : I → Fin n) (factor : I → E)
    (en : SemiprimeSourceLayout.Enumerations I (Fin n) E r Q) (eps : ℚ) (R B : ℕ)
    (howner : ∀ v,(Finset.univ.filter (fun i => owner i=v)).card≤B)
    (hQ : 1≤Q) (hAQ : Subexp.TailInterval.intervalStart r Q R≤Q)
    (i : I) (v : Fin n) (k : ℕ) (hk : k≤R) :
    coefficient (SemiprimeJetBits.decode (acquiredRow owner factor en eps R B i v)) k=
      ((SemiprimeSourceLayout.builtLayout owner factor en eps R).row i v).coeff k := by
  have hkR : k<R+1 := by omega
  obtain ⟨hp,h⟩ := acquire_read owner factor en eps R B howner hQ hAQ i v ⟨k,hkR⟩
  rw [SemiprimeJetBits.coefficient_decode]
  change ((acquiredRow owner factor en eps R B i v)[k]?.getD _).value=_
  rw [Array.getElem?_eq_getElem (by rw [acquire_row_size]; exact hkR)]
  exact h.1

/-- The physical source supplies the SAME common representation used by corrected-port bounds. -/
theorem acquire_representation (owner : I → Fin n) (factor : I → E)
    (en : SemiprimeSourceLayout.Enumerations I (Fin n) E r Q) (eps : ℚ) (R B : ℕ)
    (howner : ∀ v,(Finset.univ.filter (fun i => owner i=v)).card≤B)
    (hQ : 1≤Q) (hAQ : Subexp.TailInterval.intervalStart r Q R≤Q)
    (i : I) (v : Fin n) (k : ℕ) (hk : k≤R) :
    Representation (coefficient (SemiprimeJetBits.decode (acquiredRow owner factor en eps R B i v)) k)
      (rowDenominator Q R) (B*2^rowNumeratorExponent Q R) := by
  apply SemiprimeLocalExecutionHeight.builtLayout_source_bound owner factor en eps R B howner hQ hAQ i v _
    (fun k hk => acquire_coefficient owner factor en eps R B howner hQ hAQ i v k hk) k hk

/-- The full cache report retains actual source production and a closed encoding polynomial. -/
theorem acquire_work (owner : I → Fin n) (factor : I → E)
    (en : SemiprimeSourceLayout.Enumerations I (Fin n) E r Q) (eps : ℚ) (R B : ℕ) :
    (acquire owner factor en eps R B).work≤
      (SemiprimeMaterializedOriginalSource.acquire owner factor en eps R).work+
      encodingBudget en.incidences.values.length n (sourceBits B Q R) R+1 := by
  exact Nat.add_le_add_right (Nat.add_le_add_left
    (encodeFamily_work (sourceBits B Q R) R en.incidences
      (SemiprimeMaterializedOriginalSource.acquire owner factor en eps R).value) _) 1

end RiemannGaussian.SemiprimeSourceWordAcquisition
