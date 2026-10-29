/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceArrayProgramLowering
import RiemannGaussian.SemiprimeRationalWordAcquisition

/-! # Literal-bank acquisition and physical compiled-register readout
Every input literal is encoded by the executed canonical digit loop, and the
output is read through the paid Boolean-address memory scan. Canonical integer
extraction and digit generation retain scalar ledgers; this is not a completed
primitive-bit compiler for original rational-leaf construction.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeSourceArrayProgramAcquisition
open SemiprimeRationalBits SemiprimeSourceMemoryBits SemiprimeSourceArrayProgramLowering
open SemiprimeBitArithmetic SemiprimeEncodedRowSelection

/-- Acquired physical literal words and the executed scalar/digit ledger. -/
structure BankRun where
  /-- Every original literal is encoded once, in original bank order. -/
  words : List RationalWord
  /-- Canonical extraction, digits and finite list construction. -/
  scalarWork : ℕ

/-- Encode the actual supplied original literal list, without encoded-word advice. -/
def acquireBank (bits : ℕ) : List ℚ → BankRun
  | [] => ⟨[],1⟩
  | q::qs =>
    let first := SemiprimeRationalWordAcquisition.encode bits q
    let rest := acquireBank bits qs
    ⟨first.word::rest.words,first.work+rest.scalarWork+3⟩

/-- Literal acquisition preserves the exact bank shape. -/
theorem acquireBank_length (bits : ℕ) (values : List ℚ) :
    (acquireBank bits values).words.length=values.length := by
  induction values with
  | nil => rfl
  | cons q qs ih => simp only [acquireBank,List.length_cons,ih]

/-- Every emitted physical word has the requested width regardless of its value. -/
theorem acquireBank_width (bits : ℕ) (values : List ℚ) :
    ∀ w∈(acquireBank bits values).words,Width w (bits+1) := by
  induction values with
  | nil => simp [acquireBank]
  | cons q qs ih =>
    intro w hw
    simp only [acquireBank,List.mem_cons] at hw
    rcases hw with rfl | hw
    · exact SemiprimeRationalWordAcquisition.encode_width bits q
    · exact ih w hw

/-- Original literal bounds give exact values and valid denominators throughout the bank. -/
theorem acquireBank_spec (bits : ℕ) (values : List ℚ)
    (h : ∀ q∈values,q.num.natAbs ≤ 2^bits ∧ q.den ≤ 2^bits) :
    (acquireBank bits values).words.map RationalWord.value=values ∧
      ∀ w∈(acquireBank bits values).words,w.Valid := by
  induction values with
  | nil => simp [acquireBank]
  | cons q qs ih =>
    have hq := h q List.mem_cons_self
    have ht := ih (fun r hr => h r (List.mem_cons_of_mem q hr))
    constructor
    · simp only [acquireBank,List.map_cons,
        SemiprimeRationalWordAcquisition.encode_value bits q hq.1 hq.2,ht.1]
    · intro w hw
      simp only [acquireBank,List.mem_cons] at hw
      rcases hw with rfl | hw
      · exact SemiprimeRationalWordAcquisition.encode_valid bits q hq.2
      · exact ht.2 w hw

/-- Exact retained acquisition work, with native scalar stages honestly identified. -/
theorem acquireBank_work (bits : ℕ) (values : List ℚ) :
    (acquireBank bits values).scalarWork=values.length*(8*(bits+1)+16)+1 := by
  induction values with
  | nil => simp [acquireBank]
  | cons q qs ih =>
    simp only [acquireBank,(SemiprimeRationalWordAcquisition.encode_work bits q).2,ih,List.length_cons]
    ring

/-- One physical readout with separate address-generation and Boolean-scan ledgers. -/
structure ReadRun where
  /-- The actual selected physical rational word. -/
  word : RationalWord
  /-- Native bounded address arithmetic and digit stages. -/
  scalarWork : ℕ
  /-- The actual Boolean-address scan/copy report. -/
  bitWork : ℕ

/-- Generate the output address and read it through the actual finite-memory primitive. -/
def readout (initial next B id : ℕ) (memory : List RationalWord) : ReadRun :=
  let index := digits B (address initial next id)
  let out := readWord memory index.bits
  ⟨out.word,index.work+6,out.clock⟩

/-- The selected word equals its stable-register source value under the proved relation. -/
theorem readout_value (initial next B id : ℕ) (memory : List RationalWord) (env : ℕ → ℚ)
    (hi : initial ≤ next) (hid : id < next) (hB : next ≤ 2^B)
    (hm : Represents initial next (memory.map RationalWord.value) env) :
    (readout initial next B id memory).word.value=env id := by
  have h := digits_value B (address initial next id) ((address_lt initial next id hi hid).trans_le hB)
  simp only [readout,SemiprimeSourceProgramBits.readWord_value,h]
  exact hm.2 id hid

/-- Actual finite memory validity suffices for the selected word. -/
theorem readout_valid (initial next B id : ℕ) (memory : List RationalWord)
    (h : ∀ w∈memory,w.Valid) : (readout initial next B id memory).word.Valid :=
  readWord_valid memory _ h

/-- Physical readout preserves the original width, including its zero default. -/
theorem readout_width (initial next B id W : ℕ) (memory : List RationalWord)
    (hW : 1 ≤ W) (h : ∀ w∈memory,Width w W) :
    Width (readout initial next B id memory).word W := readWord_width memory _ W hW h

/-- Both ledger components are bounded by actual memory and physical address dimensions. -/
theorem readout_work (initial next B id W : ℕ) (memory : List RationalWord)
    (hB : 1 ≤ B) (hm : ∀ w∈memory,Width w W) :
    (readout initial next B id memory).scalarWork=4*B+7 ∧
      (readout initial next B id memory).bitWork ≤
        (memory.length+1)*(8*W+15*B+30) := by
  constructor
  · simp only [readout,digits_work]
  · exact readWord_clock memory _ W B hB (digits_length _ _).le hm

end RiemannGaussian.SemiprimeSourceArrayProgramAcquisition
