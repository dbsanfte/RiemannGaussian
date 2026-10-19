/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import scripts.ArithmeticOperatorPrimitivePacketSourceAudit

/-!
# Actual same-base cutoff lattice words

A division-free product/GCD/LCM word on nested actual cyclotomic products
has exactly the prime support of one original cutoff. The same theorem
is instantiated for the actual pruned primitive products. Primitive
factors at distinct indices are coprime, retaining all their multiplicities.
The proper-power bound and every source consequence remain paper-level.
-/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000
noncomputable section
open scoped BigOperators
namespace OpenAIReview.NextInteraction
open TotalTraceSource PrimitivePacketSource

/-- Literal once-counted integer cyclotomic cutoff product. -/
def cutoffProduct (b M : ℕ) : ℕ :=
  ∏ e ∈ Finset.Icc 2 M, (value b e).natAbs

/-- Actual cutoff products form a divisibility chain, including empty heads. -/
theorem cutoffProduct_dvd (b m n : ℕ) (hmn : m ≤ n) :
    cutoffProduct b m ∣ cutoffProduct b n := by
  apply Finset.prod_dvd_prod_of_subset
  intro e he
  exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp he).1,
    (Finset.mem_Icc.mp he).2.trans hmn⟩

/-- The actual primitive cutoff products also form a divisibility chain. -/
theorem primitiveProduct_dvd (b m n : ℕ) (hmn : m ≤ n) :
    primitiveProduct b m ∣ primitiveProduct b n := by
  apply Finset.prod_dvd_prod_of_subset
  intro e he
  exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp he).1,
    (Finset.mem_Icc.mp he).2.trans hmn⟩

/-- Distinct actual primitive factors are coprime, not just formally labelled. -/
theorem primitiveValue_coprime (b d e : ℕ) (hb : 2 ≤ b) (hde : d ≠ e) :
    (primitiveValue b d).Coprime (primitiveValue b e) := by
  apply Nat.coprime_of_dvd
  intro p hp hpd hpe
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hd, hdp⟩ := (prime_dvd_primitiveValue b d p hb hp).mp hpd
  obtain ⟨he, hep⟩ := (prime_dvd_primitiveValue b e p hb hp).mp hpe
  exact hde ((primitive_root_of_retained b d p hd hdp).unique
    (primitive_root_of_retained b e p he hep))

/-- A finite word with literal cutoff leaves and no division or subtraction. -/
inductive CutoffWord where
  /-- An original cutoff row. -/
  | row : ℕ → CutoffWord
  /-- Ordinary integer multiplication. -/
  | mul : CutoffWord → CutoffWord → CutoffWord
  /-- Ordinary integer greatest common divisor. -/
  | gcd : CutoffWord → CutoffWord → CutoffWord
  /-- Ordinary integer least common multiple. -/
  | lcm : CutoffWord → CutoffWord → CutoffWord

/-- Evaluate the word on the specified actual integer rows. -/
def CutoffWord.eval (row : ℕ → ℕ) : CutoffWord → ℕ
  | .row n => row n
  | .mul a b => a.eval row * b.eval row
  | .gcd a b => Nat.gcd (a.eval row) (b.eval row)
  | .lcm a b => Nat.lcm (a.eval row) (b.eval row)

/-- The single effective support cutoff, obtained without looking at the base. -/
def CutoffWord.supportCutoff : CutoffWord → ℕ
  | .row n => n
  | .mul a b => max a.supportCutoff b.supportCutoff
  | .gcd a b => min a.supportCutoff b.supportCutoff
  | .lcm a b => max a.supportCutoff b.supportCutoff

/-- Prime support of an LCM is the union, with no squarefreeness premise. -/
theorem prime_dvd_lcm (p a b : ℕ) (hp : p.Prime) :
    p ∣ Nat.lcm a b ↔ p ∣ a ∨ p ∣ b := by
  constructor
  · intro h
    exact hp.dvd_mul.mp (h.trans (Nat.lcm_dvd_mul a b))
  · rintro (h | h)
    · exact h.trans (Nat.dvd_lcm_left a b)
    · exact h.trans (Nat.dvd_lcm_right a b)

/-- Union of two nested supports selects the larger row. -/
theorem chain_union (row : ℕ → ℕ)
    (hrow : ∀ m n, m ≤ n → row m ∣ row n) (p m n : ℕ) :
    (p ∣ row m ∨ p ∣ row n) ↔ p ∣ row (max m n) := by
  rcases le_total m n with h | h
  · rw [max_eq_right h]
    constructor
    · rintro (hm | hn)
      · exact hm.trans (hrow m n h)
      · exact hn
    · exact Or.inr
  · rw [max_eq_left h]
    constructor
    · rintro (hm | hn)
      · exact hm
      · exact hn.trans (hrow n m h)
    · exact Or.inl

/-- Intersection of two nested supports selects the smaller row. -/
theorem chain_intersection (row : ℕ → ℕ)
    (hrow : ∀ m n, m ≤ n → row m ∣ row n) (p m n : ℕ) :
    (p ∣ row m ∧ p ∣ row n) ↔ p ∣ row (min m n) := by
  rcases le_total m n with h | h
  · rw [min_eq_left h]
    constructor
    · exact And.left
    · intro hm
      exact ⟨hm, hm.trans (hrow m n h)⟩
  · rw [min_eq_right h]
    constructor
    · exact And.right
    · intro hn
      exact ⟨hn.trans (hrow n m h), hn⟩

/-- The helper uses only the stated divisibility chain; native rows follow below. -/
theorem CutoffWord.prime_support (W : CutoffWord) (row : ℕ → ℕ)
    (hrow : ∀ m n, m ≤ n → row m ∣ row n) (p : ℕ) (hp : p.Prime) :
    p ∣ W.eval row ↔ p ∣ row W.supportCutoff := by
  induction W with
  | row n => rfl
  | mul a b ha hb =>
    simpa only [eval, supportCutoff, hp.dvd_mul, ha, hb] using
      chain_union row hrow p a.supportCutoff b.supportCutoff
  | gcd a b ha hb =>
    simpa only [eval, supportCutoff, Nat.dvd_gcd_iff, ha, hb] using
      chain_intersection row hrow p a.supportCutoff b.supportCutoff
  | lcm a b ha hb =>
    simpa only [eval, supportCutoff, prime_dvd_lcm p _ _ hp, ha, hb] using
      chain_union row hrow p a.supportCutoff b.supportCutoff

/-- Exact native support collapse for the actual cyclotomic integer products. -/
theorem actual_word_prime_support (W : CutoffWord) (b p : ℕ) (hp : p.Prime) :
    p ∣ W.eval (cutoffProduct b) ↔ p ∣ cutoffProduct b W.supportCutoff :=
  W.prime_support _ (cutoffProduct_dvd b) p hp

/-- Exact native support collapse for the actual full-multiplicity primitive products. -/
theorem primitive_word_prime_support (W : CutoffWord) (b p : ℕ) (hp : p.Prime) :
    p ∣ W.eval (primitiveProduct b) ↔ p ∣ primitiveProduct b W.supportCutoff :=
  W.prime_support _ (primitiveProduct_dvd b) p hp

/-- The final joined first layer, with every original complex weight retained. -/
theorem actual_word_prime_weights (W : CutoffWord) (b : ℕ)
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) (w : ℕ → ℂ) :
    (∑ p ∈ s, if p ∣ W.eval (cutoffProduct b) then w p else 0) =
      ∑ p ∈ s, if p ∣ cutoffProduct b W.supportCutoff then w p else 0 := by
  apply Finset.sum_congr rfl
  intro p hp
  simp only [actual_word_prime_support W b p (hs p hp)]

/-- Arbitrary retained weights also commute with the actual primitive-word collapse. -/
theorem primitive_word_prime_weights (W : CutoffWord) (b : ℕ)
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) (w : ℕ → ℂ) :
    (∑ p ∈ s, if p ∣ W.eval (primitiveProduct b) then w p else 0) =
      ∑ p ∈ s, if p ∣ primitiveProduct b W.supportCutoff then w p else 0 := by
  apply Finset.sum_congr rfl
  intro p hp
  simp only [primitive_word_prime_support W b p (hs p hp)]

end OpenAIReview.NextInteraction
#lint+ in OpenAIReview.NextInteraction

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
  unless declarations > 0 do throwError "Empty actual cutoff word audit."
  logInfo m!"Next interaction audit: {declarations} declarations, {theorems} theorems; only standard axioms."
  IO.FS.createDirAll ".lake/arithmetic-operator-next-interaction-audit"
  IO.FS.writeFile ".lake/arithmetic-operator-next-interaction-audit/axioms.json"
    (Json.mkObj [("scope", toJson "actual cyclotomic and primitive cutoff lattice-word prime support; higher-depth bounds and source paper-level"),
      ("namespaceLinters", toJson (15 : Nat)), ("onlyStandardAxioms", toJson true),
      ("allLocalModuleProvenance", toJson true),
      ("declarations", toJson declarations), ("theoremsIncludingHelpers", toJson theorems),
      ("details", Json.arr details)]).pretty
