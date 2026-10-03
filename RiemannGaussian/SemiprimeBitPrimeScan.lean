/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeBitProductSort

/-!
# Boolean products and first-gap scanning after witness sorting

Full product words and arithmetic reports remain upstream of the gap
result. Comparisons, equality tests, increments and width fitting use
Boolean routines only. Declared clocks count those primitives and stated
list/flag/output cells. Input root acquisition, event generation, encoding
and complete machine/memory refinement remain separate obligations.
-/

namespace RiemannGaussian.SemiprimeBitPrimeScan

open SemiprimeBitArithmetic SemiprimeBitDivision SemiprimeBitProductSort SemiprimePrimeSieve

/-- The complete nonzero test equals false exactly at value zero. -/
theorem nonzeroBits_false_iff (bits : List Bool) :
    (nonzeroBits bits).nonzero=false ↔ bitValue bits=0 := by
  have h := nonzeroBits_correct bits
  constructor
  · intro hb
    by_contra hn
    have hp := h.mpr (by omega)
    rw [hb] at hp
    contradiction
  · intro hz
    cases hb : (nonzeroBits bits).nonzero with
    | false => rfl
    | true => have hp := h.mp hb; omega

/-- Full subtraction and zero-test reports before their ordering flags. -/
structure WordOrder where
  /-- Actual subtraction word and final borrow. -/
  difference : SubReport
  /-- Actual OR scan of the whole difference word. -/
  nonzero : NonzeroReport
  /-- No borrow and a zero difference, computed using Boolean gates. -/
  equal : Bool
  /-- Primitive clocks and two NOT gates, AND gate and output cell. -/
  clock : ℕ

/-- Compare without evaluating either word as a natural number. -/
def orderWords (left right : List Bool) : WordOrder :=
  let difference := subBits left right false
  let nonzero := nonzeroBits difference.result.bits
  ⟨difference,nonzero,!difference.borrow && !nonzero.nonzero,
    bitCost difference.result+nonzero.clock+4⟩

theorem orderWords_less (left right : List Bool) :
    (orderWords left right).difference.borrow=true ↔ bitValue left<bitValue right := by
  simpa only [orderWords,bitNat,Bool.false_eq_true,if_false,Nat.add_zero] using
    subBits_borrow_iff left right false

/-- Equality is proved from the retained borrow and full difference word;
an underflow or high-zero-padded encoding cannot create a false equality. -/
theorem orderWords_equal (left right : List Bool) :
    (orderWords left right).equal=true ↔ bitValue left=bitValue right := by
  simp only [orderWords,Bool.and_eq_true,Bool.not_eq,Bool.not_eq_true]
  have hl := orderWords_less left right
  change (subBits left right false).borrow=true ↔ _ at hl
  constructor
  · rintro ⟨hb,hz⟩
    have hd := subBits_difference hb
    have hzv := (nonzeroBits_false_iff _).mp hz
    have hge : bitValue right≤bitValue left := by
      by_contra hn
      have ht := hl.mpr (by omega)
      rw [hb] at ht
      contradiction
    omega
  · intro he
    have hb : (subBits left right false).borrow=false := by
      cases hb : (subBits left right false).borrow with
      | false => rfl
      | true => have ht := hl.mp hb; omega
    refine ⟨hb,(nonzeroBits_false_iff _).mpr ?_⟩
    rw [subBits_difference hb,he,Nat.sub_self]

theorem orderWords_cost {W : ℕ} {left right : List Bool}
    (hl : left.length≤W) (hr : right.length≤W) :
    (orderWords left right).clock≤15*W+7 := by
  have hs := subBits_cost left right false
  have hn := nonzeroBits_cost (subBits left right false).result.bits
  have hw := (subBits_counts left right false).2.2.2.2
  change bitCost (subBits left right false).result+
    (nonzeroBits (subBits left right false).result.bits).clock+4≤_
  omega

/-- All actual product words and their multiplication reports. -/
structure ProductWords where
  /-- Every input occurrence has its full product report, with no deduplication. -/
  products : List BitReport
  /-- All multiplication primitives and map list tests/cons cells. -/
  clock : ℕ

/-- Build products using Boolean multiplication; natural product evaluation
is confined to downstream specifications. Each list frame pays two cells. -/
def buildProducts : List WordPair → ProductWords
  | [] => ⟨[],1⟩
  | v::vs =>
    let product := mulBits v.1 v.2
    let tail := buildProducts vs
    ⟨product::tail.products,bitCost product+tail.clock+2⟩

/-- Natural product projection for proof specifications only. -/
def productValues (products : List BitReport) : List ℕ :=
  products.map fun report => bitValue report.bits

theorem productValues_cons (report : BitReport) (products : List BitReport) :
    productValues (report::products)=bitValue report.bits::productValues products := rfl

theorem buildProducts_values (rows : List WordPair) :
    productValues (buildProducts rows).products=rows.map pairValue := by
  induction rows with
  | nil => rfl
  | cons v vs ih => simp only [buildProducts,productValues,List.map_cons,mulBits_correct,pairValue] at ih ⊢; rw [ih]

theorem buildProducts_length (rows : List WordPair) :
    (buildProducts rows).products.length=rows.length := by
  induction rows with
  | nil => rfl
  | cons v vs ih => simp only [buildProducts,List.length_cons,ih]

theorem buildProducts_width {L : ℕ} {rows : List WordPair} (h : BoundedWords L rows) :
    ∀ report∈(buildProducts rows).products, report.bits.length≤3*L := by
  induction rows with
  | nil => simp [buildProducts]
  | cons v vs ih =>
    intro report hr
    simp only [buildProducts,List.mem_cons] at hr
    rcases hr with rfl|hr
    · exact (bounded_mulBits (h v List.mem_cons_self).1 (h v List.mem_cons_self).2).2
    · exact ih (fun w hw => h w (List.mem_cons_of_mem _ hw)) report hr

theorem buildProducts_cost {L : ℕ} {rows : List WordPair} (h : BoundedWords L rows) :
    (buildProducts rows).clock≤(24*(L+1)^2+3)*rows.length+1 := by
  induction rows with
  | nil => simp only [buildProducts,List.length_nil,Nat.mul_zero,Nat.zero_add,le_refl]
  | cons v vs ih =>
    have hc := (bounded_mulBits (h v List.mem_cons_self).1 (h v List.mem_cons_self).2).1
    have ht := ih (fun w hw => h w (List.mem_cons_of_mem _ hw))
    simp only [buildProducts,List.length_cons]
    nlinarith

/-- Word result and the composed actual scan clock. -/
structure GapWords where
  /-- A copied missing-candidate word, or a proved exhausted window. -/
  result : Option (List Bool)
  /-- Every subtraction, zero scan, increment, fit and stated guard/output cell. -/
  clock : ℕ
  /-- Actual recursive invocations, including terminal guards. -/
  invocations : ℕ

/-- Bound the candidate by Boolean subtraction, then compare to the next
full product. Both recursive branches consume one product occurrence.
Equality increments with Boolean addition and fits one extra limit bit. -/
def scanWordGaps (candidate limit : List Bool) (products : List BitReport) : GapWords :=
    let bound := subBits limit candidate false
    if bound.borrow=true then ⟨none,bitCost bound.result+2,1⟩
    else
      match hp : products with
      | [] =>
        let output := fitBits candidate candidate
        ⟨some output.bits,bitCost bound.result+bitCost output+3,1⟩
      | product::products =>
        let order := orderWords candidate product.bits
        if order.difference.borrow=true then
          let output := fitBits candidate candidate
          ⟨some output.bits,bitCost bound.result+order.clock+bitCost output+4,1⟩
        else if order.equal=true then
          let increment := addBits candidate [true] false
          let next := fitBits increment.bits (false::limit)
          let tail := scanWordGaps next.bits limit products
          ⟨tail.result,bitCost bound.result+order.clock+bitCost increment+bitCost next+tail.clock+5,
            tail.invocations+1⟩
        else
          let tail := scanWordGaps candidate limit products
          ⟨tail.result,bitCost bound.result+order.clock+tail.clock+4,tail.invocations+1⟩
termination_by products.length
decreasing_by
  all_goals simp only [List.length_cons]; omega

/-- The increment data path is Boolean addition of literal one. -/
theorem incrementBits_value (candidate : List Bool) :
    bitValue (addBits candidate [true] false).bits=bitValue candidate+1 := by
  simpa only [bitValue,bitNat,if_true,Bool.false_eq_true,if_false,Nat.mul_zero,Nat.add_zero] using
    addBits_correct candidate [true] false

/-- One extra limit bit suffices for the next candidate even at the upper
endpoint. Fitting preserves the actual increment; it does not wrap silently. -/
theorem fittedIncrement_value {candidate limit : List Bool}
    (h : bitValue candidate≤bitValue limit) :
    bitValue (fitBits (addBits candidate [true] false).bits (false::limit)).bits=
      bitValue candidate+1 := by
  have hl := bitValue_lt_width limit
  have hp : 0<(2 : ℕ)^limit.length := pow_pos (by decide) _
  have hw : bitValue (addBits candidate [true] false).bits<2^(false::limit).length := by
    rw [incrementBits_value]
    simp only [List.length_cons,pow_succ]
    omega
  rw [fitBits_value hw,incrementBits_value]

theorem fittedIncrement_width (candidate limit : List Bool) :
    (fitBits (addBits candidate [true] false).bits (false::limit)).bits.length=limit.length+1 := by
  exact (fitBits_counts _ _).1

/-- A false upper-limit borrow is the exact downstream window condition. -/
theorem withinLimit_iff (candidate limit : List Bool) :
    ¬(subBits limit candidate false).borrow=true ↔ bitValue candidate≤bitValue limit := by
  simpa only [bitNat,Bool.false_eq_true,if_false,Nat.add_zero,Nat.not_lt] using
    not_congr (subBits_borrow_iff limit candidate false)

/-- The actual Boolean scan equals the full previous first-gap recurrence,
for every physical encoding and product stream, even before sortedness. -/
theorem scanWordGaps_correct (candidate limit : List Bool) (products : List BitReport) :
    (scanWordGaps candidate limit products).result.map bitValue=
      firstGap (bitValue candidate) (bitValue limit+1-bitValue candidate)
        (productValues products) := by
  induction products generalizing candidate with
  | nil =>
    rw [scanWordGaps]
    split_ifs with hb
    · have hlt := (subBits_borrow_iff limit candidate false).mp hb
      have hz : bitValue limit+1-bitValue candidate=0 := by
        simp only [bitNat,Bool.false_eq_true,if_false,Nat.add_zero] at hlt
        omega
      simp only [Option.map_none,hz,firstGap]
    · have hle := (withinLimit_iff candidate limit).mp hb
      have hc : bitValue limit+1-bitValue candidate=(bitValue limit-bitValue candidate)+1 := by omega
      simp only [Option.map_some,fitBits_self,productValues,List.map_nil,hc,firstGap]
  | cons product products ih =>
    rw [scanWordGaps]
    split_ifs with hb
    · have hlt := (subBits_borrow_iff limit candidate false).mp hb
      have hz : bitValue limit+1-bitValue candidate=0 := by
        simp only [bitNat,Bool.false_eq_true,if_false,Nat.add_zero] at hlt
        omega
      simp only [Option.map_none,hz,firstGap]
    · have hle := (withinLimit_iff candidate limit).mp hb
      have hc : bitValue limit+1-bitValue candidate=(bitValue limit-bitValue candidate)+1 := by omega
      dsimp only
      split_ifs with hless heq
      · have hlt := (orderWords_less candidate product.bits).mp hless
        have hnlt : ¬bitValue product.bits<bitValue candidate := by omega
        have hneq : ¬bitValue product.bits=bitValue candidate := by omega
        simp only [Option.map_some,fitBits_self,productValues_cons,hc,firstGap,
          if_neg hnlt,if_neg hneq]
      · have he := (orderWords_equal candidate product.bits).mp heq
        have hnlt : ¬bitValue product.bits<bitValue candidate := by omega
        have hep : bitValue product.bits=bitValue candidate := he.symm
        dsimp only
        rw [ih,fittedIncrement_value hle]
        simp only [productValues_cons,hc,firstGap,if_neg hnlt,if_pos hep]
        congr 1
        omega
      · have hnlt : ¬bitValue candidate<bitValue product.bits :=
          fun h => hless ((orderWords_less candidate product.bits).mpr h)
        have hneq : bitValue candidate≠bitValue product.bits :=
          fun h => heq ((orderWords_equal candidate product.bits).mpr h)
        have hlt : bitValue product.bits<bitValue candidate := by omega
        dsimp only
        rw [ih]
        simp only [productValues_cons,hc,firstGap,if_pos hlt]

/-- Every scan frame has bounded physical words; all recursive calls consume
a product. Both terminal and repeated-product work are in the actual clock. -/
theorem scanWordGaps_bounds {L : ℕ} (candidate limit : List Bool) (products : List BitReport)
    (hc : candidate.length≤L+1) (hl : limit.length≤L)
    (hp : ∀ report∈products, report.bits.length≤3*L) :
    (scanWordGaps candidate limit products).clock≤
      (products.length+1)*(100*(L+1)+24) ∧
    (scanWordGaps candidate limit products).invocations≤products.length+1 := by
  have hsub : bitCost (subBits limit candidate false).result≤12*(L+1)+2 := by
    have h := subBits_cost limit candidate false
    have hw : max limit.length candidate.length≤L+1 := by omega
    omega
  have hcopy : bitCost (fitBits candidate candidate)≤4*(L+1)+1 := by
    have h := fitBits_cost candidate candidate
    omega
  induction products generalizing candidate with
  | nil =>
    rw [scanWordGaps]
    split_ifs <;> dsimp only [List.length_nil] <;> constructor <;> omega
  | cons product products ih =>
    have hwidth := hp product List.mem_cons_self
    have hpt : ∀ report∈products, report.bits.length≤3*L :=
      fun report hrep => hp report (List.mem_cons_of_mem _ hrep)
    have ht := ih candidate hc hpt hsub hcopy
    have hnwidth : (fitBits (addBits candidate [true] false).bits (false::limit)).bits.length≤L+1 := by
      rw [fittedIncrement_width]
      omega
    have hnsub : bitCost (subBits limit
        (fitBits (addBits candidate [true] false).bits (false::limit)).bits false).result≤12*(L+1)+2 := by
      have h := subBits_cost limit
        (fitBits (addBits candidate [true] false).bits (false::limit)).bits false
      have hw : max limit.length
          (fitBits (addBits candidate [true] false).bits (false::limit)).bits.length≤L+1 := by omega
      omega
    have hncopy : bitCost (fitBits
        (fitBits (addBits candidate [true] false).bits (false::limit)).bits
        (fitBits (addBits candidate [true] false).bits (false::limit)).bits)≤4*(L+1)+1 := by
      have h := fitBits_cost
        (fitBits (addBits candidate [true] false).bits (false::limit)).bits
        (fitBits (addBits candidate [true] false).bits (false::limit)).bits
      omega
    have hn := ih _ hnwidth hpt hnsub hncopy
    have ho : (orderWords candidate product.bits).clock≤45*(L+1)+7 := by
      have h := orderWords_cost (by omega : candidate.length≤3*(L+1))
        (by omega : product.bits.length≤3*(L+1))
      nlinarith
    have hi : bitCost (addBits candidate [true] false)≤11*(L+1)+4 := by
      have h := addBits_cost candidate [true] false
      have hw : max candidate.length ([true] : List Bool).length≤L+1 := by
        simp only [List.length_cons,List.length_nil]
        omega
      omega
    have hf : bitCost (fitBits (addBits candidate [true] false).bits (false::limit))≤4*(L+1)+1 := by
      have h := fitBits_cost (addBits candidate [true] false).bits (false::limit)
      simp only [List.length_cons] at h
      omega
    have hscale : 100*(L+1)+24≤((product::products).length+1)*(100*(L+1)+24) :=
      Nat.le_mul_of_pos_left _ (by simp only [List.length_cons]; omega)
    rw [scanWordGaps]
    split_ifs with hb
    · dsimp only
      constructor
      · omega
      · simp only [List.length_cons]; omega
    · dsimp only
      split_ifs <;> dsimp only [List.length_cons] <;> constructor
      all_goals nlinarith [ht.1,ht.2,hn.1,hn.2]

/-- Rich public inputs, sorted factor words, all products and the gap result
remain available before any natural modulus projection. -/
structure SieveWords where
  /-- Original physical candidate word. -/
  candidate : List Bool
  /-- Original physical public upper-limit word. -/
  limit : List Bool
  /-- Full sorted word-pair carrier and its actual sort report. -/
  sorted : WordReport
  /-- All computed product words and their multiplication reports. -/
  products : ProductWords
  /-- Actual missing-candidate word and scan report. -/
  gap : GapWords
  /-- All three stage clocks plus five declared carrier/output cells. -/
  clock : ℕ

/-- The supplied-word sorting/product/scan data path uses Boolean operations
and structural list recursion throughout. Clock arithmetic is instrumentation. -/
def runWordSieve (candidate limit : List Bool) (rows : List WordPair) : SieveWords :=
  let sorted := sortWords rows
  let products := buildProducts sorted.rows
  let gap := scanWordGaps candidate limit products.products
  ⟨candidate,limit,sorted,products,gap,sorted.clock+products.clock+gap.clock+5⟩

theorem runWordSieve_correct (candidate limit : List Bool) (rows : List WordPair) :
    (runWordSieve candidate limit rows).gap.result.map bitValue=
      firstGap (bitValue candidate) (bitValue limit+1-bitValue candidate)
        ((sortWords rows).rows.map pairValue) := by
  simpa only [runWordSieve,buildProducts_values] using
    scanWordGaps_correct candidate limit (buildProducts (sortWords rows).rows).products

/-- The complete supplied-word backend has a uniform declared primitive/list
clock; no scalar multiplication, natural equality or countdown computes it. -/
theorem runWordSieve_cost {L : ℕ} (candidate limit : List Bool) (rows : List WordPair)
    (hc : candidate.length≤L+1) (hl : limit.length≤L) (hw : BoundedWords L rows) :
    (runWordSieve candidate limit rows).clock≤
      272*(L+1)^2*(rows.length+1)*(Nat.clog 2 rows.length+1) := by
  have hs := sortWords_bounds hw
  have hp := buildProducts_cost (sortWords_bounded hw)
  have hg := scanWordGaps_bounds candidate limit
    (buildProducts (sortWords rows).rows).products hc hl
    (buildProducts_width (sortWords_bounded hw))
  simp only [buildProducts_length,sortWords_length] at hp hg
  have hpk : 24*(L+1)^2+3≤27*(L+1)^2 := by nlinarith
  have hps := Nat.mul_le_mul_right rows.length hpk
  have hpc : (buildProducts (sortWords rows).rows).clock≤27*(L+1)^2*rows.length+1 := by omega
  have hgk : 100*(L+1)+24≤124*(L+1)^2 := by nlinarith
  have hgs := Nat.mul_le_mul_left (rows.length+1) hgk
  have hgc : (scanWordGaps candidate limit (buildProducts (sortWords rows).rows).products).clock≤
      124*(L+1)^2*(rows.length+1) := by nlinarith [hg.1]
  have hbase : 27*(L+1)^2*rows.length+124*(L+1)^2*(rows.length+1)+7≤
      160*(L+1)^2*(rows.length+1) := by
    nlinarith [Nat.zero_le ((L+1)^2*rows.length)]
  have hdepth : 160*(L+1)^2*(rows.length+1)≤
      160*(L+1)^2*(rows.length+1)*(Nat.clog 2 rows.length+1) :=
    Nat.le_mul_of_pos_right _ (by omega)
  have hweight : 100*rows.length+160*(rows.length+1)≤272*(rows.length+1) := by omega
  have hscale := Nat.mul_le_mul_right ((L+1)^2*(Nat.clog 2 rows.length+1)) hweight
  change (sortWords rows).clock+(buildProducts (sortWords rows).rows).clock+
    (scanWordGaps candidate limit (buildProducts (sortWords rows).rows).products).clock+5≤_
  nlinarith [hs.1]

/-- Canonical-word input interface for the bounded public sieve. Root,
event generation and encoding are not priced by this backend report. -/
def publicWordSieve (B : ℕ) : SieveWords :=
  runWordSieve (max 2 B).bits (2*max 1 B).bits (wordEvents (2*max 1 B))

theorem publicWordSieve_correct (B : ℕ) :
    (publicWordSieve B).gap.result.map bitValue=
      firstGap (max 2 B) (2*max 1 B+1-max 2 B) (sortedValues (2*max 1 B)) := by
  rw [publicWordSieve,runWordSieve_correct,bitValue_natBits,bitValue_natBits]
  exact congrArg (firstGap (max 2 B) (2*max 1 B+1-max 2 B)) (sortedWordValues_eq _)

/-- Expose the original scan's actual successful option before its default
projection. Every composite before the least prime is marked in the window. -/
theorem firstGap_some_least (B : ℕ) (hB : 0<B) :
    firstGap (max 2 B) (2*max 1 B+1-max 2 B) (sortedValues (2*max 1 B))=
      some (SemiprimeEuclidRowBudget.publicPrimeAtLeast B hB) := by
  rw [show max 1 B=B from max_eq_right hB]
  have hp := SemiprimeEuclidRowBudget.publicPrimeAtLeast_prime B hB
  have hge := SemiprimeEuclidRowBudget.publicPrimeAtLeast_ge B hB
  have hle := SemiprimeEuclidRowBudget.publicPrimeAtLeast_le B hB
  have hs : max 2 B≤SemiprimeEuclidRowBudget.publicPrimeAtLeast B hB := max_le hp.two_le hge
  have hmissing : SemiprimeEuclidRowBudget.publicPrimeAtLeast B hB∉sortedValues (2*B) := by
    intro hm
    have he := (sortedValues_perm (2*B)).mem_iff.mp hm
    exact ((eventValues_mem_iff hp.two_le).mp he).2 hp
  have hbefore : ∀ x, max 2 B≤x → x<SemiprimeEuclidRowBudget.publicPrimeAtLeast B hB →
      x∈sortedValues (2*B) := by
    intro x hx hxp
    have hx2 : 2≤x := (le_max_left _ _).trans hx
    have hxB : B≤x := (le_max_right _ _).trans hx
    have hxX : x≤2*B := hxp.le.trans hle
    have hcomp : ¬x.Prime := by
      intro hprime
      exact (not_le_of_gt hxp)
        (SemiprimeEuclidRowBudget.publicPrimeAtLeast_minimal B hB hprime hxB)
    exact (sortedValues_perm (2*B)).mem_iff.mpr
      ((eventValues_mem_iff hx2).mpr ⟨hxX,hcomp⟩)
  rw [firstGap_eq_gapSpec _ _ _ (sortedValues_ordered _)]
  exact gapSpec_eq_some_of_firstMissing _ _ _ _ hs (by omega) hmissing hbefore

/-- Positive public input produces a genuine least-prime word; no default
value is substituted for a failed Boolean scan. -/
theorem publicWordSieve_some (B : ℕ) (hB : 0<B) :
    (publicWordSieve B).gap.result.map bitValue=
      some (SemiprimeEuclidRowBudget.publicPrimeAtLeast B hB) := by
  rw [publicWordSieve_correct]
  exact firstGap_some_least B hB

theorem publicWordSieve_word (B : ℕ) (hB : 0<B) :
    ∃ word, (publicWordSieve B).gap.result=some word ∧
      bitValue word=SemiprimeEuclidRowBudget.publicPrimeAtLeast B hB := by
  have hv := publicWordSieve_some B hB
  cases hword : (publicWordSieve B).gap.result with
  | none => rw [hword] at hv; cases hv
  | some word =>
    rw [hword,Option.map_some] at hv
    exact ⟨word,rfl,Option.some.inj hv⟩

/-- Uniform declared sort/product/scan clock for every complete actual
public event family. The root/event/encoding input interface remains unpaid. -/
theorem publicWordSieve_cost (B : ℕ) :
    (publicWordSieve B).clock≤272*(Nat.clog 2 (2*max 1 B+1)+1)^2*
      (2*max 1 B*(Nat.log2 (2*max 1 B)+1)^2+1)*
      (3*Nat.clog 2 (2*max 1 B+1)+1) := by
  have hstart : max 2 B≤2*max 1 B := by omega
  have hc := natBits_length_le hstart
  have hl := natBits_length_le (Nat.le_refl (2*max 1 B))
  have hr := runWordSieve_cost (max 2 B).bits (2*max 1 B).bits (wordEvents (2*max 1 B))
    (by omega) hl (wordEvents_bounded _)
  simp only [wordEvents_length] at hr
  have he := properPairs_length_le (2*max 1 B)
  have hd := properPairs_clog_length_le (2*max 1 B)
  have hm := Nat.mul_le_mul (Nat.add_le_add_right he 1) (Nat.add_le_add_right hd 1)
  have hs := Nat.mul_le_mul_left (272*(Nat.clog 2 (2*max 1 B+1)+1)^2) hm
  change (publicWordSieve B).clock≤_ at hr
  exact hr.trans (by simpa only [Nat.mul_assoc] using hs)

/-- Downstream natural modulus view of the proved successful word result. -/
def wordScanRowModulus (N : ℕ) : ℕ :=
  ((publicWordSieve (max 1 (SemiprimeLehmanCoverage.sixthWidth N))).gap.result.map bitValue).getD 2

theorem wordScanRowModulus_eq (N : ℕ) :
    wordScanRowModulus N=SemiprimeEuclidRowBudget.publicRowModulus N := by
  have hB : 0<max 1 (SemiprimeLehmanCoverage.sixthWidth N) := by omega
  simp only [wordScanRowModulus,publicWordSieve_some _ hB,Option.getD_some,
    SemiprimeEuclidRowBudget.publicRowModulus]

/-- The complete original row list is unchanged after the Boolean scan. -/
theorem wordScan_publicPackets_eq (N : ℕ) :
    SemiprimeEuclidRowFamily.publicPackets N (wordScanRowModulus N)=
      SemiprimeEuclidRowFamily.publicPackets N (SemiprimeEuclidRowBudget.publicRowModulus N) := by
  rw [wordScanRowModulus_eq]

/-- Shared companion recovery with the Boolean-scanned public modulus. -/
noncomputable def recoverWordScannedCompanions (N : ℕ) : Option ℕ :=
  SemiprimeReflectedCompanions.recoverReflectedCompanions N (wordScanRowModulus N)

theorem recoverWordScannedCompanions_eq (N : ℕ) : recoverWordScannedCompanions N=
    SemiprimeReflectedCompanions.recoverReflectedCompanions N
      (SemiprimeEuclidRowBudget.publicRowModulus N) := by
  rw [recoverWordScannedCompanions,wordScanRowModulus_eq]

theorem recoverWordScannedCompanions_sound {N d : ℕ}
    (h : recoverWordScannedCompanions N=some d) : SemiprimeGroupSelection.ProperDivisor N d :=
  SemiprimeReflectedCompanions.recoverReflectedCompanions_sound h

end RiemannGaussian.SemiprimeBitPrimeScan
