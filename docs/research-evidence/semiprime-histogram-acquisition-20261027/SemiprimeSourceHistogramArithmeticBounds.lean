/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceHistogramArithmetic

/-! # Fixed-depth physical histogram arithmetic bounds
All report clocks are retained. Width premises concern only actual acquired
input payloads; every intermediate shape follows the executed raw operators.
-/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace RiemannGaussian.SemiprimeSourceHistogramArithmeticBounds
open SemiprimeRationalBits SemiprimeSourceHistogramArithmetic
open SemiprimeSourceIncidenceHistogram (Feature)
open SemiprimeReportPolynomialGrowth
/-- Enlarge only an actually proved input/output physical shape. -/
theorem widen {x : RationalWord} {A B : ℕ} (hx : Width x A) (h : A ≤ B) : Width x B :=
  ⟨hx.1.trans h,hx.2.trans h⟩

/-- Uniform raw arithmetic shape after a fixed number of operator levels. -/
def grow (W d : ℕ) : ℕ := 4^d*(W+2)

/-- One fixed quadratic budget dominates every primitive in depth at most 32. -/
def unitBudget (W : ℕ) : ℕ := 300*(grow W 32+1)^2+1000

/-- Positive widths are intrinsic to the chosen fixed arithmetic envelope. -/
theorem grow_pos (W d : ℕ) : 1 ≤ grow W d := by
  have h : 0<4^d*(W+2) := by positivity
  exact h

/-- Larger fixed depths conservatively enlarge physical shape bounds. -/
theorem grow_mono (W : ℕ) {a b : ℕ} (h : a ≤ b) : grow W a ≤ grow W b := by
  unfold grow
  gcongr

/-- Each raw binary operator fits the next fixed level. -/
theorem grow_step (W d : ℕ) : 3*grow W d+1 ≤ grow W (d+1) := by
  have hp := grow_pos W d
  simp only [grow,pow_succ]
  unfold grow at hp
  nlinarith

/-- Literal unsigned inputs are valid physical shapes. -/
theorem unsigned_width (bits : List Bool) (W : ℕ) (hW : 1 ≤ W) (hb : bits.length ≤ W) :
    Width (unsigned bits) W := ⟨hb,by simpa only [unsigned,List.length_cons,List.length_nil] using hW⟩

/-- Literal signed minus one has constant physical width. -/
theorem minusOne_width (W : ℕ) (hW : 1 ≤ W) : Width minusOne W := ⟨hW,hW⟩

/-- Static raw addition has derived next-level width and paid lower clocks. -/
theorem add_bound (x y : RationalReport) (W d : ℕ) (hd : d ≤ 32)
    (hx : Width x.word (grow W d)) (hy : Width y.word (grow W d)) :
    Width (add x y).word (grow W (d+1)) ∧
      (add x y).clock ≤ x.clock+y.clock+unitBudget W := by
  have h := rawAddBits_cost_width x.word y.word hx hy
  refine ⟨widen h.2 (grow_step W d),?_⟩
  have hg := grow_mono W hd
  have hc : 300*(grow W d+1)^2 ≤ 300*(grow W 32+1)^2 := by gcongr
  unfold add unitBudget
  dsimp only
  omega

/-- Static raw multiplication has the same fixed-depth shape/work envelope. -/
theorem mul_bound (x y : RationalReport) (W d : ℕ) (hd : d ≤ 32)
    (hx : Width x.word (grow W d)) (hy : Width y.word (grow W d)) :
    Width (mul x y).word (grow W (d+1)) ∧
      (mul x y).clock ≤ x.clock+y.clock+unitBudget W := by
  have h := rawMulBits_cost_width x.word y.word hx hy
  refine ⟨widen h.2 (grow_step W d),?_⟩
  have hg := grow_mono W hd
  have hc : 300*(grow W d+1)^2 ≤ 300*(grow W 32+1)^2 := by gcongr
  unfold mul unitBudget
  dsimp only
  omega

/-- Sign-bit negation has no unproved word-size or normalization condition. -/
theorem neg_bound (x : RationalReport) (W d : ℕ) (hx : Width x.word (grow W d)) :
    Width (neg x).word (grow W d) ∧ (neg x).clock ≤ x.clock+unitBudget W := by
  refine ⟨hx,?_⟩
  unfold neg rawNegBits unitBudget
  dsimp only
  omega

/-- All coefficient shapes and the once-only actual L−1 acquisition cost. -/
theorem coefficient_bound (L : List Bool) (W : ℕ) (hW : 1 ≤ W) (hL : L.length ≤ W) :
    (∀ f : Feature,Width (coefficientWord (coefficients L) f) (grow W 1)) ∧
      (coefficients L).clock ≤ unitBudget W := by
  have hu := unsigned_width L W hW hL
  have hm := minusOne_width W hW
  have hraw := rawAddBits_cost_width (unsigned L) minusOne hu hm
  have hgw : W ≤ grow W 0 := by simp [grow]
  have hg : W ≤ grow W 1 := hgw.trans (grow_mono W (by decide : 0 ≤ 1))
  have hp : Width (coefficients L).predecessor (grow W 1) :=
    widen hraw.2 ((Nat.add_le_add_right (Nat.mul_le_mul_left 3 hgw) 1).trans (grow_step W 0))
  refine ⟨?_,?_⟩
  · intro f
    fin_cases f
    · exact unsigned_width [true] _ (grow_pos W 1) (by simp only [List.length_cons,List.length_nil];exact grow_pos W 1)
    · exact hp
    · exact widen hu hg
    · exact widen hm hg
  · have hmax : W ≤ grow W 32 := hgw.trans (grow_mono W (by decide : 0 ≤ 32))
    have hc : 300*(W+1)^2 ≤ 300*(grow W 32+1)^2 := by gcongr
    unfold coefficients unitBudget
    dsimp only
    omega

/-- Every term's intermediate shapes and actual producer report are derived. -/
theorem term_bound (L : List Bool)
    (hist : Feature → Feature → SemiprimeSourceHistogramSquares.State) (fg : Feature × Feature)
    (W : ℕ) (hW : 1 ≤ W) (hL : L.length ≤ W)
    (hh : (hist fg.1 fg.2).bits.length ≤ W) :
    Width (term (coefficients L) hist fg).word (grow W 3) ∧
      (term (coefficients L) hist fg).clock ≤ (hist fg.1 fg.2).clock+2*unitBudget W := by
  have hs := (coefficient_bound L W hW hL).1
  have hfirst := rawMulBits_cost_width (coefficientWord (coefficients L) fg.1)
    (coefficientWord (coefficients L) fg.2) (hs fg.1) (hs fg.2)
  have hfirstw := widen hfirst.2 (grow_step W 1)
  have hu := unsigned_width (hist fg.1 fg.2).bits W hW hh
  have hW2 : W ≤ grow W 2 := (show W ≤ grow W 0 by simp [grow]).trans
    (grow_mono W (by decide : 0 ≤ 2))
  have hout := rawMulBits_cost_width
    (rawMulBits (coefficientWord (coefficients L) fg.1) (coefficientWord (coefficients L) fg.2)).word
    (unsigned (hist fg.1 fg.2).bits) hfirstw (widen hu hW2)
  refine ⟨widen hout.2 (grow_step W 2),?_⟩
  have h1 : 300*(grow W 1+1)^2 ≤ 300*(grow W 32+1)^2 := by
    have h := grow_mono W (by decide : 1 ≤ 32)
    gcongr
  have h2 : 300*(grow W 2+1)^2 ≤ 300*(grow W 32+1)^2 := by
    have h := grow_mono W (by decide : 2 ≤ 32)
    gcongr
  have houtc : (rawMulBits
      (rawMulBits (coefficientWord (coefficients L) fg.1) (coefficientWord (coefficients L) fg.2)).word
      (unsigned (hist fg.1 fg.2).bits)).clock ≤ 300*(grow W 2+1)^2 := hout.1
  unfold term unitBudget
  dsimp only
  omega

/-- The actual constant-size list fold pays every term producer and raw adder. -/
theorem sumTerms_bound (L : List Bool)
    (hist : Feature → Feature → SemiprimeSourceHistogramSquares.State)
    (pairs : List (Feature × Feature)) (W : ℕ) (hW : 1 ≤ W) (hL : L.length ≤ W)
    (hh : ∀ f g,(hist f g).bits.length ≤ W) (hlen : pairs.length ≤ 16) :
    Width (sumTerms (coefficients L) hist pairs).word (grow W (pairs.length+3)) ∧
      (sumTerms (coefficients L) hist pairs).clock ≤
        (pairs.map (fun fg => (hist fg.1 fg.2).clock)).sum+(3*pairs.length+1)*unitBudget W := by
  induction pairs with
  | nil =>
    refine ⟨⟨by simp [sumTerms,zeroWord],by simpa only [sumTerms,zeroWord,List.length_cons,List.length_nil] using grow_pos W 3⟩,?_⟩
    simp only [sumTerms,List.map_nil,List.sum_nil,List.length_nil]
    unfold unitBudget
    omega
  | cons fg pairs ih =>
    have hrest := ih (by simp only [List.length_cons] at hlen;omega)
    have hterm := term_bound L hist fg W hW hL (hh fg.1 fg.2)
    have hw := widen hterm.1 (grow_mono W (show 3 ≤ pairs.length+3 by omega))
    have hraw := rawAddBits_cost_width (term (coefficients L) hist fg).word
      (sumTerms (coefficients L) hist pairs).word hw hrest.1
    have hmax := grow_mono W (show pairs.length+3 ≤ 32 by simp only [List.length_cons] at hlen;omega)
    have hc : 300*(grow W (pairs.length+3)+1)^2 ≤ 300*(grow W 32+1)^2 := by gcongr
    refine ⟨?_,?_⟩
    · simpa only [sumTerms,List.length_cons,Nat.add_assoc] using widen hraw.2 (grow_step W (pairs.length+3))
    · have hpaid : (rawAddBits (term (coefficients L) hist fg).word
          (sumTerms (coefficients L) hist pairs).word).clock+3 ≤ unitBudget W := by
        unfold unitBudget
        omega
      simp only [sumTerms,List.map_cons,List.sum_cons,List.length_cons]
      nlinarith [hrest.2,hterm.2]

/-- Literal feature list has exactly sixteen entries. -/
theorem featurePairs_length : featurePairs.length=16 := by decide

/-- Complete physical incidence arithmetic has fixed-degree width and clock overhead.
The actual sixteen histogram report clocks are summed, never replaced by values. -/
theorem incidence_bound (cache : SemiprimeSourceHistogramScales.Cache)
    (hist : Feature → Feature → SemiprimeSourceHistogramSquares.State)
    (W : ℕ) (hW : 1 ≤ W) (hL : cache.alphabet.length ≤ W) (hS : cache.square.length ≤ W)
    (hh : ∀ f g,(hist f g).bits.length ≤ W) :
    Width (incidence cache hist).word (grow W 20) ∧
      (incidence cache hist).clock ≤
        (featurePairs.map (fun fg => (hist fg.1 fg.2).clock)).sum+60*unitBudget W := by
  have hcs := coefficient_bound cache.alphabet W hW hL
  have ht := sumTerms_bound cache.alphabet hist featurePairs W hW hL hh (by rw [featurePairs_length])
  rw [featurePairs_length] at ht
  have hu := unsigned_width cache.square W hW hS
  have hmax : W ≤ grow W 19 := (show W ≤ grow W 0 by simp [grow]).trans
    (grow_mono W (by decide : 0 ≤ 19))
  have hout := rawMulBits_cost_width (unsigned cache.square)
    (sumTerms (coefficients cache.alphabet) hist featurePairs).word (widen hu hmax) ht.1
  have hc : 300*(grow W 19+1)^2 ≤ 300*(grow W 32+1)^2 := by
    have h := grow_mono W (by decide : 19 ≤ 32)
    gcongr
  refine ⟨widen hout.2 (grow_step W 19),?_⟩
  have hpaid : (rawMulBits (unsigned cache.square)
      (sumTerms (coefficients cache.alphabet) hist featurePairs).word).clock+1000 ≤ unitBudget W := by
    have hr := hout.1
    change (rawMulBits (unsigned cache.square)
      (sumTerms (coefficients cache.alphabet) hist featurePairs).word).clock ≤ 300*(grow W 19+1)^2 at hr
    unfold unitBudget
    omega
  unfold incidence
  dsimp only
  nlinarith [hcs.2,ht.2]

/-- Actual signed head arithmetic has fixed-depth physical shape and retains
all Q/fixed/free/histogram acquisition reports once. -/
theorem head_bound (cache : SemiprimeSourceHistogramScales.Cache)
    (q p f : SemiprimeSourceCompactBits.Report) (C : RationalReport) (W : ℕ)
    (hW : 1 ≤ W) (hA : cache.fourth.length ≤ W) (hG : cache.head.length ≤ W)
    (hq : q.bits.length ≤ W) (hp : p.bits.length ≤ W) (hf : f.bits.length ≤ W)
    (hC : Width C.word W) :
    Width (head cache q p f C).word (grow W 8) ∧
      (head cache q p f C).clock ≤ q.clock+p.clock+f.clock+C.clock+30*unitBudget W := by
  let qw := borrowed (unsigned q.bits)
  let pw := borrowed (unsigned p.bits)
  let fw := borrowed (unsigned f.bits)
  let cw := borrowed C.word
  let aw := borrowed (unsigned cache.fourth)
  let gw := borrowed (unsigned cache.head)
  let tw := borrowed (unsigned [false,true])
  have hbase : W ≤ grow W 0 := by simp [grow]
  have u (bits : List Bool) (hb : bits.length ≤ W) :
      Width (borrowed (unsigned bits)).word (grow W 0) := widen (unsigned_width bits W hW hb) hbase
  have hqw := u q.bits hq
  have hpw := u p.bits hp
  have hfw := u f.bits hf
  have hcw : Width cw.word (grow W 0) := widen hC hbase
  have haw := u cache.fourth hA
  have hgw := u cache.head hG
  have htw : Width tw.word (grow W 0) := unsigned_width _ _ (grow_pos W 0) (by simp [grow])
  let qf := mul qw fw
  have hqf := mul_bound qw fw W 0 (by decide) hqw hfw
  let li := add cw qf
  have hli := add_bound cw qf W 1 (by decide)
    (widen hcw (grow_mono W (by decide : 0 ≤ 1))) hqf.1
  let left := mul aw li
  have hleft := mul_bound aw li W 2 (by decide)
    (widen haw (grow_mono W (by decide : 0 ≤ 2))) hli.1
  let tp := mul tw pw
  have htp := mul_bound tw pw W 0 (by decide) htw hpw
  let tpf := mul tp fw
  have htpf := mul_bound tp fw W 1 (by decide) htp.1
    (widen hfw (grow_mono W (by decide : 0 ≤ 1)))
  let ff := mul fw fw
  have hff := mul_bound fw fw W 0 (by decide) hfw hfw
  let positive := add tpf ff
  have hpositive := add_bound tpf ff W 2 (by decide) htpf.1
    (widen hff.1 (grow_mono W (by decide : 1 ≤ 2)))
  let nf := neg fw
  have hnf := neg_bound fw W 0 hfw
  let inner := add positive nf
  have hinner := add_bound positive nf W 3 (by decide) hpositive.1
    (widen hnf.1 (grow_mono W (by decide : 0 ≤ 3)))
  let gq := mul gw qw
  have hgq := mul_bound gw qw W 0 (by decide) hgw hqw
  let right := mul gq inner
  have hright := mul_bound gq inner W 4 (by decide)
    (widen hgq.1 (grow_mono W (by decide : 1 ≤ 4))) hinner.1
  let out := add left right
  have hout := add_bound left right W 5 (by decide)
    (widen hleft.1 (grow_mono W (by decide : 3 ≤ 5))) hright.1
  refine ⟨widen hout.1 (grow_mono W (by decide : 6 ≤ 8)),?_⟩
  have hqw0 : qw.clock=0 := rfl
  have hpw0 : pw.clock=0 := rfl
  have hfw0 : fw.clock=0 := rfl
  have hcw0 : cw.clock=0 := rfl
  have haw0 : aw.clock=0 := rfl
  have hgw0 : gw.clock=0 := rfl
  have htw0 : tw.clock=0 := rfl
  have hunit : 1000 ≤ unitBudget W := by unfold unitBudget;omega
  change q.clock+p.clock+f.clock+C.clock+out.clock+1000 ≤ _
  nlinarith [hqf.2,hli.2,hleft.2,htp.2,htpf.2,hff.2,hpositive.2,hnf.2,hinner.2,hgq.2,hright.2,hout.2]

/-- Actual weighting has three physical operators; both complete lane clocks stay. -/
theorem weighted_bound (cache : SemiprimeSourceHistogramScales.Cache) (I H : RationalReport)
    (W : ℕ) (hW : 1 ≤ W) (hA : cache.weights.incidence.length ≤ W)
    (hB : cache.weights.head.length ≤ W) (hI : Width I.word W) (hH : Width H.word W) :
    Width (weighted cache I H).word (grow W 2) ∧
      (weighted cache I H).clock ≤ I.clock+H.clock+3*unitBudget W := by
  let aw := borrowed (unsigned cache.weights.incidence)
  let bw := borrowed (unsigned cache.weights.head)
  have hbase : W ≤ grow W 0 := by simp [grow]
  have haw : Width aw.word (grow W 0) := widen (unsigned_width _ _ hW hA) hbase
  have hbw : Width bw.word (grow W 0) := widen (unsigned_width _ _ hW hB) hbase
  have hleft := mul_bound aw I W 0 (by decide) haw (widen hI hbase)
  have hright := mul_bound bw H W 0 (by decide) hbw (widen hH hbase)
  have hout := add_bound (mul aw I) (mul bw H) W 1 (by decide) hleft.1 hright.1
  refine ⟨hout.1,?_⟩
  have ha0 : aw.clock=0 := rfl
  have hb0 : bw.clock=0 := rfl
  change (add (mul aw I) (mul bw H)).clock ≤ _
  nlinarith [hleft.2,hright.2,hout.2]

/-- Original input-width caps can be enlarged without changing the executed data. -/
theorem grow_width_mono {W V : ℕ} (h : W ≤ V) (d : ℕ) : grow W d ≤ grow V d := by
  unfold grow
  gcongr

/-- Fixed-depth arithmetic budgets are monotone in actual input payload width. -/
theorem unitBudget_mono {W V : ℕ} (h : W ≤ V) : unitBudget W ≤ unitBudget V := by
  unfold unitBudget
  have hg := grow_width_mono h 32
  gcongr

/-- Constants are fixed before every source query or acquired payload width. -/
theorem unitBudget_monomial : ∃ C k : ℕ,∀ W,unitBudget W ≤ C*(W+1)^k := by
  have h : SemiprimeReportPolynomialGrowth.Bound (fun W => unitBudget W) := by
    simp only [unitBudget,grow]
    boundArithmetic
  exact h

/-- A term never discards its actual histogram producer clock. -/
theorem term_retains (cache : Coefficients)
    (hist : Feature → Feature → SemiprimeSourceHistogramSquares.State) (fg : Feature × Feature) :
    (hist fg.1 fg.2).clock ≤ (term cache hist fg).clock := by
  unfold term
  dsimp only
  omega

/-- Literal finite summation retains every actually invoked histogram producer. -/
theorem sumTerms_retains (cache : Coefficients)
    (hist : Feature → Feature → SemiprimeSourceHistogramSquares.State) (pairs : List (Feature × Feature)) :
    (pairs.map (fun fg => (hist fg.1 fg.2).clock)).sum ≤ (sumTerms cache hist pairs).clock := by
  induction pairs with
  | nil => simp [sumTerms]
  | cons fg pairs ih =>
    have ht := term_retains cache hist fg
    simp only [sumTerms,List.map_cons,List.sum_cons]
    omega

/-- Complete incidence arithmetic retains the whole actual sixteen-producer ledger. -/
theorem incidence_retains (cache : SemiprimeSourceHistogramScales.Cache)
    (hist : Feature → Feature → SemiprimeSourceHistogramSquares.State) :
    (featurePairs.map (fun fg => (hist fg.1 fg.2).clock)).sum ≤ (incidence cache hist).clock := by
  have h := sumTerms_retains (coefficients cache.alphabet) hist featurePairs
  unfold incidence
  dsimp only
  omega

/-- Actual head input acquisitions are retained independently of their values. -/
theorem head_retains (cache : SemiprimeSourceHistogramScales.Cache)
    (q p f : SemiprimeSourceCompactBits.Report) (C : RationalReport) :
    q.clock+p.clock+f.clock+C.clock ≤ (head cache q p f C).clock := by
  unfold head
  dsimp only
  omega

end RiemannGaussian.SemiprimeSourceHistogramArithmeticBounds
