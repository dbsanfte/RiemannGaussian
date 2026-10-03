/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeWindowConstruction

/-!
# Charged Euclidean inverse acquisition for the retained window

Euclid maintains its two coefficients modulo the public input. The actual
quotients, products and reductions are retained, including initialization.
These arithmetic counts and bounded operands do not yet certify a complete
bit implementation or universal one-sixth semiprime coverage.
-/

namespace RiemannGaussian.SemiprimeWindowInverse

open SemiprimeWindowConstruction SemiprimeTotientWindow

/-- Every actual state and temporary of one positive Euclidean step. -/
structure EuclidFrame where
  /-- First current remainder. -/
  first : ℕ
  /-- Positive second current remainder. -/
  second : ℕ
  /-- Reduced coefficient of the first remainder. -/
  firstCoefficient : ℕ
  /-- Reduced coefficient of the second remainder. -/
  secondCoefficient : ℕ
  /-- Actual Euclidean quotient. -/
  quotient : ℕ
  /-- Actual next remainder. -/
  remainder : ℕ
  /-- Unreduced coefficient product. -/
  product : ℕ
  /-- That product reduced modulo the public input. -/
  productResidue : ℕ
  /-- The first coefficient plus one modulus before subtraction. -/
  padded : ℕ
  /-- Actual reduced coefficient of the next remainder. -/
  nextCoefficient : ℕ

/-- Compute one quotient, one product, three remainders, one addition and
one natural subtraction. No signed or unreduced Bezout coefficients grow. -/
def makeFrame (N r0 r1 c0 c1 : ℕ) : EuclidFrame :=
  let quotient := r0/r1
  let remainder := r0%r1
  let product := quotient*c1
  let productResidue := product%N
  let padded := c0+N
  let nextCoefficient := (padded-productResidue)%N
  ⟨r0,r1,c0,c1,quotient,remainder,product,productResidue,padded,nextCoefficient⟩

/-- Actual Euclidean output, charged arithmetic and the complete state trace. -/
structure InverseReport where
  /-- The gcd computed by this run. -/
  gcd : ℕ
  /-- Its canonical modular coefficient. -/
  coefficient : ℕ
  /-- Number of positive Euclidean steps. -/
  steps : ℕ
  /-- All actual quotient calls. -/
  quotients : ℕ
  /-- All actual coefficient multiplications. -/
  multiplications : ℕ
  /-- All actual remainder calls, including initial normalization if present. -/
  reductions : ℕ
  /-- Every positive step, in its execution order. -/
  trace : List EuclidFrame

/-- Executable Euclid keeps coefficients reduced after every actual update. -/
def euclidLoop (N r0 r1 c0 c1 : ℕ) : InverseReport :=
  if hz : r1=0 then
    ⟨r0,c0,0,0,0,0,[]⟩
  else
    let frame := makeFrame N r0 r1 c0 c1
    let tail := euclidLoop N r1 frame.remainder c1 frame.nextCoefficient
    ⟨tail.gcd,tail.coefficient,tail.steps+1,tail.quotients+1,
      tail.multiplications+1,tail.reductions+3,frame::tail.trace⟩
termination_by r1
decreasing_by exact Nat.mod_lt _ (Nat.pos_of_ne_zero hz)

/-- Modular subtraction is performed without truncating the intended
difference: the padded coefficient exceeds the reduced product. -/
theorem makeFrame_coefficient {N : ℕ} (hN : 0<N) (r0 r1 c0 c1 : ℕ) :
    ((makeFrame N r0 r1 c0 c1).nextCoefficient : ZMod N)=
      (c0 : ZMod N)-(r0/r1 : ℕ)*(c1 : ZMod N) := by
  have hm : r0/r1*c1%N≤c0+N := by have h:=Nat.mod_lt (r0/r1*c1) hN; omega
  simp only [makeFrame,ZMod.natCast_mod,Nat.cast_sub hm,Nat.cast_add,
    ZMod.natCast_self,Nat.cast_mul,add_zero]

/-- The exact modular remainder-coefficient invariant survives each step. -/
theorem makeFrame_invariant {N : ℕ} (hN : 0<N) (a r0 r1 c0 c1 : ℕ)
    (hc0 : (c0 : ZMod N)*(a : ZMod N)=(r0 : ZMod N))
    (hc1 : (c1 : ZMod N)*(a : ZMod N)=(r1 : ZMod N)) :
    ((makeFrame N r0 r1 c0 c1).nextCoefficient : ZMod N)*(a : ZMod N)=
      ((makeFrame N r0 r1 c0 c1).remainder : ZMod N) := by
  have hd := congrArg (fun n : ℕ => (n : ZMod N)) (Nat.mod_add_div r0 r1)
  simp only [Nat.cast_add,Nat.cast_mul] at hd
  rw [makeFrame_coefficient hN]
  change _=((r0%r1 : ℕ) : ZMod N)
  linear_combination hc0-(r0/r1 : ℕ)*hc1-hd

/-- The actual returned Euclidean gcd equals the public natural gcd. -/
theorem euclidLoop_gcd (N r0 r1 c0 c1 : ℕ) :
    (euclidLoop N r0 r1 c0 c1).gcd=Nat.gcd r0 r1 := by
  induction r1 using Nat.strong_induction_on generalizing r0 c0 c1 with
  | h r1 ih =>
    by_cases hz : r1=0
    · subst r1
      rw [euclidLoop,dif_pos rfl]
      exact (Nat.gcd_zero_right r0).symm
    · rw [euclidLoop,dif_neg hz]
      dsimp only [makeFrame]
      rw [ih _ (Nat.mod_lt _ (Nat.pos_of_ne_zero hz))]
      exact (Nat.gcd_comm _ _).trans
        ((Nat.gcd_rec r1 r0).symm.trans (Nat.gcd_comm r1 r0))

/-- The returned coefficient represents the returned gcd modulo N. -/
theorem euclidLoop_invariant {N : ℕ} (hN : 0<N) (a r0 r1 c0 c1 : ℕ)
    (hc0 : (c0 : ZMod N)*(a : ZMod N)=(r0 : ZMod N))
    (hc1 : (c1 : ZMod N)*(a : ZMod N)=(r1 : ZMod N)) :
    ((euclidLoop N r0 r1 c0 c1).coefficient : ZMod N)*(a : ZMod N)=
      ((euclidLoop N r0 r1 c0 c1).gcd : ZMod N) := by
  induction r1 using Nat.strong_induction_on generalizing r0 c0 c1 with
  | h r1 ih =>
    by_cases hz : r1=0
    · subst r1
      rw [euclidLoop,dif_pos rfl]
      exact hc0
    · rw [euclidLoop,dif_neg hz]
      dsimp only
      exact ih _ (Nat.mod_lt _ (Nat.pos_of_ne_zero hz)) _ _ _ hc1
        (makeFrame_invariant hN a r0 r1 c0 c1 hc0 hc1)

/-- Coefficient reduction is maintained through the complete actual run. -/
theorem euclidLoop_coefficient_lt {N : ℕ} (hN : 0<N) (r0 r1 c0 c1 : ℕ)
    (hc0 : c0<N) (hc1 : c1<N) : (euclidLoop N r0 r1 c0 c1).coefficient<N := by
  induction r1 using Nat.strong_induction_on generalizing r0 c0 c1 with
  | h r1 ih =>
    by_cases hz : r1=0
    · subst r1
      rw [euclidLoop,dif_pos rfl]
      exact hc0
    · rw [euclidLoop,dif_neg hz]
      dsimp only
      exact ih _ (Nat.mod_lt _ (Nat.pos_of_ne_zero hz)) _ _ _ hc1 (Nat.mod_lt _ hN)

/-- The counters and trace charge exactly the operations of this loop. -/
theorem euclidLoop_counts (N r0 r1 c0 c1 : ℕ) :
    (euclidLoop N r0 r1 c0 c1).quotients=(euclidLoop N r0 r1 c0 c1).steps ∧
    (euclidLoop N r0 r1 c0 c1).multiplications=(euclidLoop N r0 r1 c0 c1).steps ∧
    (euclidLoop N r0 r1 c0 c1).reductions=3*(euclidLoop N r0 r1 c0 c1).steps ∧
    (euclidLoop N r0 r1 c0 c1).trace.length=(euclidLoop N r0 r1 c0 c1).steps := by
  induction r1 using Nat.strong_induction_on generalizing r0 c0 c1 with
  | h r1 ih =>
    by_cases hz : r1=0
    · subst r1
      rw [euclidLoop,dif_pos rfl]
      simp only [Nat.mul_zero,List.length_nil,and_self]
    · have ht := ih (r0%r1) (Nat.mod_lt _ (Nat.pos_of_ne_zero hz)) r1 c1
        (makeFrame N r0 r1 c0 c1).nextCoefficient
      rw [euclidLoop,dif_neg hz]
      dsimp only [makeFrame,List.length_cons] at ht ⊢
      omega

/-- In two consecutive positive Euclidean steps the second remainder
is at most half the earlier divisor. -/
theorem euclid_remainder_half {b c : ℕ} (hc : 0<c) (hcb : c<b) : b%c≤b/2 := by
  have hr := Nat.mod_lt b hc
  by_cases hsmall : c≤b/2
  · omega
  · have hq := Nat.div_pos (by omega : c≤b) hc
    have hm : c≤c*(b/c) := by simpa using Nat.mul_le_mul_left c hq
    have hd := Nat.mod_add_div b c
    omega

/-- Actual Euclidean depth is bounded by twice the initial divisor's
binary length, including cases where the first remainder is larger. -/
theorem euclidLoop_steps (N r0 r1 c0 c1 : ℕ) :
    (euclidLoop N r0 r1 c0 c1).steps≤2*Nat.clog 2 (r1+1) := by
  induction r1 using Nat.strong_induction_on generalizing r0 c0 c1 with
  | h r1 ih =>
    by_cases hz : r1=0
    · subst r1
      rw [euclidLoop,dif_pos rfl]
      exact Nat.zero_le _
    · have hp := Nat.pos_of_ne_zero hz
      have hl := clog_halving hp
      have hr := Nat.mod_lt r0 hp
      rw [euclidLoop,dif_neg hz]
      dsimp only [makeFrame]
      by_cases hc : r0%r1=0
      · rw [euclidLoop,dif_pos hc]
        dsimp only
        omega
      · have hcp := Nat.pos_of_ne_zero hc
        have hh := euclid_remainder_half hcp hr
        have hlt : r1%(r0%r1)<r1 := lt_of_le_of_lt hh (Nat.div_lt_self hp (by decide))
        have ht := ih _ hlt (r0%r1)
          ((c0+N-(r0/r1*c1)%N)%N)
          ((c1+N-((r1/(r0%r1))*((c0+N-(r0/r1*c1)%N)%N))%N)%N)
        have hm := Nat.clog_mono_right 2 (Nat.add_le_add_right hh 1)
        rw [euclidLoop,dif_neg hc]
        dsimp only [makeFrame]
        omega

/-- Compute a modular gcd coefficient from N and a alone. The two
initial residue reductions are retained in the actual operation report. -/
def countedInverse (N a : ℕ) : InverseReport :=
  let report := euclidLoop N N (a%N) 0 (1%N)
  { report with reductions := report.reductions+2 }

/-- The returned gcd is correct even for a nonunit input. -/
theorem countedInverse_gcd (N a : ℕ) : (countedInverse N a).gcd=Nat.gcd N a := by
  rw [countedInverse,euclidLoop_gcd,Nat.gcd_rec N a,Nat.gcd_comm]

/-- Every returned coefficient is canonical for a positive public modulus. -/
theorem countedInverse_coefficient_lt {N : ℕ} (hN : 0<N) (a : ℕ) :
    (countedInverse N a).coefficient<N :=
  euclidLoop_coefficient_lt hN _ _ _ _ hN (Nat.mod_lt _ hN)

/-- The executable inverse actually satisfies its modular gcd equation. -/
theorem countedInverse_correct {N : ℕ} (hN : 0<N) (a : ℕ) :
    ((countedInverse N a).coefficient : ZMod N)*(a : ZMod N)=
      (Nat.gcd N a : ZMod N) := by
  have h := euclidLoop_invariant hN a N (a%N) 0 (1%N)
    (by simp) (by simp only [ZMod.natCast_mod,Nat.cast_one,one_mul])
  simpa only [countedInverse,euclidLoop_gcd,Nat.gcd_rec N a,Nat.gcd_comm] using h

/-- All inverse arithmetic is logarithmic in the public modulus: one
quotient and one multiplication per step, three reductions per step,
and both initial normalizations. -/
theorem countedInverse_budget {N : ℕ} (hN : 0<N) (a : ℕ) :
    (countedInverse N a).steps≤2*Nat.clog 2 (N+1) ∧
    (countedInverse N a).quotients=(countedInverse N a).steps ∧
    (countedInverse N a).multiplications=(countedInverse N a).steps ∧
    (countedInverse N a).reductions=3*(countedInverse N a).steps+2 ∧
    (countedInverse N a).trace.length=(countedInverse N a).steps := by
  have hs := euclidLoop_steps N N (a%N) 0 (1%N)
  have hm := Nat.clog_mono_right 2 (Nat.add_le_add_right (Nat.le_of_lt (Nat.mod_lt a hN)) 1)
  obtain ⟨hq,hp,hr,ht⟩ := euclidLoop_counts N N (a%N) 0 (1%N)
  dsimp only [countedInverse]
  exact ⟨by omega,hq,hp,by omega,ht⟩

/-- Bounds on all states and temporaries in an actual Euclidean frame. -/
def FrameBounded (N : ℕ) (frame : EuclidFrame) : Prop :=
  frame.first≤N ∧ frame.second≤N ∧ 0<frame.second ∧
  frame.firstCoefficient<N ∧ frame.secondCoefficient<N ∧ frame.quotient≤N ∧
  frame.remainder<frame.second ∧ frame.product<N^2 ∧ frame.productResidue<N ∧
  frame.padded<2*N ∧ frame.nextCoefficient<N

/-- Bounded input remainders and reduced coefficients yield only bounded
temporaries, including the literal product before residue reduction. -/
theorem makeFrame_bounded {N r0 r1 c0 c1 : ℕ} (hN : 0<N)
    (hr0 : r0≤N) (hr1 : r1≤N) (hp : 0<r1) (hc0 : c0<N) (hc1 : c1<N) :
    FrameBounded N (makeFrame N r0 r1 c0 c1) := by
  have hq : r0/r1≤N := le_trans (Nat.div_le_self _ _) hr0
  have hproduct : r0/r1*c1<N^2 := by
    calc
      r0/r1*c1≤N*c1 := Nat.mul_le_mul_right c1 hq
      _<N*N := Nat.mul_lt_mul_of_pos_left hc1 hN
      _=N^2 := by rw [pow_two]
  exact ⟨hr0,hr1,hp,hc0,hc1,hq,Nat.mod_lt _ hp,hproduct,
    Nat.mod_lt _ hN,by dsimp only [makeFrame]; omega,Nat.mod_lt _ hN⟩

/-- Every frame retained by the recursive run satisfies the same bounds;
this checks all intermediate states rather than only the returned inverse. -/
theorem euclidLoop_trace_bounded {N : ℕ} (hN : 0<N) (r0 r1 c0 c1 : ℕ)
    (hr0 : r0≤N) (hr1 : r1≤N) (hc0 : c0<N) (hc1 : c1<N) :
    ∀ frame∈(euclidLoop N r0 r1 c0 c1).trace,FrameBounded N frame := by
  induction r1 using Nat.strong_induction_on generalizing r0 c0 c1 with
  | h r1 ih =>
    by_cases hz : r1=0
    · subst r1
      rw [euclidLoop,dif_pos rfl]
      intro frame hf
      exact False.elim (List.not_mem_nil hf)
    · have hp := Nat.pos_of_ne_zero hz
      have hrem := Nat.mod_lt r0 hp
      rw [euclidLoop,dif_neg hz]
      dsimp only
      intro frame hf
      rcases List.mem_cons.mp hf with rfl | hf
      · exact makeFrame_bounded hN hr0 hr1 hp hc0 hc1
      · exact ih _ hrem _ _ _ hr1 (le_trans (Nat.le_of_lt hrem) hr1) hc1
          (Nat.mod_lt _ hN) frame hf

/-- The entire natural-only inverse trace has bounded public-input states. -/
theorem countedInverse_trace_bounded {N : ℕ} (hN : 0<N) (a : ℕ) :
    ∀ frame∈(countedInverse N a).trace,FrameBounded N frame :=
  euclidLoop_trace_bounded hN _ _ _ _ le_rfl (Nat.le_of_lt (Nat.mod_lt _ hN))
    hN (Nat.mod_lt _ hN)

/-- Every integer below the modulus squared needs at most twice the
public input's binary width. This is an operand bound, not a bit backend. -/
theorem below_square_bit_width {N t : ℕ} (ht : t<N^2) :
    Nat.clog 2 (t+1)≤2*Nat.clog 2 (N+1) := by
  have hm : t+1≤N^2 := by omega
  have hn := Nat.le_pow_clog (by decide : 1<(2 : ℕ)) (N+1)
  have hs := Nat.pow_le_pow_left (by omega : N≤2^Nat.clog 2 (N+1)) 2
  apply Nat.clog_le_of_le_pow
  calc
    t+1≤N^2 := hm
    _≤(2^Nat.clog 2 (N+1))^2 := hs
    _=2^(2*Nat.clog 2 (N+1)) := by rw [←pow_mul]; congr 1; omega

/-- Every inverse product has at most 2L bits and every padded coefficient
at most L+1 bits, with L the width of the public modulus. -/
theorem countedInverse_temporary_widths {N : ℕ} (hN : 0<N) (a : ℕ)
    {frame : EuclidFrame} (hf : frame∈(countedInverse N a).trace) :
    Nat.clog 2 (frame.product+1)≤2*Nat.clog 2 (N+1) ∧
      Nat.clog 2 (frame.padded+1)≤Nat.clog 2 (N+1)+1 := by
  obtain ⟨_,_,_,_,_,_,_,hp,_,hpad,_⟩ := countedInverse_trace_bounded hN a frame hf
  constructor
  · exact below_square_bit_width hp
  · have hn := Nat.le_pow_clog (by decide : 1<(2 : ℕ)) (N+1)
    apply Nat.clog_le_of_le_pow
    rw [pow_succ]
    omega

/-- A public unit makes the actual returned gcd equal to one. -/
theorem countedInverse_unit_gcd {N : ℕ} (h : (ZMod N)ˣ) :
    (countedInverse N (h : ZMod N).val).gcd=1 := by
  rw [countedInverse_gcd,Nat.gcd_comm]
  exact ZMod.val_coe_unit_coprime h

/-- The computed canonical coefficient is exactly the actual unit inverse;
the unit is used for proof, never supplied as advice to the executable code. -/
theorem countedInverse_unit {N : ℕ} [NeZero N] (h : (ZMod N)ˣ) :
    (countedInverse N (h : ZMod N).val).coefficient=
      ((h⁻¹ : (ZMod N)ˣ) : ZMod N).val := by
  have hN : 0<N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hc := countedInverse_correct hN (h : ZMod N).val
  have hg : Nat.gcd N (h : ZMod N).val=1 := by
    rw [←countedInverse_gcd]
    exact countedInverse_unit_gcd h
  rw [hg,Nat.cast_one,ZMod.natCast_zmod_val] at hc
  have he : ((countedInverse N (h : ZMod N).val).coefficient : ZMod N)=
      ((h⁻¹ : (ZMod N)ˣ) : ZMod N) := by
    calc
      _=((countedInverse N (h : ZMod N).val).coefficient : ZMod N)*
          ((h : ZMod N)*((h⁻¹ : (ZMod N)ˣ) : ZMod N)) := by rw [h.mul_inv,mul_one]
      _=1*((h⁻¹ : (ZMod N)ˣ) : ZMod N) := by rw [←mul_assoc,hc]
      _=_ := one_mul _
  have hv := congrArg ZMod.val he
  simpa only [ZMod.val_natCast,Nat.mod_eq_of_lt (countedInverse_coefficient_lt hN _)] using hv

/-- Retain the actual inverse run even when its input is not a unit. -/
structure InitialisedSource (N : ℕ) where
  /-- The actual charged inverse computation. -/
  inverse : InverseReport
  /-- Actual ready window, constructed only when the gcd equals one. -/
  source : Option (ReadySource N)

/-- Natural-only initialization computes its inverse rather than accepting
an inverse, order, factor or coverage witness as an algorithm input. -/
def initialiseSource (N a B : ℕ) : InitialisedSource N :=
  let inverse := countedInverse N a
  let source := if inverse.gcd=1 then
    some (prepareSource (buildRawSource N a inverse.coefficient B)) else none
  ⟨inverse,source⟩

/-- All actual multiplications, including inverse acquisition. -/
def initialMultiplications {N : ℕ} (source : InitialisedSource N) : ℕ :=
  source.inverse.multiplications+
    (source.source.map fun ready => rawMultiplications ready.raw).getD 0

/-- All actual reductions, including both inverse input normalizations. -/
def initialReductions {N : ℕ} (source : InitialisedSource N) : ℕ :=
  source.inverse.reductions+
    (source.source.map fun ready => rawReductions ready.raw).getD 0

/-- Actual binary-power halvings, separately from inverse quotients. -/
def initialHalvings {N : ℕ} (source : InitialisedSource N) : ℕ :=
  (source.source.map fun ready => rawHalvings ready.raw).getD 0

/-- A proof-side unit guarantees successful initialization with the exact
canonical inverse, without adding it to the executable input interface. -/
theorem initialiseSource_unit {N : ℕ} [NeZero N] (h : (ZMod N)ˣ) (B : ℕ) :
    (initialiseSource N (h : ZMod N).val B).source=
      some (prepareSource (buildRawSource N (h : ZMod N).val
        ((h⁻¹ : (ZMod N)ˣ) : ZMod N).val B)) := by
  dsimp only [initialiseSource]
  rw [if_pos (countedInverse_unit_gcd h),countedInverse_unit h]

/-- The inverse is acquired once and its complete report is retained. -/
theorem initialiseSource_inverse (N a B : ℕ) :
    (initialiseSource N a B).inverse=countedInverse N a := rfl

/-- Nonunits are rejected by the actual gcd result, retaining their report. -/
theorem initialiseSource_nonunit {N a : ℕ} (hg : Nat.gcd N a≠1) (B : ℕ) :
    (initialiseSource N a B).source=none := by
  dsimp only [initialiseSource]
  rw [countedInverse_gcd,if_neg hg]

/-- Every certified actual window is rebuilt from its public scalar alone,
with identical sorted arrays, collision and checked factor. -/
theorem windowCertified_initialisation {N : ℕ}
    {window : SemiprimeTotientWindow.Source N} (hw : WindowCertified window) :
    ∃ ready,(initialiseSource N window.active.val.val
      (SemiprimeLehmanCoverage.sixthWidth N)).source=some ready ∧
      ready.babies=window.babies ∧ ready.giants=window.giants ∧
      ready.collision=window.collision ∧ ready.factor=window.factor := by
  cases hw with
  | @remaining p q g h z s hp hq hdata =>
    let : NeZero (p*q) := ⟨Nat.mul_ne_zero hp.ne_zero hq.ne_zero⟩
    have hw := WindowCertified.remaining hp hq hdata
    obtain ⟨hb,hg,hc,hf⟩ := windowCertified_reconstruction hw
    refine ⟨_,?_,hb,hg,hc,hf⟩
    exact initialiseSource_unit h _

/-- The complete arithmetic initialization at public width pays inverse
work in addition to both powers and walks. Sorting and the square root
retain their separate charges; arithmetic primitives are not unit bit costs. -/
theorem initialiseSource_budget {N : ℕ} (hN : 0<N) (a : ℕ) :
    initialMultiplications (initialiseSource N a (SemiprimeLehmanCoverage.sixthWidth N))≤
      4*SemiprimeLehmanCoverage.sixthWidth N+6*Nat.clog 2 (N+1)+2 ∧
    initialReductions (initialiseSource N a (SemiprimeLehmanCoverage.sixthWidth N))≤
      8*SemiprimeLehmanCoverage.sixthWidth N+12*Nat.clog 2 (N+1)+7 ∧
    (initialiseSource N a (SemiprimeLehmanCoverage.sixthWidth N)).inverse.quotients≤
      2*Nat.clog 2 (N+1) ∧
    initialHalvings (initialiseSource N a (SemiprimeLehmanCoverage.sixthWidth N))≤
      2*Nat.clog 2 (N+1)+1 := by
  obtain ⟨hs,hq,hp,hr,_⟩ := countedInverse_budget hN a
  obtain ⟨hm,hred,hh⟩ := buildRawSource_public_counts hN a (countedInverse N a).coefficient
  dsimp only [initialMultiplications,initialReductions,initialHalvings,initialiseSource]
  split <;> simp only [Option.map_some,Option.getD_some,Option.map_none,Option.getD_none,
    prepareSource] <;> omega

/-- Initialization of every actual public leaf fits the ORIGINAL input's
width and bit length, including all inverse quotients and reductions. -/
theorem publicWindow_initialisation_budget {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    {window : SemiprimeTotientWindow.Source
      (SemiprimeKernelDescent.leafInput (SemiprimeTotientWindow.publicPacket (p*q)).parent.source)}
    (hs : (SemiprimeTotientWindow.publicPacket (p*q)).source=some window) :
    let N := SemiprimeKernelDescent.leafInput (SemiprimeTotientWindow.publicPacket (p*q)).parent.source
    let source := initialiseSource N window.active.val.val (SemiprimeLehmanCoverage.sixthWidth N)
    initialMultiplications source≤4*SemiprimeLehmanCoverage.sixthWidth (p*q)+6*Nat.clog 2 (p*q+1)+2 ∧
    initialReductions source≤8*SemiprimeLehmanCoverage.sixthWidth (p*q)+12*Nat.clog 2 (p*q+1)+7 ∧
    source.inverse.quotients≤2*Nat.clog 2 (p*q+1) ∧
    initialHalvings source≤2*Nat.clog 2 (p*q+1)+1 := by
  have hw := publicWindow_source_certified hp hq hs
  have hbounds := windowCertified_input_bounds hw
  have hN : 0<SemiprimeKernelDescent.leafInput
      (SemiprimeTotientWindow.publicPacket (p*q)).parent.source := by
    omega
  have hb := initialiseSource_budget hN window.active.val.val
  have hn := SemiprimeLongPowerRouting.certified_leaf_input_le
    (SemiprimeKernelDescent.publicTrace_certified hp hq)
  have hwidth := SemiprimeKernelDescent.sixthWidth_mono hn
  have hl := Nat.clog_mono_right 2 (Nat.add_le_add_right hn 1)
  dsimp only
  change SemiprimeKernelDescent.leafInput
    (SemiprimeTotientWindow.publicPacket (p*q)).parent.source≤p*q at hn
  change SemiprimeLehmanCoverage.sixthWidth
    (SemiprimeKernelDescent.leafInput (SemiprimeTotientWindow.publicPacket (p*q)).parent.source)≤
      SemiprimeLehmanCoverage.sixthWidth (p*q) at hwidth
  change Nat.clog 2
    (SemiprimeKernelDescent.leafInput (SemiprimeTotientWindow.publicPacket (p*q)).parent.source+1)≤
      Nat.clog 2 (p*q+1) at hl
  omega

end RiemannGaussian.SemiprimeWindowInverse
