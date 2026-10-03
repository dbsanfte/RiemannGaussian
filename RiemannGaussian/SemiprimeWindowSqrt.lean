/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeWindowInverse

/-!
# Charged integer square roots for the retained window

A restoring base-four recurrence computes the public centre root and the
optional quadratic-decoder root with explicit counters and bounded states.
Its exact equality to the old roots preserves every retained recovery row.
Complete primitive bit costs and universal one-sixth coverage remain open.
-/

namespace RiemannGaussian.SemiprimeWindowSqrt

open SemiprimeWindowConstruction SemiprimeWindowInverse SemiprimeTotientWindow
open SemiprimeLongPowerRouting

/-- Actual inputs and temporaries of one positive restoring-root frame. -/
structure SqrtFrame where
  /-- Public input to this recursive frame. -/
  input : ℕ
  /-- Root of the input with its final base-four digit removed. -/
  childRoot : ℕ
  /-- Remainder retained with that child root. -/
  childRemainder : ℕ
  /-- Actual final base-four digit. -/
  digit : ℕ
  /-- Four times the child remainder plus that digit. -/
  expanded : ℕ
  /-- Four times the child root plus one, the actual comparison threshold. -/
  trial : ℕ
  /-- Whether the next root bit equals one. -/
  odd : Bool
  /-- Actual root returned by this frame. -/
  root : ℕ
  /-- Actual square remainder returned by this frame. -/
  remainder : ℕ

/-- Restore one base-four digit using three constant shifts, one comparison,
two unconditional additions and at most one addition and subtraction. -/
def makeSqrtFrame (n r u : ℕ) : SqrtFrame :=
  let digit := n%4
  let expanded := 4*u+digit
  let trial := 4*r+1
  let doubled := 2*r
  if trial≤expanded then
    ⟨n,r,u,digit,expanded,trial,true,doubled+1,expanded-trial⟩
  else
    ⟨n,r,u,digit,expanded,trial,false,doubled,expanded⟩

/-- Actual root, remainder, arithmetic counts and all recursive frames. -/
structure SqrtReport where
  /-- Computed natural root. -/
  root : ℕ
  /-- Computed remainder after subtracting the square of the root. -/
  remainder : ℕ
  /-- Number of positive recursive digit pairs. -/
  steps : ℕ
  /-- Actual divisions by four. -/
  quotients : ℕ
  /-- Actual reductions modulo four. -/
  digitReductions : ℕ
  /-- Actual multiplications by two or four, each a fixed binary shift. -/
  shifts : ℕ
  /-- Actual additions including the optional root-bit addition. -/
  additions : ℕ
  /-- Actual remainder subtractions. -/
  subtractions : ℕ
  /-- Actual trial comparisons. -/
  comparisons : ℕ
  /-- Actual recursion stopping tests, including the final zero. -/
  zeroTests : ℕ
  /-- Every positive recursive frame, in descending input order. -/
  trace : List SqrtFrame

/-- Executable restoring square root does not multiply two variable
operands or call a supplied square-root implementation. -/
def countedSqrt (n : ℕ) : SqrtReport :=
  if hn : n=0 then ⟨0,0,0,0,0,0,0,0,0,1,[]⟩
  else
    let child := countedSqrt (n/4)
    let frame := makeSqrtFrame n child.root child.remainder
    let bit := if frame.odd=true then 1 else 0
    ⟨frame.root,frame.remainder,child.steps+1,child.quotients+1,
      child.digitReductions+1,child.shifts+3,child.additions+2+bit,
      child.subtractions+bit,child.comparisons+1,child.zeroTests+1,frame::child.trace⟩
termination_by n
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by decide)

/-- A single restoring step preserves the exact square/remainder equation
and the strict gap to the square of the next root. -/
theorem makeSqrtFrame_invariant {n r u : ℕ} (he : r^2+u=n/4) (hu : u≤2*r) :
    (makeSqrtFrame n r u).root^2+(makeSqrtFrame n r u).remainder=n ∧
      (makeSqrtFrame n r u).remainder≤2*(makeSqrtFrame n r u).root := by
  have hd := Nat.mod_add_div n 4
  have hmod := Nat.mod_lt n (by decide : 0<(4 : ℕ))
  unfold makeSqrtFrame
  dsimp only
  split
  · rename_i htrial
    have hsub := Nat.sub_add_cancel htrial
    constructor
    · dsimp only
      nlinarith
    · dsimp only
      omega
  · rename_i htrial
    constructor
    · dsimp only
      nlinarith
    · dsimp only
      omega

/-- The complete actual recurrence returns an exact square remainder and
the maximal natural root, for every natural input including zero. -/
theorem countedSqrt_invariant (n : ℕ) :
    (countedSqrt n).root^2+(countedSqrt n).remainder=n ∧
      (countedSqrt n).remainder≤2*(countedSqrt n).root := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n=0
    · subst n
      rw [countedSqrt,dif_pos rfl]
      exact ⟨rfl,le_rfl⟩
    · obtain ⟨he,hu⟩ := ih (n/4) (Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by decide))
      rw [countedSqrt,dif_neg hn]
      exact makeSqrtFrame_invariant he hu

/-- The executable root is exactly the preceding mathematical integer root. -/
theorem countedSqrt_correct (n : ℕ) : (countedSqrt n).root=Nat.sqrt n := by
  obtain ⟨he,hu⟩ := countedSqrt_invariant n
  apply Nat.eq_sqrt'.mpr
  constructor <;> nlinarith

/-- The retained remainder equals the literal input minus the root square. -/
theorem countedSqrt_remainder (n : ℕ) :
    (countedSqrt n).remainder=n-(Nat.sqrt n)^2 := by
  obtain ⟨he,_⟩ := countedSqrt_invariant n
  rw [countedSqrt_correct] at he
  omega

/-- Removing a base-four digit lowers the ceiling logarithm exactly once. -/
theorem clog_quartering {n : ℕ} (hn : 0<n) :
    Nat.clog 4 (n+1)=Nat.clog 4 (n/4+1)+1 := by
  have h := Nat.clog_of_two_le (by decide : 1<(4 : ℕ)) (by omega : 2≤n+1)
  have hd : (n+1+4-1)/4=n/4+1 := by omega
  rwa [hd] at h

/-- The actual positive recursion depth is exactly the number of digit pairs. -/
theorem countedSqrt_steps (n : ℕ) : (countedSqrt n).steps=Nat.clog 4 (n+1) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n=0
    · subst n
      rw [countedSqrt,dif_pos rfl]
      exact (Nat.clog_one_right 4).symm
    · have hc := ih (n/4) (Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by decide))
      rw [countedSqrt,dif_neg hn]
      dsimp only
      rw [hc,clog_quartering (Nat.pos_of_ne_zero hn)]

/-- Every retained arithmetic counter charges the actual restoring code. -/
theorem countedSqrt_counts (n : ℕ) :
    (countedSqrt n).quotients=(countedSqrt n).steps ∧
    (countedSqrt n).digitReductions=(countedSqrt n).steps ∧
    (countedSqrt n).shifts=3*(countedSqrt n).steps ∧
    (countedSqrt n).additions=2*(countedSqrt n).steps+(countedSqrt n).subtractions ∧
    (countedSqrt n).subtractions≤(countedSqrt n).steps ∧
    (countedSqrt n).comparisons=(countedSqrt n).steps ∧
    (countedSqrt n).zeroTests=(countedSqrt n).steps+1 ∧
    (countedSqrt n).trace.length=(countedSqrt n).steps := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n=0
    · subst n
      rw [countedSqrt,dif_pos rfl]
      simp only [Nat.mul_zero,Nat.zero_add,List.length_nil,le_refl,and_self]
    · have hc := ih (n/4) (Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by decide))
      rw [countedSqrt,dif_neg hn]
      dsimp only [List.length_cons]
      split <;> omega

/-- Base-four digit pairs never outnumber the public input's binary digits. -/
theorem clog_four_le_two (n : ℕ) : Nat.clog 4 (n+1)≤Nat.clog 2 (n+1) := by
  have h := Nat.le_pow_clog (by decide : 1<(2 : ℕ)) (n+1)
  exact Nat.clog_le_of_le_pow (le_trans h (Nat.pow_le_pow_left (by decide) _))

/-- All root arithmetic is logarithmic in the input size and uses only
fixed shifts, comparisons, additions, digit extraction and subtraction. -/
theorem countedSqrt_budget (n : ℕ) :
    (countedSqrt n).steps≤Nat.clog 2 (n+1) ∧
    (countedSqrt n).quotients≤Nat.clog 2 (n+1) ∧
    (countedSqrt n).digitReductions≤Nat.clog 2 (n+1) ∧
    (countedSqrt n).shifts≤3*Nat.clog 2 (n+1) ∧
    (countedSqrt n).additions≤3*Nat.clog 2 (n+1) ∧
    (countedSqrt n).subtractions≤Nat.clog 2 (n+1) ∧
    (countedSqrt n).comparisons≤Nat.clog 2 (n+1) ∧
    (countedSqrt n).zeroTests≤Nat.clog 2 (n+1)+1 := by
  have hs : (countedSqrt n).steps≤Nat.clog 2 (n+1) := by
    rw [countedSqrt_steps]
    exact clog_four_le_two n
  obtain ⟨hq,hd,hshift,ha,hsub,hc,hz,_⟩ := countedSqrt_counts n
  omega

/-- The fixed fields of a restoring frame retain their literal inputs. -/
theorem makeSqrtFrame_fields (n r u : ℕ) :
    (makeSqrtFrame n r u).input=n ∧ (makeSqrtFrame n r u).childRoot=r ∧
    (makeSqrtFrame n r u).childRemainder=u ∧ (makeSqrtFrame n r u).digit=n%4 ∧
    (makeSqrtFrame n r u).expanded=4*u+n%4 ∧ (makeSqrtFrame n r u).trial=4*r+1 := by
  unfold makeSqrtFrame
  dsimp only
  split <;> exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- Every state and temporary in a retained frame has a public-size bound. -/
def SqrtFrameBounded (N : ℕ) (frame : SqrtFrame) : Prop :=
  frame.input≤N ∧ frame.childRoot≤frame.input/4 ∧ frame.childRemainder≤frame.input/4 ∧
  frame.digit<4 ∧ frame.expanded≤frame.input ∧ frame.trial≤frame.input+1 ∧
  frame.root≤frame.input ∧ frame.remainder≤frame.input

/-- No restoring temporary exceeds the current input plus one. -/
theorem makeSqrtFrame_bounded {n r u : ℕ} (he : r^2+u=n/4) (hu : u≤2*r) :
    SqrtFrameBounded n (makeSqrtFrame n r u) := by
  obtain ⟨hi,hr,hrem,hd,hex,htrial⟩ := makeSqrtFrame_fields n r u
  obtain ⟨heout,_⟩ := makeSqrtFrame_invariant he hu
  have hself : r≤r^2 := by simpa only [pow_two] using Nat.le_mul_self r
  have houtself : (makeSqrtFrame n r u).root≤(makeSqrtFrame n r u).root^2 := by
    simpa only [pow_two] using Nat.le_mul_self (makeSqrtFrame n r u).root
  have hdiv := Nat.mod_add_div n 4
  have hmod := Nat.mod_lt n (by decide : 0<(4 : ℕ))
  unfold SqrtFrameBounded
  rw [hi,hr,hrem,hd,hex,htrial]
  exact ⟨le_rfl,by omega,by omega,hmod,by nlinarith,by omega,by omega,by omega⟩

/-- The entire recursion, including every smaller digit-prefix state,
retains the original input's bound on its actual temporaries. -/
theorem countedSqrt_trace_bounded (n : ℕ) :
    ∀ frame∈(countedSqrt n).trace,SqrtFrameBounded n frame := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n=0
    · subst n
      rw [countedSqrt,dif_pos rfl]
      intro frame hf
      exact False.elim (List.not_mem_nil hf)
    · have hlt := Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by decide : 1<(4 : ℕ))
      obtain ⟨he,hu⟩ := countedSqrt_invariant (n/4)
      rw [countedSqrt,dif_neg hn]
      dsimp only
      intro frame hf
      rcases List.mem_cons.mp hf with rfl | hf
      · exact makeSqrtFrame_bounded he hu
      · obtain ⟨hi,hrest⟩ := ih (n/4) hlt frame hf
        exact ⟨le_trans hi (Nat.div_le_self _ _),hrest⟩

/-- Actual root temporaries have at most one extra bit beyond the public
input width, uniformly across every positive recursive frame. -/
theorem countedSqrt_temporary_widths (n : ℕ) {frame : SqrtFrame}
    (hf : frame∈(countedSqrt n).trace) :
    Nat.clog 2 (frame.expanded+1)≤Nat.clog 2 (n+1) ∧
      Nat.clog 2 (frame.trial+1)≤Nat.clog 2 (n+1)+1 := by
  obtain ⟨hi,_,_,_,he,ht,_,_⟩ := countedSqrt_trace_bounded n frame hf
  constructor
  · exact Nat.clog_mono_right 2 (by omega)
  · have hn := Nat.le_pow_clog (by decide : 1<(2 : ℕ)) (n+1)
    apply Nat.clog_le_of_le_pow
    rw [pow_succ]
    omega

/-- Retain every computed input and both charged backend reports of the
optional quadratic decoder. The gcd uses the existing counted Euclid. -/
structure DecoderReport where
  /-- Actual public sum signal. -/
  signal : ℕ
  /-- Actual nonnegative quadratic discriminant. -/
  discriminant : ℕ
  /-- Actual square root computation and its complete report. -/
  squareRoot : SqrtReport
  /-- Actual candidate from the quadratic formula. -/
  candidate : ℕ
  /-- Actual counted Euclidean gcd computation of N and the candidate. -/
  gcdRun : InverseReport
  /-- Proper divisor returned after checking the computed gcd. -/
  factor : Option ℕ

/-- Compute the quadratic candidate with restoring sqrt and counted Euclid.
The signal reduction, discriminant product and candidate halving are separate
explicit operations in addition to the two retained recursive reports. -/
def countedDecoder (N m : ℕ) : DecoderReport :=
  let signal := (N+1)%m
  let discriminant := signal*signal-4*N
  let squareRoot := countedSqrt discriminant
  let candidate := (signal-squareRoot.root)/2
  let gcdRun := countedInverse N candidate
  let factor := if 1<gcdRun.gcd ∧ gcdRun.gcd<N then some gcdRun.gcd else none
  ⟨signal,discriminant,squareRoot,candidate,gcdRun,factor⟩

/-- The counted quadratic candidate equals the existing public specification. -/
theorem countedDecoder_candidate (N m : ℕ) :
    (countedDecoder N m).candidate=sumCandidate N m := by
  simp only [countedDecoder,countedSqrt_correct,sumCandidate,sumSignal,pow_two]

/-- The fully computed gcd check returns exactly the existing decoded factor. -/
theorem countedDecoder_factor (N m : ℕ) :
    (countedDecoder N m).factor=recoverKnownOrder N m := by
  unfold countedDecoder recoverKnownOrder SemiprimeGroupSelection.checkedSignal
  dsimp only
  rw [countedInverse_gcd,countedSqrt_correct]
  simp only [sumCandidate,sumSignal,pow_two]

/-- The counted decoder never returns an improper divisor. -/
theorem countedDecoder_sound {N m d : ℕ} (hf : (countedDecoder N m).factor=some d) :
    SemiprimeGroupSelection.ProperDivisor N d := by
  rw [countedDecoder_factor] at hf
  exact recoverKnownOrder_sound hf

/-- The actual sum signal cannot exceed N+1, even when the proposed modulus
is zero or otherwise incorrect. Its discriminant remains at most N squared. -/
theorem countedDecoder_input_bounds {N : ℕ} (hN : 0<N) (m : ℕ) :
    (countedDecoder N m).signal≤N+1 ∧ (countedDecoder N m).discriminant≤N^2 ∧
      (countedDecoder N m).candidate≤N := by
  have hs := Nat.mod_le (N+1) m
  have hd : ((N+1)%m)^2≤(N+1)^2 := Nat.pow_le_pow_left hs 2
  dsimp only [countedDecoder]
  constructor
  · exact hs
  constructor
  · rw [←pow_two]
    have hupper : ((N+1)%m)^2≤N^2+4*N := by nlinarith
    omega
  · omega

/-- The decoder root input has at most twice the original input's bit width. -/
theorem countedDecoder_root_bits {N : ℕ} (hN : 0<N) (m : ℕ) :
    Nat.clog 2 ((countedDecoder N m).discriminant+1)≤2*Nat.clog 2 (N+1) := by
  have hd := (countedDecoder_input_bounds hN m).2.1
  have hn := Nat.le_pow_clog (by decide : 1<(2 : ℕ)) (N+1)
  have hs := Nat.pow_le_pow_left hn 2
  have he : (countedDecoder N m).discriminant+1≤(N+1)^2 := by nlinarith
  apply Nat.clog_le_of_le_pow
  calc
    _≤(N+1)^2 := he
    _≤(2^Nat.clog 2 (N+1))^2 := hs
    _=2^(2*Nat.clog 2 (N+1)) := by rw [←pow_mul]; congr 1; omega

/-- Both recursive decoder backends fit logarithmic ORIGINAL-input bounds,
with no supplied gcd, root or factor. -/
theorem countedDecoder_budget {N : ℕ} (hN : 0<N) (m : ℕ) :
    (countedDecoder N m).squareRoot.steps≤2*Nat.clog 2 (N+1) ∧
    (countedDecoder N m).gcdRun.quotients≤2*Nat.clog 2 (N+1) ∧
    (countedDecoder N m).gcdRun.multiplications≤2*Nat.clog 2 (N+1) ∧
    (countedDecoder N m).gcdRun.reductions≤6*Nat.clog 2 (N+1)+2 := by
  have hr := (countedSqrt_budget (countedDecoder N m).discriminant).1
  have hbits := countedDecoder_root_bits hN m
  have hg := countedInverse_budget hN (countedDecoder N m).candidate
  change (countedDecoder N m).squareRoot.steps≤_ at hr
  change (countedDecoder N m).gcdRun.steps≤_ ∧
    (countedDecoder N m).gcdRun.quotients=(countedDecoder N m).gcdRun.steps ∧
    (countedDecoder N m).gcdRun.multiplications=(countedDecoder N m).gcdRun.steps ∧
    (countedDecoder N m).gcdRun.reductions=3*(countedDecoder N m).gcdRun.steps+2 ∧ _ at hg
  omega

/-- Raw arithmetic construction at an explicitly computed public centre. -/
def rawAtCentre (N a inverse B centre : ℕ) : RawSource N :=
  let block := 2*B
  let target := countedPower N a centre
  let step := countedPower N inverse block
  let babies := countedWalk N 1 a block 0
  let giants := countedWalk N target.value step.value block 0
  ⟨a,inverse,centre,block,target,step,babies,giants⟩

/-- Actual centre-root report, ready rows and optional decoder report. -/
structure RootedSource (N : ℕ) where
  /-- The actual restoring computation of the public centre root. -/
  centreRoot : SqrtReport
  /-- Actual raw data, sorted rows, collision and factor. -/
  ready : ReadySource N
  /-- The actual decoder, constructed only after a global collision. -/
  decoder : Option DecoderReport

/-- The retained window computes both roots and the optional decoder gcd
with the counted implementations, caching every actual report once. -/
def buildRootedSource (N a inverse B : ℕ) : RootedSource N :=
  let centreRoot := countedSqrt N
  let centre := (N+1-2*centreRoot.root)/4
  let raw := rawAtCentre N a inverse B centre
  let babies := SemiprimeProgressionPrefix.sortedRecords raw.babies.records
  let giants := SemiprimeProgressionPrefix.sortedRecords raw.giants.records
  let collision := SemiprimeProgressionPrefix.matchSorted babies giants
  let decoder := collision.map fun (i,j) => countedDecoder N (centre-(raw.block*j+i))
  let factor := decoder.bind fun report => report.factor
  let ready := ReadySource.mk raw babies giants collision factor
  ⟨centreRoot,ready,decoder⟩

/-- The actual computed centre produces the exact preceding raw rows. -/
theorem buildRootedSource_raw (N a inverse B : ℕ) :
    (buildRootedSource N a inverse B).ready.raw=buildRawSource N a inverse B := by
  change rawAtCentre N a inverse B ((N+1-2*(countedSqrt N).root)/4)=_
  rw [countedSqrt_correct]
  rfl

/-- Optional counted decoding keeps precisely the old global candidate. -/
theorem optionalDecoder_factor (N centre block : ℕ) (collision : Option (ℕ×ℕ)) :
    ((collision.map fun (i,j) => countedDecoder N (centre-(block*j+i))).bind
      fun report => report.factor)=
      match collision with
      | none => none
      | some (i,j) => recoverKnownOrder N (centre-(block*j+i)) := by
  cases collision with
  | none => rfl
  | some pair => exact countedDecoder_factor _ _

/-- Every ready field equals the preceding source after all root and gcd
implementations are substituted, including unsuccessful candidates. -/
theorem buildRootedSource_ready (N a inverse B : ℕ) :
    (buildRootedSource N a inverse B).ready=prepareSource (buildRawSource N a inverse B) := by
  unfold buildRootedSource
  dsimp only
  rw [countedSqrt_correct,optionalDecoder_factor]
  rfl

/-- Retain inverse acquisition and the optional fully constructed source. -/
structure RootedInitialSource (N : ℕ) where
  /-- Actual inverse acquisition report, including nonunit results. -/
  inverse : InverseReport
  /-- Actual window, only present after the unit test succeeds. -/
  source : Option (RootedSource N)

/-- N, its public active scalar and width are the only executable inputs. -/
def initialiseRootedSource (N a B : ℕ) : RootedInitialSource N :=
  let inverse := countedInverse N a
  let source := if inverse.gcd=1 then
    some (buildRootedSource N a inverse.coefficient B) else none
  ⟨inverse,source⟩

/-- The new natural-only source equals the earlier initialization on both
unit and nonunit inputs, retaining every successful or failed window result. -/
theorem initialiseRootedSource_ready (N a B : ℕ) :
    (initialiseRootedSource N a B).source.map (fun source => source.ready)=
      (initialiseSource N a B).source := by
  dsimp only [initialiseRootedSource,initialiseSource]
  split
  · simp only [Option.map_some,buildRootedSource_ready]
  · rfl

/-- Every certified actual public window is rebuilt with identical arrays,
global equality and factor, using counted roots and the counted decoder gcd. -/
theorem windowCertified_rooted_initialisation {N : ℕ}
    {window : SemiprimeTotientWindow.Source N} (hw : WindowCertified window) :
    ∃ source,(initialiseRootedSource N window.active.val.val
      (SemiprimeLehmanCoverage.sixthWidth N)).source=some source ∧
      source.ready.babies=window.babies ∧ source.ready.giants=window.giants ∧
      source.ready.collision=window.collision ∧ source.ready.factor=window.factor := by
  obtain ⟨ready,hs,hb,hg,hc,hf⟩ := windowCertified_initialisation hw
  have he := initialiseRootedSource_ready N window.active.val.val (SemiprimeLehmanCoverage.sixthWidth N)
  rw [hs] at he
  cases hsource : (initialiseRootedSource N window.active.val.val
      (SemiprimeLehmanCoverage.sixthWidth N)).source with
  | none => rw [hsource] at he; cases he
  | some source =>
    rw [hsource] at he
    have hready : source.ready=ready := Option.some.inj he
    refine ⟨source,rfl,?_,?_,?_,?_⟩ <;> rw [hready] <;> assumption

/-- All variable-operand products in inverse, rows and optional decoder,
including the collision offset and the quadratic discriminant square. -/
def rootedMultiplications {N : ℕ} (source : RootedInitialSource N) : ℕ :=
  source.inverse.multiplications+(source.source.map fun rooted =>
    rawMultiplications rooted.ready.raw+
      (rooted.decoder.map fun report => report.gcdRun.multiplications+2).getD 0).getD 0

/-- All general remainder calls in inverse, rows and optional decoder.
Base-four digit extraction is retained separately in each root report. -/
def rootedReductions {N : ℕ} (source : RootedInitialSource N) : ℕ :=
  source.inverse.reductions+(source.source.map fun rooted =>
    rawReductions rooted.ready.raw+
      (rooted.decoder.map fun report => report.gcdRun.reductions+1).getD 0).getD 0

/-- Every Euclidean quotient, including the optional candidate gcd. -/
def rootedEuclidQuotients {N : ℕ} (source : RootedInitialSource N) : ℕ :=
  source.inverse.quotients+(source.source.map fun rooted =>
    (rooted.decoder.map fun report => report.gcdRun.quotients).getD 0).getD 0

/-- Every actual restoring digit pair across centre and optional decoder. -/
def rootedSqrtSteps {N : ℕ} (source : RootedInitialSource N) : ℕ :=
  (source.source.map fun rooted => rooted.centreRoot.steps+
    (rooted.decoder.map fun report => report.squareRoot.steps).getD 0).getD 0

/-- All actual binary-power halvings, separately from restoring division. -/
def rootedHalvings {N : ℕ} (source : RootedInitialSource N) : ℕ :=
  (source.source.map fun rooted => rawHalvings rooted.ready.raw).getD 0

/-- Optional decoding keeps bounded work even for a false global candidate,
and costs nothing when there is no retained collision. -/
theorem optionalDecoder_budget {N : ℕ} (hN : 0<N) (centre block : ℕ)
    (collision : Option (ℕ×ℕ)) :
    let decoder := collision.map fun (i,j) => countedDecoder N (centre-(block*j+i))
    (decoder.map fun report => report.gcdRun.multiplications+2).getD 0≤2*Nat.clog 2 (N+1)+2 ∧
    (decoder.map fun report => report.gcdRun.reductions+1).getD 0≤6*Nat.clog 2 (N+1)+3 ∧
    (decoder.map fun report => report.gcdRun.quotients).getD 0≤2*Nat.clog 2 (N+1) ∧
    (decoder.map fun report => report.squareRoot.steps).getD 0≤2*Nat.clog 2 (N+1) := by
  cases collision with
  | none => dsimp only; exact ⟨Nat.zero_le _,Nat.zero_le _,Nat.zero_le _,Nat.zero_le _⟩
  | some pair =>
    have hd := countedDecoder_budget hN (centre-(block*pair.2+pair.1))
    simp only [Option.map_some,Option.getD_some]
    omega

/-- The complete retained initialization and optional decoder have linear
row arithmetic plus logarithmic inverse, gcd and restoring-root work.
This remains an operation-count theorem, not a full primitive bit backend. -/
theorem initialiseRootedSource_budget {N : ℕ} (hN : 0<N) (a : ℕ) :
    let source := initialiseRootedSource N a (SemiprimeLehmanCoverage.sixthWidth N)
    rootedMultiplications source≤4*SemiprimeLehmanCoverage.sixthWidth N+8*Nat.clog 2 (N+1)+4 ∧
    rootedReductions source≤8*SemiprimeLehmanCoverage.sixthWidth N+18*Nat.clog 2 (N+1)+10 ∧
    rootedEuclidQuotients source≤4*Nat.clog 2 (N+1) ∧
    rootedSqrtSteps source≤3*Nat.clog 2 (N+1) ∧
    rootedHalvings source≤2*Nat.clog 2 (N+1)+1 := by
  obtain ⟨hi,hq,hp,hr,_⟩ := countedInverse_budget hN a
  obtain ⟨hm,hred,hh⟩ := buildRawSource_public_counts hN a (countedInverse N a).coefficient
  have hroot := (countedSqrt_budget N).1
  let source := buildRootedSource N a (countedInverse N a).coefficient
    (SemiprimeLehmanCoverage.sixthWidth N)
  have hdecoder := optionalDecoder_budget hN source.ready.raw.centre source.ready.raw.block
    source.ready.collision
  change (source.decoder.map fun report => report.gcdRun.multiplications+2).getD 0≤_ ∧
    (source.decoder.map fun report => report.gcdRun.reductions+1).getD 0≤_ ∧
    (source.decoder.map fun report => report.gcdRun.quotients).getD 0≤_ ∧
    (source.decoder.map fun report => report.squareRoot.steps).getD 0≤_ at hdecoder
  have hraw := buildRootedSource_raw N a (countedInverse N a).coefficient
    (SemiprimeLehmanCoverage.sixthWidth N)
  change source.ready.raw=buildRawSource N a (countedInverse N a).coefficient
    (SemiprimeLehmanCoverage.sixthWidth N) at hraw
  have hcentre : source.centreRoot=countedSqrt N := rfl
  dsimp only
  dsimp only [rootedMultiplications,rootedReductions,rootedEuclidQuotients,
    rootedSqrtSteps,rootedHalvings,initialiseRootedSource]
  split
  · simp only [Option.map_some,Option.getD_some]
    change (countedInverse N a).multiplications+(rawMultiplications source.ready.raw+
        (source.decoder.map fun report => report.gcdRun.multiplications+2).getD 0)≤_ ∧
      (countedInverse N a).reductions+(rawReductions source.ready.raw+
        (source.decoder.map fun report => report.gcdRun.reductions+1).getD 0)≤_ ∧
      (countedInverse N a).quotients+
        (source.decoder.map fun report => report.gcdRun.quotients).getD 0≤_ ∧
      source.centreRoot.steps+(source.decoder.map fun report => report.squareRoot.steps).getD 0≤_ ∧
      rawHalvings source.ready.raw≤_
    rw [hraw,hcentre]
    omega
  · simp only [Option.map_none,Option.getD_none]
    omega

/-- The actual public leaf's fully constructed window and optional decoder
fit the ORIGINAL input bounds after every retained kernel descent. -/
theorem publicWindow_rooted_initialisation_budget {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    {window : SemiprimeTotientWindow.Source
      (SemiprimeKernelDescent.leafInput (SemiprimeTotientWindow.publicPacket (p*q)).parent.source)}
    (hs : (SemiprimeTotientWindow.publicPacket (p*q)).source=some window) :
    let N := SemiprimeKernelDescent.leafInput (SemiprimeTotientWindow.publicPacket (p*q)).parent.source
    let source := initialiseRootedSource N window.active.val.val (SemiprimeLehmanCoverage.sixthWidth N)
    rootedMultiplications source≤4*SemiprimeLehmanCoverage.sixthWidth (p*q)+8*Nat.clog 2 (p*q+1)+4 ∧
    rootedReductions source≤8*SemiprimeLehmanCoverage.sixthWidth (p*q)+18*Nat.clog 2 (p*q+1)+10 ∧
    rootedEuclidQuotients source≤4*Nat.clog 2 (p*q+1) ∧
    rootedSqrtSteps source≤3*Nat.clog 2 (p*q+1) ∧
    rootedHalvings source≤2*Nat.clog 2 (p*q+1)+1 := by
  have hw := publicWindow_source_certified hp hq hs
  have hbounds := windowCertified_input_bounds hw
  have hN : 0<SemiprimeKernelDescent.leafInput
      (SemiprimeTotientWindow.publicPacket (p*q)).parent.source := by omega
  have hb := initialiseRootedSource_budget hN window.active.val.val
  have hn := SemiprimeLongPowerRouting.certified_leaf_input_le
    (SemiprimeKernelDescent.publicTrace_certified hp hq)
  have hwidth := SemiprimeKernelDescent.sixthWidth_mono hn
  have hl := Nat.clog_mono_right 2 (Nat.add_le_add_right hn 1)
  dsimp only at hb ⊢
  change SemiprimeKernelDescent.leafInput
    (SemiprimeTotientWindow.publicPacket (p*q)).parent.source≤p*q at hn
  change SemiprimeLehmanCoverage.sixthWidth
    (SemiprimeKernelDescent.leafInput (SemiprimeTotientWindow.publicPacket (p*q)).parent.source)≤
      SemiprimeLehmanCoverage.sixthWidth (p*q) at hwidth
  change Nat.clog 2
    (SemiprimeKernelDescent.leafInput (SemiprimeTotientWindow.publicPacket (p*q)).parent.source+1)≤
      Nat.clog 2 (p*q+1) at hl
  omega

/-- Every actually constructed zero-based exponent label lies in its block. -/
theorem countedWalk_label_bound (N start step len : ℕ)
    {record : ℕ×ℕ} (hr : record∈(countedWalk N start step len 0).records) : record.2<len := by
  rw [countedWalk_records] at hr
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hr
  simpa only [Nat.zero_add] using List.mem_range.mp hi

/-- The actual global match retains bounded labels even on nonunit raw
inputs, without assuming that the decoder succeeds. -/
theorem buildRootedSource_collision_bounds {N a inverse B i j : ℕ}
    (hs : (buildRootedSource N a inverse B).ready.collision=some (i,j)) :
    i<2*B ∧ j<2*B := by
  have he := congrArg (fun source : ReadySource N => source.collision)
    (buildRootedSource_ready N a inverse B)
  rw [he] at hs
  change SemiprimeProgressionPrefix.matchSorted
    (SemiprimeProgressionPrefix.sortedRecords
      (countedWalk N 1 a (2*B) 0).records)
    (SemiprimeProgressionPrefix.sortedRecords
      (countedWalk N (countedPower N a (quarterCentre N)).value
        (countedPower N inverse (2*B)).value (2*B) 0).records)=some (i,j) at hs
  obtain ⟨x,hx,y,hy,_,hi,hj⟩ := SemiprimeProgressionPrefix.matchSorted_sound hs
  constructor
  · rw [←hi]
    exact countedWalk_label_bound _ _ _ _ (SemiprimeProgressionPrefix.mem_sortedRecords.mp hx)
  · rw [←hj]
    exact countedWalk_label_bound _ _ _ _ (SemiprimeProgressionPrefix.mem_sortedRecords.mp hy)

/-- The actually used block-label product needs at most 2L+2 bits at the
public sixth-root width, including a collision decoded to no factor. -/
theorem publicWidth_offset_product_bits {N a inverse i j : ℕ} (hN : 0<N)
    (hs : (buildRootedSource N a inverse (SemiprimeLehmanCoverage.sixthWidth N)).ready.collision=
      some (i,j)) :
    Nat.clog 2 ((2*SemiprimeLehmanCoverage.sixthWidth N)*j+1)≤2*Nat.clog 2 (N+1)+2 := by
  obtain ⟨_,hj⟩ := buildRootedSource_collision_bounds hs
  have hB := sixthWidth_le_input hN
  have hjN : j<2*N := by omega
  have hp : (2*SemiprimeLehmanCoverage.sixthWidth N)*j<(2*N)^2 := by
    calc
      _≤(2*N)*j := Nat.mul_le_mul_right j (by omega)
      _<(2*N)*(2*N) := Nat.mul_lt_mul_of_pos_left hjN (by omega)
      _=(2*N)^2 := by rw [pow_two]
  have hbits := below_square_bit_width hp
  have hb := block_exponent_bits (le_refl N)
  omega

/-- The literal discriminant square has at most 2L+1 bits even when an
incorrect collision gives modulus zero and signal N+1. -/
theorem countedDecoder_product_bits {N : ℕ} (hN : 0<N) (m : ℕ) :
    Nat.clog 2 ((countedDecoder N m).signal^2+1)≤2*Nat.clog 2 (N+1)+1 := by
  have hsignal := (countedDecoder_input_bounds hN m).1
  have hn := Nat.le_pow_clog (by decide : 1<(2 : ℕ)) (N+1)
  have hs := Nat.pow_le_pow_left (le_trans hsignal hn) 2
  have he : (2^Nat.clog 2 (N+1))^2=2^(2*Nat.clog 2 (N+1)) := by
    rw [←pow_mul]; congr 1; omega
  rw [he] at hs
  have hp := Nat.one_le_pow (2*Nat.clog 2 (N+1)) 2 (by decide)
  apply Nat.clog_le_of_le_pow
  rw [show 2^(2*Nat.clog 2 (N+1)+1)=2^(2*Nat.clog 2 (N+1))*2 from pow_succ _ _]
  omega

/-- Every optional-decoder root temporary is bounded at the ORIGINAL
leaf input's bit width, rather than its larger discriminant magnitude. -/
theorem countedDecoder_temporary_widths {N : ℕ} (hN : 0<N) (m : ℕ)
    {frame : SqrtFrame} (hf : frame∈(countedDecoder N m).squareRoot.trace) :
    Nat.clog 2 (frame.expanded+1)≤2*Nat.clog 2 (N+1) ∧
      Nat.clog 2 (frame.trial+1)≤2*Nat.clog 2 (N+1)+1 := by
  have hr := countedSqrt_temporary_widths (countedDecoder N m).discriminant hf
  have hb := countedDecoder_root_bits hN m
  omega

end RiemannGaussian.SemiprimeWindowSqrt
