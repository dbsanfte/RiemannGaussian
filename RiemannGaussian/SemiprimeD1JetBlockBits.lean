/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1JetPolynomialBitsBounds

/-! # Actual copied coefficient blocks of the fresh outer nilpotent axis
The extractor scans and copies cached words. Quotient coefficients occur only
in its correctness statement, never as runtime input answers.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace RiemannGaussian.SemiprimeD1JetBlockBits
open scoped BigOperators
open SemiprimeD1JetAxes SemiprimeD1JetBoxIndex SemiprimeD1JetInterpretation
open SemiprimeD1JetAffineCoefficient (JetRun)
open SemiprimeBitArithmetic

/-- Old axes at the child's unchanged current scalar precision. -/
def oldContext (old : Context) (p : ℕ) : Context:=⟨old.axes,p⟩

/-- New actual context, with the freshly adjoined outer axis. -/
def newContext (old : Context) (q p : ℕ) : Context:=⟨q::old.axes,p⟩

/-- Read one actual offset coefficient and physically copy its word. -/
def readCopy (words : List (List Bool)) (i : ℕ) : SemiprimeSourceCompactBits.Report :=
  let source:=SemiprimeD1JetRingBits.read words i
  let out:=SemiprimeSourceCompactBits.copy source.bits
  ⟨out.bits,source.clock+out.clock+3⟩

/-- Actual copied word is exactly the corresponding original cached coefficient. -/
theorem readCopy_bits (words : List (List Bool)) (i : ℕ) :
    (readCopy words i).bits=(words[i]?).getD [] := by
  simp only [readCopy,SemiprimeSourceCompactBits.copy_bits,SemiprimeD1JetRingBits.read_bits]

/-- Extract one fresh-axis block by actual finite reads/copies, with no upstream report discarded.
This internal cached-list primitive leaves the once-only input acquisition to its caller. -/
def extract (old : Context) (j : ℕ) (words : List (List Bool)) : JetRun :=
  let reports:=(List.range old.rank).map (fun i=>readCopy words (j*old.rank+i))
  ⟨reports.map (fun r=>r.bits),(reports.map (fun r=>r.clock)).sum+5*old.rank+5⟩

/-- Standalone block extraction also retains the actual input acquisition report once. -/
def extractRun (old : Context) (j : ℕ) (input : JetRun) : JetRun :=
  let out:=extract old j input.words
  ⟨out.words,input.clock+out.clock+3⟩

/-- Every actual extracted block has exactly the original dense rank. -/
theorem extract_shape (old : Context) (j : ℕ) (words : List (List Bool)) :
    (extract old j words).words.length=old.rank := by simp [extract]

/-- Actual copied coordinates are the literal offset reads of the original vector. -/
theorem extract_word (old : Context) (j i : ℕ) (words : List (List Bool)) (hi : i<old.rank) :
    ((extract old j words).words[i]?).getD []=(words[j*old.rank+i]?).getD [] := by
  simp only [extract,List.getElem?_map,List.getElem?_range hi,Option.map_some,
    Option.getD_some,readCopy_bits]

/-- Actual copied coefficient residues preserve the child's unchanged current precision. -/
theorem extract_coefficient (old : Context) (q p j i : ℕ) (words : List (List Bool)) (hi : i<old.rank) :
    SemiprimeD1JetRingBits.coefficient (oldContext old p) (extract old j words).words i=
      SemiprimeD1JetRingBits.coefficient (newContext old q p) words (j*old.rank+i) := by
  simp only [SemiprimeD1JetRingBits.coefficient,extract_word old j i words hi]
  rfl

/-- Every original block coordinate lies in the actual new dense shape. -/
theorem block_index_lt (old : Context) (q j i : ℕ) (hj : j<q) (hi : i<old.rank) :
    j*old.rank+i<q*old.rank := by nlinarith

/-- Actual fresh/old exponents of a coefficient block. -/
noncomputable def blockExponent (old : Context) (j : ℕ) (e : Fin old.axes.length→₀ℕ) :
    Fin (old.axes.length+1)→₀ℕ :=
  Finsupp.single 0 j+Finsupp.embDomain (SemiprimeD1JetAlgebra.axisShift old.axes.length) e

/-- Native radix routing identifies the actual block offset with fresh exponent j. -/
theorem exponent_block (old : Context) (q j i : ℕ) (hpos : ∀q∈old.axes,0<q) (hi : i<old.rank) :
    exponent (q::old.axes) (j*old.rank+i)=blockExponent old j (exponent old.axes i) := by
  have hn : 0<old.rank:=List.prod_pos hpos
  have hdiv : (j*old.rank+i)/old.rank=j := by
    rw [Nat.mul_comm j old.rank,Nat.mul_add_div hn,Nat.div_eq_of_lt hi,Nat.add_zero]
  have hmod : (j*old.rank+i)%old.rank=i := by
    rw [Nat.mul_comm j old.rank,Nat.mul_add_mod,Nat.mod_eq_of_lt hi]
  ext k
  refine Fin.cases ?_ (fun v=>?_) k
  · have hz : (Finsupp.embDomain (SemiprimeD1JetAlgebra.axisShift old.axes.length)
        (exponent old.axes i)) 0=0 := by
      apply Finsupp.embDomain_of_notMem_range
      rintro ⟨v,hv⟩
      exact Fin.succ_ne_zero v hv
    change (j*old.rank+i)/old.axes.prod=(Finsupp.single (0:Fin (old.axes.length+1)) j) 0+
      (Finsupp.embDomain (SemiprimeD1JetAlgebra.axisShift old.axes.length) (exponent old.axes i)) 0
    simpa only [Finsupp.single_eq_same,hz,Nat.add_zero,Context.rank] using hdiv
  · change digitFn old.axes ((j*old.rank+i)%old.axes.prod) v=
      (Finsupp.single (0:Fin (old.axes.length+1)) j) v.succ+
      (Finsupp.embDomain (SemiprimeD1JetAlgebra.axisShift old.axes.length) (exponent old.axes i))
        ((SemiprimeD1JetAlgebra.axisShift old.axes.length) v)
    have hmod' : (j*old.rank+i)%old.axes.prod=i := by simpa only [Context.rank] using hmod
    rw [hmod',Finsupp.embDomain_apply_self]
    simp only [Finsupp.single_apply,Ne.symm (Fin.succ_ne_zero v),ite_false,Nat.zero_add,exponent_apply]

/-- Actual copied words preserve the original physical word width. -/
theorem extract_bounded (old : Context) (j p : ℕ) (words : List (List Bool))
    (hw : ∀w∈words,w.length ≤ p) :
    ∀w∈(extract old j words).words,w.length ≤ p := by
  intro w h
  rcases List.mem_map.mp h with ⟨r,hr,rfl⟩
  rcases List.mem_map.mp hr with ⟨i,_,rfl⟩
  simp only [readCopy,SemiprimeSourceCompactBits.copy_bits]
  exact SemiprimeD1JetRingBounds.read_length words (j*old.rank+i) p hw

/-- Extracted vectors have derived old-axis shape and unchanged current precision width. -/
theorem extract_good (old : Context) (j p : ℕ) (words : List (List Bool))
    (hw : ∀w∈words,w.length ≤ p) :
    SemiprimeD1JetAffineCoefficientBounds.Good (oldContext old p) (extract old j words).words :=
  ⟨extract_shape old j words,extract_bounded old j p words hw⟩

/-- Cached original canonical words remain canonical after a read, including default zero. -/
theorem read_compact (words : List (List Bool)) (i : ℕ)
    (hw : ∀w∈words,SemiprimeSourceCompactBits.Compact w) :
    SemiprimeSourceCompactBits.Compact (SemiprimeD1JetRingBits.read words i).bits := by
  induction words generalizing i with
  | nil => trivial
  | cons w words ih =>
    cases i with
    | zero => exact hw w List.mem_cons_self
    | succ i => exact ih i (fun v hv=>hw v (List.mem_cons_of_mem w hv))

/-- Physical extraction preserves canonical acquired child words, with no new normalization oracle. -/
theorem extract_compact (old : Context) (j : ℕ) (words : List (List Bool))
    (hw : ∀w∈words,SemiprimeSourceCompactBits.Compact w) :
    ∀w∈(extract old j words).words,SemiprimeSourceCompactBits.Compact w := by
  intro w h
  rcases List.mem_map.mp h with ⟨r,hr,rfl⟩
  rcases List.mem_map.mp hr with ⟨i,_,rfl⟩
  simp only [readCopy,SemiprimeSourceCompactBits.copy_bits]
  exact read_compact words (j*old.rank+i) hw

/-- One actual read/copy pays the source scan and every copied physical bit. -/
theorem readCopy_clock (words : List (List Bool)) (i p : ℕ)
    (hw : ∀w∈words,w.length ≤ p) :
    (readCopy words i).clock ≤ 3*words.length+3*p+5 := by
  have hr:=SemiprimeD1JetRingBits.read_clock words i
  have hh:=SemiprimeD1JetRingBounds.read_length words i p hw
  have hc:=SemiprimeSourceCompactBits.copy_clock (SemiprimeD1JetRingBits.read words i).bits
  change (SemiprimeD1JetRingBits.read words i).clock+
    (SemiprimeSourceCompactBits.copy (SemiprimeD1JetRingBits.read words i).bits).clock+3 ≤ _
  omega

/-- The complete actual copied block has original-cache polynomial scan/bit work. -/
theorem extract_clock (old : Context) (j p : ℕ) (words : List (List Bool))
    (hw : ∀w∈words,w.length ≤ p) :
    (extract old j words).clock ≤ old.rank*(3*words.length+3*p+5)+5*old.rank+5 := by
  have h:=SemiprimeD1JetRingBounds.sum_clocks_le
    ((List.range old.rank).map (fun i=>readCopy words (j*old.rank+i))) (3*words.length+3*p+5) (by
      intro r hr
      rcases List.mem_map.mp hr with ⟨i,_,rfl⟩
      exact readCopy_clock words (j*old.rank+i) p hw)
  simp only [List.length_map,List.length_range] at h
  exact Nat.add_le_add_right h (5*old.rank+5)

/-- Standalone extraction retains the actual upstream report as well as all block work. -/
theorem extractRun_clock (old : Context) (j p : ℕ) (input : JetRun)
    (hw : ∀w∈input.words,w.length ≤ p) :
    (extractRun old j input).clock ≤ input.clock+
      old.rank*(3*input.words.length+3*p+5)+5*old.rank+8 := by
  have h:=extract_clock old j p input.words hw
  change input.clock+(extract old j input.words).clock+3 ≤ _
  omega

noncomputable section
/-- Canonical fresh-axis coefficient block of the concrete quotient. This finite
mathematical readout is not called by the runtime extractor. -/
def blockValue (old : Context) (q p j : ℕ) (hpos : ∀q∈old.axes,0<q) (hj : j<q)
    (f : Carrier (newContext old q p)) : Carrier (oldContext old p) :=
  ∑i : Fin old.rank,basis (oldContext old p) i.val
    (SemiprimeD1JetAlgebra.coefficient (dims (q::old.axes))
      (exponent (q::old.axes) (j*old.rank+i.val))
      (exponent_inBox (q::old.axes) (j*old.rank+i.val)
        (by intro x hx;rcases List.mem_cons.mp hx with rfl|hx
            ;exact Nat.zero_lt_of_lt hj
            ;exact hpos x hx)
        (block_index_lt old q j i.val hj i.isLt)) f)

/-- A dense block coordinate has the exact explicit fresh/old exponent in the actual box. -/
theorem block_inBox (old : Context) (q j i : ℕ) (hpos : ∀q∈old.axes,0<q) (hj : j<q) (hi : i<old.rank) :
    SemiprimeD1JetAlgebra.InBox (dims (q::old.axes)) (blockExponent old j (exponent old.axes i)) := by
  have h:=exponent_inBox (q::old.axes) (j*old.rank+i)
    (by intro x hx;rcases List.mem_cons.mp hx with rfl|hx
        ;exact Nat.zero_lt_of_lt hj
        ;exact hpos x hx) (block_index_lt old q j i hj hi)
  simpa only [exponent_block old q j i hpos hi] using h

/-- Every old coordinate of the canonical readout is exactly the child's fresh-j coefficient. -/
theorem blockValue_coefficient (old : Context) (q p j i : ℕ) (hpos : ∀q∈old.axes,0<q)
    (hj : j<q) (hi : i<old.rank) (f : Carrier (newContext old q p)) :
    SemiprimeD1JetAlgebra.coefficient (dims old.axes) (exponent old.axes i)
      (exponent_inBox old.axes i hpos hi) (blockValue old q p j hpos hj f)=
      SemiprimeD1JetAlgebra.coefficient (dims (q::old.axes))
        (blockExponent old j (exponent old.axes i)) (block_inBox old q j i hpos hj hi) f := by
  classical
  have hip : i<old.axes.prod := hi
  let a : Fin old.axes.prod→ZMod (2^p) := fun k=>
    SemiprimeD1JetAlgebra.coefficient (dims (q::old.axes))
      (exponent (q::old.axes) (j*old.rank+k.val))
      (exponent_inBox (q::old.axes) (j*old.rank+k.val)
        (by intro x hx;rcases List.mem_cons.mp hx with rfl|hx
            ;exact Nat.zero_lt_of_lt hj
            ;exact hpos x hx)
        (block_index_lt old q j k.val hj k.isLt)) f
  have hlinear:=quotient_coefficient_sum (R:=ZMod (2^p)) (dims old.axes)
    (exponent old.axes i) (exponent_inBox old.axes i hpos hip) Finset.univ
    (fun k : Fin old.axes.prod=>basis ⟨old.axes,p⟩ k.val (a k))
  apply hlinear.trans
  let index : Fin old.axes.prod:=⟨i,hip⟩
  rw [Finset.sum_eq_single index]
  · simp only [basis,SemiprimeD1JetAlgebra.coefficient_project,MvPowerSeries.coeff_monomial,
      index,ite_true]
    change SemiprimeD1JetAlgebra.coefficient (dims (q::old.axes))
      (exponent (q::old.axes) (j*old.rank+i)) _ f=_
    have hx:=exponent_block old q j i hpos hi
    have hdense:=exponent_inBox (q::old.axes) (j*old.rank+i)
      (by intro x hx;rcases List.mem_cons.mp hx with rfl|hx
          ;exact Nat.zero_lt_of_lt hj
          ;exact hpos x hx) (block_index_lt old q j i hj hi)
    have hxy : (⟨exponent (q::old.axes) (j*old.rank+i),hdense⟩ :
        {e // SemiprimeD1JetAlgebra.InBox (dims (q::old.axes)) e})=
        ⟨blockExponent old j (exponent old.axes i),block_inBox old q j i hpos hj hi⟩ := Subtype.ext hx
    exact congrArg (fun e : {e // SemiprimeD1JetAlgebra.InBox (dims (q::old.axes)) e}=>
      SemiprimeD1JetAlgebra.coefficient (dims (q::old.axes)) e.val e.property f) hxy
  · intro k _ hk
    have hn : exponent old.axes i≠exponent old.axes k.val := by
      intro he
      exact hk (Fin.ext (exponent_injective old.axes hpos i k.val hip k.isLt he).symm)
    simp only [basis,SemiprimeD1JetAlgebra.coefficient_project,MvPowerSeries.coeff_monomial,hn,ite_false]
  · intro hn
    exact False.elim (hn (Finset.mem_univ index))

/-- The executed copied block is exactly the quotient's canonical fresh-axis coefficient block. -/
theorem extract_value (old : Context) (q p j : ℕ) (words : List (List Bool))
    (hpos : ∀q∈old.axes,0<q) (hj : j<q) :
    interpret (oldContext old p) (extract old j words).words=
      blockValue old q p j hpos hj (interpret (newContext old q p) words) := by
  classical
  unfold interpret blockValue
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  rw [extract_coefficient old q p j i.val words i.isLt]
  symm
  exact coefficient_interpret (newContext old q p) words
    (by intro x hx;rcases List.mem_cons.mp hx with rfl|hx
        ;exact Nat.zero_lt_of_lt hj
        ;exact hpos x hx)
    (j*old.rank+i.val) (block_index_lt old q j i.val hj i.isLt)

/-- Standalone report-retaining extraction has the identical canonical coefficient-block value. -/
theorem extractRun_value (old : Context) (q p j : ℕ) (input : JetRun)
    (hpos : ∀q∈old.axes,0<q) (hj : j<q) :
    interpret (oldContext old p) (extractRun old j input).words=
      blockValue old q p j hpos hj (interpret (newContext old q p) input.words) :=
  extract_value old q p j input.words hpos hj

/-- Standalone extraction derives output shape/width from the actual acquired child words. -/
theorem extractRun_good (old : Context) (j p : ℕ) (input : JetRun)
    (hw : ∀w∈input.words,w.length ≤ p) :
    SemiprimeD1JetAffineCoefficientBounds.Good (oldContext old p) (extractRun old j input).words :=
  extract_good old j p input.words hw

end
end RiemannGaussian.SemiprimeD1JetBlockBits
