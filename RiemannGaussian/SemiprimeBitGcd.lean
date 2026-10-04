/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeMergedIndexAcquisition
import RiemannGaussian.SemiprimeBitDivision

/-!
# Boolean Euclidean GCD and checked divisor extraction

The data path uses Boolean words, the frozen restoring division circuit,
and a physically constructed list of fuel cells. Natural GCD, modulo and
word evaluation occur only in specifications and proofs. Two successive
remainders halve the positive divisor, so the public fuel always suffices.
The clocks charge the existing Boolean/cell/test primitives, including
fuel construction, padded words and zero inputs. This scalar backend does
not pay the full collision acquisition or the whole factorizer's bit cost.
-/

namespace RiemannGaussian.SemiprimeBitGcd

open SemiprimeBitArithmetic SemiprimeBitDivision SemiprimeGroupSelection

/-- Literal loop-budget cells and the work to construct them. -/
structure GcdFuel where
  /-- The recursive algorithm consumes these cells rather than a native counter. -/
  cells : List Unit
  /-- Input reads, list tests and newly written fuel cells. -/
  clock : ℕ

/-- Construct two fuel cells for every physical input bit and one terminal
cell. A paired frame pays two reads, two tests and four writes. -/
def buildGcdFuel : List Bool → List Bool → GcdFuel
  | [],[] => ⟨[()],3⟩
  | _::xs,[] =>
    let child := buildGcdFuel xs []
    ⟨()::()::child.cells,child.clock+5⟩
  | [],_::ys =>
    let child := buildGcdFuel [] ys
    ⟨()::()::child.cells,child.clock+5⟩
  | _::xs,_::ys =>
    let child := buildGcdFuel xs ys
    ⟨()::()::()::()::child.cells,child.clock+8⟩
termination_by xs ys => xs.length+ys.length
decreasing_by all_goals simp_wf <;> omega

/-- Exact fuel size and its charged linear construction cost. -/
theorem buildGcdFuel_counts (xs ys : List Bool) :
    (buildGcdFuel xs ys).cells.length=2*(xs.length+ys.length)+1 ∧
      (buildGcdFuel xs ys).clock≤5*(xs.length+ys.length)+3 := by
  induction xs generalizing ys with
  | nil =>
    induction ys with
    | nil => simp [buildGcdFuel]
    | cons bit ys ih =>
      simp only [buildGcdFuel,List.length_cons,List.length_nil] at *
      omega
  | cons bit xs ih =>
    cases ys with
    | nil =>
      have hc := ih []
      simp only [buildGcdFuel,List.length_cons,List.length_nil] at *
      omega
    | cons other ys =>
      have hc := ih ys
      simp only [buildGcdFuel,List.length_cons] at *
      omega

/-- Actual output word, total primitive clock and the actual division count. -/
structure GcdReport where
  /-- The last positive divisor, or the first input when the second is zero. -/
  bits : List Bool
  /-- Every performed circuit, scan and fuel-frame primitive. -/
  clock : ℕ
  /-- Calls of the restoring quotient/remainder backend. -/
  divisions : ℕ
  /-- An explicit failure flag for arbitrary insufficient supplied fuel. -/
  exhausted : Bool

/-- Fuelled Euclid on actual bit words. Each visited frame pays the fuel
test/read and the Boolean branch; the divisor scan and division are charged
separately, even though division scans the divisor again. -/
def gcdLoop (xs ys : List Bool) : List Unit → GcdReport
  | [] => ⟨xs,1,0,true⟩
  | _::fuel =>
    let check := nonzeroBits ys
    if check.nonzero=true then
      let division := divideBits xs ys
      let child := gcdLoop ys division.remainder fuel
      ⟨child.bits,check.clock+division.clock+child.clock+3,
        child.divisions+1,child.exhausted⟩
    else
      ⟨xs,check.clock+3,0,false⟩

/-- A stopped loop computes GCD; the exhaustion flag cannot be ignored. -/
theorem gcdLoop_correct_of_stopped (xs ys : List Bool) (fuel : List Unit)
    (hstop : (gcdLoop xs ys fuel).exhausted=false) :
    bitValue (gcdLoop xs ys fuel).bits=(bitValue xs).gcd (bitValue ys) := by
  induction fuel generalizing xs ys with
  | nil => simp [gcdLoop] at hstop
  | cons cell fuel ih =>
    by_cases hb : (nonzeroBits ys).nonzero=true
    · have hc : (gcdLoop ys (divideBits xs ys).remainder fuel).exhausted=false := by
        simpa only [gcdLoop,if_pos hb] using hstop
      have he := ih ys (divideBits xs ys).remainder hc
      simp only [gcdLoop,if_pos hb]
      rw [he,(divideBits_correct xs ys).2]
      calc
        (bitValue ys).gcd (bitValue xs%bitValue ys)=
            (bitValue xs%bitValue ys).gcd (bitValue ys) := Nat.gcd_comm _ _
        _=(bitValue ys).gcd (bitValue xs) := (Nat.gcd_rec _ _).symm
        _=(bitValue xs).gcd (bitValue ys) := Nat.gcd_comm _ _
    · have hz : bitValue ys=0 := by
        have hn : ¬0<bitValue ys := by
          intro hp
          exact hb ((nonzeroBits_correct ys).mpr hp)
        omega
      simp only [gcdLoop,if_neg hb,hz,Nat.gcd_zero_right]

/-- Every two positive Euclidean steps halve the divisor. The theorem
bounds the actual division calls and proves that literal fuel suffices. -/
theorem gcdLoop_stops_pow (k : ℕ) (xs ys : List Bool) (fuel : List Unit)
    (hy : bitValue ys<2^k) (hf : 2*k+1≤fuel.length) :
    (gcdLoop xs ys fuel).exhausted=false ∧
      (gcdLoop xs ys fuel).divisions≤2*k := by
  induction k generalizing xs ys fuel with
  | zero =>
    have hz : bitValue ys=0 := by simpa using hy
    have hb : ¬(nonzeroBits ys).nonzero=true := by
      intro hp
      have hpos := (nonzeroBits_correct ys).mp hp
      omega
    cases fuel with
    | nil => simp only [List.length_nil] at hf; omega
    | cons cell fuel => simp [gcdLoop,hb]
  | succ k ih =>
    cases fuel with
    | nil => simp only [List.length_nil] at hf; omega
    | cons cell fuel =>
      by_cases hb : (nonzeroBits ys).nonzero=true
      · have hpos := (nonzeroBits_correct ys).mp hb
        cases fuel with
        | nil => simp only [List.length_cons,List.length_nil] at hf; omega
        | cons other fuel =>
          let remainder := (divideBits xs ys).remainder
          by_cases hr : (nonzeroBits remainder).nonzero=true
          · have hrpos := (nonzeroBits_correct remainder).mp hr
            have he : bitValue remainder=bitValue xs%bitValue ys :=
              (divideBits_correct xs ys).2
            have hs := SemiprimeQuotientRows.two_remainders_half
              (a:=bitValue xs) (b:=bitValue ys) hpos (by
              simpa only [←he] using hrpos)
            have hn : bitValue (divideBits ys remainder).remainder<2^k := by
              rw [(divideBits_correct ys remainder).2]
              rw [←he] at hs
              rw [pow_succ] at hy
              omega
            have hremaining : 2*k+1≤fuel.length := by
              simp only [List.length_cons] at hf
              omega
            have hc := ih remainder (divideBits ys remainder).remainder fuel hn hremaining
            simp only [gcdLoop,if_pos hb]
            change (gcdLoop ys remainder (other::fuel)).exhausted=false ∧
              (gcdLoop ys remainder (other::fuel)).divisions+1≤2*(k+1)
            simp only [gcdLoop,if_pos hr]
            constructor
            · exact hc.1
            · omega
          · simp only [gcdLoop,if_pos hb]
            change (gcdLoop ys remainder (other::fuel)).exhausted=false ∧
              (gcdLoop ys remainder (other::fuel)).divisions+1≤2*(k+1)
            simp only [gcdLoop,if_neg hr]
            constructor
            · trivial
            · omega
      · simp [gcdLoop,hb]

/-- Neither Euclid nor an exhausted supplied loop grows a physical input
word. Fixed-width division retains padding, which is charged later. -/
theorem gcdLoop_width {L : ℕ} {xs ys : List Bool} (fuel : List Unit)
    (hx : xs.length≤L) (hy : ys.length≤L) :
    (gcdLoop xs ys fuel).bits.length≤L := by
  induction fuel generalizing xs ys with
  | nil => simpa only [gcdLoop] using hx
  | cons cell fuel ih =>
    by_cases hb : (nonzeroBits ys).nonzero=true
    · have hpos := (nonzeroBits_correct ys).mp hb
      have hw := (divideBits_widths (xs:=xs) hpos).1
      have hc := ih hy (by omega : (divideBits xs ys).remainder.length≤L)
      simpa only [gcdLoop,if_pos hb] using hc
    · simpa only [gcdLoop,if_neg hb] using hx

/-- Complete loop clock, including repeated divisor scans and every
physical frame. This bound also applies to insufficient supplied fuel. -/
theorem gcdLoop_cost {L : ℕ} {xs ys : List Bool} (fuel : List Unit)
    (hx : xs.length≤L) (hy : ys.length≤L) :
    (gcdLoop xs ys fuel).clock≤
      fuel.length*(72*(L+1)^2+3*L+4)+1 := by
  induction fuel generalizing xs ys with
  | nil => simp [gcdLoop]
  | cons cell fuel ih =>
    have hz := nonzeroBits_cost ys
    by_cases hb : (nonzeroBits ys).nonzero=true
    · have hpos := (nonzeroBits_correct ys).mp hb
      have hw := (divideBits_widths (xs:=xs) hpos).1
      have hc := ih hy (by omega : (divideBits xs ys).remainder.length≤L)
      have hd := bounded_divideBits (by omega : xs.length≤3*L) hy
      simp only [gcdLoop,if_pos hb,List.length_cons]
      nlinarith
    · simp only [gcdLoop,if_neg hb,List.length_cons]
      nlinarith

/-- Public GCD constructs its own sufficient physical fuel. -/
def gcdBits (xs ys : List Bool) : GcdReport :=
  let fuel := buildGcdFuel xs ys
  let child := gcdLoop xs ys fuel.cells
  {child with clock := child.clock+fuel.clock+1}

/-- GCD is correct and never exhausts its self-constructed fuel, for all
words, including both zero values and arbitrarily high zero padding. -/
theorem gcdBits_correct (xs ys : List Bool) :
    bitValue (gcdBits xs ys).bits=(bitValue xs).gcd (bitValue ys) ∧
      (gcdBits xs ys).exhausted=false := by
  have hf := (buildGcdFuel_counts xs ys).1
  have hs := (gcdLoop_stops_pow ys.length xs ys (buildGcdFuel xs ys).cells
    (bitValue_lt_width ys) (by omega)).1
  exact ⟨gcdLoop_correct_of_stopped xs ys _ hs,hs⟩

/-- The actual number of division calls is at most twice the second
word's physical bit length, rather than a unit-cost native GCD call. -/
theorem gcdBits_divisions (xs ys : List Bool) :
    (gcdBits xs ys).divisions≤2*ys.length := by
  have hf := (buildGcdFuel_counts xs ys).1
  exact (gcdLoop_stops_pow ys.length xs ys (buildGcdFuel xs ys).cells
    (bitValue_lt_width ys) (by omega)).2

/-- A bounded physical input width is preserved by the GCD output. -/
theorem gcdBits_width {L : ℕ} {xs ys : List Bool}
    (hx : xs.length≤L) (hy : ys.length≤L) :
    (gcdBits xs ys).bits.length≤L :=
  gcdLoop_width _ hx hy

/-- Uniform cubic bit-primitive bound pays fuel allocation and every
restoring division. Natural clock arithmetic is proof instrumentation. -/
theorem gcdBits_cost {L : ℕ} {xs ys : List Bool}
    (hx : xs.length≤L) (hy : ys.length≤L) :
    (gcdBits xs ys).clock≤400*(L+1)^3 := by
  obtain ⟨hf,hbuild⟩ := buildGcdFuel_counts xs ys
  have hloop := gcdLoop_cost (buildGcdFuel xs ys).cells hx hy
  have hframe : 72*(L+1)^2+3*L+4≤79*(L+1)^2 := by nlinarith
  have hsize : (buildGcdFuel xs ys).cells.length≤4*L+1 := by omega
  have hm := Nat.mul_le_mul hsize hframe
  have hclock : (gcdBits xs ys).clock≤(4*L+1)*(79*(L+1)^2)+10*L+5 := by
    dsimp only [gcdBits]
    omega
  have hcube : (4*L+1)*(79*(L+1)^2)+10*L+5≤400*(L+1)^3 := by
    nlinarith [sq_nonneg (L:ℤ)]
  exact le_trans hclock hcube

/-- Retained GCD, optional checked factor word and their composed clock. -/
structure CheckedBitsReport where
  /-- The complete Boolean GCD report used by this actual check. -/
  gcd : GcdReport
  /-- A word is returned only after two Boolean borrow comparisons. -/
  factor : Option (List Bool)
  /-- GCD, both comparisons, the literal one cell, gate and output tests. -/
  clock : ℕ

/-- Implement the existing checked-signal interface with Boolean circuits.
The lower comparison is one minus the GCD; the upper comparison is the GCD
minus the modulus. Their final borrows recognize exactly a proper factor. -/
def checkedSignalBits (modulus signal : List Bool) : CheckedBitsReport :=
  let divisor := gcdBits modulus signal
  let lower := subBits [true] divisor.bits false
  let upper := subBits divisor.bits modulus false
  let proper := Bool.and lower.borrow upper.borrow
  let factor := if proper=true then some divisor.bits else none
  ⟨divisor,factor,divisor.clock+bitCost lower.result+bitCost upper.result+5⟩

/-- Both actual borrow bits together are exactly the proper-GCD condition,
including zero moduli, saturated signals, prime powers and padded inputs. -/
theorem checkedSignalBits_condition (modulus signal : List Bool) :
    Bool.and (subBits [true] (gcdBits modulus signal).bits false).borrow
        (subBits (gcdBits modulus signal).bits modulus false).borrow=true ↔
      1<(bitValue modulus).gcd (bitValue signal) ∧
        (bitValue modulus).gcd (bitValue signal)<bitValue modulus := by
  have hlo := subBits_borrow_iff [true] (gcdBits modulus signal).bits false
  have hhi := subBits_borrow_iff (gcdBits modulus signal).bits modulus false
  simp only [bitValue,bitNat,if_true,Nat.mul_zero,Nat.add_zero,
    Bool.false_eq_true,if_false] at hlo
  simp only [bitNat,Bool.false_eq_true,if_false,Nat.add_zero] at hhi
  rw [Bool.and_eq_true,hlo,hhi,(gcdBits_correct modulus signal).1]

/-- The executable word routine returns exactly the established checked
signal value. No natural GCD or ordering oracle computes its output. -/
theorem checkedSignalBits_exact (modulus signal : List Bool) :
    (checkedSignalBits modulus signal).factor.map bitValue=
      checkedSignal (bitValue modulus) (bitValue signal) := by
  have hc := checkedSignalBits_condition modulus signal
  have hg := (gcdBits_correct modulus signal).1
  by_cases hb : Bool.and (subBits [true] (gcdBits modulus signal).bits false).borrow
      (subBits (gcdBits modulus signal).bits modulus false).borrow=true
  · have hd := hc.mp hb
    simp only [checkedSignalBits,if_pos hb,Option.map_some,hg,checkedSignal,if_pos hd]
  · have hd : ¬(1<(bitValue modulus).gcd (bitValue signal) ∧
        (bitValue modulus).gcd (bitValue signal)<bitValue modulus) := by
      intro hp
      exact hb (hc.mpr hp)
    simp only [checkedSignalBits,if_neg hb,Option.map_none,checkedSignal,if_neg hd]

/-- Every returned Boolean word evaluates to a checked proper divisor. -/
theorem checkedSignalBits_sound {modulus signal divisor : List Bool}
    (h : (checkedSignalBits modulus signal).factor=some divisor) :
    ProperDivisor (bitValue modulus) (bitValue divisor) := by
  apply checkedSignal_sound
  rw [←checkedSignalBits_exact modulus signal,h,Option.map_some]

/-- A returned factor retains the bounded physical GCD width. -/
theorem checkedSignalBits_width {L : ℕ} {modulus signal divisor : List Bool}
    (hm : modulus.length≤L) (hs : signal.length≤L)
    (h : (checkedSignalBits modulus signal).factor=some divisor) :
    divisor.length≤L := by
  unfold checkedSignalBits at h
  dsimp only at h
  split_ifs at h
  cases h
  exact gcdBits_width hm hs

/-- One checked divisor extraction has a fully composed cubic scalar
bit-primitive bound, paying fuel construction and both borrow comparisons. -/
theorem checkedSignalBits_cost {L : ℕ} {modulus signal : List Bool}
    (hm : modulus.length≤L) (hs : signal.length≤L) :
    (checkedSignalBits modulus signal).clock≤500*(L+1)^3 := by
  have hg := gcdBits_cost hm hs
  have hw := gcdBits_width hm hs
  have hlo := subBits_cost [true] (gcdBits modulus signal).bits false
  have hhi := subBits_cost (gcdBits modulus signal).bits modulus false
  have hlowidth : max ([true]:List Bool).length (gcdBits modulus signal).bits.length≤L+1 :=
    max_le (by simp) (by omega)
  have hhiwidth : max (gcdBits modulus signal).bits.length modulus.length≤L :=
    max_le hw hm
  have hbound : (checkedSignalBits modulus signal).clock≤
      400*(L+1)^3+24*L+21 := by
    dsimp only [checkedSignalBits]
    omega
  have hpower : L+1≤(L+1)^3 := Nat.le_self_pow (by decide : 3≠0) (L+1)
  have hlast : 400*(L+1)^3+24*L+21≤500*(L+1)^3 := by omega
  exact le_trans hbound hlast

end RiemannGaussian.SemiprimeBitGcd
