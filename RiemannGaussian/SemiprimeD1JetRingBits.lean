/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1JetRouting

/-! # Executed dense truncated multijet coordinate arithmetic
All scalar arithmetic uses physical Boolean operations. Native coordinate
routing/list-control costs remain distinguished from a full address-bit clock.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1JetRingBits
open SemiprimeBitArithmetic SemiprimeD1JetAxes
/-- Scalar physical coordinate word and retained report. -/
abbrev Scalar := SemiprimeSourceCompactBits.Report

/-- Actual coefficient list and complete retained scalar/control report. -/
structure Run where
  /-- Dense coefficients, new axes outermost. -/
  words : List (List Bool)
  /-- Physical coordinate arithmetic, list reads and finite route/control reports. -/
  clock : ℕ

/-- Finite cached-list read; the selected word is borrowed, not reencoded. -/
def read : List (List Bool)→ℕ→Scalar
  | [],_ => ⟨[],1⟩
  | w::_,0 => ⟨w,3⟩
  | _::ws,i+1 => let tail:=read ws i;⟨tail.bits,tail.clock+3⟩

/-- Literal cached read with the zero coefficient default. -/
theorem read_bits (ws : List (List Bool)) (i : ℕ) : (read ws i).bits=(ws[i]?).getD [] := by
  induction ws generalizing i with
  | nil => simp [read]
  | cons w ws ih => cases i <;> simp [read,ih]

/-- Every actual cached-list traversal is charged. -/
theorem read_clock (ws : List (List Bool)) (i : ℕ) : (read ws i).clock≤3*ws.length+1 := by
  induction ws generalizing i with
  | nil => simp [read]
  | cons w ws ih =>
    cases i with
    | zero => simp only [read,List.length_cons];omega
    | succ i =>
      have h:=ih i
      simp only [read,List.length_cons]
      omega

/-- Coefficient interpretation in the actual modular scalar ring. -/
def coefficient (ctx : Context) (ws : List (List Bool)) (i : ℕ) : ZMod (2^ctx.precision) :=
  bitValue ((ws[i]?).getD [])

/-- Actual modular sum of cached reports, retaining EVERY earlier report. -/
def sumReports (p : ℕ) : List Scalar→Scalar
  | [] => ⟨[],1⟩
  | r::rs =>
    let tail:=sumReports p rs
    let out:=SemiprimeD1JetScalarBits.add p r.bits tail.bits
    ⟨out.bits,r.clock+tail.clock+out.clock+3⟩

/-- Every modular sum prefix has target width independently of its values. -/
theorem sumReports_length (p : ℕ) (rs : List Scalar) : (sumReports p rs).bits.length≤p := by
  cases rs with
  | nil => exact Nat.zero_le _
  | cons r rs => exact SemiprimeD1JetScalarBits.add_length _ _ _

/-- The actual modular accumulator equals the sum of ALL cached input coefficients. -/
theorem sumReports_value (p : ℕ) (rs : List Scalar) :
    (bitValue (sumReports p rs).bits:ZMod (2^p))=
      (rs.map (fun r => (bitValue r.bits:ZMod (2^p)))).sum := by
  induction rs with
  | nil => simp [sumReports,bitValue]
  | cons r rs ih =>
    change (bitValue (SemiprimeD1JetScalarBits.add p r.bits (sumReports p rs).bits).bits:ZMod (2^p))=_
    rw [SemiprimeD1JetScalarBits.add_zmod,ih]
    rfl

/-- Sum cost retains all callback reports plus actual bounded modular additions. -/
theorem sumReports_clock (p : ℕ) (rs : List Scalar)
    (hw : ∀r∈rs,r.bits.length≤p) :
    (sumReports p rs).clock≤(rs.map (fun r : Scalar => r.clock)).sum+rs.length*(20*p+15)+1 := by
  induction rs with
  | nil => simp [sumReports]
  | cons r rs ih =>
    have hh:=hw r List.mem_cons_self
    have ht:=ih (fun s hs => hw s (List.mem_cons_of_mem r hs))
    have ha:=SemiprimeD1JetScalarBits.add_clock p r.bits (sumReports p rs).bits
    have hl:=sumReports_length p rs
    have hm : max r.bits.length (sumReports p rs).bits.length≤p := max_le hh hl
    simp only [sumReports,List.map_cons,List.sum_cons,List.length_cons]
    nlinarith

/-- Actual single coordinate sum from two cached coefficient arrays. -/
def addAt (ctx : Context) (a b : List (List Bool)) (i : ℕ) : Scalar :=
  let left:=read a i
  let right:=read b i
  let out:=SemiprimeD1JetScalarBits.add ctx.precision left.bits right.bits
  ⟨out.bits,left.clock+right.clock+out.clock+3⟩

/-- Dense coordinate sum materializes each output report once. -/
def add (ctx : Context) (a b : List (List Bool)) : Run :=
  let reports:=(List.range ctx.rank).map (addAt ctx a b)
  ⟨reports.map (fun r : Scalar => r.bits),(reports.map (fun r : Scalar => r.clock)).sum+10*ctx.rank+5⟩

/-- One acquired monomial product, with context-derived nilpotent truncation. -/
def term (ctx : Context) (a b : List (List Bool)) (k : ℕ) (ij : ℕ×ℕ) : Scalar :=
  let route:=SemiprimeD1JetRouting.route ctx.axes ij.1 ij.2
  if route.value=some k then
    let left:=read a ij.1
    let right:=read b ij.2
    let out:=SemiprimeD1JetScalarBits.mul ctx.precision left.bits right.bits
    ⟨out.bits,route.clock+left.clock+right.clock+out.clock+5⟩
  else ⟨[],route.clock+3⟩

/-- Explicit native schoolbook pair plan, not an advised coefficient/route table. -/
def plan (N : ℕ) : List (ℕ×ℕ) :=
  (List.range N).flatMap (fun i => (List.range N).map (fun j => (i,j)))

/-- One output coordinate acquires every native-routed scalar report once. -/
def mulAt (ctx : Context) (a b : List (List Bool)) (k : ℕ) : Scalar :=
  let pairs:=plan ctx.rank
  let terms:=pairs.map (term ctx a b k)
  let out:=sumReports ctx.precision terms
  ⟨out.bits,out.clock+20*pairs.length+ctx.rank+10⟩

/-- Actual dense truncated schoolbook convolution with paid cached-list reads. -/
def mul (ctx : Context) (a b : List (List Bool)) : Run :=
  let reports:=(List.range ctx.rank).map (mulAt ctx a b)
  ⟨reports.map (fun r : Scalar => r.bits),(reports.map (fun r : Scalar => r.clock)).sum+10*ctx.rank+5⟩

/-- Native routing defines the finite bounded-exponent convolution, independently
of all coefficient word values and physical arithmetic. -/
def convolution (ctx : Context) (a b : List (List Bool)) (k : ℕ) : ZMod (2^ctx.precision) :=
  ((plan ctx.rank).map (fun ij =>
    if SemiprimeD1JetRouting.admissible ctx.axes ij.1 ij.2 ∧
      SemiprimeD1JetRouting.sumIndex ctx.axes ij.1 ij.2=k then
      coefficient ctx a ij.1*coefficient ctx b ij.2 else 0)).sum

/-- Every individual acquired term has the independent bounded-monomial meaning. -/
theorem term_value (ctx : Context) (a b : List (List Bool)) (k : ℕ) (ij : ℕ×ℕ) :
    (bitValue (term ctx a b k ij).bits:ZMod (2^ctx.precision))=
      if SemiprimeD1JetRouting.admissible ctx.axes ij.1 ij.2 ∧
        SemiprimeD1JetRouting.sumIndex ctx.axes ij.1 ij.2=k then
        coefficient ctx a ij.1*coefficient ctx b ij.2 else 0 := by
  rw [term,SemiprimeD1JetRouting.route_value]
  by_cases ha : SemiprimeD1JetRouting.admissible ctx.axes ij.1 ij.2
  · by_cases hk : SemiprimeD1JetRouting.sumIndex ctx.axes ij.1 ij.2=k
    · simp only [ha,hk,ite_true,true_and]
      simpa only [read_bits,coefficient] using
        SemiprimeD1JetScalarBits.mul_zmod ctx.precision (read a ij.1).bits (read b ij.2).bits
    · simp [ha,hk,bitValue]
  · simp [ha,bitValue]

/-- The acquired output coordinate is exactly the full truncated convolution. -/
theorem mulAt_value (ctx : Context) (a b : List (List Bool)) (k : ℕ) :
    (bitValue (mulAt ctx a b k).bits:ZMod (2^ctx.precision))=convolution ctx a b k := by
  change (bitValue (sumReports ctx.precision _).bits:ZMod (2^ctx.precision))=_
  rw [sumReports_value]
  simp only [List.map_map,Function.comp_def,term_value,convolution]

/-- No nilpotent output coefficients are omitted or allocated outside the shape. -/
theorem mul_shape (ctx : Context) (a b : List (List Bool)) : (mul ctx a b).words.length=ctx.rank := by
  simp [mul]

/-- Dense addition has exactly the actual context rank. -/
theorem add_shape (ctx : Context) (a b : List (List Bool)) : (add ctx a b).words.length=ctx.rank := by
  simp [add]

/-- Every acquired output product coefficient has physical target width. -/
theorem mulAt_length (ctx : Context) (a b : List (List Bool)) (k : ℕ) :
    (mulAt ctx a b k).bits.length≤ctx.precision := sumReports_length _ _

/-- The acquired coordinate sum has its actual modular-ring meaning. -/
theorem addAt_value (ctx : Context) (a b : List (List Bool)) (i : ℕ) :
    (bitValue (addAt ctx a b i).bits:ZMod (2^ctx.precision))=
      coefficient ctx a i+coefficient ctx b i := by
  simpa only [addAt,read_bits,coefficient] using
    SemiprimeD1JetScalarBits.add_zmod ctx.precision (read a i).bits (read b i).bits

/-- The entire output vector denotes exactly the finite truncated convolution. -/
theorem mul_values (ctx : Context) (a b : List (List Bool)) :
    ((mul ctx a b).words.map (fun w => (bitValue w:ZMod (2^ctx.precision))))=
      (List.range ctx.rank).map (convolution ctx a b) := by
  simp only [mul,List.map_map,Function.comp_def,mulAt_value]

/-- The entire acquired addition vector denotes actual coefficientwise addition. -/
theorem add_values (ctx : Context) (a b : List (List Bool)) :
    ((add ctx a b).words.map (fun w => (bitValue w:ZMod (2^ctx.precision))))=
      (List.range ctx.rank).map (fun i => coefficient ctx a i+coefficient ctx b i) := by
  simp only [add,List.map_map,Function.comp_def,addAt_value]

/-- Every actual sum accumulator prefix is compact. -/
theorem sumReports_compact (p : ℕ) (rs : List Scalar) :
    SemiprimeSourceCompactBits.Compact (sumReports p rs).bits := by
  cases rs with
  | nil => trivial
  | cons r rs => exact SemiprimeD1JetScalarBits.add_compact _ _ _

/-- Every acquired product coordinate is compact, including literal zero bins. -/
theorem mulAt_compact (ctx : Context) (a b : List (List Bool)) (k : ℕ) :
    SemiprimeSourceCompactBits.Compact (mulAt ctx a b k).bits := sumReports_compact _ _

/-- Every acquired sum coordinate has target width. -/
theorem addAt_length (ctx : Context) (a b : List (List Bool)) (i : ℕ) :
    (addAt ctx a b i).bits.length≤ctx.precision := SemiprimeD1JetScalarBits.add_length _ _ _

/-- Every acquired sum coordinate is compact. -/
theorem addAt_compact (ctx : Context) (a b : List (List Bool)) (i : ℕ) :
    SemiprimeSourceCompactBits.Compact (addAt ctx a b i).bits := SemiprimeD1JetScalarBits.add_compact _ _ _

/-- Every complete product output word has actual target width. -/
theorem mul_bounded (ctx : Context) (a b : List (List Bool)) :
    ∀w∈(mul ctx a b).words,w.length≤ctx.precision := by
  intro w hw
  rcases List.mem_map.mp hw with ⟨r,hr,rfl⟩
  rcases List.mem_map.mp hr with ⟨k,_,rfl⟩
  exact mulAt_length _ _ _ _

/-- Every complete product output word is compact. -/
theorem mul_compact (ctx : Context) (a b : List (List Bool)) :
    ∀w∈(mul ctx a b).words,SemiprimeSourceCompactBits.Compact w := by
  intro w hw
  rcases List.mem_map.mp hw with ⟨r,hr,rfl⟩
  rcases List.mem_map.mp hr with ⟨k,_,rfl⟩
  exact mulAt_compact _ _ _ _

/-- Every complete sum output word has actual target width. -/
theorem add_bounded (ctx : Context) (a b : List (List Bool)) :
    ∀w∈(add ctx a b).words,w.length≤ctx.precision := by
  intro w hw
  rcases List.mem_map.mp hw with ⟨r,hr,rfl⟩
  rcases List.mem_map.mp hr with ⟨k,_,rfl⟩
  exact addAt_length _ _ _ _

/-- Every complete sum output word is compact. -/
theorem add_compact (ctx : Context) (a b : List (List Bool)) :
    ∀w∈(add ctx a b).words,SemiprimeSourceCompactBits.Compact w := by
  intro w hw
  rcases List.mem_map.mp hw with ⟨r,hr,rfl⟩
  rcases List.mem_map.mp hr with ⟨k,_,rfl⟩
  exact addAt_compact _ _ _ _

end RiemannGaussian.SemiprimeD1JetRingBits
