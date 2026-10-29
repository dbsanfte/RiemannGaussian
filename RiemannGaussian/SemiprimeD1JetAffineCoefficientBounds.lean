/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1JetAffineCoefficient
import RiemannGaussian.SemiprimeD1JetRingBounds

/-! # Physical single-coefficient recursion resources from actual original rows
All recursive output widths follow executed truncation; no intermediate fit or
arithmetic-work answer is a premise. Native tuple/index metadata stays explicit.
-/
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace RiemannGaussian.SemiprimeD1JetAffineCoefficientBounds
open SemiprimeD1JetAxes SemiprimeD1JetAffineCoefficient

/-- Structural shape and target physical width of an acquired vector. -/
def Good (ctx : Context) (ws : List (List Bool)) : Prop :=
  ws.length=ctx.rank ∧ ∀w∈ws,w.length≤ctx.precision

/-- Every allocated zero vector has its actual context shape and width. -/
theorem zero_good (ctx : Context) : Good ctx (zero ctx).words := by
  simp [Good,zero]

/-- Every allocated unit vector is physically reduced to the original precision. -/
theorem one_good (ctx : Context) : Good ctx (one ctx).words := by
  constructor
  · simp [one]
  · intro w hw
    rcases List.mem_map.mp hw with ⟨i,_,rfl⟩
    split_ifs
    · exact SemiprimeD1JetScalarBits.reduce_length _ _
    · exact Nat.zero_le _

/-- Concrete modular addition always returns target shape and width. -/
theorem add_good (ctx : Context) (a b : List (List Bool)) :
    Good ctx (SemiprimeD1JetRingBits.add ctx a b).words :=
  ⟨SemiprimeD1JetRingBits.add_shape _ _ _,SemiprimeD1JetRingBits.add_bounded _ _ _⟩

/-- Concrete modular multiplication always returns target shape and width. -/
theorem mul_good (ctx : Context) (a b : List (List Bool)) :
    Good ctx (SemiprimeD1JetRingBits.mul ctx a b).words :=
  ⟨SemiprimeD1JetRingBits.mul_shape _ _ _,SemiprimeD1JetRingBits.mul_bounded _ _ _⟩

/-- Every actual branch-sum prefix has physical target shape and width. -/
theorem sumRuns_good (ctx : Context) (rs : List JetRun) : Good ctx (sumRuns ctx rs).words := by
  cases rs with
  | nil => exact zero_good ctx
  | cons r rs => exact add_good _ _ _

/-- Every requested-coefficient subcall truncates all its returned physical words. -/
theorem evaluate_good (ctx : Context) (K : ℕ) (rows : List Row) (beta : List ℕ) :
    Good ctx (evaluate ctx K rows beta).words := by
  cases rows with
  | nil =>
    change Good ctx (if (SemiprimeD1AffineCoefficient.zeroTest beta).1 then one ctx else zero ctx).words
    split
    · exact one_good ctx
    · exact zero_good ctx
  | cons row rows => exact add_good _ _ _

/-- Returned coefficient words are canonically compact at every recursive subcall. -/
theorem evaluate_compact (ctx : Context) (K : ℕ) (rows : List Row) (beta : List ℕ) :
    ∀w∈(evaluate ctx K rows beta).words,SemiprimeSourceCompactBits.Compact w := by
  cases rows with
  | nil =>
    change ∀w∈(if (SemiprimeD1AffineCoefficient.zeroTest beta).1 then one ctx else zero ctx).words,_
    split
    · intro w hw
      rcases List.mem_map.mp hw with ⟨i,_,rfl⟩
      split_ifs
      · exact SemiprimeD1JetScalarBits.reduce_compact _ _
      · trivial
    · simp [zero,SemiprimeSourceCompactBits.Compact]
  | cons row rows => exact SemiprimeD1JetRingBits.add_compact _ _ _

/-- Fixed polynomial cost of a whole concrete dense addition. -/
def addBudget (ctx : Context) (W : ℕ) : ℕ :=
  ctx.rank*(6*ctx.rank+11*W+9*ctx.precision+17)+10*ctx.rank+5

/-- A cached list of branch reports retains every report and every physical sum. -/
theorem sumRuns_clock (ctx : Context) (rs : List JetRun)
    (hg : ∀r∈rs,Good ctx r.words) :
    (sumRuns ctx rs).clock≤(rs.map (fun r=>r.clock)).sum+
      rs.length*(addBudget ctx ctx.precision+3)+ctx.rank+1 := by
  induction rs with
  | nil => simp [sumRuns,zero]
  | cons r rs ih =>
    have hr:=hg r List.mem_cons_self
    have ht:=sumRuns_good ctx rs
    have hi:=ih (fun s hs=>hg s (List.mem_cons_of_mem r hs))
    have ha:=SemiprimeD1JetRingBounds.add_clock ctx r.words (sumRuns ctx rs).words ctx.precision
      hr.1.le ht.1.le hr.2 ht.2
    change r.clock+(sumRuns ctx rs).clock+
      (SemiprimeD1JetRingBits.add ctx r.words (sumRuns ctx rs).words).clock+3≤_
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    unfold addBudget at hi ⊢
    nlinarith

/-- Original source row shape/width, including every actual mode vector. -/
def Source (ctx : Context) (W A : ℕ) (row : Row) : Prop :=
  row.base.length≤ctx.rank ∧ (∀w∈row.base,w.length≤W) ∧ row.coefficients.length≤A ∧
    ∀v∈row.coefficients,v.length≤ctx.rank ∧ ∀w∈v,w.length≤W

/-- Borrowed mode-vector reads preserve original shape/width or literal zero. -/
theorem read_source (ctx : Context) (W : ℕ) (hp : ctx.precision≤W)
    (vs : List (List (List Bool))) (hv : ∀v∈vs,v.length≤ctx.rank ∧ ∀w∈v,w.length≤W)
    (i : ℕ) :
    (SemiprimeD1AffineCoefficient.read (zero ctx).words vs i).1.length≤ctx.rank ∧
      ∀w∈(SemiprimeD1AffineCoefficient.read (zero ctx).words vs i).1,w.length≤W := by
  induction vs generalizing i with
  | nil => exact ⟨(zero_good ctx).1.le,fun w hw=>((zero_good ctx).2 w hw).trans hp⟩
  | cons v vs ih =>
    cases i with
    | zero => exact hv v List.mem_cons_self
    | succ i => exact ih (fun u hu=>hv u (List.mem_cons_of_mem v hu)) i

/-- Literal finite report-sum bound, without an acquired-sum oracle. -/
theorem map_clock_le (is : List ℕ) (f : ℕ→JetRun) (B : ℕ)
    (h : ∀i∈is,(f i).clock≤B) : (is.map (fun i=>(f i).clock)).sum≤ is.length*B := by
  induction is with
  | nil => simp
  | cons i is ih =>
    have hh:=h i List.mem_cons_self
    have ht:=ih (fun j hj=>h j (List.mem_cons_of_mem i hj))
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    nlinarith

/-- Fixed polynomial overhead for one actual physical recursion stage. -/
def stageConstant (ctx : Context) (K T W A : ℕ) : ℕ :=
  (K+1)*(6*T+3*A+
    2*SemiprimeD1JetRingBounds.mulBudget ctx.axes.length ctx.rank W ctx.precision+
    2*addBudget ctx W+4*ctx.rank+9*ctx.precision+50)

/-- One row pays all actual cached children, source reads and concrete arithmetic. -/
theorem evaluate_step_clock (ctx : Context) (K : ℕ) (row : Row) (rows : List Row)
    (beta : List ℕ) (W A B : ℕ) (hp : ctx.precision≤W) (hs : Source ctx W A row)
    (hchild : ∀target : List ℕ,target.length=beta.length→(evaluate ctx K rows target).clock≤B) :
    (evaluate ctx K (row::rows) beta).clock≤(K+1)*B+stageConstant ctx K beta.length W A := by
  let branch (i : ℕ) : JetRun :=
    let exponent:=SemiprimeD1AffineCoefficient.read 0 beta i
    if exponent.1=0 then ⟨(zero ctx).words,exponent.2+3⟩
    else
      let target:=SemiprimeD1AffineCoefficient.decrement beta i
      let child:=evaluate ctx K rows target.1
      let coeff:=SemiprimeD1AffineCoefficient.read (zero ctx).words row.coefficients i
      let out:=SemiprimeD1JetRingBits.mul ctx coeff.1 child.words
      ⟨out.words,exponent.2+target.2+child.clock+coeff.2+out.clock+5⟩
  have hgood (i : ℕ) : Good ctx (branch i).words := by
    unfold branch
    dsimp only
    split
    · exact zero_good ctx
    · exact mul_good _ _ _
  have hbranch (i : ℕ) : (branch i).clock≤B+6*beta.length+3*A+
      SemiprimeD1JetRingBounds.mulBudget ctx.axes.length ctx.rank W ctx.precision+10 := by
    have he:=SemiprimeD1AffineCoefficientBounds.read_work 0 beta i
    have ht:=SemiprimeD1AffineCoefficientBounds.decrement_work beta i
    have hc:=SemiprimeD1AffineCoefficientBounds.read_work (zero ctx).words row.coefficients i
    have hh:=hchild (SemiprimeD1AffineCoefficient.decrement beta i).1
      (SemiprimeD1AffineCoefficient.decrement_length beta i)
    have hsource:=read_source ctx W hp row.coefficients hs.2.2.2 i
    have hreturn:=evaluate_good ctx K rows (SemiprimeD1AffineCoefficient.decrement beta i).1
    have hm:=SemiprimeD1JetRingBounds.mul_clock ctx
      (SemiprimeD1AffineCoefficient.read (zero ctx).words row.coefficients i).1
      (evaluate ctx K rows (SemiprimeD1AffineCoefficient.decrement beta i).1).words W
      hsource.1 hreturn.1.le hsource.2 (fun w hw=>(hreturn.2 w hw).trans hp)
    unfold branch
    dsimp only
    split <;> dsimp only <;> have hrow:=hs.2.2.1 <;> omega
  have hsumbound:=map_clock_le (List.range K) branch
    (B+6*beta.length+3*A+SemiprimeD1JetRingBounds.mulBudget ctx.axes.length ctx.rank W ctx.precision+10)
    (fun i _=>hbranch i)
  have hsum:=sumRuns_clock ctx ((List.range K).map branch) (by
    intro r hr
    rcases List.mem_map.mp hr with ⟨i,_,rfl⟩
    exact hgood i)
  simp only [List.map_map,Function.comp_def,List.length_map,List.length_range] at hsumbound hsum
  have hbase:=hchild beta rfl
  have hreturn:=evaluate_good ctx K rows beta
  have hm:=SemiprimeD1JetRingBounds.mul_clock ctx row.base (evaluate ctx K rows beta).words W
    hs.1 hreturn.1.le hs.2.1 (fun w hw=>(hreturn.2 w hw).trans hp)
  have hgprod:=mul_good ctx row.base (evaluate ctx K rows beta).words
  have hgtotal:=sumRuns_good ctx ((List.range K).map branch)
  have hadd:=SemiprimeD1JetRingBounds.add_clock ctx
    (SemiprimeD1JetRingBits.mul ctx row.base (evaluate ctx K rows beta).words).words
    (sumRuns ctx ((List.range K).map branch)).words W hgprod.1.le hgtotal.1.le
    (fun w hw=>(hgprod.2 w hw).trans hp) (fun w hw=>(hgtotal.2 w hw).trans hp)
  have hab : addBudget ctx ctx.precision≤addBudget ctx W := by
    unfold addBudget
    nlinarith
  change (zero ctx).clock+(evaluate ctx K rows beta).clock+
    (sumRuns ctx ((List.range K).map branch)).clock+
    (SemiprimeD1JetRingBits.mul ctx row.base (evaluate ctx K rows beta).words).clock+
    (SemiprimeD1JetRingBits.add ctx
      (SemiprimeD1JetRingBits.mul ctx row.base (evaluate ctx K rows beta).words).words
      (sumRuns ctx ((List.range K).map branch)).words).clock+10*K+8≤_
  simp only [zero]
  unfold stageConstant addBudget at *
  nlinarith

/-- Closed physical coefficient-acquisition budget. -/
def budget (ctx : Context) (K L T W A : ℕ) : ℕ :=
  (L+1)*stageConstant ctx K T W A*(K+1)^L

/-- Actual physical coefficient acquisition is poly(dimensions,width)*(K+1)^rows.
All recursive shapes, branch bounds and intermediate arithmetic widths are derived. -/
theorem evaluate_clock (ctx : Context) (K : ℕ) (rows : List Row) (beta : List ℕ)
    (W A : ℕ) (hp : ctx.precision≤W) (hs : ∀row∈rows,Source ctx W A row) :
    (evaluate ctx K rows beta).clock≤budget ctx K rows.length beta.length W A := by
  induction rows generalizing beta with
  | nil =>
    have hz:=SemiprimeD1AffineCoefficientBounds.zeroTest_work beta
    have ho:=SemiprimeD1JetScalarBits.reduce_clock ctx.precision [true]
    have htest : (evaluate ctx K [] beta).clock≤3*beta.length+9*ctx.precision+3*ctx.rank+20 := by
      change (SemiprimeD1AffineCoefficient.zeroTest beta).2+
        (if (SemiprimeD1AffineCoefficient.zeroTest beta).1 then one ctx else zero ctx).clock+3≤_
      split <;> simp only [one,zero] <;> omega
    unfold budget stageConstant
    simp only [List.length_nil,pow_zero,Nat.mul_one,Nat.zero_add]
    nlinarith
  | cons row rows ih =>
    have hh:=evaluate_step_clock ctx K row rows beta W A
      (budget ctx K rows.length beta.length W A) hp (hs row List.mem_cons_self)
      (fun target ht=>by simpa only [ht] using ih target (fun r hr=>hs r (List.mem_cons_of_mem row hr)))
    have hn:=SemiprimeD1AffineCoefficientBounds.recursion_budget K rows.length
      (stageConstant ctx K beta.length W A)
    unfold budget at hh ⊢
    simp only [List.length_cons]
    exact hh.trans hn

end RiemannGaussian.SemiprimeD1JetAffineCoefficientBounds
