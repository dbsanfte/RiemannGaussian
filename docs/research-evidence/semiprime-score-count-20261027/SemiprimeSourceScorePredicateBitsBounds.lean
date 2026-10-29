/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceScorePredicateBits
import RiemannGaussian.SemiprimeReportPolynomialGrowth
import RiemannGaussian.SemiprimeSourceSearchState

/-! # Original-metadata resource bounds for physical score truth acquisition
Physical row/key widths follow original Fin colours and original ID caps.
No intermediate Fits, score value, predicate truth or callback-cost oracle.
-/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace RiemannGaussian.SemiprimeSourceScorePredicateBitsBounds
open SemiprimeRationalBits SemiprimeMaterializedWords SemiprimeMaterializedScoreEnvironment
open SemiprimeSourceScorePredicateBits SemiprimeSourceOffsetInputsCore
open SemiprimeReportPolynomialGrowth
open OAI.Algorithms.SubexponentialSAT Subexp.ConstructivePacking SqrtLog

/-- Concrete row shape/word widths, discharged from original acquisition. -/
def RowBound (W Q : ℕ) (row : Row) : Prop := row.length ≤ Q ∧ ∀ x∈row,Width x W
/-- Concrete key and row payload bounds. -/
def PairsBound (W Q : ℕ) (ps : Pairs) : Prop :=
  ∀ p∈ps,Width p.1 W ∧ RowBound W Q p.2

/-- Physical width monotonicity preserves both original bit lists. -/
theorem width_mono {x : RationalWord} {W V : ℕ} (hx : Width x W) (h : W ≤ V) : Width x V :=
  ⟨hx.1.trans h,hx.2.trans h⟩

/-- Exact original-coordinate acquisition shape. -/
theorem acquireCoordinates_length {r : ℕ} (cs : List (Fin r)) :
    (acquireCoordinates cs).value.length=cs.length := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp only [acquireCoordinates,List.length_cons,ih]

/-- Every acquired colour width follows its original Fin-r bound. -/
theorem acquireCoordinates_bounded {r : ℕ} (cs : List (Fin r)) (W : ℕ) (hW : r+1 ≤ W) :
    ∀ x∈(acquireCoordinates cs).value,Width x W := by
  induction cs with
  | nil => simp [acquireCoordinates]
  | cons c cs ih =>
    intro x hx
    simp only [acquireCoordinates,List.mem_cons] at hx
    rcases hx with rfl|hx
    · exact width_mono (encodeNat_spec c.val).2.2 (by omega)
    · exact ih x hx

/-- Physical original cached rows have public length Q and derived widths. -/
theorem acquireWord_bounded {r Q : ℕ} (w : CachedWord r Q) (W : ℕ) (hW : r+1 ≤ W) :
    RowBound W Q (acquireWord w).value := by
  refine ⟨?_,acquireCoordinates_bounded _ W hW⟩
  simp only [acquireWord,acquireCoordinates_length,Array.length_toList,w.size_eq]
  exact le_rfl

/-- Original coordinate colour bounds pay every actual bit increment and row cell. -/
theorem acquireCoordinates_work {r : ℕ} (cs : List (Fin r)) :
    (acquireCoordinates cs).work ≤ cs.length*(20*(r+1)^2+7)+1 := by
  induction cs with
  | nil => simp [acquireCoordinates]
  | cons c cs ih =>
    have h := (encodeNat_clock c.val).trans (show 20*(c.val+1)^2+4 ≤ 20*(r+1)^2+4 by gcongr;exact c.isLt.le)
    simp only [acquireCoordinates,List.length_cons]
    nlinarith

/-- Original-data row acquisition budget. -/
def wordBudget (r Q : ℕ) : ℕ := Q*(20*(r+1)^2+9)+3

/-- Entire actual cache-word producer is paid from original r,Q. -/
theorem acquireWord_work {r Q : ℕ} (w : CachedWord r Q) :
    (acquireWord w).work ≤ wordBudget r Q := by
  have h := acquireCoordinates_work w.data.toList
  simp only [Array.length_toList,w.size_eq] at h
  unfold acquireWord wordBudget
  dsimp only
  rw [w.size_eq]
  nlinarith

/-- Acquired fixed-row keys use only original reverse-prefix indices. -/
theorem acquireFixed_bounded {r Q : ℕ} (fixed : List (CachedWord r Q)) (N W : ℕ)
    (hn : fixed.length ≤ N) (hN : N+1 ≤ W) (hr : r+1 ≤ W) :
    PairsBound W Q (acquireFixed fixed).value := by
  induction fixed with
  | nil => simp [acquireFixed,PairsBound]
  | cons w ws ih =>
    intro p hp
    simp only [acquireFixed,List.mem_cons] at hp
    rcases hp with rfl|hp
    · exact ⟨width_mono (encodeNat_spec ws.length).2.2 (by simp only [List.length_cons] at hn;omega),
        acquireWord_bounded w W hr⟩
    · exact ih (by simp only [List.length_cons] at hn;omega) p hp

/-- Acquired override keys use their ORIGINAL finite ID cap. -/
theorem acquireOverrides_bounded {r Q : ℕ} (ps : List (ℕ × CachedWord r Q)) (N W : ℕ)
    (hn : ∀ p∈ps,p.1 ≤ N) (hN : N+1 ≤ W) (hr : r+1 ≤ W) :
    PairsBound W Q (acquireOverrides ps).value := by
  induction ps with
  | nil => simp [acquireOverrides,PairsBound]
  | cons p ps ih =>
    intro q hq
    simp only [acquireOverrides,List.mem_cons] at hq
    rcases hq with rfl|hq
    · exact ⟨width_mono (encodeNat_spec p.1).2.2 (by have := hn p List.mem_cons_self;omega),
        acquireWord_bounded p.2 W hr⟩
    · exact ih (fun q hq => hn q (List.mem_cons_of_mem p hq)) q hq

/-- Actual cache acquisition preserves list lengths. -/
theorem acquireFixed_length {r Q : ℕ} (fixed : List (CachedWord r Q)) :
    (acquireFixed fixed).value.length=fixed.length := by
  induction fixed with
  | nil => rfl
  | cons w ws ih => simp only [acquireFixed,List.length_cons,ih]

/-- Actual override cache acquisition preserves list lengths. -/
theorem acquireOverrides_length {r Q : ℕ} (ps : List (ℕ × CachedWord r Q)) :
    (acquireOverrides ps).value.length=ps.length := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp only [acquireOverrides,List.length_cons,ih]

/-- Actual double-comparison clock; no validity is required for this width bound. -/
def equalityBudget (W : ℕ) : ℕ := 400*(W+1)^2+3

/-- The actual physical equality report has the displayed width budget. -/
theorem equalWord_work (x y : RationalWord) (W : ℕ) (hx : Width x W) (hy : Width y W) :
    (equalWord x y).work ≤ equalityBudget W := by
  have hxy := SemiprimeSourceComparisonBits.compare_clock x y W hx hy
  have hyx := SemiprimeSourceComparisonBits.compare_clock y x W hy hx
  unfold equalWord equalityBudget
  dsimp only
  omega

/-- Full selected-row copying budget including all original list cells. -/
def copyBudget (W Q : ℕ) : ℕ := Q*(8*W+9)+3

/-- Selected coordinate-row copy work follows its actual row shape. -/
theorem copyRow_work (row : Row) (W Q : ℕ) (h : RowBound W Q row) :
    (copyRow row).work ≤ copyBudget W Q := by
  have hc := (SemiprimeSourceMemoryBits.copyMemory_clock row W h.2).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_right (8*W+9) h.1) 1)
  unfold copyRow copyBudget
  dsimp only
  omega

/-- Per visited key, physical payload copy/equality and branch/control work. -/
def scanStep (W : ℕ) : ℕ := 8*W+6+equalityBudget W+4

/-- Original key cache bounds propagate through every ACTUAL scan branch. -/
theorem scan_bounded (target : RationalWord) (fallback : Unit → Run Row) (ps : Pairs)
    (W Q : ℕ) (hp : PairsBound W Q ps) (hf : RowBound W Q (fallback ()).value) :
    RowBound W Q (scan target fallback ps).value := by
  induction ps with
  | nil => exact hf
  | cons p ps ih =>
    have hh := hp p List.mem_cons_self
    have ht := ih (fun q hq => hp q (List.mem_cons_of_mem p hq))
    simp only [scan]
    split_ifs
    · simpa only [copyRow_value] using hh.2
    · exact ht

/-- The actual lazy fallback is charged only when executed; every visited key is paid. -/
theorem scan_work (target : RationalWord) (fallback : Unit → Run Row) (ps : Pairs)
    (W Q F : ℕ) (ht : Width target W) (hp : PairsBound W Q ps)
    (hf : (fallback ()).work ≤ F) (hcopy : copyBudget W Q ≤ F) :
    (scan target fallback ps).work ≤ ps.length*scanStep W+F := by
  induction ps with
  | nil => simpa only [scan,List.length_nil,Nat.zero_mul,Nat.zero_add] using hf
  | cons p ps ih =>
    have hh := hp p List.mem_cons_self
    have ht' := ih (fun q hq => hp q (List.mem_cons_of_mem p hq))
    have hkey := SemiprimeSourceMemoryBits.copyWord_clock p.1 W hh.1
    have hsame := equalWord_work (SemiprimeSourceMemoryBits.copyWord p.1).word target W
      (by simpa only [SemiprimeSourceMemoryBits.copyWord_word] using hh.1) ht
    have hc := (copyRow_work p.2 W Q hh.2).trans hcopy
    simp only [scan,List.length_cons]
    unfold scanStep at ht' ⊢
    split_ifs <;> dsimp only <;> nlinarith

/-- Original finite-key encoding budget. -/
def idBudget (N : ℕ) : ℕ := 20*(N+1)^2+4
/-- Original-data fixed-prefix acquisition, including actual suffix-length reads. -/
theorem acquireFixed_work {r Q : ℕ} (fixed : List (CachedWord r Q)) (N : ℕ)
    (hn : fixed.length ≤ N) :
    (acquireFixed fixed).work ≤ fixed.length*(idBudget N+wordBudget r Q+N+5)+1 := by
  induction fixed with
  | nil => simp [acquireFixed]
  | cons w ws ih =>
    have ht := ih (by simp only [List.length_cons] at hn;omega)
    have hk := (encodeNat_clock ws.length).trans
      (show 20*(ws.length+1)^2+4 ≤ idBudget N by unfold idBudget;gcongr;simp only [List.length_cons] at hn;omega)
    have hw := acquireWord_work w
    simp only [acquireFixed,List.length_cons]
    have hl : ws.length ≤ N := by simp only [List.length_cons] at hn;omega
    nlinarith

/-- Original bounded override keys pay all actual bit acquisitions. -/
theorem acquireOverrides_work {r Q : ℕ} (ps : List (ℕ × CachedWord r Q)) (N : ℕ)
    (hn : ∀ p∈ps,p.1 ≤ N) :
    (acquireOverrides ps).work ≤ ps.length*(idBudget N+wordBudget r Q+4)+1 := by
  induction ps with
  | nil => simp [acquireOverrides]
  | cons p ps ih =>
    have ht := ih (fun q hq => hn q (List.mem_cons_of_mem p hq))
    have hk := (encodeNat_clock p.1).trans
      (show 20*(p.1+1)^2+4 ≤ idBudget N by unfold idBudget;gcongr;exact hn p List.mem_cons_self)
    have hw := acquireWord_work p.2
    simp only [acquireOverrides,List.length_cons]
    nlinarith

/-- Entire actual original environment acquisition, with no word advice. -/
def acquisitionBudget (r Q N s : ℕ) : ℕ :=
  wordBudget r Q+N*(idBudget N+wordBudget r Q+N+5)+1+
    s*(idBudget N+wordBudget r Q+4)+1+5

/-- Full original environment acquisition work follows only original list/key caps. -/
theorem acquireEnvironment_work {r Q : ℕ} (env : Environment r Q) (N s : ℕ)
    (hf : env.fixed.length ≤ N) (ho : env.overrides.length ≤ s)
    (hk : ∀ p∈env.overrides,p.1 ≤ N) :
    (acquireEnvironment env).work ≤ acquisitionBudget r Q N s := by
  have hd := acquireWord_work env.default
  have hfix := (acquireFixed_work env.fixed N hf).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_right _ hf) 1)
  have hov := (acquireOverrides_work env.overrides N hk).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_right _ ho) 1)
  unfold acquireEnvironment acquisitionBudget
  dsimp only
  omega

/-- Original-data key lookup budget through both possible finite scans. -/
def readBudget (W Q N s : ℕ) : ℕ := idBudget N+(N+s)*scanStep W+copyBudget W Q+3

/-- Actual returned rows preserve original shape through both scans. -/
theorem readEnvironment_bounded (env : PhysicalEnvironment) (i W Q : ℕ)
    (hd : RowBound W Q env.default) (hf : PairsBound W Q env.fixed)
    (ho : PairsBound W Q env.overrides) :
    RowBound W Q (readEnvironment env i).value := by
  apply scan_bounded _ _ _ W Q ho
  apply scan_bounded _ _ _ W Q hf
  simpa only [copyRow_value] using hd

/-- All original-target acquisition, visited key copies/comparisons and selected-row copy are paid. -/
theorem readEnvironment_work (env : PhysicalEnvironment) (i W Q N s : ℕ)
    (hi : i ≤ N) (hN : N+1 ≤ W)
    (hd : RowBound W Q env.default) (hf : PairsBound W Q env.fixed)
    (ho : PairsBound W Q env.overrides)
    (hfl : env.fixed.length ≤ N) (hol : env.overrides.length ≤ s) :
    (readEnvironment env i).work ≤ readBudget W Q N s := by
  have ht := width_mono (encodeNat_spec i).2.2 (by omega : i+1 ≤ W)
  have hc := copyRow_work env.default W Q hd
  have hfix := (scan_work (encodeNat i).word (fun _ => copyRow env.default) env.fixed
    W Q (copyBudget W Q) ht hf hc le_rfl).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_right _ hfl) _)
  have hov := (scan_work (encodeNat i).word
    (fun _ => scan (encodeNat i).word (fun _ => copyRow env.default) env.fixed) env.overrides
    W Q (N*scanStep W+copyBudget W Q) ht ho hfix (Nat.le_add_left _ _)).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_right _ hol) _)
  have hk := (encodeNat_clock i).trans
    (show 20*(i+1)^2+4 ≤ idBudget N by unfold idBudget;gcongr)
  unfold readEnvironment readBudget
  dsimp only
  nlinarith

/-- Finite coordinate address acquisition and full memory scan budget. -/
def coordinateBudget (W Q : ℕ) : ℕ :=
  20*(Q+1)^2+(Q+1)*(8*W+15*(Q+1)+30)+3

/-- Every physical coordinate read has the same original row-width cap. -/
theorem coordinate_bounded (row : Row) (i W Q : ℕ) (hW : 1 ≤ W)
    (hr : RowBound W Q row) : Width (coordinate row i).word W :=
  SemiprimeSourceMemoryBits.readWord_width row _ W hW hr.2

/-- Address bits are actually acquired, and every visited payload is charged. -/
theorem coordinate_work (row : Row) (i W Q : ℕ) (hi : i ≤ Q) (hr : RowBound W Q row) :
    (coordinate row i).clock ≤ coordinateBudget W Q := by
  have ha : (natBits i).bits.length ≤ Q+1 := (natBits_length i).trans (by omega)
  have hread := (SemiprimeSourceMemoryBits.readWord_clock row (natBits i).bits W (Q+1)
    (by omega) ha hr.2).trans
    (Nat.mul_le_mul_right _ (Nat.add_le_add_right hr.1 1))
  have hn := (natBits_clock i).trans
    (show 20*(i+1)^2 ≤ 20*(Q+1)^2 by gcongr)
  unfold coordinate coordinateBudget
  dsimp only
  omega

/-- Complete actual whole-row equality budget. -/
def rowEqualityBudget (W Q : ℕ) : ℕ := Q*(2*coordinateBudget W Q+equalityBudget W+3)+1

/-- Every coordinate branch/copy/address and both physical comparisons remain paid. -/
theorem equalRows_work (left right : Row) (q W Q : ℕ) (hW : 1 ≤ W)
    (hl : RowBound W Q left) (hr : RowBound W Q right) (hq : q ≤ Q) :
    (equalRows left right q).work ≤ q*(2*coordinateBudget W Q+equalityBudget W+3)+1 := by
  induction q with
  | zero => simp [equalRows]
  | succ q ih =>
    have ht := ih (by omega)
    have ha := coordinate_work left q W Q (by omega) hl
    have hb := coordinate_work right q W Q (by omega) hr
    have hs := equalWord_work (coordinate left q).word (coordinate right q).word W
      (coordinate_bounded left q W Q hW hl) (coordinate_bounded right q W Q hW hr)
    simp only [equalRows]
    nlinarith

/-- Actual terminal lookup/equality work at derived original metadata caps. -/
def terminalStepBudget (W Q N s : ℕ) : ℕ :=
  4*readBudget W Q N s+2*rowEqualityBudget W Q+2*coordinateBudget W Q+equalityBudget W+10

/-- Physical terminal work uses only bounded original support IDs and acquired caches. -/
theorem terminal_work (env : PhysicalEnvironment) {Q : ℕ} (p : ScoreProgram Q)
    (W N s : ℕ) (hW : 1 ≤ W) (hN : N+1 ≤ W)
    (hd : RowBound W Q env.default) (hf : PairsBound W Q env.fixed)
    (ho : PairsBound W Q env.overrides)
    (hfl : env.fixed.length ≤ N) (hol : env.overrides.length ≤ s)
    (hp : ∀ i∈support p,i ≤ N) :
    (terminal env p).work ≤ terminalStepBudget W Q N s := by
  have hread (i : ℕ) (hi : i ≤ N) := readEnvironment_work env i W Q N s hi hN hd hf ho hfl hol
  have hrow (i : ℕ) := readEnvironment_bounded env i W Q hd hf ho
  cases p with
  | incidence a b c d =>
    have ha := hread a (hp a (by simp [support]))
    have hb := hread b (hp b (by simp [support]))
    have hc := hread c (hp c (by simp [support]))
    have hd' := hread d (hp d (by simp [support]))
    have hh := equalRows_work (readEnvironment env a).value (readEnvironment env c).value Q W Q
      hW (hrow a) (hrow c) le_rfl
    have hs := equalRows_work (readEnvironment env b).value (readEnvironment env d).value Q W Q
      hW (hrow b) (hrow d) le_rfl
    change _ ≤ _ at hh hs
    unfold SemiprimeSourceScorePredicateBits.terminal terminalStepBudget rowEqualityBudget
    dsimp only
    omega
  | head t a b =>
    have ha := hread a (hp a (by simp [support]))
    have hb := hread b (hp b (by simp [support]))
    have hca := coordinate_work (readEnvironment env a).value t.val W Q t.isLt.le (hrow a)
    have hcb := coordinate_work (readEnvironment env b).value t.val W Q t.isLt.le (hrow b)
    have hs := equalWord_work (coordinate (readEnvironment env a).value t.val).word
      (coordinate (readEnvironment env b).value t.val).word W
      (coordinate_bounded _ _ W Q hW (hrow a)) (coordinate_bounded _ _ W Q hW (hrow b))
    unfold SemiprimeSourceScorePredicateBits.terminal terminalStepBudget
    dsimp only
    omega

/-- Physical width derived only from ORIGINAL colour, coordinate and ID dimensions. -/
def workingWidth (r Q N : ℕ) : ℕ := r+Q+N+3
/-- Complete original-environment acquisition plus actual terminal work. -/
def terminalBudget (r Q N s : ℕ) : ℕ :=
  acquisitionBudget r Q N s+terminalStepBudget (workingWidth r Q N) Q N s+2

/-- The ORIGINAL-data terminal has a complete retained bound with no encoded
words, Fits, predicate truth or callback-work premise. -/
theorem terminal_original_work {r Q : ℕ} (env : Environment r Q) (p : ScoreProgram Q)
    (N s : ℕ) (hf : env.fixed.length ≤ N) (ho : env.overrides.length ≤ s)
    (hk : ∀ v∈env.overrides,v.1 ≤ N) (hp : ∀ i∈support p,i ≤ N) :
    (terminal_original env p).work ≤ terminalBudget r Q N s := by
  let W := workingWidth r Q N
  have hN : N+1 ≤ W := by dsimp [W,workingWidth];omega
  have hr : r+1 ≤ W := by dsimp [W,workingWidth];omega
  have ha := acquireEnvironment_work env N s hf ho hk
  have hd := acquireWord_bounded env.default W hr
  have hfix := acquireFixed_bounded env.fixed N W hf hN hr
  have hov := acquireOverrides_bounded env.overrides N W hk hN hr
  have ht := terminal_work (acquireEnvironment env).value p W N s
    (by dsimp [W,workingWidth];omega) hN hd hfix hov
    (by simpa only [acquireEnvironment,acquireFixed_length] using hf)
    (by simpa only [acquireEnvironment,acquireOverrides_length] using ho) hp
  unfold terminal_original terminalBudget
  dsimp only
  change (acquireEnvironment env).work+(terminal (acquireEnvironment env).value p).work+2 ≤ _
  exact Nat.add_le_add_right (Nat.add_le_add ha ht) 2

/-- All original metadata bounded by S gives a fixed monomial, without an
exponential global-assignment resource or a supplied terminal-cost oracle. -/
theorem terminalBudget_monomial : ∃ C k : ℕ,∀ r Q N s S,
    r ≤ S → Q ≤ S → N ≤ S → s ≤ S → terminalBudget r Q N s ≤ C*(S+1)^k := by
  have hh : Bound (fun S => terminalBudget S S S S) := by
    simp only [terminalBudget,acquisitionBudget,terminalStepBudget,workingWidth,wordBudget,
      idBudget,readBudget,rowEqualityBudget,coordinateBudget,equalityBudget,copyBudget,scanStep]
    boundArithmetic
  obtain ⟨C,k,h⟩ := hh
  refine ⟨C,k,?_⟩
  intro r Q N s S hr hQ hN hs
  apply le_trans _ (h S)
  simp only [terminalBudget,acquisitionBudget,terminalStepBudget,workingWidth,wordBudget,
    idBudget,readBudget,rowEqualityBudget,coordinateBudget,equalityBudget,copyBudget,scanStep]
  gcongr

/-- Actual ORIGINAL compiled score descriptors discharge their ID cap from
the acquired original index enumeration, not an advised terminal budget. -/
theorem compiled_terminal_original_work {I V E : Type} [DecidableEq V] [DecidableEq E]
    {r Q : ℕ} (owner : I → V) (factor : I → E)
    (indices : FiniteEnumeration (V ⊕ E)) (terms : List (Packing.ScoreTerm I V Q))
    (env : Environment r Q) (p : ScoreProgram Q)
    (hcompiled : p∈(SemiprimeMaterializedSourceWords.compileAll owner factor indices.values terms).value)
    (N s : ℕ) (hindices : indices.values.length ≤ N)
    (hf : env.fixed.length ≤ N) (ho : env.overrides.length ≤ s)
    (hk : ∀ v∈env.overrides,v.1 ≤ N) :
    (terminal_original env p).work ≤ terminalBudget r Q N s := by
  apply terminal_original_work env p N s hf ho hk
  intro i hi
  exact (SemiprimeSourceSearchState.compileAll_support_lt owner factor indices terms p hcompiled i hi).le.trans hindices

end RiemannGaussian.SemiprimeSourceScorePredicateBitsBounds
