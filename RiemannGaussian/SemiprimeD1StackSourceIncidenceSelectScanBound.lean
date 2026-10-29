/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourceIncidenceSelectVariable
import RiemannGaussian.SemiprimeD1StackSourceIncidenceSelectCandidateBound
/-! # Actual whole-catalogue and committed-variable physical polynomial caps
The retained score pair is always an actual prior query result. Its physical
width, each parsed catalogue field and every actual query/rollback cap remain
paid uniformly throughout the complete chronological candidate scan.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceIncidenceSelectScanBound
open SemiprimeD1StackSourceIncidenceSelectCandidate SemiprimeD1StackSourceIncidenceSelectScan
open SemiprimeD1StackSourceIncidenceSelectVariable SemiprimeD1StackSourceIncidenceSelectCandidateBound
open SemiprimeD1StackSourceIncidenceSelectCommit
namespace Spec
export SemiprimeD1StackSourceIncidenceSelectSpec (scoredPick)
end Spec
/-- Only literal retained ID/score byte widths are interpreted here. -/
def PairBound (S:Nat) (pair:List Bool×List Bool) :Prop :=pair.1.length ≤ S ∧ pair.2.length ≤ (S+1)^3
/-- Actual strict-update caching never allocates an ID or score from any other source. -/
theorem pick_bound (S:Nat) (a b:List Bool×List Bool) (ha:PairBound S a) (hb:PairBound S b) :
    PairBound S (Spec.scoredPick a b) :=by
  unfold Spec.scoredPick
  split
  · exact hb
  · exact ha
/-- Each actually scanned ID has a paid catalogue width, and its actual query word has a paid binary width. -/
theorem scored_bound (ids:List (List Bool)) (rows:List (List Bool×List Bool))
    (square cube fourth:List Bool) (entry:List Bool×List Bool) (S:Nat)
    (hi:entry.1.length+entry.2.length ≤ S)
    (hd:(SemiprimeD1StackOwnerLookup.records rows []).length+square.length+cube.length+fourth.length ≤ S) :
    PairBound S (scored ids rows square cube fourth entry) :=
  ⟨by dsimp only [scored];omega,scoreWord_uniform ids entry.1 rows square cube fourth S hd⟩
/-- Exact retained incumbent after any actual scan prefix has the same physical width cap. -/
theorem scanBest_bound (ids:List (List Bool)) (rows:List (List Bool×List Bool))
    (square cube fourth:List Bool) (entries:List (List Bool×List Bool)) (best:List Bool×List Bool) (S:Nat)
    (hb:PairBound S best) (he:∀entry∈entries,entry.1.length+entry.2.length ≤ S)
    (hd:(SemiprimeD1StackOwnerLookup.records rows []).length+square.length+cube.length+fourth.length ≤ S) :
    PairBound S (scanBest ids rows square cube fourth best entries) :=by
  induction entries generalizing best with
  | nil=>exact hb
  | cons entry entries ih=>
    exact ih (Spec.scoredPick best (scored ids rows square cube fourth entry))
      (pick_bound S _ _ hb (scored_bound ids rows square cube fourth entry S (he entry List.mem_cons_self) hd))
      (fun e h=>he e (List.mem_cons_of_mem _ h))
/-- Own actual later-candidate clock is linear in the actual catalogue record count times a fixed stage polynomial. -/
theorem scanClock_uniform (ids:List (List Bool)) (rows:List (List Bool×List Bool))
    (square cube fourth:List Bool) (entries:List (List Bool×List Bool)) (best:List Bool×List Bool) (S:Nat)
    (hn:ids.length+1 ≤ S) (hw:∀word∈ids,word.length ≤ S)
    (hb:PairBound S best) (he:∀entry∈entries,entry.1.length+entry.2.length ≤ S)
    (hd:(SemiprimeD1StackOwnerLookup.records rows []).length+square.length+cube.length+fourth.length ≤ S) :
    scanClock ids (SemiprimeD1TensorTapeCodec.vectorBits ids) rows square cube fourth best entries ≤
      entries.length*(100000000000000000000*(S+1)^12)+2 :=by
  induction entries generalizing best with
  | nil=>simp only [scanClock,List.length_nil,Nat.zero_mul,Nat.zero_add,Nat.le_refl]
  | cons entry entries ih=>
    have hs:=scored_bound ids rows square cube fourth entry S (he entry List.mem_cons_self) hd
    have hnxt:=pick_bound S best _ hb hs
    have hi:=ih (Spec.scoredPick best (scored ids rows square cube fourth entry)) hnxt
      (fun e h=>he e (List.mem_cons_of_mem _ h))
    have hc:=candidateBound_uniform ids entry.1 entry.2 rows square cube fourth best.1 best.2 S hn hw
      (he entry List.mem_cons_self) hb.1 hb.2 hd
    simp only [scanClock,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega
/-- The complete first-plus-tail scan has the same actual catalogue-count cap and paid incumbent widths. -/
theorem catalogue_uniform (ids:List (List Bool)) (rows:List (List Bool×List Bool))
    (square cube fourth:List Bool) (first:List Bool×List Bool) (entries:List (List Bool×List Bool)) (S:Nat)
    (hn:ids.length+1 ≤ S) (hw:∀word∈ids,word.length ≤ S)
    (he:∀entry∈first::entries,entry.1.length+entry.2.length ≤ S)
    (hd:(SemiprimeD1StackOwnerLookup.records rows []).length+square.length+cube.length+fourth.length ≤ S) :
    catalogueClock ids (SemiprimeD1TensorTapeCodec.vectorBits ids) rows square cube fourth first entries ≤
      (entries.length+1)*(100000000000000000000*(S+1)^12)+2 ∧
      PairBound S (winnerPair ids rows square cube fourth first entries) :=by
  have hf:=scored_bound ids rows square cube fourth first S (he first List.mem_cons_self) hd
  have ht:=scanClock_uniform ids rows square cube fourth entries (scored ids rows square cube fourth first) S hn hw hf
    (fun e h=>he e (List.mem_cons_of_mem _ h)) hd
  have hc:=candidateBound_uniform ids first.1 first.2 rows square cube fourth [] [] S hn hw
    (he first List.mem_cons_self) (Nat.zero_le _) (Nat.zero_le _) hd
  refine ⟨?_,scanBest_bound ids rows square cube fourth entries _ S hf (fun e h=>he e (List.mem_cons_of_mem _ h)) hd⟩
  unfold catalogueClock
  simp only [Nat.add_mul,Nat.one_mul]
  omega
/-- A full actual marked-variable scan/commit has a fixed thirteen-degree physical-input cap. -/
theorem variableBound_uniform (ids:List (List Bool)) (rows:List (List Bool×List Bool))
    (square cube fourth:List Bool) (first:List Bool×List Bool) (entries:List (List Bool×List Bool)) (S:Nat)
    (hn:ids.length+1 ≤ S) (hw:∀word∈ids,word.length ≤ S)
    (hcat:(SemiprimeD1StackOwnerLookup.records (first::entries) []).length ≤ S)
    (he:∀entry∈first::entries,entry.1.length+entry.2.length ≤ S)
    (hd:(SemiprimeD1StackOwnerLookup.records rows []).length+square.length+cube.length+fourth.length ≤ S) :
    variableBound ids rows square cube fourth first entries ≤ 100000000000000000000000*(S+1)^13 ∧
      PairBound S (winnerPair ids rows square cube fourth first entries) :=by
  have hc:=catalogue_uniform ids rows square cube fourth first entries S hn hw he hd
  have hk:=SemiprimeD1StackSourceEnvironmentEncoding.variableKey_length ids.length
  have hcount:entries.length+1 ≤ S:=by
    have h:=records_count_le (first::entries)
    simp only [List.length_cons] at h
    omega
  have h13:S+1 ≤ (S+1)^13:=by simpa only [pow_one] using
    SemiprimeD1StackSourceIncidenceBounds.pow_mono (S+1) (by omega) 1 13 (by decide)
  have h313:(S+1)^3 ≤ (S+1)^13:=SemiprimeD1StackSourceIncidenceBounds.pow_mono (S+1) (by omega) 3 13 (by decide)
  have h1213:(S+1)^12 ≤ (S+1)^13:=SemiprimeD1StackSourceIncidenceBounds.pow_mono (S+1) (by omega) 12 13 (by decide)
  have hclock:catalogueClock ids (SemiprimeD1TensorTapeCodec.vectorBits ids) rows square cube fourth first entries ≤
      100000000000000000000*(S+1)^13+2:=by
    calc
      _ ≤ (entries.length+1)*(100000000000000000000*(S+1)^12)+2:=hc.1
      _ ≤ (S+1)*(100000000000000000000*(S+1)^12)+2:=Nat.add_le_add_right
        (Nat.mul_le_mul_right _ (by omega : entries.length+1 ≤ S+1)) _
      _=100000000000000000000*(S+1)^13+2:=by ring
  refine ⟨?_,hc.2⟩
  have hbID:=hc.2.1
  have hbScore:=hc.2.2
  unfold variableBound commitBound
  omega
end RiemannGaussian.SemiprimeD1StackSourceIncidenceSelectScanBound
