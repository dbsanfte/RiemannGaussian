/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourceIncidenceSelectCandidate
import RiemannGaussian.SemiprimeD1StackSourceIncidenceSelectScore
/-! # Complete actual catalogue scan with first-on-tie score caching
The physical false terminator and real EOF peek finish each scan. Every real
candidate source step rolls back its temporary environment before the next
candidate is parsed, so every comparison uses the same actual old prefix.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceIncidenceSelectScan
open SemiprimeD1StackSourceIncidenceSelect SemiprimeD1StackSourceIncidenceSelectPrimitives
open SemiprimeD1StackSourceIncidenceSelectView SemiprimeD1StackSourceIncidenceSelectCandidate
open SemiprimeD1StackProcedureTrace
namespace E
export SemiprimeD1StackSourceEnvironmentEncoding (variableKey)
end E
namespace Pick
export SemiprimeD1StackSourceIncidenceSelectSpec (Scored scoredPick)
end Pick
local notation "ctl" => Label.local
/-- Actual parsed candidate ID paired with its closed source's own binary score word. -/
def scored (ids:List (List Bool)) (rows:List (List Bool×List Bool))
    (square cube fourth:List Bool) (entry:List Bool×List Bool) :Pick.Scored :=
  (entry.1,scoreWord ids entry.1 rows square cube fourth)
/-- Exact incumbent words after the chronological actual remaining scan. -/
def scanBest (ids:List (List Bool)) (rows:List (List Bool×List Bool))
    (square cube fourth:List Bool) (best:Pick.Scored) (entries:List (List Bool×List Bool)) :Pick.Scored :=
  (entries.map (scored ids rows square cube fourth)).foldl Pick.scoredPick best
/-- Own sum of actual candidate primitive/call caps and final false-pop/EOF-peek, never an original report clock. -/
def scanClock (ids:List (List Bool)) (pfx:List Bool) (rows:List (List Bool×List Bool))
    (square cube fourth:List Bool) :Pick.Scored→List (List Bool×List Bool)→Nat
  | _,[]=>2
  | best,entry::entries=>
    candidateBound ids entry.1 entry.2 pfx rows square cube fourth best.1 best.2+
      scanClock ids pfx rows square cube fourth (Pick.scoredPick best (scored ids rows square cube fourth entry)) entries
/-- The actual later-candidate loop retains complete source/environment banks and exact first-on-tie incumbent words. -/
theorem scan_run (ids:List (List Bool)) (pfx:List Bool) (rows:List (List Bool×List Bool))
    (square cube fourth catalogue owners factors todo:List Bool) (best:Pick.Scored) (entries:List (List Bool×List Bool)) :
    ∃t ≤ scanClock ids pfx rows square cube fourth best entries,
      Runs program t (ctl (.header false))
        (clean ids [] pfx (SemiprimeD1StackOwnerLookup.records rows []) square cube fourth catalogue owners factors todo
          (SemiprimeD1StackOwnerLookup.records entries []) (E.variableKey ids.length) best.1 best.2 [])
        (ctl .copyWinner)
        (clean ids [] pfx (SemiprimeD1StackOwnerLookup.records rows []) square cube fourth catalogue owners factors todo []
          (E.variableKey ids.length) (scanBest ids rows square cube fourth best entries).1
          (scanBest ids rows square cube fourth best entries).2 []) :=by
  induction entries generalizing best with
  | nil=>
    let before:=clean ids [] pfx (SemiprimeD1StackOwnerLookup.records rows []) square cube fourth catalogue owners factors todo
      [false] (E.variableKey ids.length) best.1 best.2 []
    have h0:=pop_run (.header false) (ctl .abort) (ctl .catalogueEOF) (ctl (.parseID false)) (aux .reader) before [false] rfl rfl
    change Runs program 1 _ _ _ (Function.update before (aux .reader) []) at h0
    rw [clean_reader] at h0
    have h1:=peek_run .catalogueEOF (ctl .copyWinner) (ctl .abort) (ctl .abort) (aux .reader)
      (clean ids [] pfx (SemiprimeD1StackOwnerLookup.records rows []) square cube fourth catalogue owners factors todo []
        (E.variableKey ids.length) best.1 best.2 []) [] rfl rfl
    exact ⟨2,Nat.le_refl _,join h0 h1⟩
  | cons entry entries ih=>
    obtain ⟨t0,ht0,h0⟩:=candidate_run false ids pfx rows square cube fourth catalogue owners factors todo
      best.1 best.2 entry.1 entry.2 entries (by intro h;cases h)
    obtain ⟨t1,ht1,h1⟩:=ih (Pick.scoredPick best (scored ids rows square cube fourth entry))
    refine ⟨t0+t1,Nat.add_le_add ht0 ht1,?_⟩
    exact join h0 h1
/-- Exact cached result of a full real first-plus-tail scan agrees with the old first-on-tie winner. -/
theorem scanBest_seed (ids:List (List Bool)) (rows:List (List Bool×List Bool))
    (square cube fourth:List Bool) (first:List Bool) (entries:List (List Bool×List Bool)) :
    (scanBest ids rows square cube fourth (first,scoreWord ids first rows square cube fourth) entries).1=
      SemiprimeD1StackSourceIncidenceSelectScore.winner rows square cube fourth ids first (entries.map Prod.fst) :=by
  have hmap:entries.map (scored ids rows square cube fourth)=
      (entries.map Prod.fst).map (fun id=>(id,scoreWord ids id rows square cube fourth)):=by
    rw [List.map_map]
    rfl
  rw [scanBest,hmap]
  exact SemiprimeD1StackSourceIncidenceSelectSpec.scored_choice
    (fun id=>scoreWord ids id rows square cube fourth) first (entries.map Prod.fst)
/-- Own actual cap for the complete scan, including the first candidate even when both its words are empty zero. -/
def catalogueClock (ids:List (List Bool)) (pfx:List Bool) (rows:List (List Bool×List Bool))
    (square cube fourth:List Bool) (first:List Bool×List Bool) (entries:List (List Bool×List Bool)) :Nat :=
  candidateBound ids first.1 first.2 pfx rows square cube fourth [] []+
    scanClock ids pfx rows square cube fourth (scored ids rows square cube fourth first) entries
/-- The complete real nonempty catalogue scan initializes once, compares every later candidate and preserves every tie. -/
theorem catalogue_run (ids:List (List Bool)) (pfx:List Bool) (rows:List (List Bool×List Bool))
    (square cube fourth catalogue owners factors todo:List Bool) (first:List Bool×List Bool)
    (entries:List (List Bool×List Bool)) :
    ∃t ≤ catalogueClock ids pfx rows square cube fourth first entries,
      Runs program t (ctl (.header true))
        (clean ids [] pfx (SemiprimeD1StackOwnerLookup.records rows []) square cube fourth catalogue owners factors todo
          (SemiprimeD1StackOwnerLookup.records (first::entries) []) (E.variableKey ids.length) [] [] [])
        (ctl .copyWinner)
        (clean ids [] pfx (SemiprimeD1StackOwnerLookup.records rows []) square cube fourth catalogue owners factors todo []
          (E.variableKey ids.length)
          (scanBest ids rows square cube fourth (scored ids rows square cube fourth first) entries).1
          (scanBest ids rows square cube fourth (scored ids rows square cube fourth first) entries).2 []) :=by
  obtain ⟨t0,ht0,h0⟩:=candidate_run true ids pfx rows square cube fourth catalogue owners factors todo [] []
    first.1 first.2 entries (by intro _;exact ⟨rfl,rfl⟩)
  obtain ⟨t1,ht1,h1⟩:=scan_run ids pfx rows square cube fourth catalogue owners factors todo
    (scored ids rows square cube fourth first) entries
  exact ⟨t0+t1,Nat.add_le_add ht0 ht1,join h0 h1⟩
end RiemannGaussian.SemiprimeD1StackSourceIncidenceSelectScan
