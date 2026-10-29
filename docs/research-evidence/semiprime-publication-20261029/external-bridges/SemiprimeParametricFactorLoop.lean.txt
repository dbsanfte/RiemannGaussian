/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg

Loop proofs adapted from OpenAI math, commit
7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a, Apache-2.0;
see vendor/openai-semiprime/LICENSE.OpenAI-Math. The actual callback is a
parameter here; the source's SAT-clause callback is never executed implicitly.
-/
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramFactorLoopContract

/-! # A generic physical factor producer for the published moment controller
The commands run the actual record, copy, setup and cleanup programs. Their
only abstract operation is an explicitly supplied finite callback command with
its execution contract. This module does not supply the macro-network callback.
-/
set_option autoImplicit false
set_option maxHeartbeats 1400000
noncomputable section
namespace RiemannGaussian.SemiprimeParametricFactorLoop
open OAI.Algorithms
open SubexponentialSAT SubexponentialSAT.SqrtLog
open BitProgram StructuredCalls MomentsProgram
open LeafProgram LeafProgram.FactorLoop
open SubexpLiftRing SubexpQuarticRing IdempotentApplyProgram.Bounds MomentsAssembly
attribute [local simp] Fin.coe_ofNat_eq_mod

/-- One actual ID callback. The accumulator is existential at every call;
only its relation to the preceding accumulator is fixed. -/
def CallbackContract (callback : Code) {n B d : ℕ} (u J : ℕ)
    (step : Raw n B d → ℕ → Raw n B d → Prop)
    (ready : (Fin 768 → List Bool) → Prop) (eligible : ℕ → Prop) (T C : ℕ) : Prop :=
  ∀ base, ready base → ∀ id seed tail regs, eligible id →
    Good Finset.univ u J seed → tail.length ≤ T →
    ∃ out, Good Finset.univ u J out ∧ step seed id out ∧
      ∃ k ≤ C, ∃ rr,
        Eval callback k
          (state base regs seed tail (Encoding.encodeNat id).reverse)
          (state base rr out tail []) ∧ rr 13=false ∧ rr 14=true ∧ rr 15=false


/-- Actual finite record iterator using the supplied worker. -/
def loop (callback : Code) : Code := RecordPrograms.iterate Factor.ports callback

/-- Copy the actual factor-ID stream and accumulator, run the worker loop, and
move its actual result to the assignment output port. -/
def command (callback : Code) : Code := .seq (Factor.copy 175 150)
  (.seq (Factor.copy 69 151) (.seq (loop callback) (Factor.move 151 67)))

/-- Preserve the controller frame, prepare the merged Boolean assignment and
weight, run actual factor workers, and restore the frame. -/
def assignment (callback : Code) : Code := .seq LeafAssignmentSetupProgram.beforeCommand
  (.seq (command callback) LeafAssignmentSetupProgram.afterCommand)

theorem inner_eval (callback : Code) {n B d : ℕ} (u J : ℕ)
    (step : Raw n B d → ℕ → Raw n B d → Prop)
    (ready : (Fin 768 → List Bool) → Prop) (eligible : ℕ → Prop) (T C : ℕ)
    (contract : CallbackContract callback u J step ready eligible T C)
    (base : Fin 768 → List Bool) (hb : ready base)
    (ids : List ℕ) (seed : Raw n B d) (regs : Fin 40 → Bool)
    (hg : Good Finset.univ u J seed) (hids : ∀ id ∈ ids, eligible id)
    (hlen : (ProgramEncoding.encodeRecords (records ids)).length ≤ T) :
    ∃ out, Good Finset.univ u J out ∧ RunRel step ids seed out ∧
      ∃ k ≤ 1+RecordPrograms.budget (fun _ => C) (records ids), ∃ rr,
        Eval (RecordPrograms.loop Factor.ports callback) k
          (RecordPrograms.afterTag Factor.ports (state base regs seed [] []) (records ids) [])
          (recordState base rr out false true false [] []) := by
  induction ids generalizing seed regs with
  | nil =>
    refine ⟨seed,hg,.nil seed,1,by simp [records,RecordPrograms.budget],regs,?_⟩
    apply Eval.while_false
    simp [RecordPrograms.afterTag,records,Factor.ports,RecordPrograms.state]
  | cons fid ids ih =>
    let bits := Encoding.encodeNat fid
    let tail := Encoding.encodeList id (records ids) ++ []
    let parsed := recordState base regs seed false true false tail bits.reverse
    obtain ⟨next,hnext,hstep,k,hk,rr,hcall,h13,h14,h15⟩ :=
      contract base hb fid seed tail parsed.regs (hids fid (by simp)) hg (by
        have hh : (ProgramEncoding.encodeRecords (records ids)).length ≤ T := by
          simp only [ProgramEncoding.encodeRecords,records,List.map_cons,Encoding.encodeList,
            List.length_cons,List.length_append] at hlen ⊢
          omega
        simpa [tail,ProgramEncoding.encodeRecords] using hh)
    have hcall' : Eval callback k parsed
        (recordState base rr next false true false tail []) := by
      rw [recordState_self base rr next false true false tail [] h13 h14 h15]
      have hp : parsed = state base parsed.regs seed tail bits.reverse :=
        recordState_eq base regs seed false true false tail bits.reverse
      rw [hp]
      exact hcall
    have hreader : Eval (RecordPrograms.reader Factor.ports) (6*bits.length+4)
        (RecordPrograms.afterTag Factor.ports (state base regs seed [] []) (records (fid::ids)) [])
        parsed := by
      simpa [parsed,recordState,records,RecordPrograms.afterTag,bits,tail] using
        RecordPrograms.reader_eval Factor.ports (state base regs seed [] []) bits tail [] true true false
    have hbranch : Eval
        (.ite Factor.ports.found (RecordPrograms.atom (.set Factor.ports.tag false))
          (RecordPrograms.atom (.pop Factor.ports.source Factor.ports.tag Factor.ports.present))) 2
        (recordState base rr next false true false tail [])
        (RecordPrograms.afterTag Factor.ports (state base rr next [] []) (records ids) []) := by
      apply Eval.ite_false (by simp [recordState])
      exact RecordPrograms.pop_list_eval Factor.ports (state base rr next [] []) (records ids) [] false true
    obtain ⟨out,hout,hrel,m,hm,rf,hrest⟩ := ih next rr hnext (fun id hi => hids id (by simp [hi])) (by
      simp only [ProgramEncoding.encodeRecords,records,List.map_cons,Encoding.encodeList,
        List.length_cons,List.length_append] at hlen ⊢
      omega)
    have hguard :
        (RecordPrograms.afterTag Factor.ports (state base regs seed [] []) (records (fid::ids)) []).regs
          Factor.ports.tag=true := by simp [RecordPrograms.afterTag,records]
    refine ⟨out,hout,.cons hstep hrel,(6*bits.length+4+(k+2))+m+1,?_,rf,?_⟩
    · simp only [records,List.map_cons,RecordPrograms.budget] at hm ⊢
      dsimp [bits]
      omega
    · exact Eval.while_true hguard (hreader.seq (hcall'.seq hbranch)) hrest

theorem loop_eval (callback : Code) {n B d : ℕ} (u J : ℕ)
    (step : Raw n B d → ℕ → Raw n B d → Prop)
    (ready : (Fin 768 → List Bool) → Prop) (eligible : ℕ → Prop) (T C : ℕ)
    (contract : CallbackContract callback u J step ready eligible T C)
    (base : Fin 768 → List Bool) (hb : ready base)
    (ids : List ℕ) (seed : Raw n B d) (regs : Fin 40 → Bool)
    (hg : Good Finset.univ u J seed) (hids : ∀ id ∈ ids, eligible id)
    (hlen : (ProgramEncoding.encodeRecords (records ids)).length ≤ T) :
    ∃ out, Good Finset.univ u J out ∧ RunRel step ids seed out ∧
      ∃ k ≤ loopBudget C ids, ∃ rr,
        Eval (loop callback) k
          (state base regs seed (ProgramEncoding.encodeRecords (records ids)) [])
          (state base rr out [] []) := by
  obtain ⟨out,hout,hr,k,hk,rr,he⟩ := inner_eval callback u J step ready eligible T C contract base hb ids seed regs hg hids hlen
  let initial := state base regs seed (ProgramEncoding.encodeRecords (records ids)) []
  have hstart : recordState base regs seed (regs 13) (regs 14) (regs 15)
      (Encoding.encodeList id (records ids) ++ []) [] = initial := by
    rw [recordState_self base regs seed _ _ _ _ _ rfl rfl rfl]
    simp [initial,ProgramEncoding.encodeRecords]
  have hset := RecordPrograms.set_found_eval Factor.ports (state base regs seed [] [])
    (regs 13) (regs 14) (regs 15) false (Encoding.encodeList id (records ids) ++ []) []
  have hpop := RecordPrograms.pop_list_eval Factor.ports (state base regs seed [] [])
    (records ids) [] (regs 13) (regs 14)
  have hrun := hset.seq (hpop.seq he)
  change Eval (loop callback) (1+(1+k))
    (recordState base regs seed (regs 13) (regs 14) (regs 15) _ [])
    (recordState base rr out false true false [] []) at hrun
  rw [hstart,recordState_eq] at hrun
  exact ⟨out,hout,hr,1+(1+k),by dsimp [loopBudget]; omega,_,hrun⟩

theorem command_eval (callback : Code) {n B d : ℕ} (u J : ℕ)
    (step : Raw n B d → ℕ → Raw n B d → Prop)
    (ready : (Fin 768 → List Bool) → Prop) (eligible : ℕ → Prop) (T C : ℕ)
    (contract : CallbackContract callback u J step ready eligible T C)
    (a : Factor.Data) (ha : ready a.stacks) (ids : List ℕ) (one : Raw n B d)
    (hg : Good Finset.univ u J one) (hids : ∀ id ∈ ids, eligible id)
    (hlen : (ProgramEncoding.encodeRecords (records ids)).length ≤ T)
    (h175 : a.stacks 175=ProgramEncoding.encodeRecords (records ids))
    (h69 : a.stacks 69=Product.bytes one)
    (h149 : a.stacks 149=[]) (h150 : a.stacks 150=[]) (h151 : a.stacks 151=[])
    (h67 : a.stacks 67=[]) (h159 : a.stacks 159=[]) :
    ∃ out, Good Finset.univ u J out ∧ RunRel step ids one out ∧
      ∃ k ≤ commandBudget n B d u J C ids, ∃ rr,
        Eval (command callback) k a ⟨rr,Function.update a.stacks 67 (Product.bytes out)⟩ := by
  let a1 := SubexpScanPrimitives.afterCopy a 175 150 0 1
  let a2 := SubexpScanPrimitives.afterCopy a1 69 151 0 1
  have h1 : Eval (Factor.copy 175 150) (7*(a.stacks 175).length+5) a a1 :=
    SubexpScanPrimitives.copy_eval a 175 150 159 0 1 (by decide) (by decide) (by decide) (by decide) h159
  have h2 : Eval (Factor.copy 69 151) (7*(a1.stacks 69).length+5) a1 a2 :=
    SubexpScanPrimitives.copy_eval a1 69 151 159 0 1 (by decide) (by decide) (by decide) (by decide)
      (by simpa [a1,SubexpScanPrimitives.afterCopy,StackRoutines.copyStacks] using h159)
  have hinput : a2=state a.stacks a2.regs one (ProgramEncoding.encodeRecords (records ids)) [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      by_cases h1 : i=149 <;> by_cases h2 : i=150 <;> by_cases h3 : i=151 <;>
        simp_all [a2,a1,SubexpScanPrimitives.afterCopy,StackRoutines.copyStacks]
  obtain ⟨out,ho,hr,nl,hl,rr,he⟩ := loop_eval callback u J step ready eligible T C contract a.stacks ha ids one
    a2.regs hg hids hlen
  rw [← hinput] at he
  let b := state a.stacks rr out [] []
  have h3 := Factor.move_eval b 151 67 (by decide) (by decide) (by decide)
    (by simpa [b,state] using h159)
  have hout : Factor.moved b 151 67 =
      ⟨(Factor.moved b 151 67).regs,Function.update a.stacks 67 (Product.bytes out)⟩ := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      by_cases h1 : i=149 <;> by_cases h2 : i=150 <;> by_cases h3 : i=151 <;>
        by_cases h4 : i=67 <;>
        simp [b,state,h1,h2,h3,h4,h149,h150,h151,h67]
  rw [hout] at h3
  have honeBound := bytes_le_capacity Finset.univ u J one hg
  have houtBound := bytes_le_capacity Finset.univ u J out ho
  refine ⟨out,ho,hr,(7*(a.stacks 175).length+5)+((7*(a1.stacks 69).length+5)+
    (nl+(9*(b.stacks 151).length+8))),?_,_,h1.seq (h2.seq (he.seq h3))⟩
  dsimp [commandBudget,byteBound]
  simp only [h175] at *
  have h69' : a1.stacks 69=Product.bytes one := by
    simpa [a1,SubexpScanPrimitives.afterCopy,StackRoutines.copyStacks] using h69
  simp only [h69']
  have hb151 : b.stacks 151=Product.bytes out := by simp [b,state]
  rw [hb151]
  omega

theorem assignment_eval (callback : Code) {n B d : ℕ} (u J : ℕ)
    (step : Raw n B d → ℕ → Raw n B d → Prop)
    (ready : (Fin 768 → List Bool) → Prop) (eligible : ℕ → Prop) (T C : ℕ)
    (contract : CallbackContract callback u J step ready eligible T C)
    (a : Factor.Data) (ha : LeafAssignmentSetupProgram.BeforeReady a)
    (hr : ready (LeafAssignmentSetupProgram.prepared a (fun _ => false) (fun _ => false)).stacks)
    (ids : List ℕ) (one : Raw n B d) (hg : Good Finset.univ u J one)
    (hids : ∀ id ∈ ids, eligible id) (hlen : (ProgramEncoding.encodeRecords (records ids)).length ≤ T)
    (h175 : a.stacks 175=ProgramEncoding.encodeRecords (records ids)) (h69 : a.stacks 69=Product.bytes one)
    (h41 : a.stacks 41=[]) (h44 : a.stacks 44=[]) (h67 : a.stacks 67=[])
    (h149 : a.stacks 149=[]) (h150 : a.stacks 150=[]) (h151 : a.stacks 151=[])
    (h159 : a.stacks 159=[]) (N W : ℕ)
    (h40 : (a.stacks 40).length ≤ byteBound n B d u J)
    (h42 : (a.stacks 42).length ≤ byteBound n B d u J)
    (hN : (a.stacks 174).length ≤ N) (hW : (LeafAssignmentSetupProgram.weight a).length ≤ W) :
    ∃ out, Good Finset.univ u J out ∧ RunRel step ids one out ∧
      ∃ k ≤ LeafProgram.FactorLoop.assignmentBudget n B d u J C ids N W, ∃ rr,
        Eval (assignment callback) k a ⟨rr,assignmentTapes a (Product.bytes out)⟩ := by
  obtain ⟨rm,rw,hbefore⟩ := LeafAssignmentSetupProgram.before_eval a ha
  let prepared := LeafAssignmentSetupProgram.prepared a rm rw
  have hready : ready prepared.stacks := by
    simpa only [prepared,LeafAssignmentSetupProgram.prepared_stacks] using hr
  obtain ⟨out,ho,hrel,k,hk,rr,hcommand⟩ := command_eval callback u J step ready eligible T C contract
    prepared hready ids one hg hids hlen
    (by simpa [prepared,LeafAssignmentSetupProgram.prepared_stacks] using h175)
    (by simpa [prepared,LeafAssignmentSetupProgram.prepared_stacks] using h69)
    (by simpa [prepared,LeafAssignmentSetupProgram.prepared_stacks] using h149)
    (by simpa [prepared,LeafAssignmentSetupProgram.prepared_stacks] using h150)
    (by simpa [prepared,LeafAssignmentSetupProgram.prepared_stacks] using h151)
    (by simpa [prepared,LeafAssignmentSetupProgram.prepared_stacks] using h67)
    (by simpa [prepared,LeafAssignmentSetupProgram.prepared_stacks] using h159)
  let engine := afterEngine a rm rw rr (Product.bytes out)
  have he41 : engine.stacks 41=[] := by simp [engine,afterEngine,LeafAssignmentSetupProgram.prepared_stacks,h41]
  have he44 : engine.stacks 44=[] := by simp [engine,afterEngine,LeafAssignmentSetupProgram.prepared_stacks,h44]
  have he359 : engine.stacks 359=[] := by
    simpa [engine,afterEngine,LeafAssignmentSetupProgram.prepared_stacks] using ha.1 359 (by simp)
  have hafter := LeafAssignmentSetupProgram.after_eval engine he41 he44 he359
  have hb := LeafAssignmentSetupProgram.beforeCost_le a (byteBound n B d u J) N W h40 h42 hN hW
  have hoB := bytes_le_capacity Finset.univ u J out ho
  have hc := LeafAssignmentSetupProgram.afterCost_le engine (byteBound n B d u J) N W
    (by simp [engine,afterEngine,LeafAssignmentSetupProgram.prepared_stacks])
    (by simp [engine,afterEngine,LeafAssignmentSetupProgram.prepared_stacks])
    (by simpa [engine,afterEngine,byteBound] using hoB)
    (by simpa [engine,afterEngine,LeafAssignmentSetupProgram.prepared_stacks] using h40)
    (by simpa [engine,afterEngine,LeafAssignmentSetupProgram.prepared_stacks] using h42)
    (by simpa [engine,afterEngine,LeafAssignmentSetupProgram.prepared_stacks] using hW)
    (by simpa [engine,afterEngine,LeafAssignmentSetupProgram.prepared_stacks] using hN)
    (by simpa [engine,afterEngine,LeafAssignmentSetupProgram.prepared_stacks] using hN)
  have hout : LeafAssignmentSetupProgram.finished engine = ⟨(LeafAssignmentSetupProgram.finished engine).regs,assignmentTapes a (Product.bytes out)⟩ := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · exact finished_afterEngine a rm rw rr (Product.bytes out) ha h67
  rw [hout] at hafter
  refine ⟨out,ho,hrel,LeafAssignmentSetupProgram.beforeCost a+(k+LeafAssignmentSetupProgram.afterCost engine),?_,
    (LeafAssignmentSetupProgram.finished engine).regs,?_⟩
  · dsimp [LeafProgram.FactorLoop.assignmentBudget]; omega
  · exact hbefore.seq (hcommand.seq hafter)

theorem assignment_contract (callback : Code) (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {n d : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (degree width : List Bool) (u J T C : ℕ)
    (one : Raw n (baseWidth p t) d) (hone : Good Finset.univ u J one)
    (step : AssignmentContext → List Bool → Raw n (baseWidth p t) d → ℕ → Raw n (baseWidth p t) d → Prop)
    (ready : AssignmentContext → List Bool → (Fin 768 → List Bool) → Prop)
    (eligible : AssignmentContext → List Bool → ℕ → Prop)
    (ids : AssignmentContext → List Bool → List ℕ)
    (weight : AssignmentContext → List Bool → RingProgram.Code (Word (baseWidth p t)) d)
    (validFrame : (Fin 768 → List Bool) → Prop)
    (callbacks : ∀ c x, CallbackContract callback u J (step c x) (ready c x) (eligible c x) T C)
    (inputs : ∀ c x (left seed : Raw n (baseWidth p t) d) high regs,
      EntryInvariant Finset.univ u J left → EntryInvariant Finset.univ u J seed →
      validFrame high → c.Matches high → high 174=x →
      AssignmentReady u J (ready c x) (eligible c x) T (ids c x) one
        (machine regs (Product.working (Product.environment p t M cache table degree width u J) left [] seed) high))
    (weights : ∀ c x (left seed : Raw n (baseWidth p t) d) high regs,
      validFrame high → c.Matches high → high 174=x →
      LeafAssignmentSetupProgram.weight
        (machine regs (Product.working (Product.environment p t M cache table degree width u J) left [] seed) high)=
          RingProgram.flat (weight c x)) :
    MomentsAssembly.Relational.AssignmentContract p t M cache table u J
      (assignmentRelation step ids one weight) (assignment callback) degree width Finset.univ validFrame
      (uniformAssignmentBudget n (baseWidth p t) d u J T C) := by
  intro c x left seed high regs hl hs hv hc hx
  dsimp only
  let e := Product.environment p t M cache table degree width u J
  let a := machine regs (Product.working e left [] seed) high
  have hi := inputs c x left seed high regs hl hs hv hc hx
  have hw := weights c x left seed high regs hv hc hx
  have hbl := bytes_le_capacity Finset.univ u J left hl
  have hbs := bytes_le_capacity Finset.univ u J seed hs
  obtain ⟨out,ho,hr,k,hk,rr,he⟩ := assignment_eval callback u J (step c x) (ready c x) (eligible c x) T C
    (callbacks c x) a hi.setup hi.engine (ids c x) one hone hi.ids_good hi.ids_length hi.ids_tape hi.one_tape
    (hi.empty 41 (by simp)) (hi.empty 44 (by simp)) (hi.empty 67 (by simp))
    (hi.empty 149 (by simp)) (hi.empty 150 (by simp)) (hi.empty 151 (by simp)) (hi.empty 159 (by simp))
    n (d*baseWidth p t)
    (by simpa [a,machine,Product.working,Product.tapes,byteBound] using hbl)
    (by simpa [a,machine,Product.working,Product.tapes,byteBound] using hbs)
    hi.assignment_length (by rw [hw]; simp)
  refine ⟨(weight c x,out),⟨rfl,hr⟩,ho,k,hk.trans (assignmentBudget_le n (baseWidth p t) d u J T C _ hi.ids_length),rr,?_⟩
  rw [assignmentTapes_machine e left seed out (weight c x) high regs rr hw] at he
  exact he

end RiemannGaussian.SemiprimeParametricFactorLoop
