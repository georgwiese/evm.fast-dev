import InitECandidate.Solver.MutableTable.HashAny32Program
import InitECandidate.Solver.Input.ClockCostCurrentConditional
import InitECandidate.Solver.Input.LocalEffectsLoop

namespace InitECandidate.Solver.MutableTable.HashAny32
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem side_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (aligned : Bool)
    (length : source.locals.lookup (ofString "key_len")=some (.val (.word 32#64))) :
    evaluateHOLFiniteState source (side aligned)=evaluateHOLFiniteState source (thirtyTwo aligned) := by
  have test20 : eval source (sizeTest 20#64)=some (.val (.word 0#64)) := by
    simp [eval,sizeTest,localVar,evalHOLExact,toExact,length,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  have test32 : eval source (sizeTest 32#64)=some (.val (.word 1#64)) := by
    simp [eval,sizeTest,localVar,evalHOLExact,toExact,length,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  simp only [eval] at test20 test32
  have skip20 : evaluateHOLFiniteState source (.ite (sizeTest 20#64) (twenty aligned) .skip)=(none,source) := by
    rw [evaluateHOLFiniteState_ite,test20]
    simp [evaluateHOLFiniteState_skip]
  have take32 : evaluateHOLFiniteState source (.ite (sizeTest 32#64) (thirtyTwo aligned) .skip)=evaluateHOLFiniteState source (thirtyTwo aligned) := by
    rw [evaluateHOLFiniteState_ite,test32]
    rfl
  rw [side_shape,evaluateHOLFiniteState_seq_line780,skip20]
  change evaluateHOLFiniteState source (.seq (.ite (sizeTest 32#64) (thirtyTwo aligned) .skip) (afterThirtyTwo aligned))=_
  rw [evaluateHOLFiniteState_seq_line780,take32]
  have terminal:=(core_summary aligned source.code).2 source
  generalize computed : evaluateHOLFiniteState source (thirtyTwo aligned)=output at terminal ⊢
  obtain ⟨answer,target⟩ := output
  cases answer with
  | none => exact (terminal rfl).elim
  | some answer => rfl

theorem front_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (length : source.locals.lookup (ofString "key_len")=some (.val (.word 32#64))) :
    source.clock-(evaluateHOLFiniteState source HashByteRuntime.front).2.clock≤0 := by
  have priced (aligned : Bool) : source.clock-(evaluateHOLFiniteState source (side aligned)).2.clock≤0 := by
    rw [side_execute source aligned length,(core_summary aligned source.code).1 source rfl]
    omega
  rw [front_shape]
  exact Input.ClockCost.conditional_current source alignmentTest (side true) (side false) 0 0 (priced true) (priced false)

theorem front_ne_none (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (length : source.locals.lookup (ofString "key_len")=some (.val (.word 32#64))) :
    (evaluateHOLFiniteState source HashByteRuntime.front).1≠none := by
  have terminal (aligned : Bool) : (evaluateHOLFiniteState source (side aligned)).1≠none := by
    rw [side_execute source aligned length]
    exact (core_summary aligned source.code).2 source
  rw [front_shape,evaluateHOLFiniteState_ite]
  generalize observed : @evalHOLExact 64 Guest.HostMemory _ source.toExact
    (fun address=>Classical.propDecidable (source.memaddrs address)) alignmentTest=value
  cases value with
  | none => simp
  | some value =>
    cases value with
    | rStruct fields => simp
    | nStruct name fields => simp
    | val payload =>
      cases payload with
      | word word =>
        simp only
        by_cases zero : word=0
        · rw [if_pos zero]; exact terminal false
        · rw [if_neg zero]; exact terminal true

theorem after_locals_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (length : source.locals.lookup (ofString "key_len")=some (.val (.word 32#64))) :
    evaluateHOLFiniteState source Hash.afterLocals=evaluateHOLFiniteState source HashByteRuntime.front := by
  rw [HashByteRuntime.after_locals_shape,evaluateHOLFiniteState_seq_line780]
  have terminal:=front_ne_none source length
  generalize computed : evaluateHOLFiniteState source HashByteRuntime.front=output at terminal ⊢
  obtain ⟨answer,target⟩ := output
  cases answer with
  | none => exact (terminal rfl).elim
  | some answer => rfl

/-- A literal32-byte original table hash spends no body source tick on
any outcome, including failed operand reads. No query-byte view is assumed. -/
theorem body_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (length : source.locals.lookup (ofString "key_len")=some (.val (.word 32#64))) :
    source.clock-(evaluateHOLFiniteState source Hash.body).2.clock≤0 := by
  let hs:=QueryBranch.bind source "h" 14695981039346656037#64
  let ws:=QueryBranch.bind hs "w" 0#64
  have wsLength : ws.locals.lookup (ofString "key_len")=some (.val (.word 32#64)) :=
    (bind_lookup_other hs "w" "key_len" 0#64 (by decide)).trans ((bind_lookup_other source "h" "key_len" _ (by decide)).trans length)
  have inner : ws.clock-(evaluateHOLFiniteState ws Hash.afterLocals).2.clock≤0 := by
    rw [after_locals_execute ws wsLength]
    exact front_cost ws wsLength
  have wPrice:=Input.ClockCost.declared_current hs "w" (.const 0#64) 0#64 Hash.afterLocals 0 rfl inner
  rw [Hash.body_shape]
  exact Input.ClockCost.declared_current source "h" (.const 14695981039346656037#64) 14695981039346656037#64 _ 0 rfl wPrice

set_option maxRecDepth 100000 in
theorem readonly (code) : Input.LocalEffects.Preserves code Hash.body := by
  simp only [Hash.body,Guest.guestFn_htab_hash,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil]
  repeat first
    | apply Input.LocalEffects.declared
    | apply Input.LocalEffects.sequence
    | apply Input.LocalEffects.conditional
    | apply Input.LocalEffects.loop
    | exact Input.LocalEffects.assign code _ _
    | exact Input.LocalEffects.returned code _
    | exact Input.LocalEffects.skip code

end InitECandidate.Solver.MutableTable.HashAny32

#print axioms InitECandidate.Solver.MutableTable.HashAny32.side_execute
#print axioms InitECandidate.Solver.MutableTable.HashAny32.front_cost
#print axioms InitECandidate.Solver.MutableTable.HashAny32.front_ne_none
#print axioms InitECandidate.Solver.MutableTable.HashAny32.after_locals_execute
#print axioms InitECandidate.Solver.MutableTable.HashAny32.body_cost
#print axioms InitECandidate.Solver.MutableTable.HashAny32.readonly
