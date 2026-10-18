import InitECandidate.Solver.MutableTable.KeysLoop

namespace InitECandidate.Solver.MutableTable.Keys
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix NaturalLayout
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix.ProgramPrefix

/-- Actual header/counter setup after allocating out, complete signed loop
and tuple return, preserving every source-table pool and outside word. -/
theorem after_output_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (plan : Plan) (valid : Valid kind plan)
    (domain : source.memaddrs = InitE.ordinaryDomain) (start : Nat) (slots : List Nat) (occupied : MemoryModel.Occupied source kind plan slots)
    (header : MemoryModel.Header source.memory kind plan (BitVec.ofNat 64 slots.length))
    (outValid : MemoryRegion.Valid (outputRegion kind start slots.length)) (earlier : ∀ pool, plan.base pool + size kind plan pool ≤ start)
    (tableLocal : source.locals.lookup (ofString "t") = some (.val (.word (cell plan .header 0))))
    (strideLocal : source.locals.lookup (ofString "stride") = some (.val (.word (BitVec.ofNat 64 (stride kind)))))
    (countLocal : source.locals.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 slots.length))))
    (outLocal : source.locals.lookup (ofString "out") = some (.val (.word (BitVec.ofNat 64 start))))
    (copyCode : source.code.lookup (ofString "memcpy") = some (CopyGeneral.formals, Copy32.body, .one))
    (enough : (rowPrice kind + 1) * slots.length ≤ source.clock) :
    ∃ paid memory target, paid ≤ (rowPrice kind + 1) * slots.length ∧
      evaluateHOLFiniteState source afterOutput = (some (.returned (pair (BitVec.ofNat 64 start) (BitVec.ofNat 64 slots.length))), target) ∧
      emptyLocalsHOLFinite target = emptyLocalsHOLFinite {source with memory := memory, clock := source.clock - paid} ∧
      MemoryModel.PoolFrame source.memory memory kind plan ∧ MemoryModel.Occupied target kind plan slots ∧
      (∀ query : BitVec 64, query.toNat < start ∨ start + stride kind * slots.length + 8 ≤ query.toNat → memory query = source.memory query) := by
  let keyed := bind source "keys" (cell plan .keys 0)
  let ordered := bind keyed "order" (cell plan .order 0)
  let indexed := bind ordered "i" 0#64
  let ready := bind indexed "k" 0#64
  have keysRead := MemoryModel.Header.read source kind plan valid domain _ header tableLocal 32 (by decide) (by decide) (cell plan .keys 0) (by simp [MemoryModel.headerEntries])
  have keyedT : keyed.locals.lookup (ofString "t") = some (.val (.word (cell plan .header 0))) := (bind_lookup_other _ "keys" "t" _ (by decide)).trans tableLocal
  have orderRead := MemoryModel.Header.read keyed kind plan valid domain _ header keyedT 56 (by decide) (by decide) (cell plan .order 0) (by simp [MemoryModel.headerEntries])
  have setup : ∃ restoreStack, Executes source afterOutputActions ready restoreStack :=
    ⟨_, .declare _ keysRead (.declare _ orderRead (.declare 0#64 rfl (.declare 0#64 rfl (.done _))))⟩
  have inherited (name : String) (word : BitVec 64) (awayK : ofString "k" ≠ ofString name) (awayI : ofString "i" ≠ ofString name)
      (awayOrder : ofString "order" ≠ ofString name) (awayKeys : ofString "keys" ≠ ofString name)
      (stored : source.locals.lookup (ofString name) = some (.val (.word word))) : ready.locals.lookup (ofString name) = some (.val (.word word)) :=
    (bind_lookup_other _ "k" name _ awayK).trans ((bind_lookup_other _ "i" name _ awayI).trans ((bind_lookup_other _ "order" name _ awayOrder).trans ((bind_lookup_other _ "keys" name _ awayKeys).trans stored)))
  have locals : Locals ready kind plan start slots.length 0 :=
    ⟨inherited "stride" _ (by decide) (by decide) (by decide) (by decide) strideLocal,
      (bind_lookup_other _ "k" "keys" _ (by decide)).trans ((bind_lookup_other _ "i" "keys" _ (by decide)).trans ((bind_lookup_other _ "order" "keys" _ (by decide)).trans (bind_lookup_same _ _ _))),
      (bind_lookup_other _ "k" "order" _ (by decide)).trans ((bind_lookup_other _ "i" "order" _ (by decide)).trans (bind_lookup_same _ _ _)),
      inherited "out" _ (by decide) (by decide) (by decide) (by decide) outLocal,
      inherited "n" _ (by decide) (by decide) (by decide) (by decide) countLocal,
      (bind_lookup_other _ "k" "i" _ (by decide)).trans (bind_lookup_same _ _ _), bind_lookup_same _ _ _⟩
  have readyModel := MemoryModel.Occupied.of_fields source ready kind plan slots occupied rfl rfl rfl
  obtain ⟨paid, memory, post, bounded, actual, frame, finalLocals, poolFrame, finalModel, outsideFrame⟩ :=
    loop_execute kind plan valid start slots outValid earlier slots.length ready domain 0 (by omega) readyModel locals copyCode enough
  have returned : evaluateHOLFiniteState post afterLoop = (some (.returned (pair (BitVec.ofNat 64 start) (BitVec.ofNat 64 slots.length))), emptyLocalsHOLFinite post) := by
    simp [afterLoop, evaluateHOLFiniteState_return, localVar, evalHOLExact, evalListHOLExact, toExact, finalLocals.out, finalLocals.count, pair, shapeOfHOLExact, sizeOfShapeWithContextHOL]
  have clockEq := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.clock) frame
  change post.clock = source.clock - paid at clockEq
  have whole : evaluateHOLFiniteState ready (.seq loop afterLoop) = (some (.returned (pair (BitVec.ofNat 64 start) (BitVec.ofNat 64 slots.length))), emptyLocalsHOLFinite post) := by
    rw [StateSteps.next_sequence ready post loop afterLoop actual (by change post.clock ≤ source.clock; omega), returned]
  obtain ⟨restoreStack, setupRun⟩ := setup
  have prefixed := ProgramPrefix.execute setupRun (.seq loop afterLoop)
  rw [whole] at prefixed
  let target := restoreStack (emptyLocalsHOLFinite post)
  have restoredFrame := ProgramPrefix.restoration_frame setupRun (emptyLocalsHOLFinite post)
  refine ⟨paid, memory, target, bounded, prefixed, ?_, poolFrame, ?_, outsideFrame⟩
  · exact restoredFrame.trans frame
  · have memoryEq := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.memory) restoredFrame
    have domainEq := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.memaddrs) restoredFrame
    have endianEq := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.be) restoredFrame
    exact MemoryModel.Occupied.of_fields post target kind plan slots finalModel memoryEq.symm domainEq.symm endianEq.symm

end InitECandidate.Solver.MutableTable.Keys

#print axioms InitECandidate.Solver.MutableTable.Keys.after_output_execute
