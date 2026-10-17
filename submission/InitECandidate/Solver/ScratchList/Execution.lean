import InitECandidate.Solver.Arenas.Prefix
import InitECandidate.Solver.Arenas.Region
import InitECandidate.Solver.PanFieldStores

namespace InitECandidate.Solver.ScratchList
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open WitnessRadix.ProgramPrefix (Action)

def amountExpression : ExpHOL 64 := .panop .mul [localVar "esz", localVar "cap"]
def actions : List Action := [.allocate "l" (.const 24#64), .allocate "p" amountExpression]
def fields (pointer capacity : BitVec 64) : List FieldStores.Field :=
  [⟨0, .saved "p" pointer⟩, ⟨8, .literal 0#64⟩, ⟨16, .saved "cap" capacity⟩]
def tail : ProgHOL 64 := FieldStores.program "l" "unused" (fields 0#64 0#64) (.return (localVar "l"))
def body : ProgHOL 64 := match Guest.guestFn_lst_new_scratch with | .function fn => progToHOL fn.body | _ => .skip

theorem body_shape : body = Arenas.Prefix.program .down actions tail := by
  simp only [body, Guest.guestFn_lst_new_scratch, progToHOL, expToHOL, shapeToHOL,
    List.map_cons, List.map_nil, Option.map_none, actions, tail, fields, FieldStores.program,
    FieldStores.address, FieldStores.Value.expression, Arenas.Prefix.program, Arenas.functionName,
    amountExpression, localVar, addConst]

def header (scratch : BitVec 64) : BitVec 64 := Arenas.rounded .down scratch 24#64
def buffer (scratch amount : BitVec 64) : BitVec 64 := Arenas.rounded .down (header scratch) amount
noncomputable def firstState (source : PanSemStateFiniteExact 64 Guest.HostMemory) (scratch : BitVec 64) :=
  WitnessRadix.QueryBranch.bind (Arenas.post {source with clock := source.clock - 1} .down scratch 24#64) "l" (header scratch)
noncomputable def entered (source : PanSemStateFiniteExact 64 Guest.HostMemory) (scratch amount : BitVec 64) :=
  WitnessRadix.QueryBranch.bind (Arenas.post {firstState source scratch with clock := (firstState source scratch).clock - 1}
    .down (header scratch) amount) "p" (buffer scratch amount)

/-- Full original scratch-list constructor, with both allocator executions,
all three real header stores and return. No backing bytes are read while the
list is empty. The exact body source-clock cost is two. -/
theorem execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (scratch memory elementSize capacity : BitVec 64)
    (code : source.code.lookup (ofString "scratch_alloc") = some (Arenas.formals, Arenas.body .down, .one))
    (scratchGlobal : source.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (memoryGlobal : source.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word memory)))
    (sizeLocal : source.locals.lookup (ofString "esz") = some (.val (.word elementSize)))
    (capLocal : source.locals.lookup (ofString "cap") = some (.val (.word capacity)))
    (aligned : memory.toNat % 8 = 0)
    (headerRoom : memory.toNat + 24 ≤ scratch.toNat)
    (bufferRoom : memory.toNat + (elementSize * capacity).toNat ≤ (header scratch).toNat)
    (mapped : ∀ offset ∈ ([0, 8, 16] : List Nat), source.memaddrs (header scratch + BitVec.ofNat 64 offset))
    (enough : 2 ≤ source.clock) :
    ∃ target : PanSemStateFiniteExact 64 Guest.HostMemory,
      evaluateHOLFiniteState source body = (some (.returned (.val (.word (header scratch)))), target) ∧
      target.memory = WitnessRadix.WordWrites.write source.memory (FieldStores.writes (header scratch)
        (fields (buffer scratch (elementSize * capacity)) capacity)) ∧
      emptyLocalsHOLFinite target = emptyLocalsHOLFinite
        {Arenas.post source .down (header scratch) (elementSize * capacity) with
          memory := target.memory
          clock := source.clock - 2} ∧
      ∀ query : BitVec 64, Arenas.Outside memory scratch query → target.memory query = source.memory query := by
  classical
  let amount := elementSize * capacity
  let first := firstState source scratch
  let ready := entered source scratch amount
  have headerPointer : first.globals.lookup (ofString "scratch_ptr") = some (.val (.word (header scratch))) := by
    simp [first, firstState, Arenas.post, Arenas.pointerName, WitnessRadix.QueryBranch.bind,
      setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, header]
  have memoryKept : first.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word memory)) := by
    simpa [first, firstState, Arenas.post, Arenas.pointerName, WitnessRadix.QueryBranch.bind,
      setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, ofString] using memoryGlobal
  have sizeFirst : first.locals.lookup (ofString "esz") = some (.val (.word elementSize)) :=
    (bind_lookup_other _ "l" "esz" _ (by decide)).trans sizeLocal
  have capFirst : first.locals.lookup (ofString "cap") = some (.val (.word capacity)) :=
    (bind_lookup_other _ "l" "cap" _ (by decide)).trans capLocal
  have amountRead : eval first amountExpression = some (.val (.word amount)) := by
    simp [eval, amountExpression, amount, localVar, evalHOLExact, evalListHOLExact, toExact,
      sizeFirst, capFirst, valueIsWord, valueWord, panOpHOL]
  have secondSetup : Arenas.Prefix.Executes .down first [.allocate "p" amountExpression] ready
      (fun target => restore first "p" target) :=
    .allocate (header scratch) memory amount amountRead code headerPointer memoryKept aligned bufferRoom
      (by change 1 ≤ source.clock - 1; omega) (.done _)
  have setup : Arenas.Prefix.Executes .down source actions ready
      (fun target => restore source "l" (restore first "p" target)) :=
    .allocate scratch memory 24#64 rfl code scratchGlobal memoryGlobal aligned headerRoom (by omega) secondSetup
  have listLocal : ready.locals.lookup (ofString "l") = some (.val (.word (header scratch))) :=
    (bind_lookup_other _ "p" "l" _ (by decide)).trans (bind_lookup_same _ _ _)
  have bufferLocal : ready.locals.lookup (ofString "p") = some (.val (.word (buffer scratch amount))) := bind_lookup_same _ _ _
  have capReady : ready.locals.lookup (ofString "cap") = some (.val (.word capacity)) :=
    (bind_lookup_other _ "p" "cap" _ (by decide)).trans capFirst
  have reads : ∀ field ∈ fields (buffer scratch amount) capacity, field.value.Ready ready "unused" 0#64 := by
    intro field member
    simp only [fields, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact bufferLocal
    · trivial
    · exact capReady
  have fieldsMapped : ∀ field ∈ fields (buffer scratch amount) capacity,
      ready.memaddrs (header scratch + BitVec.ofNat 64 field.offset) := by
    intro field member
    apply mapped
    simp only [fields, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> simp
  have separated : ∀ reader ∈ fields (buffer scratch amount) capacity,
      ∀ writer ∈ fields (buffer scratch amount) capacity,
      reader.value.Avoid 0#64 (header scratch + BitVec.ofNat 64 writer.offset) := by
    intro reader readerIn writer writerIn
    simp only [fields, List.mem_cons, List.not_mem_nil, or_false] at readerIn
    rcases readerIn with rfl | rfl | rfl <;> trivial
  have storesRun := FieldStores.execute ready "l" "unused" (header scratch) 0#64
    (fields (buffer scratch amount) capacity) listLocal reads fieldsMapped separated (.return (localVar "l"))
  let stored := {ready with memory := (WitnessRadix.WordWrites.write source.memory
    (FieldStores.writes (header scratch) (fields (buffer scratch amount) capacity)))}
  have returned : evaluateHOLFiniteState stored (.return (localVar "l")) =
      (some (.returned (.val (.word (header scratch)))), emptyLocalsHOLFinite stored) := by
    have saved : stored.locals.lookup (ofString "l") = some (.val (.word (header scratch))) := listLocal
    simp [evaluateHOLFiniteState_return, localVar, evalHOLExact, toExact, saved, shapeOfHOLExact, sizeOfShapeWithContextHOL]
  change evaluateHOLFiniteState ready tail = evaluateHOLFiniteState stored (.return (localVar "l")) at storesRun
  rw [returned] at storesRun
  have run := Arenas.Prefix.execute setup tail
  rw [storesRun] at run
  let target := restore source "l" (restore first "p" (emptyLocalsHOLFinite stored))
  refine ⟨target, ?_, rfl, ?_, ?_⟩
  · rw [body_shape]
    exact run
  · have clocks : source.clock - 1 - 1 = source.clock - 2 := by omega
    have overwrite : (source.globals.update (ofString "scratch_ptr", .val (.word (header scratch)))).update
        (ofString "scratch_ptr", .val (.word (buffer scratch amount))) =
        source.globals.update (ofString "scratch_ptr", .val (.word (buffer scratch amount))) := by
      apply HolFiniteMapExact.ext
      funext query
      by_cases same : ofString "scratch_ptr" = query <;> simp [HolFiniteMapExact.update, FUPDATE, same]
    change emptyLocalsHOLFinite {source with
      globals := (source.globals.update (ofString "scratch_ptr", .val (.word (header scratch)))).update
        (ofString "scratch_ptr", .val (.word (buffer scratch amount)))
      memory := target.memory
      clock := source.clock - 1 - 1} = emptyLocalsHOLFinite {source with
      globals := source.globals.update (ofString "scratch_ptr", .val (.word (buffer scratch amount)))
      memory := target.memory
      clock := source.clock - 2}
    rw [overwrite, clocks]
  · intro query outsideArena
    change WitnessRadix.WordWrites.write source.memory (FieldStores.writes (header scratch)
      (fields (buffer scratch amount) capacity)) query = _
    apply WitnessRadix.WordWrites.write_away
    have geometry := Arenas.downward_guards scratch memory 24#64 aligned headerRoom
    have endBound : (header scratch).toNat + 24 ≤ scratch.toNat := geometry.2.2.2.1
    have startBound : memory.toNat ≤ (header scratch).toNat := geometry.2.2.1
    have away : ∀ offset < 24, query ≠ header scratch + BitVec.ofNat 64 offset := by
      intro offset inside equal
      have number := WitnessRadix.byteAddress_toNat (header scratch) offset
        (by have bound := scratch.isLt; omega)
      change (header scratch + BitVec.ofNat 64 offset).toNat = (header scratch).toNat + offset at number
      have same := congrArg BitVec.toNat equal
      rcases outsideArena with below | above <;> omega
    simp only [FieldStores.writes, fields, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨away 0 (by decide), away 8 (by decide), away 16 (by decide)⟩

end InitECandidate.Solver.ScratchList

#print axioms InitECandidate.Solver.ScratchList.body_shape
#print axioms InitECandidate.Solver.ScratchList.execute
