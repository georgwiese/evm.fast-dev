import InitECandidate.Solver.Input.MemoryWordCalls
import InitECandidate.Solver.GasBudget.MemoryWriterBytes

namespace InitECandidate.Solver.Input.MemoryWordCalls
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch GasBudget.MemoryWriter

def le32Body : ProgHOL 64 := match Guest.guestFn_st_le32 with | .function fn => progToHOL fn.body | _ => .skip
def le64Body : ProgHOL 64 := match Guest.guestFn_st_le64 with | .function fn => progToHOL fn.body | _ => .skip
def leClauses : List (Nat × Nat) := [(0,0),(1,8),(2,16),(3,24)]
def le64FirstArgs : List (ExpHOL 64) := [localVar "p",localVar "v"]
def le64SecondArgs : List (ExpHOL 64) := [.op .add [localVar "p",.const 4#64],.shift .lsr (localVar "v") (.const 32#64)]
def le64Tail : ProgHOL 64 := .seq (.call (some (none,none)) (ofString "st_le32") le64SecondArgs) (.return (.const 0#64))
def le64Image (memory : WordWrites.Memory) (endian : Bool) (pointer value : BitVec 64) :=
  GasBudget.Be32Stores.written (GasBudget.Be32Stores.written memory endian pointer value leClauses) endian (pointer + 4#64) (value >>> 32) leClauses
def le64First (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer value : BitVec 64) :=
  {source with memory := GasBudget.Be32Stores.written source.memory source.be pointer value leClauses,clock := source.clock - 1}
def le64Post (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer value : BitVec 64) :=
  {source with memory := le64Image source.memory source.be pointer value,clock := source.clock - 2}

theorem le32_shape : le32Body = GasBudget.Be32Stores.stores leClauses := by
  simp [le32Body,Guest.guestFn_st_le32,progToHOL,expToHOL,List.map_cons,List.map_nil,GasBudget.Be32Stores.stores,GasBudget.Be32Stores.address,GasBudget.Be32Stores.byteValue,leClauses,localVar]

theorem le64_shape : le64Body = .seq (.call (some (none,none)) (ofString "st_le32") le64FirstArgs) le64Tail := by
  simp only [le64Body,Guest.guestFn_st_le64,progToHOL,expToHOL,List.map_cons,List.map_nil,Option.map_none,le64FirstArgs,le64SecondArgs,le64Tail,localVar]

set_option maxRecDepth 100000 in
theorem le32_code (code) (installed : OriginalCode.Installed code) : code.lookup (ofString "st_le32") = some (formals,le32Body,.one) := by
  have checked := OriginalCode.indexed code installed 20 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_st_le32) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,formals,le32Body,Guest.guestFn_st_le32,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

set_option maxRecDepth 100000 in
theorem le64_code (code) (installed : OriginalCode.Installed code) : code.lookup (ofString "st_le64") = some (formals,le64Body,.one) := by
  have checked := OriginalCode.indexed code installed 21 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_st_le64) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,formals,le64Body,Guest.guestFn_st_le64,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

theorem le32_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer value : BitVec 64) (arguments : List (ExpHOL 64))
    (installed : OriginalCode.Installed source.code)
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some [.val (.word pointer),.val (.word value)])
    (mapped : BytesMapped source pointer 4) (enough : 1 ≤ source.clock) :
    evaluateHOLFiniteState source (.call (some (none,none)) (ofString "st_le32") arguments) =
      (none,{source with memory := GasBudget.Be32Stores.written source.memory source.be pointer value leClauses,clock := source.clock - 1}) := by
  obtain ⟨callee,called,p,v⟩ := environment source.code.lookup (ofString "st_le32") le32Body pointer value (le32_code source.code installed)
  let entry := callEntryStateHOLFinite source callee
  have run := GasBudget.Be32Stores.execute entry pointer value leClauses p v
    (by intro clause member; simp only [leClauses,List.mem_cons,List.not_mem_nil,or_false] at member; rcases member with rfl | rfl | rfl | rfl <;> decide)
    (by intro clause member; apply mapped clause.1; simp only [leClauses,List.mem_cons,List.not_mem_nil,or_false] at member; rcases member with rfl | rfl | rfl | rfl <;> decide)
  rw [← le32_shape] at run
  exact evaluateHOLFiniteState_call_return_caller_locals source none (ofString "st_le32") arguments [.val (.word pointer),.val (.word value)] _ callee .one
    (.val (.word 0#64)) _ args called (by omega) run (by simp [shapeOfHOLExact,shapeEqHOL])

theorem le64_body_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer value : BitVec 64)
    (installed : OriginalCode.Installed source.code)
    (p : source.locals.lookup (ofString "p") = some (.val (.word pointer))) (v : source.locals.lookup (ofString "v") = some (.val (.word value)))
    (mapped : BytesMapped source pointer 8) (enough : 2 ≤ source.clock) :
    evaluateHOLFiniteState source le64Body = (some (.returned (.val (.word 0#64))),emptyLocalsHOLFinite (le64Post source pointer value)) := by
  have firstArgs : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) le64FirstArgs = some [.val (.word pointer),.val (.word value)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,le64FirstArgs,localVar,p,v]
  have firstMapped : BytesMapped source pointer 4 := by simpa only [BitVec.add_zero] using mapped.subrange 0 4 (by decide)
  have firstRun := le32_execute source pointer value le64FirstArgs installed firstArgs firstMapped (by omega)
  let first := le64First source pointer value
  have secondArgs : evalListHOLFinite first (h := fun address => Classical.propDecidable (first.memaddrs address)) le64SecondArgs = some [.val (.word (pointer + 4#64)),.val (.word (value >>> 32))] := by
    simp [first,le64First,evalListHOLFinite,evalListHOLExact,evalHOLExact,le64SecondArgs,localVar,p,v,valueIsWord,valueWord,wordOpHOL,wordOp,wordShiftHOL]
  have secondRun := le32_execute first (pointer + 4#64) (value >>> 32) le64SecondArgs installed secondArgs (mapped.subrange 4 4 (by decide)) (by change 1 ≤ source.clock - 1; omega)
  have subtract : source.clock - 1 - 1 = source.clock - 2 := by omega
  have secondActual : evaluateHOLFiniteState first (.call (some (none,none)) (ofString "st_le32") le64SecondArgs) = (none,le64Post source pointer value) := by
    simpa only [first,le64First,le64Post,le64Image,subtract] using secondRun
  rw [le64_shape,StateSteps.next_sequence source first _ _ firstRun (Nat.sub_le _ _),le64Tail,
    StateSteps.next_sequence first (le64Post source pointer value) _ _ secondActual (by change source.clock - 2 ≤ source.clock - 1; omega)]
  exact BuildEntry.zero_return (le64Post source pointer value)

private theorem le64_frame (source : PanSemStateFiniteExact 64 Guest.HostMemory) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (pointer value : BitVec 64) :
    {emptyLocalsHOLFinite (le64Post (callEntryStateHOLFinite source callee) pointer value) with locals := source.locals} =
      {source with memory := le64Image source.memory source.be pointer value,clock := source.clock - 3} := by
  have clock : source.clock - 1 - 2 = source.clock - 3 := by omega
  simp only [le64Post,callEntryStateHOLFinite,emptyLocalsHOLFinite,clock]

theorem le64_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer value : BitVec 64) (arguments : List (ExpHOL 64))
    (installed : OriginalCode.Installed source.code)
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some [.val (.word pointer),.val (.word value)])
    (mapped : BytesMapped source pointer 8) (enough : 3 ≤ source.clock) :
    evaluateHOLFiniteState source (.call (some (none,none)) (ofString "st_le64") arguments) =
      (none,{source with memory := le64Image source.memory source.be pointer value,clock := source.clock - 3}) := by
  obtain ⟨callee,called,p,v⟩ := environment source.code.lookup (ofString "st_le64") le64Body pointer value (le64_code source.code installed)
  let entry := callEntryStateHOLFinite source callee
  have run := le64_body_execute entry pointer value installed p v mapped (by change 2 ≤ source.clock - 1; omega)
  have actual := evaluateHOLFiniteState_call_return_caller_locals source none (ofString "st_le64") arguments [.val (.word pointer),.val (.word value)] _ callee .one
    (.val (.word 0#64)) _ args called (by omega) run (by simp [shapeOfHOLExact,shapeEqHOL])
  rw [le64_frame source callee pointer value] at actual
  exact actual

end InitECandidate.Solver.Input.MemoryWordCalls

#print axioms InitECandidate.Solver.Input.MemoryWordCalls.le32_shape
#print axioms InitECandidate.Solver.Input.MemoryWordCalls.le64_shape
#print axioms InitECandidate.Solver.Input.MemoryWordCalls.le32_code
#print axioms InitECandidate.Solver.Input.MemoryWordCalls.le64_code
#print axioms InitECandidate.Solver.Input.MemoryWordCalls.le32_execute
#print axioms InitECandidate.Solver.Input.MemoryWordCalls.le64_body_execute
#print axioms InitECandidate.Solver.Input.MemoryWordCalls.le64_execute
