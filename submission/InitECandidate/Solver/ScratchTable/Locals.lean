import InitECandidate.Solver.ScratchTable.Program

namespace InitECandidate.Solver.ScratchTable
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

structure Locals (source : PanSemStateFiniteExact 64 Guest.HostMemory) (scratch : BitVec 64) : Prop where
  table : source.locals.lookup (ofString "t") = some (.val (.word (cursor scratch 72)))
  capacity : source.locals.lookup (ofString "cap") = some (.val (.word 4#64))
  stride : source.locals.lookup (ofString "stride") = some (.val (.word 24#64))

theorem Locals.stored {source : PanSemStateFiniteExact 64 Guest.HostMemory} {scratch : BitVec 64}
    (locals : Locals source scratch) (fields : List FieldStores.Field) : Locals (stored source scratch fields) scratch := ⟨locals.table, locals.capacity, locals.stride⟩

theorem Locals.allocated {source : PanSemStateFiniteExact 64 Guest.HostMemory} {scratch : BitVec 64}
    (locals : Locals source scratch) (name : String) (next : BitVec 64)
    (notTable : ofString name ≠ ofString "t") (notCap : ofString name ≠ ofString "cap")
    (notStride : ofString name ≠ ofString "stride") :
    Locals (Arenas.Prefix.expectedState source name next) scratch :=
  ⟨(bind_lookup_other _ name "t" _ notTable).trans locals.table,
    (bind_lookup_other _ name "cap" _ notCap).trans locals.capacity,
    (bind_lookup_other _ name "stride" _ notStride).trans locals.stride⟩

theorem capacity_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (scratch : BitVec 64)
    (locals : Locals source scratch) : eval source (localVar "cap") = some (.val (.word 4#64)) := by
  simp [eval, localVar, evalHOLExact, toExact, locals.capacity]

theorem keys_amount (source : PanSemStateFiniteExact 64 Guest.HostMemory) (scratch : BitVec 64)
    (locals : Locals source scratch) : eval source (WitnessRadix.TableNew.capacityTimes (localVar "stride")) = some (.val (.word 96#64)) := by
  simp [eval, WitnessRadix.TableNew.capacityTimes, localVar, evalHOLExact, evalListHOLExact, toExact,
    locals.capacity, locals.stride, valueIsWord, valueWord, panOpHOL]

theorem words_amount (source : PanSemStateFiniteExact 64 Guest.HostMemory) (scratch : BitVec 64)
    (locals : Locals source scratch) : eval source (WitnessRadix.TableNew.capacityTimes (.const 8#64)) = some (.val (.word 32#64)) := by
  simp [eval, WitnessRadix.TableNew.capacityTimes, localVar, evalHOLExact, evalListHOLExact, toExact,
    locals.capacity, valueIsWord, valueWord, panOpHOL]

theorem expected_scratch (source : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String) (next : BitVec 64) :
    (Arenas.Prefix.expectedState source name next).globals.lookup (ofString "scratch_ptr") = some (.val (.word next)) := by
  simp [Arenas.Prefix.expectedState, WitnessRadix.QueryBranch.bind, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]

theorem expected_memory (source : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String) (next memory : BitVec 64)
    (stored : source.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word memory))) :
    (Arenas.Prefix.expectedState source name next).globals.lookup (ofString "frame_mem_ptr") = some (.val (.word memory)) := by
  simpa [Arenas.Prefix.expectedState, WitnessRadix.QueryBranch.bind, setVarHOLFinite,
    HolFiniteMapExact.update, FUPDATE, ofString] using stored

theorem pointer_executes (source : PanSemStateFiniteExact 64 Guest.HostMemory) (scratch : BitVec 64)
    (offset : Nat) (name : String) (pointer : BitVec 64)
    (table : source.locals.lookup (ofString "t") = some (.val (.word (cursor scratch 72))))
    (saved : source.locals.lookup (ofString name) = some (.val (.word pointer)))
    (mapped : source.memaddrs (cursor scratch 72 + BitVec.ofNat 64 offset)) :
    Arenas.Prefix.Executes .down source (Arenas.Prefix.fieldActions "t" "unused" (pointerFields offset name pointer))
      (stored source scratch (pointerFields offset name pointer)) id := by
  apply Arenas.Prefix.field_stores .down source "t" "unused" (cursor scratch 72) 0#64
    (pointerFields offset name pointer) table
  · intro field member
    simp only [pointerFields, List.mem_singleton] at member
    subst field
    exact saved
  · intro field member
    simp only [pointerFields, List.mem_singleton] at member
    subst field
    exact mapped
  · intro reader readerIn writer writerIn
    simp only [pointerFields, List.mem_singleton] at readerIn
    subst reader
    trivial

end InitECandidate.Solver.ScratchTable

#print axioms InitECandidate.Solver.ScratchTable.Locals.allocated
#print axioms InitECandidate.Solver.ScratchTable.keys_amount
#print axioms InitECandidate.Solver.ScratchTable.words_amount
#print axioms InitECandidate.Solver.ScratchTable.pointer_executes
