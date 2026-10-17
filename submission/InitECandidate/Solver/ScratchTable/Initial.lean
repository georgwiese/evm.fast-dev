import InitECandidate.Solver.ScratchTable.Locals

namespace InitECandidate.Solver.ScratchTable
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Actual initial allocation, key stride and four header stores for the
20-byte/capacity4 delete table used by frame_new. -/
theorem initial_executes (source : PanSemStateFiniteExact 64 Guest.HostMemory) (scratch memory : BitVec 64)
    (code : source.code.lookup (ofString "scratch_alloc") = some (Arenas.formals, Arenas.body .down, .one))
    (scratchGlobal : source.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (memoryGlobal : source.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word memory)))
    (keyLocal : source.locals.lookup (ofString "key_len") = some (.val (.word 20#64)))
    (capLocal : source.locals.lookup (ofString "cap") = some (.val (.word 4#64)))
    (scratchAligned : scratch.toNat % 8 = 0) (memoryAligned : memory.toNat % 8 = 0)
    (room : memory.toNat + 72 ≤ scratch.toNat)
    (mapped : ∀ offset, offset + 8 ≤ 72 → offset % 8 = 0 →
      source.memaddrs (cursor scratch 72 + BitVec.ofNat 64 offset))
    (enough : 1 ≤ source.clock) :
    Arenas.Prefix.Executes .down source firstActions (initialState source scratch)
      (fun post => restore source "t" (restore (tableState source scratch) "stride" post)) := by
  let table := tableState source scratch
  let ready := strideState source scratch
  have keyTable : table.locals.lookup (ofString "key_len") = some (.val (.word 20#64)) :=
    (bind_lookup_other _ "t" "key_len" _ (by decide)).trans keyLocal
  have keyReady : ready.locals.lookup (ofString "key_len") = some (.val (.word 20#64)) :=
    (bind_lookup_other _ "stride" "key_len" _ (by decide)).trans keyTable
  have capTable : table.locals.lookup (ofString "cap") = some (.val (.word 4#64)) :=
    (bind_lookup_other _ "t" "cap" _ (by decide)).trans capLocal
  have capReady : ready.locals.lookup (ofString "cap") = some (.val (.word 4#64)) :=
    (bind_lookup_other _ "stride" "cap" _ (by decide)).trans capTable
  have tableReady : ready.locals.lookup (ofString "t") = some (.val (.word (cursor scratch 72))) :=
    (bind_lookup_other _ "stride" "t" _ (by decide)).trans (bind_lookup_same _ _ _)
  have strideReady : ready.locals.lookup (ofString "stride") = some (.val (.word 24#64)) := bind_lookup_same _ _ _
  have reads : ∀ field ∈ headerFields, field.value.Ready ready "unused" 0#64 := by
    intro field member
    simp only [headerFields, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · exact keyReady
    · exact strideReady
    · exact capReady
    · trivial
  have fieldsMapped : ∀ field ∈ headerFields, ready.memaddrs (cursor scratch 72 + BitVec.ofNat 64 field.offset) := by
    intro field member
    apply mapped
    · simp only [headerFields, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl <;> decide
    · simp only [headerFields, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl <;> decide
  have separated : ∀ reader ∈ headerFields, ∀ writer ∈ headerFields,
      reader.value.Avoid 0#64 (cursor scratch 72 + BitVec.ofNat 64 writer.offset) := by
    intro reader member writer writerIn
    simp only [headerFields, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> trivial
  have headerSetup := Arenas.Prefix.field_stores .down ready "t" "unused" (cursor scratch 72) 0#64
    headerFields tableReady reads fieldsMapped separated
  change Arenas.Prefix.Executes .down ready (Arenas.Prefix.fieldActions "t" "unused" headerFields)
    (initialState source scratch) id at headerSetup
  have strideRead : eval table WitnessRadix.TableNew.stride = some (.val (.word 24#64)) := by
    simp [eval, WitnessRadix.TableNew.stride, localVar, evalHOLExact, evalListHOLExact, toExact,
      keyTable, valueIsWord, valueWord, wordOpHOL, wordOp, AndOp.and]
  have rest : Arenas.Prefix.Executes .down table
      (.declare "stride" WitnessRadix.TableNew.stride :: Arenas.Prefix.fieldActions "t" "unused" headerFields)
      (initialState source scratch) (fun post => restore table "stride" post) :=
    .declare 24#64 strideRead headerSetup
  have rounding : Arenas.rounded .down scratch 72#64 = cursor scratch 72 := by
    simpa only [cursor, BitVec.sub_zero] using Arenas.rounded_decrement scratch 0 72 72 scratchAligned
      (by decide) (by decide) (by decide) (by decide) (by omega)
  exact Arenas.Prefix.allocate_expected source _ "t" (.const 72#64) _ _ scratch memory 72#64 (cursor scratch 72)
    rfl code scratchGlobal memoryGlobal memoryAligned room rounding enough rest

theorem initial_locals (source : PanSemStateFiniteExact 64 Guest.HostMemory) (scratch : BitVec 64)
    (capLocal : source.locals.lookup (ofString "cap") = some (.val (.word 4#64))) :
    Locals (initialState source scratch) scratch := by
  have table : (strideState source scratch).locals.lookup (ofString "t") = some (.val (.word (cursor scratch 72))) :=
    (bind_lookup_other _ "stride" "t" _ (by decide)).trans (bind_lookup_same _ _ _)
  have capacity : (strideState source scratch).locals.lookup (ofString "cap") = some (.val (.word 4#64)) :=
    (bind_lookup_other _ "stride" "cap" _ (by decide)).trans
      ((bind_lookup_other _ "t" "cap" _ (by decide)).trans capLocal)
  exact ⟨table, capacity, bind_lookup_same _ _ _⟩

end InitECandidate.Solver.ScratchTable

#print axioms InitECandidate.Solver.ScratchTable.initial_executes
#print axioms InitECandidate.Solver.ScratchTable.initial_locals
