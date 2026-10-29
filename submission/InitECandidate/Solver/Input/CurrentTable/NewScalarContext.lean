import InitECandidate.Solver.Input.CurrentTable.NewPersistentArray
import InitECandidate.Solver.Input.CurrentTable.NewArraysProgram
import InitECandidate.Solver.Input.CurrentTable.NewFinalStores

namespace InitECandidate.Solver.Input.CurrentTable.New
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix QueryBranch

/-- Only the actual scalar bindings, header region and allocator frontier
needed for normal current construction. No particular key width or initialized
array model is required to protect earlier memory. -/
structure ScalarContext (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table cursor cap stride : BitVec 64) : Prop where
  arena : CurrentStartup.ArenaState source
  heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor))
  cursorArena : AllocatedBytes.Arena cursor 0
  cursorBound : cursor.toNat≤2952790016
  cursorAligned : cursor.toNat%8=0
  tableArena : AllocatedBytes.Arena table 88
  tableAligned : table.toNat%8=0
  tableBefore : table.toNat≤cursor.toNat
  tableCell : source.locals.lookup (ofString "t")=some (.val (.word table))
  capCell : source.locals.lookup (ofString "ncap")=some (.val (.word cap))
  strideCell : source.locals.lookup (ofString "stride")=some (.val (.word stride))

theorem ScalarContext.after_array {source : PanSemStateFiniteExact 64 Guest.HostMemory} {table cursor cap stride : BitVec 64}
    (context : ScalarContext source table cursor cap stride) (amount : BitVec 64) (name : String) (offset : Nat)
    (notTable : ofString name≠ofString "t") (notCap : ofString name≠ofString "ncap") (notStride : ofString name≠ofString "stride")
    (inside : offset<88) (room : cursor.toNat+amount.toNat≤2952790016) :
    ScalarContext (arrayEntry source table cursor amount name offset) table (PersistentAlloc.rounded cursor amount) cap stride := by
  have checked:=PersistentAlloc.guards cursor amount room
  have physical:=array_persistent_frame source table cursor amount table name offset context.tableArena inside context.cursorArena room (Nat.le_refl _) context.tableBefore
  obtain ⟨heapCell,clock,locals,globals,memory⟩:=array_frame source table cursor amount name offset
  refine ⟨physical.current_arena context.arena,heapCell,?_,checked.2.2.2.1,checked.2.2.2.2,context.tableArena,context.tableAligned,?_,?_,?_,?_⟩
  · exact ⟨by have lower:=context.cursorArena.lower; have grows:=checked.2.2.1; omega,by have upper:=checked.2.2.2.1; omega⟩
  · have grows:=checked.2.2.1
    have before:=context.tableBefore
    omega
  · exact (locals _ (Ne.symm notTable)).trans context.tableCell
  · exact (locals _ (Ne.symm notCap)).trans context.capCell
  · exact (locals _ (Ne.symm notStride)).trans context.strideCell

/-- The final four real metadata stores return the same table pointer
and protect all earlier words, with complete runtime/allocator preservation. -/
theorem scalar_final_frame (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (table cursor cap stride : BitVec 64)
    (context : ScalarContext source table cursor cap stride) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source finalFields=(some (.returned value),post)) :
    value=.val (.word table) ∧ PersistentNormalFrame source post table := by
  have actual:=final_fields_execute source table cap context.arena.domain context.tableArena context.tableAligned context.tableCell context.capCell
  have resultEq:=congrArg Prod.fst (normal.symm.trans actual)
  have endpoint : post=emptyLocalsHOLFinite (finishStored source table cap):=congrArg Prod.snd (normal.symm.trans actual)
  have valueEq : value=.val (.word table):=by simpa only [Option.some.injEq,PanSemResultExact.returned.injEq] using resultEq
  refine ⟨valueEq,⟨⟨cursor,?_,context.cursorArena,context.cursorBound,context.cursorAligned,context.tableBefore⟩,?_,?_,?_⟩⟩
  · rw [endpoint]; exact context.heapCell
  · rw [endpoint]; rfl
  · intros; rw [endpoint]; rfl
  · intro query before
    rw [endpoint]
    change (finishStored source table cap).memory query=source.memory query
    have away (offset : Nat) (inside : offset<88) : query≠table+BitVec.ofNat 64 offset := by
      have number:=byteAddress_toNat table offset (by have upper:=context.tableArena.upper; omega)
      change (table+BitVec.ofNat 64 offset).toNat=table.toNat+offset at number
      intro same
      have equal:=congrArg BitVec.toNat same
      rw [number] at equal
      omega
    simp [finishStored,putField,StoreWord.put,away 56 (by decide),away 64 (by decide),away 72 (by decide),away 80 (by decide)]

end InitECandidate.Solver.Input.CurrentTable.New

#print axioms InitECandidate.Solver.Input.CurrentTable.New.ScalarContext.after_array
#print axioms InitECandidate.Solver.Input.CurrentTable.New.scalar_final_frame
