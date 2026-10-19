import InitECandidate.Solver.Mpt.DestroyStorageProgram
import InitECandidate.Solver.MutableTable.KeysGeometry
import InitECandidate.Solver.WitnessRadix.StateSteps

namespace InitECandidate.Solver.Mpt.DestroyStorage
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch MutableTable NaturalLayout

theorem selected_key_arena (plan : Plan) (valid : Valid .word plan) (slot : Nat) (inside : slot < plan.capacity) :
    AllocatedBytes.Arena (cell plan .keys 0 + BitVec.ofNat 64 slot * BitVec.ofNat 64 (stride .word)) 32 := by
  have region := Keys.key_region_valid .word plan valid slot inside
  have pointer : cell plan .keys 0 + BitVec.ofNat 64 slot * BitVec.ofNat 64 (stride .word) =
      MemoryRegion.pointer (Keys.keyRegion .word plan slot) := by
    simp only [cell,Nat.add_zero,Keys.scaled_pointer,MemoryRegion.pointer,Keys.keyRegion]
  rw [pointer]
  constructor
  · rw [MemoryRegion.pointer_number _ region]
    exact region.lower
  · rw [MemoryRegion.pointer_number _ region]
    exact region.upper

theorem live_count_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (object : TableFamily.Object) (cursor : Nat)
    (table : TableState source object.kind object.plan object.slots cursor object.floor)
    (domain : source.memaddrs = InitE.ordinaryDomain)
    (innerLocal : source.locals.lookup (ofString "inner") = some (.val (.word object.pointer))) :
    eval source (.load .one (.op .add [localVar "inner",.const 24#64])) =
      some (.val (.word (BitVec.ofNat 64 object.slots.length))) := by
  have mapped : source.memaddrs (object.pointer + 24#64) := by
    rw [domain]
    have geometry := NaturalLayout.mapped object.kind object.plan table.valid .header 24 (by change 24 < 72; decide) (by decide)
    simpa [TableFamily.Object.pointer,cell,BitVec.ofNat_add] using geometry
  have stored : source.memory (object.pointer + 24#64) = .word (BitVec.ofNat 64 object.slots.length) := by
    have cell := table.header 24 (BitVec.ofNat 64 object.slots.length) (by simp [MemoryModel.headerEntries])
    simpa [TableFamily.Object.pointer,NaturalLayout.cell,BitVec.ofNat_add] using cell
  simp [eval,localVar,evalHOLExact,evalListHOLExact,toExact,innerLocal,valueIsWord,valueWord,wordOpHOL,wordOp,
    memLoadHOLExact,isWfShapeExactHOL,mapped,stored]

theorem condition_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (index count : BitVec 64)
    (indexSmall : index.toNat < 2^63) (countSmall : count.toNat < 2^63)
    (indexLocal : source.locals.lookup (ofString "i") = some (.val (.word index)))
    (countLocal : source.locals.lookup (ofString "cap") = some (.val (.word count))) :
    eval source condition = some (.val (.word (if index.toNat < count.toNat then 1#64 else 0#64))) := by
  change index.toNat < 9223372036854775808 at indexSmall
  change count.toNat < 9223372036854775808 at countSmall
  change eval source condition = some (.val (.word (if index < count then 1#64 else 0#64)))
  simp [eval,condition,localVar,evalHOLExact,toExact,indexLocal,countLocal,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,Flapjack.Compiler.Encoders.Asm.holAsmSignedLess,indexSmall,countSmall,BitVec.lt_def]

theorem loop_body_safe (key : MlS) (notS : key ≠ ofString "s") (notK : key ≠ ofString "k") (notI : key ≠ ofString "i") :
    Input.LocalPrefix key loopBody := by
  unfold loopBody afterItem mark markCall increment
  exact .decCall _ _ _ _ notS (.seq (.ite _ (.decCall _ _ _ _ notK (.call none _ _ (by intro name impossible; cases impossible))) .skip)
    (.assign _ _ notI))

theorem live_count_small (source : PanSemStateFiniteExact 64 Guest.HostMemory) (object : TableFamily.Object) (cursor : Nat)
    (table : TableState source object.kind object.plan object.slots cursor object.floor) : object.slots.length < 2^63 := by
  have count := MemoryModel.Occupied.length_le source object.kind object.plan object.slots table.occupied
  have upper := table.valid.upper .used
  have rounded := (NaturalLayout.rounded_bounds object.plan.capacity).1
  change object.plan.base .used + NaturalLayout.rounded object.plan.capacity ≤ 33806089496 at upper
  omega

theorem after_item_dispatch (source : PanSemStateFiniteExact 64 Guest.HostMemory) (key value : BitVec 64)
    (slotLocal : source.locals.lookup (ofString "s") = some (Slot.triple 1#64 key value)) :
    evaluateHOLFiniteState source afterItem = evaluateHOLFiniteState source (.seq mark increment) := by
  simp [afterItem,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,evalHOLExact,localVar,toExact,slotLocal,Slot.triple,
    Flapjack.Compiler.Encoders.Asm.wordCmpHOL]

theorem increment_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (index : Nat)
    (indexLocal : source.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 index)))) :
    evaluateHOLFiniteState source increment = (none,bind source "i" (BitVec.ofNat 64 (index + 1))) := by
  apply StateSteps.assign_execute source "i" _ (BitVec.ofNat 64 index) _ indexLocal
  simp [eval,localVar,evalHOLExact,evalListHOLExact,toExact,indexLocal,valueIsWord,valueWord,wordOpHOL,wordOp,BitVec.ofNat_add]

end InitECandidate.Solver.Mpt.DestroyStorage

#print axioms InitECandidate.Solver.Mpt.DestroyStorage.selected_key_arena
#print axioms InitECandidate.Solver.Mpt.DestroyStorage.live_count_read
#print axioms InitECandidate.Solver.Mpt.DestroyStorage.condition_read
#print axioms InitECandidate.Solver.Mpt.DestroyStorage.loop_body_safe
#print axioms InitECandidate.Solver.Mpt.DestroyStorage.live_count_small
#print axioms InitECandidate.Solver.Mpt.DestroyStorage.after_item_dispatch
#print axioms InitECandidate.Solver.Mpt.DestroyStorage.increment_execute
