import InitECandidate.Solver.MutableTable.KeysGeometry

namespace InitECandidate.Solver.MutableTable.Keys
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix NaturalLayout
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

structure Locals (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (plan : Plan) (start count number : Nat) : Prop where
  stride : source.locals.lookup (ofString "stride") = some (.val (.word (BitVec.ofNat 64 (NaturalLayout.stride kind))))
  keys : source.locals.lookup (ofString "keys") = some (.val (.word (cell plan .keys 0)))
  order : source.locals.lookup (ofString "order") = some (.val (.word (cell plan .order 0)))
  out : source.locals.lookup (ofString "out") = some (.val (.word (BitVec.ofNat 64 start)))
  count : source.locals.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 count)))
  index : source.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 number)))
  cursor : source.locals.lookup (ofString "k") = some (.val (.word (BitVec.ofNat 64 number)))

theorem Locals.of_locals (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (plan : Plan) (start count index : Nat)
    (locals : Locals source kind plan start count index) (same : source.locals = target.locals) : Locals target kind plan start count index := by
  rcases locals with ⟨stride, keys, order, out, count, index, cursor⟩
  constructor <;> rw [← same] <;> assumption

theorem Locals.bind_slot (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (plan : Plan) (start count index slot : Nat)
    (locals : Locals source kind plan start count index) : Locals (bind source "slot" (BitVec.ofNat 64 slot)) kind plan start count index := by
  exact ⟨(bind_lookup_other _ "slot" "stride" _ (by decide)).trans locals.stride,
    (bind_lookup_other _ "slot" "keys" _ (by decide)).trans locals.keys,
    (bind_lookup_other _ "slot" "order" _ (by decide)).trans locals.order,
    (bind_lookup_other _ "slot" "out" _ (by decide)).trans locals.out,
    (bind_lookup_other _ "slot" "n" _ (by decide)).trans locals.count,
    (bind_lookup_other _ "slot" "i" _ (by decide)).trans locals.index,
    (bind_lookup_other _ "slot" "k" _ (by decide)).trans locals.cursor⟩

def nextState (source : PanSemStateFiniteExact 64 Guest.HostMemory) (memory : WordWrites.Memory) (paid index : Nat) :=
  bind (bind {source with memory := memory, clock := source.clock - paid} "k" (BitVec.ofNat 64 (index + 1))) "i" (BitVec.ofNat 64 (index + 1))

theorem Locals.next (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (plan : Plan) (start count index : Nat)
    (locals : Locals source kind plan start count index) (memory : WordWrites.Memory) (paid : Nat) : Locals (nextState source memory paid index) kind plan start count (index + 1) := by
  exact ⟨(bind_lookup_other _ "i" "stride" _ (by decide)).trans ((bind_lookup_other _ "k" "stride" _ (by decide)).trans locals.stride),
    (bind_lookup_other _ "i" "keys" _ (by decide)).trans ((bind_lookup_other _ "k" "keys" _ (by decide)).trans locals.keys),
    (bind_lookup_other _ "i" "order" _ (by decide)).trans ((bind_lookup_other _ "k" "order" _ (by decide)).trans locals.order),
    (bind_lookup_other _ "i" "out" _ (by decide)).trans ((bind_lookup_other _ "k" "out" _ (by decide)).trans locals.out),
    (bind_lookup_other _ "i" "n" _ (by decide)).trans ((bind_lookup_other _ "k" "n" _ (by decide)).trans locals.count),
    bind_lookup_same _ _ _, (bind_lookup_other _ "i" "k" _ (by decide)).trans (bind_lookup_same _ _ _)⟩

/-- The original key enumerator uses a signed comparison. Physical array
extents and the occupied count derive its signed-safe natural meaning. -/
theorem condition_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (plan : Plan) (valid : Valid kind plan)
    (start count index : Nat) (countBound : count ≤ plan.capacity) (indexBound : index ≤ count)
    (locals : Locals source kind plan start count index) :
    @evalHOLFinite 64 Guest.HostMemory _ source (fun address => Classical.propDecidable (source.memaddrs address)) condition =
      some (.val (.word (if index < count then 1#64 else 0#64))) := by
  have capSmall := GrowRuntime.capacity_signed_small kind plan valid
  have countSmall : count < 2 ^ 64 := by omega
  have indexSmall : index < 2 ^ 64 := by omega
  have countSign : count < 2 ^ 63 := by omega
  have indexSign : index < 2 ^ 63 := by omega
  norm_num only [Nat.reducePow] at countSmall indexSmall countSign indexSign
  by_cases active : index < count <;>
    simp [condition, localVar, evalHOLFinite, evalHOLExact, toExact, locals.index, locals.count,
      Flapjack.Compiler.Encoders.Asm.wordCmpHOL, Flapjack.Compiler.Encoders.Asm.holAsmSignedLess,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt countSmall, Nat.mod_eq_of_lt indexSmall, countSign, indexSign, active]

theorem copy_arguments (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (plan : Plan) (start count index slot : Nat)
    (locals : Locals source kind plan start count index)
    (slotLocal : source.locals.lookup (ofString "slot") = some (.val (.word (BitVec.ofNat 64 slot)))) :
    evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) [scaled "out" "k", scaled "keys" "slot", localVar "stride"] =
      some (CopyGeneral.values (MemoryRegion.pointer (destinationRegion kind start index)) (MemoryRegion.pointer (keyRegion kind plan slot)) (stride kind)) := by
  simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, toExact, localVar, scaled, locals.out, locals.cursor, locals.keys, locals.stride, slotLocal,
    valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL, CopyGeneral.values, MemoryRegion.pointer, keyRegion, destinationRegion, cell,
    Nat.add_zero, scaled_pointer]

theorem after_copy_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (plan : Plan) (start count index : Nat)
    (locals : Locals source kind plan start count index) :
    evaluateHOLFiniteState source afterCopy = (none, nextState source source.memory 0 index) := by
  have read (target : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String)
      (stored : target.locals.lookup (ofString name) = some (.val (.word (BitVec.ofNat 64 index)))) :
      eval target (.op .add [localVar name, .const 1#64]) = some (.val (.word (BitVec.ofNat 64 (index + 1)))) := by
    simp [eval, localVar, evalHOLExact, evalListHOLExact, toExact, stored, valueIsWord, valueWord, wordOpHOL, wordOp, BitVec.ofNat_add]
  let advanced := bind source "k" (BitVec.ofNat 64 (index + 1))
  have kRun := StateSteps.assign_execute source "k" (.op .add [localVar "k", .const 1#64]) _ _ locals.cursor (read source "k" locals.cursor)
  have advancedI : advanced.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 index))) := (bind_lookup_other _ "k" "i" _ (by decide)).trans locals.index
  have iRun := StateSteps.assign_execute advanced "i" (.op .add [localVar "i", .const 1#64]) _ _ advancedI (read advanced "i" advancedI)
  rw [afterCopy, StateSteps.next_sequence source advanced (advance "k") (advance "i") kRun (Nat.le_refl _)]
  simpa only [advance, nextState, Nat.sub_zero] using iRun

end InitECandidate.Solver.MutableTable.Keys

#print axioms InitECandidate.Solver.MutableTable.Keys.Locals.of_locals
#print axioms InitECandidate.Solver.MutableTable.Keys.Locals.bind_slot
#print axioms InitECandidate.Solver.MutableTable.Keys.Locals.next
#print axioms InitECandidate.Solver.MutableTable.Keys.condition_read
#print axioms InitECandidate.Solver.MutableTable.Keys.copy_arguments
#print axioms InitECandidate.Solver.MutableTable.Keys.after_copy_execute
