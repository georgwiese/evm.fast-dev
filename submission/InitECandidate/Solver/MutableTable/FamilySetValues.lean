import InitECandidate.Solver.MutableTable.FamilyValues
import InitECandidate.Solver.MutableTable.SetNormalCallValues
import InitECandidate.Solver.GasBudget.WarmKeysInvariant
import InitECandidate.Solver.MutableTable.SetEarlierFootprint

namespace InitECandidate.Solver.MutableTable.TableFamily
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix NaturalLayout

/-- An actual original setter in an arbitrary live table family. It derives
reached growth room and a common new cursor, retains every reader model and
all pairwise pool separation, and keeps every table's stable header pointer. -/
theorem set_normal_values {ι : Type} [DecidableEq ι] (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat)
    (objects : ι → Object) (writer : ι) (family : Model source cursor objects)
    (environment : GasBudget.WarmKeys.Environment source) (query value : BitVec 64) (arguments : List (ExpHOL 64))
    (property : ι → BitVec 64 → Prop) (values : ValuesHave source objects property) (owned : property writer value)
    (queryFits : query.toNat + KeyHash.keySize (objects writer).kind < 2 ^ 64)
    (queryMapped : ∀ offset < KeyHash.keySize (objects writer).kind, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress query offset)))
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some (TableCall.values (objects writer).pointer query value))
    (normal : evaluateHOLFiniteState source (.call (some (none, none)) (ofString "htab_set") arguments) = (none, target)) :
    ∃ (paid nextCursor : Nat) (next : Object),
      paid ≤ source.clock ∧ target.clock = source.clock - paid ∧ cursor ≤ nextCursor ∧
      next.kind = (objects writer).kind ∧ next.floor = (objects writer).floor ∧
      Model target nextCursor (Function.update objects writer next) ∧
      (∀ index, (Function.update objects writer next index).pointer = (objects index).pointer) ∧
      paid + GrowRuntime.growthPotential (objects writer).kind (objects writer).plan.capacity ≤
        Set.noGrowthPrice (objects writer).kind (objects writer).slots.length + 1 + GrowRuntime.growthPotential (objects writer).kind next.plan.capacity ∧
      (objects writer).slots.length ≤ next.slots.length ∧ next.slots.length ≤ (objects writer).slots.length + 1 ∧
      next.plan.capacity ≤ max (objects writer).plan.capacity (4 * (next.slots.length + 1)) ∧
      target.locals = source.locals ∧ target.code = source.code ∧ GasBudget.WarmKeys.Environment target ∧ HeapGlobals source target ∧
      (∀ address : BitVec 64, address.toNat < (objects writer).floor → target.memory address = source.memory address) ∧
      (∀ address : BitVec 64, address.toNat < cursor → TableFootprint.Outside (objects writer).kind (objects writer).plan address →
        TableFootprint.Outside next.kind next.plan address ∧ target.memory address = source.memory address) ∧ ValuesHave target (Function.update objects writer next) property := by
  let old := objects writer
  have table := family.tables writer
  obtain ⟨bits, power, minimum⟩ := table.power
  obtain ⟨paid, globals, memory, plan, slots, bounded, unchanged, fits, post, valid, half, locals, writerValues⟩ :=
    Set.model_call_bound_values source target old.kind old.plan table.valid cursor table.bounded table.aligned table.earlier environment.domain environment.little old.slots table.half table.header table.occupied
      query value (property writer) (values writer) owned bits power minimum queryFits queryMapped table.heap environment.allocCode environment.trapCode environment.zeroCode environment.hashCode environment.copyCode environment.memeqCode
      environment.findCode environment.insertCode environment.growCode environment.setCode arguments args normal
  obtain ⟨nextCursor, forward, cursorBound, cursorAligned, heap, before⟩ := post.cursor valid table.bounded table.aligned table.earlier table.heap
  obtain ⟨nextBits, _, nextMinimum, nextPower⟩ := post.next_power table.valid bits power minimum
  have memoryEq := congrArg PanSemStateFiniteExact.memory post.frame
  change target.memory = memory at memoryEq
  have clock := congrArg PanSemStateFiniteExact.clock post.frame
  change target.clock = source.clock - paid at clock
  have codes := congrArg PanSemStateFiniteExact.code post.frame
  have domain := congrArg PanSemStateFiniteExact.memaddrs post.frame
  have endian := congrArg PanSemStateFiniteExact.be post.frame
  change target.code = source.code at codes
  change target.memaddrs = source.memaddrs at domain
  change target.be = source.be at endian
  let next : Object := {old with plan := plan, slots := slots}
  have writerTable : TableState target next.kind next.plan next.slots nextCursor next.floor :=
    ⟨valid, half, by rw [memoryEq]; exact post.header, post.occupied, ⟨nextBits, nextPower, nextMinimum⟩,
      heap, cursorBound, cursorAligned, before, post.pool_floor old.floor table.lower table.earlier⟩
  have separated (reader : ι) (different : reader ≠ writer) : Apart next (objects reader) :=
    post.reader_separate (objects reader).kind (objects reader).plan (family.tables reader).earlier (family.apart writer reader (Ne.symm different))
  have readerTable (reader : ι) (different : reader ≠ writer) :
      TableState target (objects reader).kind (objects reader).plan (objects reader).slots nextCursor (objects reader).floor := by
    have oldReader := family.tables reader
    obtain ⟨header, model⟩ := post.other_model valid (objects reader).kind (objects reader).plan oldReader.valid (separated reader different)
      (objects reader).slots oldReader.header oldReader.occupied
    exact ⟨oldReader.valid, oldReader.half, header, model, oldReader.power, heap, cursorBound, cursorAligned,
      (by intro pool; have earlier := oldReader.earlier pool; omega), oldReader.lower⟩
  have nextFamily : Model target nextCursor (Function.update objects writer next) := by
    constructor
    · intro index
      by_cases same : index = writer
      · subst index
        simpa only [Function.update_self] using writerTable
      · simpa only [Function.update_of_ne same] using readerTable index same
    · intro first second different
      by_cases firstWriter : first = writer
      · subst first
        simpa only [Function.update_self, Function.update_of_ne (Ne.symm different)] using separated second (Ne.symm different)
      · by_cases secondWriter : second = writer
        · subst second
          simpa only [Function.update_self, Function.update_of_ne firstWriter] using (separated first firstWriter).symm
        · simpa only [Function.update_of_ne firstWriter, Function.update_of_ne secondWriter] using family.apart first second different
  refine ⟨paid, nextCursor, next, fits, clock, forward, rfl, rfl, nextFamily, ?_, post.amortized_power bits power minimum table.half bounded unchanged,
    post.countBound.1, post.countBound.2, post.capacity_high_water, locals, codes, environment.of_fields codes domain endian, post.heap_globals,
    (fun address earlier => post.protected_before valid old.floor table.lower table.earlier address earlier), ?_, ?_⟩
  · intro index
    by_cases same : index = writer
    · subst index
      simpa only [Function.update_self, Object.pointer] using post.header_pointer
    · rw [Function.update_of_ne same]
  · intro address earlier outside
    have nextOutside := post.outside_earlier valid address earlier outside
    exact ⟨nextOutside, post.protected_word address nextOutside⟩

  · intro index
    by_cases same : index=writer
    · subst index
      simpa only [Function.update_self] using writerValues
    · change Get.OccupiedValuesHave target (cell (Function.update objects writer next index).plan .values 0)
        (BitVec.ofNat 64 (Function.update objects writer next index).plan.capacity) (Function.update objects writer next index).slots (property index)
      rw [Function.update_of_ne same]
      apply (values index).of_agreement source target _ _ _ _
      intro slot inside member
      have tableValid := (family.tables index).valid
      have capNumber : (BitVec.ofNat 64 (objects index).plan.capacity).toNat=(objects index).plan.capacity := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (capacity_small (objects index).kind _ tableValid)]
      rw [capNumber] at inside
      rw [scaled_cell]
      exact post.other_pools valid (objects index).kind (objects index).plan tableValid (separated index same)
        .values _ (word_offset_inside (objects index).kind _ .values slot.toNat (Or.inl rfl) inside)

end InitECandidate.Solver.MutableTable.TableFamily

#print axioms InitECandidate.Solver.MutableTable.TableFamily.set_normal_values
