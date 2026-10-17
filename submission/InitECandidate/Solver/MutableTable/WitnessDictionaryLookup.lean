import InitECandidate.Solver.MutableTable.WitnessDictionaryRecords
import InitECandidate.Solver.MutableTable.NodeDbDictionary32
import InitECandidate.Solver.DictionaryValues

namespace InitECandidate.Solver.MutableTable.WitnessBuild
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString
attribute [local instance] Classical.propDecidable

def sliceEntries (plan : AllocatedLayout.Plan) (slices : Nat→Graph.Slice) (input : List (Find.Key32×BitVec 64)) : List (Find.Key32×Graph.Slice):=
  input.map (fun entry=>(entry.1,recordSlices plan slices entry.2))

theorem lookup_output (answer : Option Graph.Slice) : NodeDb.output answer=QueryExecution.valueOf answer := by
  cases answer <;> rfl

/-- Entire actual original witness lookup from the constructor's preserved
physical/history/record invariant, for every query at every alignment. It
returns precisely the last matching input slice as the original three-field return value. -/
theorem dictionary_lookup (source : PanSemStateFiniteExact 64 Guest.HostMemory) (plan : AllocatedLayout.Plan)
    (ready : AllocatedLayout.Ready plan) (domain : source.memaddrs=InitE.ordinaryDomain)
    (bits : Nat) (small : bits<64) (power : plan.capacity=2^bits) (scratch : BitVec 64) (count : Nat)
    (input : List (Find.Key32×BitVec 64)) (logical : Find.Model32 (BitVec 64))
    (built : Layout32.Built bits source plan scratch count input logical) (history : History plan input)
    (slices : Nat→Graph.Slice) (records : Records source plan slices)
    (queryPointer : BitVec 64) (query : Find.Key32) (view : MemoryBytes.ByteView source queryPointer query)
    (fits : queryPointer.toNat+32<2^64) (little : source.be=false)
    (dbLocal : source.locals.lookup (ofString "db")=some (.val (.word (BitVec.ofNat 64 plan.table))))
    (hashLocal : source.locals.lookup (ofString "hash")=some (.val (.word queryPointer)))
    (hashCode : source.code.lookup (ofString "htab_hash")=some (Hash.formals,Hash.body,.one))
    (memeqCode : source.code.lookup (ofString "memeq")=some (Memeq32.formals,Memeq32.body,.one))
    (findCode : source.code.lookup (ofString "htab_find_slot")=some (Find.formals,Find.body,.one))
    (getCode : source.code.lookup (ofString "htab_get")=some (Get.formals,Get.body,Get.pairShape))
    (enough : 6*input.length+3≤source.clock) :
    ∃ paid target,paid≤6*input.length+3 ∧
      evaluateHOLFiniteState source NodeDb.body=(some (.returned (QueryExecution.valueOf (lastValue query (sliceEntries plan slices input)))),target) ∧
      emptyLocalsHOLFinite target=emptyLocalsHOLFinite {source with clock:=source.clock-paid} := by
  classical
  let p:=Layout32.parameters plan queryPointer
  have header : Find.HeaderData source (BitVec.ofNat 64 plan.table) p:=
    ⟨built.header.find.mapped,built.header.find.capacity,built.header.find.keyLength,built.header.find.stride,built.header.find.keys,built.header.find.used⟩
  have model : Find.KeyModel32 source p plan.capacity logical := by
    constructor
    · exact built.keys.used
    · intro i inside key value cell;exact built.keys.view i inside key value cell
  have invariants:=Placement.build_invariants plan.capacity (Find.hashHome bits) input logical built.trace
  obtain ⟨order,lengthBound,covered⟩:=Placement.build_cover plan.capacity (Find.hashHome bits) input logical built.trace
  have inputBound:=History.length_bound plan input history
  have room:=ready.room
  have capacity : p.capacity=BitVec.ofNat 64 (2^bits):=by simp [p,Layout32.parameters,TableEmpty.parameters,power]
  have valsMapped : source.memaddrs (BitVec.ofNat 64 plan.table+40#64) := by
    rw [Layout32.header_cell plan 40]
    exact Layout32.word_mapped source plan ready domain .header 40 (by change 40<72;decide) (by decide)
  obtain ⟨paid,target,bound,run,frame⟩:=NodeDb.dictionary32_lookup source (BitVec.ofNat 64 plan.table) p header rfl bits small capacity logical
    (by simpa only [← power] using model) (fun key=>lastValue key input) (by simpa only [← power] using invariants.2.1)
    (by simpa only [← power] using invariants.1) order (by omega) (by simpa only [← power] using covered)
    (by intro i inside;exact Layout32.key_fits plan ready queryPointer i (by rw [power];exact inside))
    query view fits little hashCode memeqCode findCode (BitVec.ofNat 64 (Layout32.base plan .values)) valsMapped built.header.values
    (by simpa only [Find.ValueModel32,← power] using built.values) getCode dbLocal hashLocal (recordSlices plan slices)
    (by intro key record found;exact history_value_cells source plan ready domain slices input history records key record found) (by omega)
  refine ⟨paid,target,by omega,?_,frame⟩
  simpa only [lookup_output,DictionaryData.lastValue_map,sliceEntries] using run

end InitECandidate.Solver.MutableTable.WitnessBuild

#print axioms InitECandidate.Solver.MutableTable.WitnessBuild.lookup_output
#print axioms InitECandidate.Solver.MutableTable.WitnessBuild.dictionary_lookup
