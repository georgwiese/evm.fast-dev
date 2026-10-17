import InitECandidate.Solver.MutableTable.FindDictionary32
import InitECandidate.Solver.MutableTable.FindCall32

namespace InitECandidate.Solver.MutableTable.Find
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Actual two-argument original lookup caller at every key alignment. All
header/hash/scan/return/call clocks are included; memory/control are pure. -/
theorem dictionary32_call {Value : Type} (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table : BitVec 64) (p : Parameters)
    (cells : HeaderCells source table p) (keyLength : p.keyLength=32#64)
    (bits : Nat) (small : bits<64) (capacity : p.capacity=BitVec.ofNat 64 (2^bits))
    (tableModel : Model32 Value) (model : KeyModel32 source p (2^bits) tableModel)
    (dictionary : Key32→Option Value) (rep : Placement.Represents (2^bits) tableModel dictionary)
    (placed : Placement.NoGaps (2^bits) (hashHome bits) tableModel)
    (order : List Nat) (room : order.length<2^bits) (covered : ∀ i<2^bits,tableModel i≠none→i∈order)
    (fits : ∀ i<2^bits,(p.keys+BitVec.ofNat 64 i*p.stride).toNat+32<2^64)
    (query : WitnessRadix.ByteKeys.Key) (queryView : WitnessRadix.MemoryBytes.ByteView source p.key query)
    (queryFits : p.key.toNat+32<2^64) (little : source.be=false)
    (hashCode : source.code.lookup (ofString "htab_hash")=some (Hash.formals,Hash.body,.one))
    (memeqCode : source.code.lookup (ofString "memeq")=some (WitnessRadix.Memeq32.formals,WitnessRadix.Memeq32.body,.one))
    (findCode : source.code.lookup (ofString "htab_find_slot")=some (formals,body,.one))
    (name : String) (expressions : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) expressions=some [.val (.word table),.val (.word p.key)])
    (enough : 6*order.length+2≤source.clock) :
    ∃ paid value,paid≤6*order.length+2 ∧ SlotSpec32 (2^bits) p.capacity value tableModel dictionary query ∧
      evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "htab_find_slot") expressions continuation)=
        (let output:=evaluateHOLFiniteState (bind {source with clock:=source.clock-paid} name value) continuation
        (output.1,restore source name output.2)) := by
  obtain ⟨callee,called,tLocal,keyLocal⟩:=environment source.code.lookup table p.key findCode
  let entry:=callEntryStateHOLFinite source callee
  have entryCells : HeaderCells entry table p:=⟨tLocal,keyLocal,cells.mapped,cells.capacity,cells.keyLength,cells.stride,cells.keys,cells.used⟩
  have queryEntry:=WitnessRadix.MemoryBytes.byteView_of_fields source entry rfl rfl rfl _ _ queryView
  have entryModel : KeyModel32 entry p (2^bits) tableModel := by
    constructor
    · exact model.used
    · intro i inside key value cell
      exact WitnessRadix.MemoryBytes.byteView_of_fields source entry rfl rfl rfl _ _ (model.view i inside key value cell)
  obtain ⟨paid,value,post,bound,run,frame,spec⟩:=dictionary32_find entry table p entryCells keyLength bits small capacity
    tableModel entryModel dictionary rep placed order room covered fits query queryEntry queryFits little hashCode memeqCode
    (by change 6*order.length+1≤source.clock-1;omega)
  have callerFrame : emptyLocalsHOLFinite post=emptyLocalsHOLFinite {source with clock:=source.clock-1-paid}:=frame
  have actual:=Input.CallNormal.pure_return_execute source post name (ofString "htab_find_slot") expressions _ body continuation callee value paid args called (by omega) run callerFrame
  have subtract : source.clock-1-paid=source.clock-(paid+1):=by omega
  exact ⟨paid+1,value,by omega,spec,by simpa only [subtract] using actual⟩

end InitECandidate.Solver.MutableTable.Find

#print axioms InitECandidate.Solver.MutableTable.Find.dictionary32_call
