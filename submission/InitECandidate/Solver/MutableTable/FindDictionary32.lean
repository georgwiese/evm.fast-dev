import InitECandidate.Solver.MutableTable.FindSlotSpec32
import InitECandidate.Solver.MutableTable.FindLift32

namespace InitECandidate.Solver.MutableTable.Find
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
attribute [local instance] Classical.propDecidable

def hashHome (bits : Nat) (query : Key32) : Nat:=(Hash.keyHash query).toNat%(2^bits)
def modelKeys {Value : Type} (table : Model32 Value) (index : Nat) : Key32:=
  match table index with | none=>fun _=>0#8 | some (key,_)=>key

/-- Physical used bytes and a covering list of logical occupied slots supply
an executable chain, with no assumed table lookup execution. -/
theorem model_chain {Value : Type} (source : PanSemStateFiniteExact 64 Guest.HostMemory) (p : Parameters)
    (bits start : Nat) (small : bits<64) (startInside : start<2^bits)
    (capacity : p.capacity=BitVec.ofNat 64 (2^bits)) (table : Model32 Value) (model : KeyModel32 source p (2^bits) table)
    (order : List Nat) (room : order.length<2^bits)
    (covered : ∀ i<2^bits,table i≠none→i∈order)
    (fits : ∀ i<2^bits,(p.keys+BitVec.ofNat 64 i*p.stride).toNat+32<2^64) :
    ∃ length≤order.length,Nonempty (Chain32 source p (pathIndex bits start 0) length) := by
  have binary : ∀ i<2^bits,usedByte source p (BitVec.ofNat 64 i)=some 0 ∨ usedByte source p (BitVec.ofNat 64 i)=some 1 := by
    intro i inside
    have actual:=model.used i inside
    cases cell : table i with
    | none=>exact Or.inl (by simpa only [cell] using actual)
    | some pair=>exact Or.inr (by simpa only [cell] using actual)
  have actualCovered : ∀ i<2^bits,usedByte source p (BitVec.ofNat 64 i)=some 1→i∈order := by
    intro i inside occupied
    apply covered i inside
    intro empty
    have actual:=model.used i inside
    rw [empty] at actual
    rw [actual] at occupied
    cases occupied
  have views : ∀ i<2^bits,usedByte source p (BitVec.ofNat 64 i)=some 1→
      WitnessRadix.MemoryBytes.ByteView source (p.keys+BitVec.ofNat 64 i*p.stride) (modelKeys table i) := by
    intro i inside occupied
    cases cell : table i with
    | none=>
      have actual:=model.used i inside
      rw [cell] at actual
      rw [actual] at occupied
      cases occupied
    | some pair=>
      obtain ⟨key,value⟩:=pair
      simpa only [modelKeys,cell] using model.view i inside key value cell
  exact chain32_of_order source p bits start small startInside capacity order room (modelKeys table) binary actualCovered views fits

/-- Complete original32-byte find_slot computes the represented dictionary's
slot or absent sentinel, with all real setup/call/loop/scope work included.
The source construction/mutations must establish the physical/model premises. -/
theorem dictionary32_find {Value : Type} (source : PanSemStateFiniteExact 64 Guest.HostMemory) (tableAddress : BitVec 64) (p : Parameters)
    (cells : HeaderCells source tableAddress p) (keyLength : p.keyLength=32#64)
    (bits : Nat) (small : bits<64) (capacity : p.capacity=BitVec.ofNat 64 (2^bits))
    (table : Model32 Value) (model : KeyModel32 source p (2^bits) table)
    (dictionary : Key32→Option Value) (rep : Placement.Represents (2^bits) table dictionary)
    (placed : Placement.NoGaps (2^bits) (hashHome bits) table)
    (order : List Nat) (room : order.length<2^bits) (covered : ∀ i<2^bits,table i≠none→i∈order)
    (fits : ∀ i<2^bits,(p.keys+BitVec.ofNat 64 i*p.stride).toNat+32<2^64)
    (query : Key32) (queryView : WitnessRadix.MemoryBytes.ByteView source p.key query)
    (queryFits : p.key.toNat+32<2^64) (little : source.be=false)
    (hashCode : source.code.lookup (ofString "htab_hash")=some (Hash.formals,Hash.body,.one))
    (memeqCode : source.code.lookup (ofString "memeq")=some (WitnessRadix.Memeq32.formals,WitnessRadix.Memeq32.body,.one))
    (enough : 6*order.length+1≤source.clock) :
    ∃ paid value target,paid≤6*order.length+1 ∧
      evaluateHOLFiniteState source body=(some (.returned (.val (.word value))),target) ∧
      emptyLocalsHOLFinite target=emptyLocalsHOLFinite {source with clock:=source.clock-paid} ∧
      SlotSpec32 (2^bits) p.capacity value table dictionary query := by
  let hash:=Hash.keyHash query
  let index:=hash &&& (p.capacity-1#64)
  let entered:=prepared source p hash index
  have startInside : hashHome bits query<2^bits:=Nat.mod_lt _ (Nat.two_pow_pos bits)
  obtain ⟨length,bound,⟨chain⟩⟩:=model_chain source p bits (hashHome bits query) small startInside capacity table model order room covered fits
  have indexEq : index=pathIndex bits (hashHome bits query) 0:=masked_start p hash bits small capacity
  have locals : Locals entered p (pathIndex bits (hashHome bits query) 0) := by
    rw [← indexEq]
    exact prepared_locals source p hash index cells.keyLocal
  have queryEntered:=WitnessRadix.MemoryBytes.byteView_of_fields source entered rfl rfl rfl _ _ queryView
  obtain ⟨paid,paidBound,result,frame⟩:=tail32_execute source p _ length chain query entered locals keyLength rfl rfl rfl queryEntered queryFits little memeqCode
    (by change 6*length≤source.clock-1;omega)
  let value:=(answer chain query).getD p.capacity
  let post:=(evaluateHOLFiniteState entered afterIndex).2
  have run : evaluateHOLFiniteState entered afterIndex=(some (.returned (.val (.word value))),post):=Prod.ext result rfl
  have framePost : emptyLocalsHOLFinite post=emptyLocalsHOLFinite {entered with clock:=source.clock-1-paid}:=frame
  obtain ⟨target,whole,wholeFrame⟩:=lift_tail32 source tableAddress p cells keyLength query queryView queryFits little hashCode value paid post run framePost (by omega)
  have spec:=chain_slot_spec source p bits small capacity table model (hashHome bits)
    (by intro key;exact Nat.mod_lt _ (Nat.two_pow_pos bits)) placed dictionary rep query length chain (by omega)
  exact ⟨paid+1,value,target,by omega,whole,wholeFrame,spec⟩

end InitECandidate.Solver.MutableTable.Find

#print axioms InitECandidate.Solver.MutableTable.Find.model_chain
#print axioms InitECandidate.Solver.MutableTable.Find.dictionary32_find
