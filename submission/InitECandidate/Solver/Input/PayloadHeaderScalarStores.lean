import InitECandidate.Solver.Input.PayloadHeaderInputWords

namespace InitECandidate.Solver.Input.PayloadHeader
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch Main

def payloadFieldActions (fields : List (Nat×Nat)) : List CallPrefix.Action:=
  fields.map (fun field=>.command (storeField field.1 (PayloadHash.fieldExpression field.2)))
def payloadFieldsStored (input : Guest.InputBlob) (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64)
    (current : PanSemStateFiniteExact 64 Guest.HostMemory) : List (Nat×Nat)→PanSemStateFiniteExact 64 Guest.HostMemory
  | []=>current
  | field::rest=>payloadFieldsStored input source heap (storedField current heap field.1 (inputWord input source field.2)) rest

/-- Compose the real scalar-load/header-store commands while deriving each
load from the original decoded record and the maintained memory frame. -/
theorem payload_fields_from_execution (input : Guest.InputBlob) (origin source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap root : BitVec 64) (counts : Nat→BitVec 64) (prepared : RequestRootHashData.Prepared input origin root counts)
    (before : root.toNat≤heap.toNat) (domain : source.memaddrs=InitE.ordinaryDomain)
    (arena : AllocatedBytes.Arena heap 248) (aligned : heap.toNat%8=0)
    (fields : List (Nat×Nat)) (tail : List CallPrefix.Action)
    (valid : ∀ field∈fields,field.1<248 ∧ field.1%8=0 ∧ field.2<136 ∧ field.2%8=0)
    (current target : PanSemStateFiniteExact 64 Guest.HostMemory) (frame : HeaderFrame input source heap current)
    (execution : CallPrefix.Execution current (payloadFieldActions fields++tail) target) :
    HeaderFrame input source heap (payloadFieldsStored input source heap current fields) ∧
      CallPrefix.Execution (payloadFieldsStored input source heap current fields) tail target := by
  induction fields generalizing current with
  | nil=>exact ⟨frame,execution⟩
  | cons field rest ih=>
    obtain ⟨inside,fieldAligned,payloadInside,payloadAligned⟩:=valid field (by simp)
    have readValue:=frame.payload_read input origin source current heap root counts prepared before domain field.2 payloadInside payloadAligned
    have run:=store_field_execute current heap field.1 (inputWord input source field.2) (PayloadHash.fieldExpression field.2)
      (frame.domain.trans domain) arena aligned inside fieldAligned frame.header readValue
    have next:=execution.command_known _ _ run
    have nextFrame:=frame.stored input source current heap field.1 (inputWord input source field.2) arena inside
    exact ih (by intro item member; exact valid item (List.mem_cons_of_mem _ member)) _ nextFrame next

end InitECandidate.Solver.Input.PayloadHeader

#print axioms InitECandidate.Solver.Input.PayloadHeader.payload_fields_from_execution
