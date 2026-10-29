import InitECandidate.Solver.PanFieldStores
import InitECandidate.Solver.WitnessRadix.AllocatedBytes
import InitECandidate.Solver.Input.OriginalEntry
import InitECandidate.Solver.Input.OriginalCode
import InitECandidate.Solver.Input.WordEnvironment
import InitECandidate.Solver.Input.QuietClock

namespace InitECandidate.Solver.Mpt.NodeInvalidate
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def body : ProgHOL 64:=match Guest.guestFn_node_invalidate with | .function fn=>progToHOL fn.body | _=>.skip
def formals : List (MlS×ShapeHOL):=[(ofString "nd",.one)]
def fields : List FieldStores.Field:=[⟨8,.literal 0#64⟩,⟨16,.literal 0#64⟩,⟨24,.literal 0#64⟩]
def post (source : PanSemStateFiniteExact 64 Guest.HostMemory) (node : BitVec 64):=
  {source with memory:=WordWrites.write source.memory (FieldStores.writes node fields)}

theorem body_shape : body=FieldStores.program "nd" "" fields (.return (.const 0#64)) := by
  simp only [body,Guest.guestFn_node_invalidate,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,
    fields,FieldStores.program,FieldStores.address,FieldStores.Value.expression,addConst,localVar]

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "node_invalidate")=some (formals,body,.one) := by
  have checked:=Input.OriginalCode.indexed code installed 233 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.Software.guestFn_node_invalidate) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,formals,body,Guest.Software.guestFn_node_invalidate,Guest.guestFn_node_invalidate,
    shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

theorem quiet (code) : Input.QuietClock.Preserves code body := by
  rw [body_shape]
  unfold fields FieldStores.program
  repeat first
    | apply Input.QuietClock.sequence
    | exact Input.QuietClock.store code _ _
    | exact Input.QuietClock.returned code _

/-- The original cache invalidation clears precisely its three metadata
words, retaining every other nonlocal field and spending no body ticks. -/
theorem execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (node : BitVec 64)
    (nd : source.locals.lookup (ofString "nd")=some (.val (.word node)))
    (domain : source.memaddrs=InitE.ordinaryDomain) (arena : AllocatedBytes.Arena node 32) (aligned : node.toNat%8=0) :
    evaluateHOLFiniteState source body=(some (.returned (.val (.word 0#64))),emptyLocalsHOLFinite (post source node)) := by
  have geometry (field : FieldStores.Field) (member : field∈fields) : field.offset<32 ∧ field.offset%8=0:=by
    simp only [fields,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl <;> exact ⟨by decide,by decide⟩
  have ready (field : FieldStores.Field) (member : field∈fields) : field.value.Ready source "" 0#64:=by
    simp only [fields,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl <;> trivial
  have avoid (reader : FieldStores.Field) (member : reader∈fields) (writer : FieldStores.Field) (writerIn : writer∈fields) :
      reader.value.Avoid 0#64 (node+BitVec.ofNat 64 writer.offset):=by
    simp only [fields,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl <;> trivial
  have run:=FieldStores.execute source "nd" "" node 0#64 fields nd ready
    (fun field member=>AllocatedBytes.word_mapped source node 32 field.offset domain arena (geometry field member).1 aligned (geometry field member).2)
    avoid (.return (.const 0#64))
  rw [body_shape,run]
  simp [evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact,sizeOfShapeWithContextHOL,post]

theorem post_away (source : PanSemStateFiniteExact 64 Guest.HostMemory) (node query : BitVec 64)
    (away8 : query≠node+8#64) (away16 : query≠node+16#64) (away24 : query≠node+24#64) :
    (post source node).memory query=source.memory query := by
  apply WordWrites.write_away
  simpa [FieldStores.writes,fields] using And.intro away8 (And.intro away16 away24)

end InitECandidate.Solver.Mpt.NodeInvalidate

#print axioms InitECandidate.Solver.Mpt.NodeInvalidate.body_shape
#print axioms InitECandidate.Solver.Mpt.NodeInvalidate.original_code
#print axioms InitECandidate.Solver.Mpt.NodeInvalidate.quiet
#print axioms InitECandidate.Solver.Mpt.NodeInvalidate.execute
#print axioms InitECandidate.Solver.Mpt.NodeInvalidate.post_away
