import InitECandidate.Solver.Mpt.NodeRlpBeginLengthNormal

namespace InitECandidate.Solver.Mpt.NodeRlpBegin
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open KeyToNibbles (SpanFrame)

/-- Present operands immediately before the real compact writer. Only
the leaf's two value fields must avoid its output; actual allocation will
derive this separation from the persistent heap frontier. -/
structure CompactData (source : PanSemStateFiniteExact 64 Guest.HostMemory) (node tag buffer pathLength : BitVec 64)
    (limit : Nat) (property : BitVec 64→BitVec 64→Prop) where
  pointer : BitVec 64
  leaf : BitVec 64
  nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node))
  tagCell : source.locals.lookup (ofString "k")=some (.val (.word tag))
  bufferCell : source.locals.lookup (ofString "cbuf")=some (.val (.word buffer))
  pathCell : source.locals.lookup (ofString "nlen")=some (.val (.word pathLength))
  leafCell : source.locals.lookup (ofString "isl")=some (.val (.word leaf))
  pointerMapped : source.memaddrs (node+32#64)
  pointerStored : source.memory (node+32#64)=.word pointer
  bufferMapped : source.memaddrs (panByteAlignHOL (width:=64) buffer)
  value : tag=1#64→TrieWalk.ValueView source.memory source.memaddrs node 48#64 56#64 limit property
  valueAway : tag=1#64→∀ offset<pathLength.toNat/2+1,
    node+48#64≠panByteAlignHOL (width:=64) (byteAddress buffer offset) ∧ node+56#64≠panByteAlignHOL (width:=64) (byteAddress buffer offset)

structure LengthData (source : PanSemStateFiniteExact 64 Guest.HostMemory) (node tag buffer : BitVec 64)
    (limit : Nat) (property : BitVec 64→BitVec 64→Prop) where
  length : BitVec 64
  nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node))
  tagCell : source.locals.lookup (ofString "k")=some (.val (.word tag))
  bufferCell : source.locals.lookup (ofString "cbuf")=some (.val (.word buffer))
  lengthCell : source.locals.lookup (ofString "clen")=some (.val (.word length))
  mapped : source.memaddrs (panByteAlignHOL (width:=64) buffer)
  value : tag=1#64→TrieWalk.ValueView source.memory source.memaddrs node 48#64 56#64 limit property

theorem compact_arguments (source : PanSemStateFiniteExact 64 Guest.HostMemory) (node tag buffer pathLength : BitVec 64)
    (limit : Nat) (property : BitVec 64→BitVec 64→Prop) (data : CompactData source node tag buffer pathLength limit property) :
    evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) compactArguments=
      some [.val (.word data.pointer),.val (.word pathLength),.val (.word data.leaf),.val (.word buffer)] := by
  simp [compactArguments,nodeField,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,data.nodeCell,data.pathCell,data.leafCell,data.bufferCell,
    valueIsWord,valueWord,wordOpHOL,wordOp,memLoadHOLExact,isWfShapeExactHOL,data.pointerMapped,data.pointerStored]

/-- A real continuing compact call derives the exact current output
length and transports the actual leaf fields through its bounded writes. -/
theorem after_compact (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (node tag buffer pathLength : BitVec 64)
    (limit : Nat) (property : BitVec 64→BitVec 64→Prop) (data : CompactData source node tag buffer pathLength limit property)
    (installed : Input.OriginalCode.Installed source.code) (normal : evaluateHOLFiniteState source compactCall=(none,target)) :
    ∃ next : LengthData target node tag buffer limit property,next.length.toNat=pathLength.toNat/2+1 ∧
      Input.OriginalCode.Installed target.code ∧ SpanFrame source target buffer (pathLength.toNat/2+1) ∧
      (∀ other,ofString "clen"≠other→target.locals.lookup other=source.locals.lookup other) := by
  obtain ⟨length,lengthCell,size,kept,_price,frame⟩:=NibblesCompact.assigned_normal source target data.pointer pathLength data.leaf buffer installed
    (ofString "clen") compactArguments (compact_arguments source node tag buffer pathLength limit property data) normal
  have domain:=congrArg PanSemStateFiniteExact.memaddrs frame.fields
  change target.memaddrs=source.memaddrs at domain
  have codes:=congrArg PanSemStateFiniteExact.code frame.fields
  change target.code=source.code at codes
  let next : LengthData target node tag buffer limit property:={
    length:=length
    nodeCell:=(kept (ofString "node") (by decide)).trans data.nodeCell
    tagCell:=(kept (ofString "k") (by decide)).trans data.tagCell
    bufferCell:=(kept (ofString "cbuf") (by decide)).trans data.bufferCell
    lengthCell:=lengthCell
    mapped:=by rw [domain]; exact data.bufferMapped
    value:=fun leaf=>(data.value leaf).of_agreement source.memory target.memory source.memaddrs target.memaddrs node 48#64 56#64 limit domain
      (frame.memory (node+48#64) (fun offset inside=>(data.valueAway leaf offset inside).1))
      (frame.memory (node+56#64) (fun offset inside=>(data.valueAway leaf offset inside).2)) }
  exact ⟨next,size,by rw [codes]; exact installed,frame,kept⟩

theorem compact_phase_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (node tag buffer pathLength : BitVec 64)
    (limit : Nat) (property : BitVec 64→BitVec 64→Prop) (data : CompactData source node tag buffer pathLength limit property)
    (fits : pathLength.toNat/2+limit+19<2^64) (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source compactAndLengths).2.clock≤pathLength.toNat/2+24 := by
  rw [path_shapes.2.2.2.2.1]
  have price:=Input.ClockCost.sequence_reached_current source compactCall lengthScope (pathLength.toNat/2+1) 23
    (NibblesCompact.call_cost source data.pointer pathLength data.leaf buffer installed (some (some (ofString "clen"))) compactArguments
      (compact_arguments source node tag buffer pathLength limit property data)) (by
        intro current run
        obtain ⟨next,size,nextInstalled,_frame,_kept⟩:=after_compact source current node tag buffer pathLength limit property data installed run
        exact length_scope_cost current node tag buffer next.length limit property next.value (by rw [size]; omega) (by omega)
          nextInstalled next.nodeCell next.tagCell next.bufferCell next.lengthCell next.mapped)
  omega

end InitECandidate.Solver.Mpt.NodeRlpBegin

#print axioms InitECandidate.Solver.Mpt.NodeRlpBegin.compact_arguments
#print axioms InitECandidate.Solver.Mpt.NodeRlpBegin.after_compact
#print axioms InitECandidate.Solver.Mpt.NodeRlpBegin.compact_phase_cost
