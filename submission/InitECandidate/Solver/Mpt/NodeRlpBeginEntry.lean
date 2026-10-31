import InitECandidate.Solver.Mpt.NodeRlpBeginPathLength
import InitECandidate.Solver.Mpt.TrieGraphRegions

namespace InitECandidate.Solver.Mpt.NodeRlpBegin
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Current registered non-hash node and persistent heap facts. All data
concern the incoming state; actual allocation room and output descriptors
are derived by the original begin execution. -/
structure Entry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (node heap : BitVec 64)
    (lower limit : Nat) (property : BitVec 64→BitVec 64→Prop) where
  graph : TrieWalk.Graph source.memory source.memaddrs
  member : graph.valid node
  active : node≠0#64
  nonHash : wordAt source.memory node≠0#64
  values : TrieWalk.Values graph limit property
  regions : graph.Regions lower heap.toNat
  heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap))
  heapLower : 2701131776≤heap.toNat
  heapUpper : heap.toNat≤2952790016
  heapAligned : heap.toNat%8=0
  domain : source.memaddrs=InitE.ordinaryDomain

def Entry.bind (source : PanSemStateFiniteExact 64 Guest.HostMemory) (node heap : BitVec 64) (lower limit : Nat)
    (property : BitVec 64→BitVec 64→Prop) (data : Entry source node heap lower limit property) (name : String) (word : BitVec 64) :
    Entry (WitnessRadix.QueryBranch.bind source name word) node heap lower limit property :={
  graph:=data.graph
  member:=data.member
  active:=data.active
  nonHash:=data.nonHash
  values:=data.values
  regions:=data.regions
  heapCell:=data.heapCell
  heapLower:=data.heapLower
  heapUpper:=data.heapUpper
  heapAligned:=data.heapAligned
  domain:=data.domain }

theorem tag_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (node heap : BitVec 64) (lower limit : Nat)
    (property : BitVec 64→BitVec 64→Prop) (data : Entry source node heap lower limit property)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node))) :
    eval source (nodeField 0)=some (.val (.word (wordAt source.memory node))) := by
  have header:=data.graph.header node data.member data.active
  simp [eval,nodeField,evalHOLExact,evalListHOLExact,toExact,localVar,nodeCell,valueIsWord,valueWord,wordOpHOL,wordOp,
    memLoadHOLExact,isWfShapeExactHOL,header.1,header.2]

theorem path_size_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (node heap : BitVec 64) (lower limit : Nat)
    (property : BitVec 64→BitVec 64→Prop) (data : Entry source node heap lower limit property)
    (pathTag : wordAt source.memory node=1#64 ∨ wordAt source.memory node=2#64)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node))) :
    eval source (nodeField 40)=some (.val (.word (wordAt source.memory (node+40#64)))) := by
  let view:=data.graph.path node data.member data.active pathTag
  have stored : source.memory (node+40#64)=.word (wordAt source.memory (node+40#64)):=by
    rw [view.size_word source.memory source.memaddrs node]
    exact view.sizeStored
  simp [eval,nodeField,evalHOLExact,evalListHOLExact,toExact,localVar,nodeCell,valueIsWord,valueWord,wordOpHOL,wordOp,
    memLoadHOLExact,isWfShapeExactHOL,view.sizeMapped,stored]

/-- Registered node/value ownership derives the current PathInput at
the actual nlen declaration. Its older value-word bounds follow from the
real node allocation extent, without a future preservation premise. -/
def path_input (source : PanSemStateFiniteExact 64 Guest.HostMemory) (node heap oldBuffer : BitVec 64) (lower limit : Nat)
    (property : BitVec 64→BitVec 64→Prop) (data : Entry source node heap lower limit property)
    (pathTag : wordAt source.memory node=1#64 ∨ wordAt source.memory node=2#64)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node)))
    (tagCell : source.locals.lookup (ofString "k")=some (.val (.word (wordAt source.memory node))))
    (bufferCell : source.locals.lookup (ofString "cbuf")=some (.val (.word oldBuffer))) :
    PathInput (bind source "nlen" (wordAt source.memory (node+40#64))) node (wordAt source.memory node)
      (wordAt source.memory (node+40#64)) limit property := by
  let view:=data.graph.path node data.member data.active pathTag
  refine {
    pointer:=view.pointer
    heap:=heap
    oldBuffer:=oldBuffer
    nodeCell:=(bind_lookup_other source "nlen" "node" _ (by decide)).trans nodeCell
    tagCell:=(bind_lookup_other source "nlen" "k" _ (by decide)).trans tagCell
    pathCell:=bind_lookup_same _ _ _
    bufferCell:=(bind_lookup_other source "nlen" "cbuf" _ (by decide)).trans bufferCell
    pointerMapped:=view.pointerMapped
    pointerStored:=view.pointerStored
    heapCell:=data.heapCell
    heapLower:=data.heapLower
    heapUpper:=data.heapUpper
    heapAligned:=data.heapAligned
    domain:=data.domain
    value:=fun leaf=>data.values.leaf node data.member data.active leaf
    valueBelow:=fun leaf=>⟨(data.graph.value_bounds lower heap.toNat data.regions _ (.leafPointer node data.member data.active leaf)).2,
      (data.graph.value_bounds lower heap.toNat data.regions _ (.leafLength node data.member data.active leaf)).2⟩ }

theorem path_scope_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (node heap oldBuffer : BitVec 64) (lower limit : Nat)
    (property : BitVec 64→BitVec 64→Prop) (data : Entry source node heap lower limit property)
    (pathTag : wordAt source.memory node=1#64 ∨ wordAt source.memory node=2#64)
    (valueFits : limit+19≤2^63) (installed : Input.OriginalCode.Installed source.code)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node)))
    (tagCell : source.locals.lookup (ofString "k")=some (.val (.word (wordAt source.memory node))))
    (bufferCell : source.locals.lookup (ofString "cbuf")=some (.val (.word oldBuffer))) :
    source.clock-(evaluateHOLFiniteState source pathScope).2.clock≤(wordAt source.memory (node+40#64)).toNat/2+26 := by
  rw [path_shapes.1]
  apply Input.ClockCost.declared_current source "nlen" (nodeField 40) (wordAt source.memory (node+40#64)) afterPathLength _
    (path_size_read source node heap lower limit property data pathTag nodeCell)
  exact after_path_length_cost _ node (wordAt source.memory node) (wordAt source.memory (node+40#64)) limit property
    (path_input source node heap oldBuffer lower limit property data pathTag nodeCell tagCell bufferCell)
    (by have :=(wordAt source.memory (node+40#64)).isLt; omega) installed

end InitECandidate.Solver.Mpt.NodeRlpBegin

#print axioms InitECandidate.Solver.Mpt.NodeRlpBegin.Entry.bind
#print axioms InitECandidate.Solver.Mpt.NodeRlpBegin.tag_read
#print axioms InitECandidate.Solver.Mpt.NodeRlpBegin.path_size_read
#print axioms InitECandidate.Solver.Mpt.NodeRlpBegin.path_input
#print axioms InitECandidate.Solver.Mpt.NodeRlpBegin.path_scope_cost
