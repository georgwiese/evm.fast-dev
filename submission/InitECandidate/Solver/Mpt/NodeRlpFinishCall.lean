import InitECandidate.Solver.Mpt.NodeRlpFinishPathNormal
import InitECandidate.Solver.Input.IgnoredCallNormal
import InitECandidate.Solver.Input.IgnoredCallTarget

namespace InitECandidate.Solver.Mpt.NodeRlpFinish
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The actual saved preparation words, independent of any caller locals. -/
structure Record (source : PanSemStateFiniteExact 64 Guest.HostMemory) (frame node tag compact length payload : BitVec 64) : Prop where
  headerMapped : source.memaddrs node
  headerStored : source.memory node=.word tag
  payloadMapped : source.memaddrs (frame+40#64)
  payloadStored : source.memory (frame+40#64)=.word payload
  bufferMapped : source.memaddrs (frame+24#64)
  bufferStored : source.memory (frame+24#64)=.word compact
  lengthMapped : source.memaddrs (frame+32#64)
  lengthStored : source.memory (frame+32#64)=.word length

theorem Record.entry {source : PanSemStateFiniteExact 64 Guest.HostMemory} {frame node tag compact length payload : BitVec 64}
    (record : Record source frame node tag compact length payload)
    (frameCell : source.locals.lookup (ofString "fr")=some (.val (.word frame)))
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node))) : PreparedEntry source frame node tag compact length payload :=
  ⟨frameCell,nodeCell,record.headerMapped,record.headerStored,record.payloadMapped,record.payloadStored,
    record.bufferMapped,record.bufferStored,record.lengthMapped,record.lengthStored⟩

theorem Record.of_memory {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {frame node tag compact length payload : BitVec 64}
    (record : Record source frame node tag compact length payload) (domain : target.memaddrs=source.memaddrs)
    (header : target.memory node=source.memory node)
    (buffer : target.memory (frame+24#64)=source.memory (frame+24#64))
    (lengthMemory : target.memory (frame+32#64)=source.memory (frame+32#64))
    (payloadMemory : target.memory (frame+40#64)=source.memory (frame+40#64)) : Record target frame node tag compact length payload :=
  ⟨by rw [domain]; exact record.headerMapped,header.trans record.headerStored,
    by rw [domain]; exact record.payloadMapped,payloadMemory.trans record.payloadStored,
    by rw [domain]; exact record.bufferMapped,buffer.trans record.bufferStored,
    by rw [domain]; exact record.lengthMapped,lengthMemory.trans record.lengthStored⟩

/-- Actual saved descriptors and exact sizing decisions for a live frame.
Its fresh compact extent lies between the original node frontier and heap. -/
structure Prepared (source : PanSemStateFiniteExact 64 Guest.HostMemory) (frame node : BitVec 64) (lower upper : Nat) where
  tag : BitVec 64
  compact : BitVec 64
  length : BitVec 64
  payload : BitVec 64
  record : Record source frame node tag compact length payload
  nonHash : tag≠0#64
  branch : tag=3#64 → payload=0#64
  sizing : tag≠3#64 → NodeRlpBegin.PathPayload source node tag compact length payload
  compactLower : tag≠3#64 → lower≤compact.toNat
  compactAligned : tag≠3#64 → compact.toNat%8=0
  compactUpper : tag≠3#64 → compact.toNat+length.toNat≤upper
  lengthSmall : tag≠3#64 → length.toNat+32<2^64
  payloadSmall : tag≠3#64 → payload.toNat+42<2^64

def Prepared.of_frame {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {frame node : BitVec 64} {lower upper : Nat}
    (prepared : Prepared source frame node lower upper) (same : Input.LocalEffects.erase target=Input.LocalEffects.erase source) : Prepared target frame node lower upper := by
  have domain:=congrArg PanSemStateFiniteExact.memaddrs same
  change target.memaddrs=source.memaddrs at domain
  have memory:=Input.LocalEffects.memory_of_erase source target same
  exact {tag:=prepared.tag,compact:=prepared.compact,length:=prepared.length,payload:=prepared.payload
         record:=prepared.record.of_memory domain (congrFun memory _) (congrFun memory _) (congrFun memory _) (congrFun memory _)
         nonHash:=prepared.nonHash,branch:=prepared.branch,sizing:=fun notBranch=>(prepared.sizing notBranch).of_frame same
         compactLower:=prepared.compactLower,compactAligned:=prepared.compactAligned,compactUpper:=prepared.compactUpper,lengthSmall:=prepared.lengthSmall,payloadSmall:=prepared.payloadSmall}

def Prepared.weaken {source : PanSemStateFiniteExact 64 Guest.HostMemory} {frame node : BitVec 64} {lower upper smaller larger : Nat}
    (prepared : Prepared source frame node lower upper) (first : smaller≤lower) (last : upper≤larger) : Prepared source frame node smaller larger :=
  {prepared with compactLower:=fun notBranch=>first.trans (prepared.compactLower notBranch)
                 compactUpper:=fun notBranch=>(prepared.compactUpper notBranch).trans last}

/-- The real begin result constructs the saved record and true compact
extent. Exact payload arithmetic is transported through its actual stores. -/
def Prepared.of_begin {origin source : PanSemStateFiniteExact 64 Guest.HostMemory} {node heap frame : BitVec 64}
    {lower limit allowance : Nat} {property : BitVec 64 → BitVec 64 → Prop} {value : ValueHOL 64}
    (output : NodeRlpBegin.Output origin source node heap frame limit value allowance)
    (data : NodeRlpBegin.Entry origin node heap lower limit property)
    (valueFits : limit+19≤2^63) (frameArena : AllocatedBytes.Arena frame 48) (scratch : 2952790016≤frame.toNat)
    (valueLow : wordAt origin.memory node=1#64 → wordAt origin.memory (node+56#64)=1#64 →
      (panByteAlignHOL (width:=64) (wordAt origin.memory (node+48#64))).toNat<2952790016) :
    Prepared source frame node heap.toNat (NodeRlpBegin.outputHeap origin node heap).toNat := by
  have header:=data.graph.header node data.member data.active
  have before:=(data.graph.footprint_bounds lower heap.toNat data.regions node (.header node data.member data.active)).2
  have memory:=output.before_heap frameArena scratch data.heapUpper node before
  have record : Record source frame node (wordAt origin.memory node) output.buffer output.length output.payload:=
    ⟨by rw [output.domain]; exact header.1,memory.trans header.2,
      by rw [output.domain]; exact output.mapped.2.2,output.payloadStored,
      by rw [output.domain]; exact output.mapped.1,output.bufferStored,
      by rw [output.domain]; exact output.mapped.2.1,output.lengthStored⟩
  refine {tag:=wordAt origin.memory node,compact:=output.buffer,length:=output.length,payload:=output.payload,record:=record,nonHash:=data.nonHash
          branch:=fun branch=>(output.branch branch).2.2
          sizing:=fun notBranch=>output.path_payload data notBranch scratch (by have room:=frameArena.upper; omega) valueLow
          compactLower:=?_,compactAligned:=?_,compactUpper:=?_,lengthSmall:=?_,payloadSmall:=?_}
  · intro notBranch
    rw [(output.path notBranch).1]
  · intro notBranch
    rw [(output.path notBranch).1]
    exact data.heapAligned
  · intro notBranch
    have path:=output.path notBranch
    have room : heap.toNat+(NodeRlpBegin.allocationAmount (wordAt origin.memory (node+40#64))).toNat≤2952790016:=by
      rw [NodeRlpBegin.allocation_amount]
      have bound:=path.2.2.2.2
      omega
    have grows:=(PersistentAlloc.guards heap (NodeRlpBegin.allocationAmount (wordAt origin.memory (node+40#64))) room).2.2.1
    rw [NodeRlpBegin.allocation_amount] at grows
    rw [path.1,NodeRlpBegin.outputHeap,if_neg notBranch]
    have length:=path.2.1
    omega
  · intro notBranch
    have path:=output.path notBranch
    have length:=path.2.1
    have room:=path.2.2.2.2
    omega
  · intro notBranch
    have path:=output.path notBranch
    have payload:=path.2.2.2.1
    have room:=path.2.2.2.2
    omega

/-- Only the saved record and genuine sizing-decision words must survive
intervening work. Future helper outcomes are not part of this footprint. -/
def Prepared.Footprint {source : PanSemStateFiniteExact 64 Guest.HostMemory} {frame node : BitVec 64} {lower upper : Nat}
    (prepared : Prepared source frame node lower upper) (query : BitVec 64) : Prop :=
  (query=node ∨ query=frame+24#64 ∨ query=frame+32#64 ∨ query=frame+40#64) ∨
    (prepared.tag≠3#64 ∧ NodeRlpBegin.PathPayload.Footprint source node prepared.tag prepared.compact prepared.length query)

def Prepared.of_memory {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {frame node : BitVec 64} {lower upper : Nat}
    (prepared : Prepared source frame node lower upper) (domain : target.memaddrs=source.memaddrs) (endian : target.be=source.be)
    (memory : ∀ query,prepared.Footprint query → target.memory query=source.memory query) : Prepared target frame node lower upper := by
  exact {
    tag:=prepared.tag,compact:=prepared.compact,length:=prepared.length,payload:=prepared.payload
    record:=prepared.record.of_memory domain (memory _ (Or.inl (Or.inl rfl)))
      (memory _ (Or.inl (Or.inr (Or.inl rfl)))) (memory _ (Or.inl (Or.inr (Or.inr (Or.inl rfl)))))
      (memory _ (Or.inl (Or.inr (Or.inr (Or.inr rfl)))))
    nonHash:=prepared.nonHash,branch:=prepared.branch
    sizing:=fun notBranch=>(prepared.sizing notBranch).of_memory domain endian (fun query required=>memory query (Or.inr ⟨notBranch,required⟩))
    compactLower:=prepared.compactLower,compactAligned:=prepared.compactAligned,compactUpper:=prepared.compactUpper
    lengthSmall:=prepared.lengthSmall,payloadSmall:=prepared.payloadSmall}

/-- The actual compact first-byte decision lies in the prepared persistent
band, using the real allocator's alignment rather than a rounded-down guess. -/
theorem Prepared.compact_byte_bounds {source : PanSemStateFiniteExact 64 Guest.HostMemory} {frame node : BitVec 64} {lower upper : Nat}
    (prepared : Prepared source frame node lower upper) (notBranch : prepared.tag≠3#64) (one : prepared.length=1#64) :
    lower≤(panByteAlignHOL (width:=64) prepared.compact).toNat ∧ (panByteAlignHOL (width:=64) prepared.compact).toNat<upper := by
  have aligned:=prepared.compactAligned notBranch
  have before:=prepared.compactLower notBranch
  have afterBuffer:=prepared.compactUpper notBranch
  have number : prepared.length.toNat=1:=by rw [one]; rfl
  rw [AllocatedBytes.aligned_number]
  omega


/-- Prepared decision words are either old persistent words or saved
scratch descriptors at offsets24/32/40, never a frame's mutable index16. -/
theorem Prepared.footprint_bands {source : PanSemStateFiniteExact 64 Guest.HostMemory} {ownerFrame owner heap : BitVec 64} {frontier : Nat}
    (prepared : Prepared source ownerFrame owner frontier heap.toNat)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (ownerMember : graph.valid owner) (ownerActive : owner≠0#64)
    (lower upper inputEnd limit cursor : Nat) (regions : graph.Regions lower upper) (beforeHeap : upper≤heap.toNat)
    (values : TrieWalk.Values graph limit (fun pointer length=>pointer.toNat+length.toNat≤inputEnd)) (inputBefore : inputEnd≤heap.toNat)
    (frameArena : AllocatedBytes.Arena ownerFrame 48) (frameAfter : cursor≤ownerFrame.toNat+24)
    (query : BitVec 64) (required : prepared.Footprint query) : query.toNat<heap.toNat ∨ cursor≤query.toNat := by
  have nodeBefore (offset : Nat) (inside : offset<TrieWalk.nodeBytes (wordAt source.memory owner)) :
      (byteAddress owner offset).toNat<heap.toNat:=
    (graph.region_query_bounds lower upper regions owner offset ownerMember ownerActive inside).2.trans_le beforeHeap
  have recordAfter (offset : Nat) (first : 24≤offset) (last : offset≤40) : cursor≤(ownerFrame+BitVec.ofNat 64 offset).toNat:=by
    have number:=byteAddress_toNat ownerFrame offset (by have room:=frameArena.upper; omega)
    change cursor≤(byteAddress ownerFrame offset).toNat
    rw [number]
    omega
  have ownerTag (leaf : prepared.tag=1#64) : wordAt source.memory owner=1#64:=by
    simp [wordAt,prepared.record.headerStored,MemoryBytes.wordBits,leaf]
  rcases required with equal|⟨notBranch,sizing⟩
  · rcases equal with equal|equal|equal|equal
    · left
      rw [equal]
      simpa only [byteAddress,BitVec.add_zero] using nodeBefore 0 (by have minimum:=TrieWalk.nodeBytes_bounds (wordAt source.memory owner); omega)
    · exact Or.inr (by rw [equal]; exact recordAfter 24 (by decide) (by decide))
    · exact Or.inr (by rw [equal]; exact recordAfter 32 (by decide) (by decide))
    · exact Or.inr (by rw [equal]; exact recordAfter 40 (by decide) (by decide))
  · rcases sizing with ⟨leaf,equal|equal⟩|⟨one,equal⟩|⟨leaf,one,equal⟩
    · exact Or.inl (by rw [equal]; exact nodeBefore 48 (by rw [ownerTag leaf]; decide))
    · exact Or.inl (by rw [equal]; exact nodeBefore 56 (by rw [ownerTag leaf]; decide))
    · exact Or.inl (by rw [equal]; exact (prepared.compact_byte_bounds notBranch one).2)
    · let view:=values.leaf owner ownerMember ownerActive (ownerTag leaf)
      have pointerWord : wordAt source.memory (owner+48#64)=view.pointer:=by simp [wordAt,view.pointerStored,MemoryBytes.wordBits]
      have lengthWord : wordAt source.memory (owner+56#64)=view.length:=by simp [wordAt,view.lengthStored,MemoryBytes.wordBits]
      have lengthOne : view.length.toNat=1:=by rw [←lengthWord,one]; rfl
      left
      rw [equal,pointerWord,AllocatedBytes.aligned_number]
      have bound:=view.extra
      omega


/-- Existing graph/value/layout facts at a real finish call. The value
property records the earlier input region used by the indexed serializer. -/
structure Entry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (node heap frame : BitVec 64)
    (lower upper inputEnd cacheLimit valueLimit : Nat) where
  graph : TrieWalk.Graph source.memory source.memaddrs
  member : graph.valid node
  active : node≠0#64
  nonHash : wordAt source.memory node≠0#64
  values : TrieWalk.Values graph valueLimit (fun pointer length=>pointer.toNat+length.toNat≤inputEnd)
  regions : graph.Regions lower upper
  disjoint : graph.Disjoint
  paths : graph.PathBytes source.be
  pathRegions : graph.PathRegions lower upper
  separated : graph.PathSeparated
  lowerAligned : lower%8=0
  stp : BitVec 64
  pad : BitVec 64
  environment : CurrentKeccak.Hash.Environment source stp pad
  heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap))
  heapLower : 2701131776≤heap.toNat
  heapUpper : heap.toNat≤2952790016
  heapAligned : heap.toNat%8=0
  beforeHeap : upper≤heap.toNat
  stateBefore : stp.toNat+200≤lower
  padBefore : pad.toNat+136≤lower
  inputBeforeState : inputEnd≤stp.toNat
  inputBeforePad : inputEnd≤pad.toNat
  cached : CachedLengths graph cacheLimit
  cacheSmall : cacheLimit+136<2^64
  valueSmall : valueLimit+546<2^64
  prepared : Prepared source frame node upper heap.toNat

def Entry.call {source : PanSemStateFiniteExact 64 Guest.HostMemory} {node heap frame : BitVec 64}
    {lower upper inputEnd cacheLimit valueLimit : Nat} (data : Entry source node heap frame lower upper inputEnd cacheLimit valueLimit)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) : Entry (callEntryStateHOLFinite source callee) node heap frame lower upper inputEnd cacheLimit valueLimit :=
  {data with environment:=data.environment.of_frame rfl,prepared:=data.prepared.of_frame rfl}

theorem Entry.tag_cases {source : PanSemStateFiniteExact 64 Guest.HostMemory} {node heap frame : BitVec 64}
    {lower upper inputEnd cacheLimit valueLimit : Nat} (data : Entry source node heap frame lower upper inputEnd cacheLimit valueLimit) :
    data.prepared.tag=1#64 ∨ data.prepared.tag=2#64 ∨ data.prepared.tag=3#64 := by
  have actual : wordAt source.memory node=data.prepared.tag:=by simp [wordAt,data.prepared.record.headerStored,MemoryBytes.wordBits]
  have bound:=data.graph.kindBound node data.member data.active
  have positive : (wordAt source.memory node).toNat≠0:=fun zero=>data.nonHash (BitVec.eq_of_toNat_eq zero)
  have cases : (wordAt source.memory node).toNat=1 ∨ (wordAt source.memory node).toNat=2 ∨ (wordAt source.memory node).toNat=3:=by omega
  rcases cases with leaf|extension|branch
  · exact Or.inl (actual.symm.trans (BitVec.eq_of_toNat_eq leaf))
  · exact Or.inr (Or.inl (actual.symm.trans (BitVec.eq_of_toNat_eq extension)))
  · exact Or.inr (Or.inr (actual.symm.trans (BitVec.eq_of_toNat_eq branch)))

theorem Entry.input_before_heap {source : PanSemStateFiniteExact 64 Guest.HostMemory} {node heap frame : BitVec 64}
    {lower upper inputEnd cacheLimit valueLimit : Nat} (data : Entry source node heap frame lower upper inputEnd cacheLimit valueLimit) : inputEnd≤heap.toNat := by
  have parent:=data.regions node data.member data.active
  have input:=data.inputBeforeState
  have workspace:=data.stateBefore
  have heap:=data.beforeHeap
  omega

theorem Entry.queries_before_heap {source : PanSemStateFiniteExact 64 Guest.HostMemory} {node heap frame : BitVec 64}
    {lower upper inputEnd cacheLimit valueLimit : Nat} (data : Entry source node heap frame lower upper inputEnd cacheLimit valueLimit)
    (query : BitVec 64) (required : SerializerQueries data.graph inputEnd query) : query.toNat<heap.toNat := by
  rcases required with field|⟨owner,member,active,tag,index,inside,equal⟩
  · rcases field with ⟨owner,offset,member,active,inside,_notHash,equal⟩|input
    · rw [equal]
      exact ((data.graph.region_query_bounds lower upper data.regions owner offset member active inside).2).trans_le data.beforeHeap
    · exact input.trans_le data.input_before_heap
  · have span:=data.paths.span owner member active tag
    have bounds:=data.pathRegions owner member active tag
    have number:=byteAddress_toNat (wordAt source.memory (owner+32#64)) index (by have fits:=span.fits; omega)
    rw [equal,AllocatedBytes.aligned_number,number]
    have before:=data.beforeHeap
    omega

theorem Entry.queries_before_heap_band {source : PanSemStateFiniteExact 64 Guest.HostMemory} {node heap frame : BitVec 64}
    {lower upper inputEnd cacheLimit valueLimit : Nat} (data : Entry source node heap frame lower upper inputEnd cacheLimit valueLimit)
    (query : BitVec 64) (required : WithBand (SerializerQueries data.graph inputEnd) upper heap.toNat query) : query.toNat<heap.toNat := by
  rcases required with original|band
  · exact data.queries_before_heap query original
  · exact band.2

def finishAllowance (tag length : BitVec 64) (cacheLimit valueLimit : Nat) : Nat:=
  if tag=3#64 then branchAllowance cacheLimit valueLimit else
    if tag=1#64 then Input.CopyAny.price length.toNat+Input.CopyAny.price valueLimit+75 else
      Input.CopyAny.price length.toNat+CurrentKeccak.Hash.bodyPrice cacheLimit+103


theorem Entry.tag {source : PanSemStateFiniteExact 64 Guest.HostMemory} {node heap frame : BitVec 64}
    {lower upper inputEnd cacheLimit valueLimit : Nat} (data : Entry source node heap frame lower upper inputEnd cacheLimit valueLimit) :
    wordAt source.memory node=data.prepared.tag := by simp [wordAt,data.prepared.record.headerStored,MemoryBytes.wordBits]

theorem Entry.branch_entry {source : PanSemStateFiniteExact 64 Guest.HostMemory} {node heap frame : BitVec 64}
    {lower upper inputEnd cacheLimit valueLimit : Nat} (data : Entry source node heap frame lower upper inputEnd cacheLimit valueLimit)
    (branch : data.prepared.tag=3#64)
    (frameCell : source.locals.lookup (ofString "fr")=some (.val (.word frame)))
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node))) : BranchEntry source frame node :=
  ⟨frameCell,nodeCell,data.prepared.record.headerMapped,by simpa only [branch] using data.prepared.record.headerStored,
    data.prepared.record.payloadMapped,by simpa only [data.prepared.branch branch] using data.prepared.record.payloadStored,
    data.prepared.record.bufferMapped,data.prepared.record.lengthMapped⟩

def Entry.leaf_view {source : PanSemStateFiniteExact 64 Guest.HostMemory} {node heap frame : BitVec 64}
    {lower upper inputEnd cacheLimit valueLimit : Nat} (data : Entry source node heap frame lower upper inputEnd cacheLimit valueLimit)
    (leaf : data.prepared.tag=1#64) : TrieWalk.ValueView source.memory source.memaddrs node 48#64 56#64 valueLimit (fun pointer length=>pointer.toNat+length.toNat≤inputEnd) :=
  data.values.leaf node data.member data.active (data.tag.trans leaf)

def Entry.branch_view {source : PanSemStateFiniteExact 64 Guest.HostMemory} {node heap frame : BitVec 64}
    {lower upper inputEnd cacheLimit valueLimit : Nat} (data : Entry source node heap frame lower upper inputEnd cacheLimit valueLimit)
    (branch : data.prepared.tag=3#64) : TrieWalk.ValueView source.memory source.memaddrs node 160#64 168#64 valueLimit (fun pointer length=>pointer.toNat+length.toNat≤inputEnd) :=
  data.values.branch node data.member data.active data.nonHash (by rw [data.tag,branch]; decide) (by rw [data.tag,branch]; decide)

theorem Entry.leaf_node_before {source : PanSemStateFiniteExact 64 Guest.HostMemory} {node heap frame : BitVec 64}
    {lower upper inputEnd cacheLimit valueLimit : Nat} (data : Entry source node heap frame lower upper inputEnd cacheLimit valueLimit)
    (leaf : data.prepared.tag=1#64) : node.toNat+64≤heap.toNat := by
  have before:=(data.regions node data.member data.active).2.2.2
  rw [data.tag,leaf] at before
  change node.toNat+64≤upper at before
  exact before.trans data.beforeHeap

/-- All three genuine finish bodies share one physical entry contract.
The branch/leaf/extension allowances remain distinct rather than charging
sixteen possible child hashes to every nonbranch node. -/
theorem Entry.body_cost {source : PanSemStateFiniteExact 64 Guest.HostMemory} {node heap frame : BitVec 64}
    {lower upper inputEnd cacheLimit valueLimit : Nat} (data : Entry source node heap frame lower upper inputEnd cacheLimit valueLimit)
    (frameCell : source.locals.lookup (ofString "fr")=some (.val (.word frame)))
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node))) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤finishAllowance data.prepared.tag data.prepared.length cacheLimit valueLimit := by
  rcases data.tag_cases with leaf|extension|branch
  · have notBranch : data.prepared.tag≠3#64:=by rw [leaf]; decide
    have entry : PreparedEntry source frame node 1#64 data.prepared.compact data.prepared.length data.prepared.payload:=by
      simpa only [leaf] using data.prepared.record.entry frameCell nodeCell
    have sized : NodeRlpBegin.PathPayload source node 1#64 data.prepared.compact data.prepared.length data.prepared.payload:=by
      simpa only [leaf] using data.prepared.sizing notBranch
    let view:=data.leaf_view leaf
    have valueSmall : view.length.toNat+32<2^64:=by have size:=view.payload.1; have fits:=data.valueSmall; omega
    have valueBefore : view.pointer.toNat+view.length.toNat≤heap.toNat:=view.extra.trans data.input_before_heap
    have price:=body_leaf_cost source frame node heap data.prepared.compact data.prepared.length data.prepared.payload entry sized data.environment.installed data.environment.domain
      data.heapCell data.heapLower data.heapUpper data.heapAligned view (data.prepared.lengthSmall notBranch) valueSmall
      (by have fits:=data.prepared.payloadSmall notBranch; omega) (data.leaf_node_before leaf) (data.prepared.compactUpper notBranch) valueBefore
    have copyBound : Input.CopyAny.price view.length.toNat≤Input.CopyAny.price valueLimit:=by
      have size:=view.payload.1
      unfold Input.CopyAny.price
      omega
    rw [finishAllowance,if_neg notBranch,if_pos leaf]
    omega
  · have notBranch : data.prepared.tag≠3#64:=by rw [extension]; decide
    have notLeaf : data.prepared.tag≠1#64:=by rw [extension]; decide
    have entry : PreparedEntry source frame node 2#64 data.prepared.compact data.prepared.length data.prepared.payload:=by
      simpa only [extension] using data.prepared.record.entry frameCell nodeCell
    have sized : NodeRlpBegin.PathPayload source node 2#64 data.prepared.compact data.prepared.length data.prepared.payload:=by
      simpa only [extension] using data.prepared.sizing notBranch
    have price:=body_extension_graph_cost source frame node heap data.prepared.compact data.prepared.length data.prepared.payload entry data.graph data.member data.active
      lower upper data.regions data.beforeHeap sized data.environment.installed data.environment.domain data.heapCell data.heapLower data.heapUpper data.heapAligned
      cacheLimit data.cached data.cacheSmall (data.prepared.lengthSmall notBranch) (data.prepared.payloadSmall notBranch) (data.prepared.compactUpper notBranch)
    rw [finishAllowance,if_neg notBranch,if_neg notLeaf]
    exact price
  · let view:=data.branch_view branch
    have price:=body_branch_cost source frame node heap data.stp data.pad (data.branch_entry branch frameCell nodeCell) data.graph data.member data.active
      lower upper inputEnd data.regions data.disjoint data.environment data.heapCell data.heapLower data.heapUpper data.heapAligned data.beforeHeap
      data.stateBefore data.padBefore data.inputBeforeState data.inputBeforePad cacheLimit data.cached data.cacheSmall valueLimit _ view data.valueSmall
    rw [finishAllowance,if_pos branch]
    exact price

theorem FinishOutput.byte_bound {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {node buffer : BitVec 64} {bytes : Nat} {keep : BitVec 64 → Prop}
    (output : FinishOutput source post node buffer bytes keep) : bytes≤2952790016 := by
  obtain ⟨next,_cell,cap,_aligned,floor⟩:=output.heap
  omega

/-- An actual normal body return installs its real exact cache and retains
the graph/path/input queries, for every real node kind. -/
theorem Entry.body_normal_band {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {node heap frame : BitVec 64}
    {lower upper inputEnd cacheLimit valueLimit : Nat} (data : Entry source node heap frame lower upper inputEnd cacheLimit valueLimit)
    (frameCell : source.locals.lookup (ofString "fr")=some (.val (.word frame)))
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node)))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body=(some (.returned value),post)) :
    ∃ bytes,value=.val (.word 0#64) ∧ bytes≤2952790016 ∧ FinishOutput source post node heap bytes (WithBand (SerializerQueries data.graph inputEnd) upper heap.toNat) := by
  rcases data.tag_cases with leaf|extension|branch
  · have notBranch : data.prepared.tag≠3#64:=by rw [leaf]; decide
    have entry : PreparedEntry source frame node 1#64 data.prepared.compact data.prepared.length data.prepared.payload:=by
      simpa only [leaf] using data.prepared.record.entry frameCell nodeCell
    have sized : NodeRlpBegin.PathPayload source node 1#64 data.prepared.compact data.prepared.length data.prepared.payload:=by
      simpa only [leaf] using data.prepared.sizing notBranch
    let view:=data.leaf_view leaf
    have valueSmall : view.length.toNat+32<2^64:=by have size:=view.payload.1; have fits:=data.valueSmall; omega
    have valueBefore : view.pointer.toNat+view.length.toNat≤heap.toNat:=view.extra.trans data.input_before_heap
    obtain ⟨header,answer,_exactHeader,output⟩:=body_leaf_normal source post frame node heap data.prepared.compact data.prepared.length data.prepared.payload entry sized
      (WithBand (SerializerQueries data.graph inputEnd) upper heap.toNat) data.queries_before_heap_band data.environment.installed data.heapCell data.heapLower data.heapUpper data.heapAligned
      view (data.prepared.lengthSmall notBranch) valueSmall (by have fits:=data.prepared.payloadSmall notBranch; omega) (data.leaf_node_before leaf)
      (data.prepared.compactUpper notBranch) valueBefore
      (reference_cache_mapped source data.graph lower upper data.regions data.environment.domain node data.member data.active 8 (by decide) (by decide))
      (reference_cache_mapped source data.graph lower upper data.regions data.environment.domain node data.member data.active 16 (by decide) (by decide))
      value normal
    exact ⟨header+data.prepared.payload.toNat,answer,output.byte_bound,output⟩
  · have notBranch : data.prepared.tag≠3#64:=by rw [extension]; decide
    have entry : PreparedEntry source frame node 2#64 data.prepared.compact data.prepared.length data.prepared.payload:=by
      simpa only [extension] using data.prepared.record.entry frameCell nodeCell
    have sized : NodeRlpBegin.PathPayload source node 2#64 data.prepared.compact data.prepared.length data.prepared.payload:=by
      simpa only [extension] using data.prepared.sizing notBranch
    exact body_extension_graph_normal_band source post frame node heap data.prepared.compact data.prepared.length data.prepared.payload data.stp data.pad entry
      data.graph data.member data.active lower upper inputEnd data.regions data.disjoint data.paths data.pathRegions data.separated data.lowerAligned sized data.environment
      data.heapCell data.heapLower data.heapUpper data.heapAligned data.beforeHeap data.stateBefore data.padBefore data.inputBeforeState data.inputBeforePad
      cacheLimit data.cached data.cacheSmall (data.prepared.lengthSmall notBranch) (data.prepared.payloadSmall notBranch) (data.prepared.compactUpper notBranch) value normal
  · let view:=data.branch_view branch
    obtain ⟨bytes,answer,_bound,output⟩:=body_branch_normal_band source post frame node heap data.stp data.pad (data.branch_entry branch frameCell nodeCell)
      data.graph data.member data.active lower upper inputEnd data.regions data.disjoint data.environment data.paths data.pathRegions data.separated data.lowerAligned
      data.heapCell data.heapLower data.heapUpper data.heapAligned data.beforeHeap data.stateBefore data.padBefore data.inputBeforeState data.inputBeforePad
      cacheLimit data.cached data.cacheSmall valueLimit _ view data.valueSmall view.extra value normal
    exact ⟨bytes,answer,output.byte_bound,output⟩


/-- The previous caller contract is a projection of actual band preservation. -/
theorem Entry.body_normal {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {node heap frame : BitVec 64}
    {lower upper inputEnd cacheLimit valueLimit : Nat} (data : Entry source node heap frame lower upper inputEnd cacheLimit valueLimit)
    (frameCell : source.locals.lookup (ofString "fr")=some (.val (.word frame)))
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node)))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body=(some (.returned value),post)) :
    ∃ bytes,value=.val (.word 0#64) ∧ bytes≤2952790016 ∧ FinishOutput source post node heap bytes (SerializerQueries data.graph inputEnd) := by
  obtain ⟨bytes,answer,bound,output⟩:=data.body_normal_band frameCell nodeCell value normal
  exact ⟨bytes,answer,bound,output.weaken_keep (fun _ required=>Or.inl required)⟩

theorem environment (codeFn : MlS→Option (List (MlS×ShapeHOL)×ProgHOL 64×ShapeHOL)) (frame node : BitVec 64)
    (known : codeFn (ofString "_node_rlp_finish")=some (formals,body,.one)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),lookupCodeHOLFinite codeFn (ofString "_node_rlp_finish") [.val (.word frame),.val (.word node)]=some (body,callee,.one) ∧
      callee.lookup (ofString "fr")=some (.val (.word frame)) ∧ callee.lookup (ofString "node")=some (.val (.word node)) :=
  Input.word_pair_environment codeFn (ofString "_node_rlp_finish") (ofString "fr") (ofString "node") body .one frame node (by decide) known

/-- The actual caller spends one call tick beyond the genuine node-kind
body allowance. Failed calls and nonnormal body outcomes remain covered. -/
theorem call_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (node heap frame : BitVec 64)
    (lower upper inputEnd cacheLimit valueLimit : Nat) (data : Entry source node heap frame lower upper inputEnd cacheLimit valueLimit)
    (destination : Option (Option MlS)) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some [.val (.word frame),.val (.word node)]) :
    source.clock-(evaluateHOLFiniteState source (.call (Input.LocalEffects.callInfo destination) (ofString "_node_rlp_finish") arguments)).2.clock≤
      finishAllowance data.prepared.tag data.prepared.length cacheLimit valueLimit+1 := by
  obtain ⟨callee,called,frameCell,nodeCell⟩:=environment source.code.lookup frame node (original_code source.code data.environment.installed)
  exact Input.ClockCost.call_current source destination (ofString "_node_rlp_finish") arguments _ body callee .one _ args called
    ((data.call callee).body_cost frameCell nodeCell)

/-- The real ignored finish caller obtains the body result from that same
execution, restores its caller locals and retains the complete physical frame. -/
theorem call_normal_band (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (node heap frame : BitVec 64)
    (lower upper inputEnd cacheLimit valueLimit : Nat) (data : Entry source node heap frame lower upper inputEnd cacheLimit valueLimit)
    (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some [.val (.word frame),.val (.word node)])
    (normal : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "_node_rlp_finish") arguments)=(none,target)) :
    target.locals=source.locals ∧ ∃ bytes,bytes≤2952790016 ∧ FinishOutput source target node heap bytes (WithBand (SerializerQueries data.graph inputEnd) upper heap.toNat) := by
  obtain ⟨callee,called,frameCell,nodeCell⟩:=environment source.code.lookup frame node (original_code source.code data.environment.installed)
  obtain ⟨_funded,built,returned,run⟩:=Input.CallNormal.ignored_callee_return source target (ofString "_node_rlp_finish") arguments _ body callee .one args called normal
  obtain ⟨bytes,_answer,bound,output⟩:=(data.call callee).body_normal_band frameCell nodeCell returned run
  have endpoint:=Input.CallNormal.ignored_target source target (ofString "_node_rlp_finish") arguments _ body callee .one args called returned built run normal
  exact ⟨by rw [endpoint],bytes,bound,output.reframe rfl (by rw [endpoint]; rfl)⟩


/-- Existing ignored-call interface retains its original selected queries. -/
theorem call_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (node heap frame : BitVec 64)
    (lower upper inputEnd cacheLimit valueLimit : Nat) (data : Entry source node heap frame lower upper inputEnd cacheLimit valueLimit)
    (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some [.val (.word frame),.val (.word node)])
    (normal : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "_node_rlp_finish") arguments)=(none,target)) :
    target.locals=source.locals ∧ ∃ bytes,bytes≤2952790016 ∧ FinishOutput source target node heap bytes (SerializerQueries data.graph inputEnd) := by
  obtain ⟨locals,bytes,bound,output⟩:=call_normal_band source target node heap frame lower upper inputEnd cacheLimit valueLimit data arguments args normal
  exact ⟨locals,bytes,bound,output.weaken_keep (fun _ required=>Or.inl required)⟩


/-- The actual two footer destinations precede a protected persistent band. -/
theorem FinishOutput.band {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {node buffer : BitVec 64} {bytes lower upper : Nat} {keep : BitVec 64 → Prop}
    (output : FinishOutput source post node buffer bytes (WithBand keep lower upper)) (nodeBefore : node.toNat+24≤lower)
    (query : BitVec 64) (band : lower≤query.toNat ∧ query.toNat<upper) : post.memory query=source.memory query := by
  have pointerNumber : (node+8#64).toNat=node.toNat+8:=byteAddress_toNat node 8 (by have small:=query.isLt; omega)
  have lengthNumber : (node+16#64).toNat=node.toNat+16:=byteAddress_toNat node 16 (by have small:=query.isLt; omega)
  apply output.memory query (Or.inr band)
  · intro equal
    have numeric:=congrArg BitVec.toNat equal
    rw [pointerNumber] at numeric
    omega
  · intro equal
    have numeric:=congrArg BitVec.toNat equal
    rw [lengthNumber] at numeric
    omega

theorem Entry.node_cache_before {source : PanSemStateFiniteExact 64 Guest.HostMemory} {node heap frame : BitVec 64}
    {lower upper inputEnd cacheLimit valueLimit : Nat} (data : Entry source node heap frame lower upper inputEnd cacheLimit valueLimit) : node.toNat+24≤upper := by
  have region:=data.regions node data.member data.active
  have minimum:=TrieWalk.nodeBytes_bounds (wordAt source.memory node)
  omega

/-- Every older saved preparation survives the real child finish caller.
The record uses high scratch, its compact byte uses the actual older band,
and its value byte comes from the same protected earlier input region. -/
def Prepared.after_finish {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    {node heap frame ownerFrame owner : BitVec 64} {lower upper inputEnd cacheLimit valueLimit bytes : Nat}
    (data : Entry source node heap frame lower upper inputEnd cacheLimit valueLimit)
    (prepared : Prepared source ownerFrame owner upper heap.toNat)
    (ownerMember : data.graph.valid owner) (ownerActive : owner≠0#64)
    (frameArena : AllocatedBytes.Arena ownerFrame 48) (scratch : 2952790016≤ownerFrame.toNat)
    (output : FinishOutput source target node heap bytes (WithBand (SerializerQueries data.graph inputEnd) upper heap.toNat)) :
    Prepared target ownerFrame owner upper heap.toNat := by
  have covers : ∀ query,RegisteredField data.graph query → WithBand (SerializerQueries data.graph inputEnd) upper heap.toNat query:=
    fun _ required=>Or.inl (Or.inl (Or.inl required))
  have fieldMemory (offset : Nat) (inside : offset<TrieWalk.nodeBytes (wordAt source.memory owner)) (kind : offset=0 ∨ 32≤offset) :
      target.memory (byteAddress owner offset)=source.memory (byteAddress owner offset):=
    output.data_memory data.graph data.member data.active lower upper data.regions data.disjoint covers owner offset ownerMember ownerActive inside kind
  have frameMemory (offset : Nat) (inside : offset≤40) :
      target.memory (ownerFrame+BitVec.ofNat 64 offset)=source.memory (ownerFrame+BitVec.ofNat 64 offset):=by
    have number:=byteAddress_toNat ownerFrame offset (by have room:=frameArena.upper; omega)
    apply output.scratch
    change 2952790016≤(byteAddress ownerFrame offset).toNat
    rw [number]
    omega
  have ownerTag (leaf : prepared.tag=1#64) : wordAt source.memory owner=1#64:=by
    simp [wordAt,prepared.record.headerStored,MemoryBytes.wordBits,leaf]
  have nodeFloor : inputEnd≤node.toNat:=by
    have region:=data.regions node data.member data.active
    have input:=data.inputBeforeState
    have workspace:=data.stateBefore
    omega
  have nodeBefore : node.toNat+24≤2952790016:=data.node_cache_before.trans (data.beforeHeap.trans data.heapUpper)
  apply prepared.of_memory output.runtime.1 output.runtime.2.1
  intro query required
  rcases required with equal|⟨notBranch,sizing⟩
  · rcases equal with equal|equal|equal|equal
    · rw [equal]
      simpa only [byteAddress,BitVec.add_zero] using fieldMemory 0 (by have minimum:=TrieWalk.nodeBytes_bounds (wordAt source.memory owner); omega) (Or.inl rfl)
    · rw [equal]
      exact frameMemory 24 (by decide)
    · rw [equal]
      exact frameMemory 32 (by decide)
    · rw [equal]
      exact frameMemory 40 (by decide)
  · rcases sizing with ⟨leaf,equal|equal⟩|⟨one,equal⟩|⟨leaf,one,equal⟩
    · rw [equal]
      exact fieldMemory 48 (by rw [ownerTag leaf]; decide) (Or.inr (by decide))
    · rw [equal]
      exact fieldMemory 56 (by rw [ownerTag leaf]; decide) (Or.inr (by decide))
    · rw [equal]
      exact output.band data.node_cache_before _ (prepared.compact_byte_bounds notBranch one)
    · let view:=data.values.leaf owner ownerMember ownerActive (ownerTag leaf)
      have pointerWord : wordAt source.memory (owner+48#64)=view.pointer:=by simp [wordAt,view.pointerStored,MemoryBytes.wordBits]
      have lengthWord : wordAt source.memory (owner+56#64)=view.length:=by simp [wordAt,view.lengthStored,MemoryBytes.wordBits]
      have lengthOne : view.length.toNat=1:=by rw [←lengthWord,one]; rfl
      have earlier : (panByteAlignHOL (width:=64) view.pointer).toNat<inputEnd:=by
        have bound:=view.extra
        rw [AllocatedBytes.aligned_number]
        omega
      rw [equal,pointerWord]
      exact output.input_memory inputEnd (fun _ required=>Or.inl (Or.inl (Or.inr required))) nodeFloor nodeBefore _ earlier

end InitECandidate.Solver.Mpt.NodeRlpFinish

#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.Record.entry
#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.Record.of_memory
#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.Prepared.of_frame
#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.Prepared.weaken
#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.Prepared.of_begin
#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.Entry.call
#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.Entry.tag_cases
#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.Entry.input_before_heap
#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.Entry.queries_before_heap

#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.Entry.tag

#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.Entry.branch_entry

#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.Entry.leaf_view

#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.Entry.branch_view

#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.Entry.leaf_node_before

#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.Entry.body_cost

#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.FinishOutput.byte_bound

#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.Entry.body_normal

#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.environment

#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.call_cost

#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.call_normal

#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.Prepared.of_memory

#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.Prepared.compact_byte_bounds

#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.Entry.queries_before_heap_band

#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.Entry.body_normal_band

#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.call_normal_band

#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.FinishOutput.band

#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.Entry.node_cache_before

#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.Prepared.after_finish

#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.Prepared.footprint_bands
