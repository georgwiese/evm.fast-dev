import InitECandidate.Solver.Mpt.NodeRlpFillProgram
import InitECandidate.Solver.Input.NoFallthrough
import InitECandidate.Solver.Input.WordPairEnvironment
import InitECandidate.Solver.Input.CallPrefixScopedActual

namespace InitECandidate.Solver.Mpt.CurrentTrieRoot
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix Input GasBudget
open Flapjack.Basis.Pure.MlString QueryBranch

theorem stopped_sequence_eq (source : PanSemStateFiniteExact 64 Guest.HostMemory) (first second : ProgHOL 64)
    (stops : (evaluateHOLFiniteState source first).1≠none) :
    evaluateHOLFiniteState source (.seq first second)=evaluateHOLFiniteState source first := by
  rw [evaluateHOLFiniteState_seq_line780]
  generalize computed : evaluateHOLFiniteState source first=output at stops ⊢
  obtain ⟨result,target⟩:=output
  cases result with
  | none=>exact (stops rfl).elim
  | some result=>rfl

namespace NodeRlp

def body : ProgHOL 64:=match Guest.Software.guestFn_node_rlp with | .function fn=>progToHOL fn.body | _=>.skip
def formals : List (MlS×ShapeHOL):=[(ofString "node",.one)]
def afterCache : ProgHOL 64:=match body with | .dec _ _ _ rest=>rest | _=>.skip
def afterCachedReturn : ProgHOL 64:=match afterCache with | .seq _ rest=>rest | _=>.skip
def fillAndReturn : ProgHOL 64:=match afterCachedReturn with | .seq _ rest=>rest | _=>.skip
def returnFooter : ProgHOL 64:=match fillAndReturn with | .seq _ rest=>rest | _=>.skip
def nodeField (offset : BitVec 64) : ExpHOL 64:=.load .one (.op .add [localVar "node",.const offset])
def tagTest : ExpHOL 64:=.cmp .equal (nodeField 0#64) (.const 0#64)
def failCall : ProgHOL 64:=.call (some (none,none)) (ofString "mpt_fail") [.const 2#64]
def fillCall : ProgHOL 64:=.call (some (none,none)) (ofString "_node_rlp_fill") [localVar "node"]

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "node_rlp")=some (formals,body,.comb [.one,.one]) := by
  have checked:=OriginalCode.indexed code installed 259 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.Software.guestFn_node_rlp) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,formals,body,
    Guest.Software.guestFn_node_rlp,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

set_option maxRecDepth 100000 in
theorem shapes : body=.dec (ofString "cached") .one (nodeField 8#64) afterCache ∧
    afterCachedReturn=.seq (.ite tagTest failCall .skip) fillAndReturn ∧ fillAndReturn=.seq fillCall returnFooter := by
  simp only [body,afterCache,afterCachedReturn,fillAndReturn,returnFooter,nodeField,tagTest,failCall,fillCall,localVar,
    Guest.Software.guestFn_node_rlp,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none]
  trivial

set_option maxRecDepth 100000 in
theorem after_cache_selected (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (cached : source.locals.lookup (ofString "cached")=some (.val (.word 0#64))) :
    evaluateHOLFiniteState source afterCache=evaluateHOLFiniteState source afterCachedReturn := by
  have shape : afterCache=.seq (.ite (.cmp .notEqual (localVar "cached") (.const 0#64))
      (.return (.rstruct [localVar "cached",nodeField 16#64])) .skip) afterCachedReturn:=by
    simp only [afterCache,afterCachedReturn,body,Guest.Software.guestFn_node_rlp,progToHOL,expToHOL,shapeToHOL,
      List.map_cons,List.map_nil,Option.map_none,localVar,nodeField]
  rw [shape,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite]
  simp [evalHOLExact,toExact,localVar,cached,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,evaluateHOLFiniteState_skip]


/-- Current physical nonhash root entry, with all serializer conditions
at the reached state. Caller reachability still has to establish them. -/
structure Entry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (node heap cursor floor : BitVec 64)
    (lower frontier inputEnd cacheLimit valueLimit : Nat) where
  persistent : NodeRlpFill.Persistent source heap lower frontier inputEnd cacheLimit valueLimit
  member : persistent.graph.valid node
  active : node≠0#64
  nonHash : wordAt source.memory node≠0#64
  live : Rlp.LiveArena source
  arena : Rlp.Validation.Arena source cursor floor
  nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node))
  cacheRoom : 251658240≤cacheLimit

def Entry.bindCached {source : PanSemStateFiniteExact 64 Guest.HostMemory} {node heap cursor floor : BitVec 64}
    {lower frontier inputEnd cacheLimit valueLimit : Nat} (data : Entry source node heap cursor floor lower frontier inputEnd cacheLimit valueLimit)
    (cached : BitVec 64) : Entry (bind source "cached" cached) node heap cursor floor lower frontier inputEnd cacheLimit valueLimit :=
  {data with
    persistent:={data.persistent with environment:=data.persistent.environment.of_frame rfl},
    live:=data.live.of_frame rfl,arena:=data.arena.of_fields source _ cursor floor rfl rfl,
    nodeCell:=(bind_lookup_other source "cached" "node" cached (by decide)).trans data.nodeCell}

theorem field_read {source : PanSemStateFiniteExact 64 Guest.HostMemory} {node heap : BitVec 64}
    {lower frontier inputEnd cacheLimit valueLimit : Nat} (data : NodeRlpFill.Persistent source heap lower frontier inputEnd cacheLimit valueLimit)
    (member : data.graph.valid node) (active : node≠0#64)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node)))
    (offset : Nat) (inside : offset<32) (aligned : offset%8=0) :
    eval source (nodeField (BitVec.ofNat 64 offset))=some (.val (.word (wordAt source.memory (node+BitVec.ofNat 64 offset)))) := by
  obtain ⟨_lower,arena,nodeAligned,_upper⟩:=data.regions node member active
  have minimum:=TrieWalk.nodeBytes_bounds (wordAt source.memory node)
  have mapped : source.memaddrs (node+BitVec.ofNat 64 offset):=AllocatedBytes.word_mapped source node _ offset data.environment.domain arena (by omega) nodeAligned aligned
  have stored : source.memory (node+BitVec.ofNat 64 offset)=.word (wordAt source.memory (node+BitVec.ofNat 64 offset)):=by
    unfold wordAt
    cases source.memory (node+BitVec.ofNat 64 offset) with | word value=>rfl
  apply Witness.load_word_read source _ _ _ _ mapped stored
  simp [eval,evalHOLExact,evalListHOLExact,toExact,nodeField,localVar,nodeCell,valueIsWord,valueWord,wordOpHOL,wordOp]

theorem Entry.field_read {source : PanSemStateFiniteExact 64 Guest.HostMemory} {node heap cursor floor : BitVec 64}
    {lower frontier inputEnd cacheLimit valueLimit : Nat} (data : Entry source node heap cursor floor lower frontier inputEnd cacheLimit valueLimit)
    (offset : Nat) (inside : offset<32) (aligned : offset%8=0) :
    eval source (nodeField (BitVec.ofNat 64 offset))=some (.val (.word (wordAt source.memory (node+BitVec.ofNat 64 offset)))) :=
  CurrentTrieRoot.NodeRlp.field_read data.persistent data.member data.active data.nodeCell offset inside aligned

def cachedTest : ExpHOL 64:=.cmp .notEqual (localVar "cached") (.const 0#64)
def cachedReturn : ProgHOL 64:=.return (.rstruct [localVar "cached",nodeField 16#64])

set_option maxRecDepth 100000 in
theorem cache_shape : afterCache=.seq (.ite cachedTest cachedReturn .skip) afterCachedReturn ∧
    returnFooter=.return (.rstruct [nodeField 8#64,nodeField 16#64]) := by
  simp only [afterCache,afterCachedReturn,fillAndReturn,returnFooter,body,cachedTest,cachedReturn,nodeField,localVar,
    Guest.Software.guestFn_node_rlp,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none]
  trivial

theorem after_tag_selected {source : PanSemStateFiniteExact 64 Guest.HostMemory} {node heap cursor floor : BitVec 64}
    {lower frontier inputEnd cacheLimit valueLimit : Nat} (data : Entry source node heap cursor floor lower frontier inputEnd cacheLimit valueLimit) :
    evaluateHOLFiniteState source afterCachedReturn=evaluateHOLFiniteState source fillAndReturn := by
  have read:=data.field_read 0 (by decide) (by decide)
  simp only [eval,BitVec.add_zero] at read
  rw [shapes.2.1,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite]
  simp [tagTest,evalHOLExact,toExact,read,data.nonHash,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,evaluateHOLFiniteState_skip]

theorem fill_tail_cost {source : PanSemStateFiniteExact 64 Guest.HostMemory} {node heap cursor floor : BitVec 64}
    {lower frontier inputEnd cacheLimit valueLimit : Nat} (data : Entry source node heap cursor floor lower frontier inputEnd cacheLimit valueLimit) :
    source.clock-(evaluateHOLFiniteState source fillAndReturn).2.clock≤NodeRlpFill.bodyPrice cacheLimit valueLimit+1 := by
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) [localVar "node"]=some [.val (.word node)]:=by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,data.nodeCell]
  have called:=NodeRlpFill.call_cost data.persistent data.member data.active data.nonHash data.live data.arena data.cacheRoom (some none) [localVar "node"] args
  rw [shapes.2.2]
  have footer : ClockCost.Bound source.code returnFooter 0:=by rw [cache_shape.2]; exact ClockCost.returned source.code _
  simpa only [Nat.add_zero] using ClockCost.sequence_current source fillCall returnFooter _ 0 called footer

theorem after_cache_cost {source : PanSemStateFiniteExact 64 Guest.HostMemory} {node heap cursor floor cached : BitVec 64}
    {lower frontier inputEnd cacheLimit valueLimit : Nat} (data : Entry source node heap cursor floor lower frontier inputEnd cacheLimit valueLimit)
    (cachedCell : source.locals.lookup (ofString "cached")=some (.val (.word cached))) :
    source.clock-(evaluateHOLFiniteState source afterCache).2.clock≤NodeRlpFill.bodyPrice cacheLimit valueLimit+1 := by
  by_cases zero : cached=0#64
  · subst cached
    rw [after_cache_selected source cachedCell,after_tag_selected data]
    exact fill_tail_cost data
  · have selected : evaluateHOLFiniteState source (.ite cachedTest cachedReturn .skip)=evaluateHOLFiniteState source cachedReturn:=by
      rw [evaluateHOLFiniteState_ite]
      simp [cachedTest,evalHOLExact,toExact,localVar,cachedCell,zero,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    have stopped : (evaluateHOLFiniteState source (.ite cachedTest cachedReturn .skip)).1≠none:=by
      rw [selected]
      exact NoFallthrough.returned _ source
    rw [cache_shape.1,stopped_sequence_eq source _ _ stopped,selected]
    exact (ClockCost.returned source.code _ source rfl).trans (by omega)

/-- Actual cached and uncached paths both have a finite source price.
Uncached roots execute the full current encoder; cached returns cost no ticks. -/
theorem body_cost {source : PanSemStateFiniteExact 64 Guest.HostMemory} {node heap cursor floor : BitVec 64}
    {lower frontier inputEnd cacheLimit valueLimit : Nat} (data : Entry source node heap cursor floor lower frontier inputEnd cacheLimit valueLimit) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤NodeRlpFill.bodyPrice cacheLimit valueLimit+1 := by
  rw [shapes.1]
  apply ClockCost.scalar_declaration_current source (ofString "cached") (nodeField 8#64) afterCache _
  intro cached
  exact after_cache_cost (data.bindCached cached) (bind_lookup_same _ _ _)

/-- Actual pointer/length result and current physical state retained for
node_hash. Existing cache hits need only the proved populated-length bound. -/
structure Output (source : PanSemStateFiniteExact 64 Guest.HostMemory) (node cursor floor : BitVec 64)
    (lower frontier inputEnd cacheLimit valueLimit : Nat) (registry : BitVec 64→Prop) (value : ValueHOL 64) where
  heap : BitVec 64
  persistent : NodeRlpFill.Persistent source heap lower frontier inputEnd cacheLimit valueLimit
  registered : persistent.graph.valid=registry
  buffer : BitVec 64
  length : BitVec 64
  answer : value=.rStruct [.val (.word buffer),.val (.word length)]
  pointerStored : source.memory (node+8#64)=.word buffer
  lengthStored : source.memory (node+16#64)=.word length
  bounded : length.toNat≤cacheLimit
  live : Rlp.LiveArena source
  arena : Rlp.Validation.Arena source cursor floor

theorem Output.of_frame {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {node cursor floor : BitVec 64}
    {lower frontier inputEnd cacheLimit valueLimit : Nat} {registry : BitVec 64→Prop} {value : ValueHOL 64}
    (output : Output source node cursor floor lower frontier inputEnd cacheLimit valueLimit registry value)
    (frame : LocalEffects.erase target=LocalEffects.erase source) :
    Nonempty (Output target node cursor floor lower frontier inputEnd cacheLimit valueLimit registry value) := by
  obtain ⟨persistent,same⟩:=output.persistent.of_frame (target:=target) frame
  have memory:=LocalEffects.memory_of_erase source target frame
  have domain:=congrArg PanSemStateFiniteExact.memaddrs frame
  have globals:=congrArg PanSemStateFiniteExact.globals frame
  exact ⟨{
    heap:=output.heap,persistent:=persistent,registered:=same.trans output.registered,buffer:=output.buffer,length:=output.length,
    answer:=output.answer,pointerStored:=(congrFun memory _).trans output.pointerStored,lengthStored:=(congrFun memory _).trans output.lengthStored,
    bounded:=output.bounded,live:=output.live.of_frame frame,arena:=output.arena.of_fields source target cursor floor domain globals}⟩

/-- Invert the actual scalar-pair return from its two observed reads. -/
theorem pair_return_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (first second : ExpHOL 64)
    (buffer length : BitVec 64) (value : ValueHOL 64)
    (firstRead : eval source first=some (.val (.word buffer))) (secondRead : eval source second=some (.val (.word length)))
    (normal : evaluateHOLFiniteState source (.return (.rstruct [first,second]))=(some (.returned value),post)) :
    value=.rStruct [.val (.word buffer),.val (.word length)] ∧ post=emptyLocalsHOLFinite source := by
  obtain ⟨read,endpoint⟩:=return_normal source post _ value normal
  have expected : eval source (.rstruct [first,second])=some (.rStruct [.val (.word buffer),.val (.word length)]):=by
    simp only [eval] at firstRead secondRead ⊢
    simp [evalHOLExact,evalListHOLExact,firstRead,secondRead]
  exact ⟨Option.some.inj (read.symm.trans expected),endpoint⟩

/-- A genuine cache hit returns immediately. Failed return reads still
cannot fall through to the encoder. -/
theorem cache_selected (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cached : BitVec 64)
    (cachedCell : source.locals.lookup (ofString "cached")=some (.val (.word cached))) (nonzero : cached≠0#64) :
    evaluateHOLFiniteState source afterCache=evaluateHOLFiniteState source cachedReturn := by
  have selected : evaluateHOLFiniteState source (.ite cachedTest cachedReturn .skip)=evaluateHOLFiniteState source cachedReturn:=by
    rw [evaluateHOLFiniteState_ite]
    simp [cachedTest,evalHOLExact,toExact,localVar,cachedCell,nonzero,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  rw [cache_shape.1,stopped_sequence_eq source _ _ (by rw [selected]; exact NoFallthrough.returned _ source),selected]

/-- Normal cached/uncached returns retain the actual bounded byte count
and complete current registry, persistent facts and restored scratch arena. -/
theorem after_cache_normal {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {node heap cursor floor : BitVec 64}
    {lower frontier inputEnd cacheLimit valueLimit : Nat} (data : Entry source node heap cursor floor lower frontier inputEnd cacheLimit valueLimit)
    (cachedCell : source.locals.lookup (ofString "cached")=some (.val (.word (wordAt source.memory (node+8#64)))))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source afterCache=(some (.returned value),post)) :
    Nonempty (Output post node cursor floor lower frontier inputEnd cacheLimit valueLimit data.persistent.graph.valid value) ∧ NodeRlpFill.Preservation source post inputEnd := by
  by_cases zero : wordAt source.memory (node+8#64)=0#64
  · have selectedCell:=cachedCell
    rw [zero] at selectedCell
    rw [after_cache_selected source selectedCell,after_tag_selected data,shapes.2.2] at normal
    have safe : LocalPrefix (ofString "node") fillCall:=.call none _ _ (by intro name impossible; cases impossible)
    obtain ⟨filled,fillRun,footerRun⟩:=sequence_returned source post fillCall returnFooter value (safe.summary_full source).2.1 normal
    have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) [localVar "node"]=some [.val (.word node)]:=by
      simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,data.nodeCell]
    obtain ⟨locals,nextHeap,persistent,same,⟨cache⟩,live,arena,fillFrame⟩:=NodeRlpFill.call_normal data.persistent data.member data.active data.nonHash data.live data.arena data.cacheRoom [localVar "node"] args fillRun
    have member : persistent.graph.valid node:=by rw [same]; exact data.member
    have nodeCell : filled.locals.lookup (ofString "node")=some (.val (.word node)):=by rw [locals]; exact data.nodeCell
    have firstRead:=field_read persistent member data.active nodeCell 8 (by decide) (by decide)
    have secondRead:=field_read persistent member data.active nodeCell 16 (by decide) (by decide)
    have pointer : wordAt filled.memory (node+8#64)=cache.buffer:=by simp [wordAt,cache.pointerStored,MemoryBytes.wordBits]
    have length : wordAt filled.memory (node+16#64)=BitVec.ofNat 64 cache.bytes:=by simp [wordAt,cache.lengthStored,MemoryBytes.wordBits]
    rw [pointer] at firstRead
    rw [length] at secondRead
    rw [cache_shape.2] at footerRun
    obtain ⟨answer,endpoint⟩:=pair_return_normal filled post _ _ cache.buffer (BitVec.ofNat 64 cache.bytes) value firstRead secondRead footerRun
    have small : cache.bytes<2^64:=by have bound:=cache.bytes_le persistent.heapUpper; omega
    let output : Output filled node cursor floor lower frontier inputEnd cacheLimit valueLimit data.persistent.graph.valid value:={
      heap:=nextHeap,persistent:=persistent,registered:=same,buffer:=cache.buffer,length:=BitVec.ofNat 64 cache.bytes,
      answer:=answer,pointerStored:=cache.pointerStored,lengthStored:=cache.lengthStored,
      bounded:=by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt small]; exact (cache.bytes_le persistent.heapUpper).trans data.cacheRoom,
      live:=live,arena:=arena}
    have frame : LocalEffects.erase post=LocalEffects.erase filled:=by rw [endpoint]; rfl
    exact ⟨output.of_frame frame,fillFrame.trans (NodeRlpFill.Preservation.of_frame inputEnd frame)⟩
  · rw [cache_selected source _ cachedCell zero] at normal
    have firstRead : eval source (localVar "cached")=some (.val (.word (wordAt source.memory (node+8#64)))):=by
      simp [eval,evalHOLExact,toExact,localVar,cachedCell]
    have secondRead:=data.field_read 16 (by decide) (by decide)
    obtain ⟨answer,endpoint⟩:=pair_return_normal source post _ _ _ _ value firstRead secondRead normal
    have pointerStored : source.memory (node+8#64)=.word (wordAt source.memory (node+8#64)):=by
      unfold wordAt
      cases source.memory (node+8#64) with | word value=>rfl
    have lengthStored : source.memory (node+16#64)=.word (wordAt source.memory (node+16#64)):=by
      unfold wordAt
      cases source.memory (node+16#64) with | word value=>rfl
    let output : Output source node cursor floor lower frontier inputEnd cacheLimit valueLimit data.persistent.graph.valid value:={
      heap:=heap,persistent:=data.persistent,registered:=rfl,buffer:=wordAt source.memory (node+8#64),length:=wordAt source.memory (node+16#64),
      answer:=answer,pointerStored:=pointerStored,lengthStored:=lengthStored,
      bounded:=data.persistent.cached node data.member data.active data.nonHash zero,live:=data.live,arena:=data.arena}
    have frame : LocalEffects.erase post=LocalEffects.erase source:=by rw [endpoint]; rfl
    exact ⟨output.of_frame frame,NodeRlpFill.Preservation.of_frame inputEnd frame⟩

theorem body_normal {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {node heap cursor floor : BitVec 64}
    {lower frontier inputEnd cacheLimit valueLimit : Nat} (data : Entry source node heap cursor floor lower frontier inputEnd cacheLimit valueLimit)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body=(some (.returned value),post)) :
    Nonempty (Output post node cursor floor lower frontier inputEnd cacheLimit valueLimit data.persistent.graph.valid value) ∧ NodeRlpFill.Preservation source post inputEnd := by
  have read:=data.field_read 8 (by decide) (by decide)
  rw [shapes.1] at normal
  obtain ⟨inner,run,endpoint⟩:=declaration_return_word source post "cached" (nodeField 8#64) (wordAt source.memory (node+8#64)) afterCache value read normal
  obtain ⟨⟨output⟩,innerFrame⟩:=after_cache_normal (data.bindCached _) (bind_lookup_same _ _ _) value run
  have frame : LocalEffects.erase post=LocalEffects.erase inner:=by rw [endpoint]; rfl
  exact ⟨output.of_frame frame,
    (NodeRlpFill.Preservation.of_frame inputEnd (source:=source) (target:=bind source "cached" (wordAt source.memory (node+8#64))) rfl).trans
      (innerFrame.trans (NodeRlpFill.Preservation.of_frame inputEnd frame))⟩

/-- The actual unary callee binding retains the same physical entry. -/
def Entry.call {source : PanSemStateFiniteExact 64 Guest.HostMemory} {node heap cursor floor : BitVec 64}
    {lower frontier inputEnd cacheLimit valueLimit : Nat} (data : Entry source node heap cursor floor lower frontier inputEnd cacheLimit valueLimit)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (nodeCell : callee.lookup (ofString "node")=some (.val (.word node))) :
    Entry (callEntryStateHOLFinite source callee) node heap cursor floor lower frontier inputEnd cacheLimit valueLimit :=
  {data with
    persistent:=data.persistent.call callee,live:=data.live.of_frame rfl,
    arena:=data.arena.of_fields source _ cursor floor rfl rfl,nodeCell:=nodeCell}

/-- The real reached scoped caller retains the returned pair, complete
registered trie, input band and caller globals outside allocation cursors. -/
theorem scoped_normal {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {node heap cursor floor : BitVec 64}
    {lower frontier inputEnd cacheLimit valueLimit : Nat} (data : Entry source node heap cursor floor lower frontier inputEnd cacheLimit valueLimit)
    (name : MlS) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=some [.val (.word node)])
    (reached : CallPrefix.Reaches source (.scoped name (.comb [.one,.one]) (ofString "node_rlp") arguments) target) :
    ∃ value,target.locals.lookup name=some value ∧
      Nonempty (Output target node cursor floor lower frontier inputEnd cacheLimit valueLimit data.persistent.graph.valid value) ∧
      NodeRlpFill.Preservation source target inputEnd := by
  obtain ⟨callee,called,nodeCell⟩:=word_environment source.code.lookup (ofString "node_rlp") (ofString "node") body (.comb [.one,.one]) node
    (original_code source.code data.live.code)
  obtain ⟨child,value,run,endpoint⟩:=reached.scoped_known name (.comb [.one,.one]) (ofString "node_rlp") arguments _ body callee (.comb [.one,.one]) args called
  obtain ⟨⟨output⟩,bodyFrame⟩:=body_normal (data.call callee nodeCell) value run
  have frame : LocalEffects.erase target=LocalEffects.erase child:=by rw [endpoint]; rfl
  refine ⟨value,?_,output.of_frame frame,?_⟩
  · rw [endpoint]
    simp [setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
  · exact (NodeRlpFill.Preservation.of_frame inputEnd (source:=source) (target:=callEntryStateHOLFinite source callee) rfl).trans
      (bodyFrame.trans (NodeRlpFill.Preservation.of_frame inputEnd frame))

/-- Price the real node_rlp caller and its full cached/uncached body,
including destination/shape errors and every other actual outcome. -/
theorem call_cost {source : PanSemStateFiniteExact 64 Guest.HostMemory} {node heap cursor floor : BitVec 64}
    {lower frontier inputEnd cacheLimit valueLimit : Nat} (data : Entry source node heap cursor floor lower frontier inputEnd cacheLimit valueLimit)
    (destination : Option (Option MlS)) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=some [.val (.word node)]) :
    source.clock-(evaluateHOLFiniteState source (.call (LocalEffects.callInfo destination) (ofString "node_rlp") arguments)).2.clock≤NodeRlpFill.bodyPrice cacheLimit valueLimit+2 := by
  obtain ⟨callee,called,nodeCell⟩:=word_environment source.code.lookup (ofString "node_rlp") (ofString "node") body (.comb [.one,.one]) node
    (original_code source.code data.live.code)
  have price:=ClockCost.call_current source destination (ofString "node_rlp") arguments _ body callee (.comb [.one,.one]) (NodeRlpFill.bodyPrice cacheLimit valueLimit+1)
    args called (body_cost (data.call callee nodeCell))
  omega

end NodeRlp

namespace NodeHash

def body : ProgHOL 64:=match Guest.Software.guestFn_node_hash with | .function fn=>progToHOL fn.body | _=>.skip
def formals : List (MlS×ShapeHOL):=[(ofString "node",.one)]
def afterCache : ProgHOL 64:=match body with | .dec _ _ _ rest=>rest | _=>.skip
def rlpCall : ProgHOL 64:=match afterCache with | .seq _ rest=>rest | _=>.skip
def afterRlp : ProgHOL 64:=match rlpCall with | .decCall _ _ _ _ rest=>rest | _=>.skip

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "node_hash")=some (formals,body,.one) := by
  have checked:=OriginalCode.indexed code installed 264 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.Software.guestFn_node_hash) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,formals,body,
    Guest.Software.guestFn_node_hash,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

set_option maxRecDepth 100000 in
theorem shapes : body=.dec (ofString "cached") .one (NodeRlp.nodeField 24#64) afterCache ∧
    rlpCall=.decCall (ofString "r") (.comb [.one,.one]) (ofString "node_rlp") [localVar "node"] afterRlp := by
  simp only [body,afterCache,rlpCall,afterRlp,NodeRlp.nodeField,localVar,
    Guest.Software.guestFn_node_hash,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil]
  trivial

set_option maxRecDepth 100000 in
theorem after_cache_selected (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (cached : source.locals.lookup (ofString "cached")=some (.val (.word 0#64))) :
    evaluateHOLFiniteState source afterCache=evaluateHOLFiniteState source rlpCall := by
  have shape : afterCache=.seq (.ite (.cmp .notEqual (localVar "cached") (.const 0#64))
      (.return (localVar "cached")) .skip) rlpCall:=by
    simp only [afterCache,rlpCall,body,Guest.Software.guestFn_node_hash,progToHOL,expToHOL,shapeToHOL,
      List.map_cons,List.map_nil,localVar]
  rw [shape,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite]
  simp [evalHOLExact,toExact,localVar,cached,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,evaluateHOLFiniteState_skip]


def afterAllocation : ProgHOL 64:=match afterRlp with | .decCall _ _ _ _ rest=>rest | _=>.skip
def hashArguments : List (ExpHOL 64):=[.rfield 0 (localVar "r"),.rfield 1 (localVar "r"),localVar "h"]
def hashCall : ProgHOL 64:=.call (some (none,none)) (ofString "keccak256") hashArguments

def bodyPrice (cacheLimit valueLimit : Nat) : Nat:=NodeRlpFill.bodyPrice cacheLimit valueLimit+CurrentKeccak.Hash.bodyPrice cacheLimit+5

set_option maxRecDepth 100000 in
theorem allocation_shape : afterRlp=.decCall (ofString "h") .one (ofString "alloc") [.const 32#64] afterAllocation ∧
    afterAllocation=.seq hashCall (.seq (.store (.op .add [localVar "node",.const 24#64]) (localVar "h")) (.return (localVar "h"))) ∧
    afterCache=.seq (.ite NodeRlp.cachedTest (.return (localVar "cached")) .skip) rlpCall := by
  simp only [body,afterCache,rlpCall,afterRlp,afterAllocation,hashCall,hashArguments,NodeRlp.cachedTest,localVar,
    Guest.Software.guestFn_node_hash,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none]
  trivial

/-- Price all allocation/hash outcomes from the actual returned RLP pair.
Only its byte-count bound is needed; readable future input is not assumed. -/
theorem after_rlp_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (buffer length : BitVec 64) (limit : Nat)
    (installed : OriginalCode.Installed source.code)
    (rCell : source.locals.lookup (ofString "r")=some (.rStruct [.val (.word buffer),.val (.word length)]))
    (bounded : length.toNat≤limit) (small : limit+136<2^64) :
    source.clock-(evaluateHOLFiniteState source afterRlp).2.clock≤CurrentKeccak.Hash.bodyPrice limit+3 := by
  rw [allocation_shape.1]
  have price:=ClockCost.scalar_scope_current source "h" (ofString "alloc") [.const 32#64] PersistentAlloc.formals PersistentAlloc.body afterAllocation .one
    1 (CurrentKeccak.Hash.bodyPrice limit+1) (PersistentAlloc.original_code source.code installed) (PersistentAlloc.body_price source.code installed) (by
      intro target h codeEq
      let ready:=CallNormal.continuationEntry source target "h" (.val (.word h))
      have readyR : ready.locals.lookup (ofString "r")=some (.rStruct [.val (.word buffer),.val (.word length)]):=by
        simpa [ready,CallNormal.continuationEntry,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,ofString] using rCell
      have readyH : ready.locals.lookup (ofString "h")=some (.val (.word h)):=by
        simp [ready,CallNormal.continuationEntry,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
      have readyCode : OriginalCode.Installed ready.code:=by change OriginalCode.Installed target.code; rw [codeEq]; exact installed
      have args : evalListHOLFinite ready (h:=fun query=>Classical.propDecidable (ready.memaddrs query)) hashArguments=
          some (CurrentKeccak.Hash.values buffer h length.toNat):=by
        simp [hashArguments,CurrentKeccak.Hash.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,readyR,readyH]
      have actual:=CurrentKeccak.Hash.call_cost ready hashArguments buffer h length.toNat (by omega) readyCode args
      have mono : CurrentKeccak.Hash.bodyPrice length.toNat≤CurrentKeccak.Hash.bodyPrice limit:=by
        have blocks : length.toNat/136≤limit/136:=Nat.div_le_div_right bounded
        simp only [CurrentKeccak.Hash.bodyPrice]
        omega
      have hashPrice : ready.clock-(evaluateHOLFiniteState ready hashCall).2.clock≤CurrentKeccak.Hash.bodyPrice limit+1:=by exact actual.trans (Nat.add_le_add_right mono 1)
      rw [allocation_shape.2.1]
      have footer : ClockCost.Bound ready.code (.seq (.store (.op .add [localVar "node",.const 24#64]) (localVar "h")) (.return (localVar "h"))) 0:=
        ClockCost.sequence ready.code _ _ 0 0 (ClockCost.store ready.code _ _) (ClockCost.returned ready.code _)
      simpa only [Nat.add_zero,ready,CallNormal.continuationEntry,setVarHOLFinite] using ClockCost.sequence_current ready hashCall _ _ 0 hashPrice footer)
  omega

/-- The real scoped RLP result supplies both hash operands and its bound. -/
theorem rlp_call_cost {source : PanSemStateFiniteExact 64 Guest.HostMemory} {node heap cursor floor : BitVec 64}
    {lower frontier inputEnd cacheLimit valueLimit : Nat} (data : NodeRlp.Entry source node heap cursor floor lower frontier inputEnd cacheLimit valueLimit) :
    source.clock-(evaluateHOLFiniteState source rlpCall).2.clock≤bodyPrice cacheLimit valueLimit := by
  obtain ⟨callee,called,nodeCell⟩:=word_environment source.code.lookup (ofString "node_rlp") (ofString "node") NodeRlp.body (.comb [.one,.one]) node
    (NodeRlp.original_code source.code data.live.code)
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) [localVar "node"]=some [.val (.word node)]:=by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,data.nodeCell]
  rw [shapes.2]
  have price:=ClockCost.scoped_reached_current source "r" (.comb [.one,.one]) (ofString "node_rlp") [localVar "node"] _ NodeRlp.body afterRlp callee (.comb [.one,.one])
    (NodeRlpFill.bodyPrice cacheLimit valueLimit+1) (CurrentKeccak.Hash.bodyPrice cacheLimit+3) args called (NodeRlp.body_cost (data.call callee nodeCell)) (by
      intro target returned run _checked
      obtain ⟨⟨output⟩,_rlpFrame⟩:=NodeRlp.body_normal (data.call callee nodeCell) returned run
      let ready:=CallNormal.continuationEntry source target "r" returned
      have rCell : ready.locals.lookup (ofString "r")=some (.rStruct [.val (.word output.buffer),.val (.word output.length)]):=by
        simp [ready,CallNormal.continuationEntry,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,output.answer]
      exact after_rlp_cost ready output.buffer output.length cacheLimit output.live.code rCell output.bounded output.persistent.cacheSmall)
  unfold bodyPrice
  omega

/-- A genuine cached hash returns without entering encoding or hashing. -/
theorem cache_selected (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cached : BitVec 64)
    (cachedCell : source.locals.lookup (ofString "cached")=some (.val (.word cached))) (nonzero : cached≠0#64) :
    evaluateHOLFiniteState source afterCache=evaluateHOLFiniteState source (.return (localVar "cached")) := by
  have selected : evaluateHOLFiniteState source (.ite NodeRlp.cachedTest (.return (localVar "cached")) .skip)=evaluateHOLFiniteState source (.return (localVar "cached")):=by
    rw [evaluateHOLFiniteState_ite]
    simp [NodeRlp.cachedTest,evalHOLExact,toExact,localVar,cachedCell,nonzero,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  rw [allocation_shape.2.2,stopped_sequence_eq source _ _ (by rw [selected]; exact NoFallthrough.returned _ source),selected]

/-- Hash-tag roots may use their real populated hash cache directly;
no nonhash encoding hypothesis is needed for that actual fast path. -/
theorem cache_hit_cost {source : PanSemStateFiniteExact 64 Guest.HostMemory} {node heap : BitVec 64}
    {lower frontier inputEnd cacheLimit valueLimit : Nat} (data : NodeRlpFill.Persistent source heap lower frontier inputEnd cacheLimit valueLimit)
    (member : data.graph.valid node) (active : node≠0#64)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node)))
    (nonzero : wordAt source.memory (node+24#64)≠0#64) : source.clock-(evaluateHOLFiniteState source body).2.clock≤0 := by
  have read:=NodeRlp.field_read data member active nodeCell 24 (by decide) (by decide)
  rw [shapes.1]
  apply ClockCost.declared_current source "cached" (NodeRlp.nodeField 24#64) (wordAt source.memory (node+24#64)) afterCache 0 read
  rw [cache_selected _ _ (bind_lookup_same _ _ _) nonzero]
  exact ClockCost.returned source.code _ _ rfl

theorem after_cache_cost {source : PanSemStateFiniteExact 64 Guest.HostMemory} {node heap cursor floor cached : BitVec 64}
    {lower frontier inputEnd cacheLimit valueLimit : Nat} (data : NodeRlp.Entry source node heap cursor floor lower frontier inputEnd cacheLimit valueLimit)
    (cachedCell : source.locals.lookup (ofString "cached")=some (.val (.word cached))) :
    source.clock-(evaluateHOLFiniteState source afterCache).2.clock≤bodyPrice cacheLimit valueLimit := by
  by_cases zero : cached=0#64
  · subst cached
    rw [after_cache_selected source cachedCell]
    exact rlp_call_cost data
  · rw [cache_selected source cached cachedCell zero]
    exact (ClockCost.returned source.code _ source rfl).trans (Nat.zero_le _)

/-- Complete actual node_hash source allowance, covering cache hits,
encoding, allocation, software Keccak, cache store and every failed outcome. -/
theorem body_cost {source : PanSemStateFiniteExact 64 Guest.HostMemory} {node heap cursor floor : BitVec 64}
    {lower frontier inputEnd cacheLimit valueLimit : Nat} (data : NodeRlp.Entry source node heap cursor floor lower frontier inputEnd cacheLimit valueLimit) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤bodyPrice cacheLimit valueLimit := by
  rw [shapes.1]
  apply ClockCost.scalar_declaration_current source (ofString "cached") (NodeRlp.nodeField 24#64) afterCache _
  intro cached
  exact after_cache_cost (data.bindCached cached) (bind_lookup_same _ _ _)

/-- Both legitimate current root kinds are covered: a nonhash node uses
the actual encoding path, while a populated hash cache returns directly. -/
theorem current_body_cost {source : PanSemStateFiniteExact 64 Guest.HostMemory} {node heap cursor floor : BitVec 64}
    {lower frontier inputEnd cacheLimit valueLimit : Nat} (data : NodeRlpFill.Persistent source heap lower frontier inputEnd cacheLimit valueLimit)
    (member : data.graph.valid node) (active : node≠0#64)
    (serializable : wordAt source.memory node≠0#64 ∨ wordAt source.memory (node+24#64)≠0#64)
    (live : Rlp.LiveArena source) (arena : Rlp.Validation.Arena source cursor floor)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node))) (cacheRoom : 251658240≤cacheLimit) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤bodyPrice cacheLimit valueLimit := by
  rcases serializable with nonHash|cached
  · exact body_cost ⟨data,member,active,nonHash,live,arena,nodeCell,cacheRoom⟩
  · exact (cache_hit_cost data member active nodeCell cached).trans (Nat.zero_le _)

theorem call_cost {source : PanSemStateFiniteExact 64 Guest.HostMemory} {node heap cursor floor : BitVec 64}
    {lower frontier inputEnd cacheLimit valueLimit : Nat} (data : NodeRlpFill.Persistent source heap lower frontier inputEnd cacheLimit valueLimit)
    (member : data.graph.valid node) (active : node≠0#64)
    (serializable : wordAt source.memory node≠0#64 ∨ wordAt source.memory (node+24#64)≠0#64)
    (live : Rlp.LiveArena source) (arena : Rlp.Validation.Arena source cursor floor) (cacheRoom : 251658240≤cacheLimit)
    (destination : Option (Option MlS)) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=some [.val (.word node)]) :
    source.clock-(evaluateHOLFiniteState source (.call (LocalEffects.callInfo destination) (ofString "node_hash") arguments)).2.clock≤bodyPrice cacheLimit valueLimit+1 := by
  obtain ⟨callee,called,nodeCell⟩:=CallNormal.unary_environment source.code.lookup (ofString "node_hash") "node" body node (original_code source.code live.code)
  exact ClockCost.call_current source destination (ofString "node_hash") arguments _ body callee .one (bodyPrice cacheLimit valueLimit) args called
    (current_body_cost (data.call callee) member active serializable (live.of_frame rfl) (arena.of_fields source _ cursor floor rfl rfl) nodeCell cacheRoom)

end NodeHash

namespace Root

def body : ProgHOL 64:=match Guest.Software.guestFn_mpt_root with | .function fn=>progToHOL fn.body | _=>.skip
def formals : List (MlS×ShapeHOL):=[(ofString "m",.one),(ofString "out",.one)]
def afterRoot : ProgHOL 64:=match body with | .dec _ _ _ rest=>rest | _=>.skip
def emptyBranch : ProgHOL 64:=match afterRoot with | .seq (.ite _ yes _) _=>yes | _=>.skip
def hashCall : ProgHOL 64:=match afterRoot with | .seq _ rest=>rest | _=>.skip
def afterHash : ProgHOL 64:=match hashCall with | .decCall _ _ _ _ rest=>rest | _=>.skip
def copyArguments : List (ExpHOL 64):=[localVar "out",.var .global (ofString "empty_trie_root"),.const 32#64]
def copyCall : ProgHOL 64:=.call (some (none,none)) (ofString "memcpy") copyArguments
def rootExpression : ExpHOL 64:=.load .one (.op .add [localVar "m",.const 0#64])
def rootTest : ExpHOL 64:=.cmp .equal (localVar "root") (.const 0#64)

/-- Actual trie header and current serializer data. A nonempty root is
encoded from a nonhash node or uses its genuine existing hash cache. -/
structure Entry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (m out root heap cursor floor : BitVec 64)
    (lower frontier inputEnd cacheLimit valueLimit : Nat) where
  persistent : NodeRlpFill.Persistent source heap lower frontier inputEnd cacheLimit valueLimit
  live : Rlp.LiveArena source
  arena : Rlp.Validation.Arena source cursor floor
  mCell : source.locals.lookup (ofString "m")=some (.val (.word m))
  outCell : source.locals.lookup (ofString "out")=some (.val (.word out))
  headerMapped : source.memaddrs m
  rootStored : source.memory m=.word root
  member : persistent.graph.valid root
  serializable : root≠0#64→wordAt source.memory root≠0#64 ∨ wordAt source.memory (root+24#64)≠0#64
  cacheRoom : 251658240≤cacheLimit

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "mpt_root")=some (formals,body,.one) := by
  have checked:=OriginalCode.indexed code installed 265 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.Software.guestFn_mpt_root) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,formals,body,
    Guest.Software.guestFn_mpt_root,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

set_option maxRecDepth 100000 in
theorem shapes : body=.dec (ofString "root") .one rootExpression afterRoot ∧
    afterRoot=.seq (.ite rootTest emptyBranch .skip) hashCall ∧
    emptyBranch=.seq copyCall (.return (.const 0#64)) ∧
    hashCall=.decCall (ofString "h") .one (ofString "node_hash") [localVar "root"] afterHash := by
  simp only [body,afterRoot,emptyBranch,hashCall,afterHash,copyCall,copyArguments,rootExpression,rootTest,localVar,
    Guest.Software.guestFn_mpt_root,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none]
  trivial


def bodyPrice (cacheLimit valueLimit : Nat) : Nat:=NodeHash.bodyPrice cacheLimit valueLimit+43

set_option maxRecDepth 100000 in
theorem after_hash_shape : afterHash=.seq (.call (some (none,none)) (ofString "memcpy") [localVar "out",localVar "h",.const 32#64]) (.return (.const 0#64)) := by
  simp only [afterHash,hashCall,afterRoot,body,localVar,Guest.Software.guestFn_mpt_root,
    progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none]

/-- A32-byte copy has a uniform allowance even when a pointer lookup,
alignment choice or memory access fails in the actual call. -/
theorem copy32_cost (code) (installed : OriginalCode.Installed code) (dst src : ExpHOL 64) :
    ClockCost.Bound code (.call (some (none,none)) (ofString "memcpy") [dst,src,.const 32#64]) 42 := by
  intro source same
  exact BufferDynamicCost.copy_cost source dst src (.const 32#64) 32 (by rw [same]; exact installed) (by decide) rfl

theorem empty_cost (code) (installed : OriginalCode.Installed code) : ClockCost.Bound code emptyBranch 42 := by
  rw [shapes.2.2.1]
  exact ClockCost.sequence code _ _ 42 0 (copy32_cost code installed (localVar "out") (.var .global (ofString "empty_trie_root"))) (ClockCost.returned code _)

theorem after_hash_cost (code) (installed : OriginalCode.Installed code) : ClockCost.Bound code afterHash 42 := by
  rw [after_hash_shape]
  exact ClockCost.sequence code _ _ 42 0 (copy32_cost code installed (localVar "out") (localVar "h")) (ClockCost.returned code _)

def Entry.bindRoot {source : PanSemStateFiniteExact 64 Guest.HostMemory} {m out root heap cursor floor : BitVec 64}
    {lower frontier inputEnd cacheLimit valueLimit : Nat} (data : Entry source m out root heap cursor floor lower frontier inputEnd cacheLimit valueLimit) :
    Entry (bind source "root" root) m out root heap cursor floor lower frontier inputEnd cacheLimit valueLimit :=
  {data with
    persistent:={data.persistent with environment:=data.persistent.environment.of_frame rfl},live:=data.live.of_frame rfl,
    arena:=data.arena.of_fields source _ cursor floor rfl rfl,mCell:=(bind_lookup_other source "root" "m" root (by decide)).trans data.mCell,
    outCell:=(bind_lookup_other source "root" "out" root (by decide)).trans data.outCell}

/-- The nonempty branch executes real node_hash and its bounded software
Keccak before the actual output copy. No normal hash result is assumed. -/
theorem hash_call_cost {source : PanSemStateFiniteExact 64 Guest.HostMemory} {m out root heap cursor floor : BitVec 64}
    {lower frontier inputEnd cacheLimit valueLimit : Nat} (data : Entry source m out root heap cursor floor lower frontier inputEnd cacheLimit valueLimit)
    (active : root≠0#64) (rootCell : source.locals.lookup (ofString "root")=some (.val (.word root))) :
    source.clock-(evaluateHOLFiniteState source hashCall).2.clock≤bodyPrice cacheLimit valueLimit := by
  obtain ⟨callee,called,nodeCell⟩:=CallNormal.unary_environment source.code.lookup (ofString "node_hash") "node" NodeHash.body root (NodeHash.original_code source.code data.live.code)
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) [localVar "root"]=some [.val (.word root)]:=by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,rootCell]
  have calleePrice:=NodeHash.current_body_cost (data.persistent.call callee) data.member active (data.serializable active)
    (data.live.of_frame rfl) (data.arena.of_fields source _ cursor floor rfl rfl) nodeCell data.cacheRoom
  rw [shapes.2.2.2]
  have price:=ClockCost.scoped_current source (ofString "h") .one (ofString "node_hash") [localVar "root"] _ NodeHash.body afterHash callee .one
    (NodeHash.bodyPrice cacheLimit valueLimit) 42 args called calleePrice (after_hash_cost source.code data.live.code)
  unfold bodyPrice
  omega

/-- The actual zero-root branch returns or aborts before the hash suffix;
a nonzero root enters the complete real hash/copy branch. -/
theorem after_root_select (source : PanSemStateFiniteExact 64 Guest.HostMemory) (root : BitVec 64)
    (rootCell : source.locals.lookup (ofString "root")=some (.val (.word root))) :
    evaluateHOLFiniteState source afterRoot=if root=0#64 then evaluateHOLFiniteState source emptyBranch else evaluateHOLFiniteState source hashCall := by
  have read : eval source rootTest=some (.val (.word (if root=0#64 then 1#64 else 0#64))):=by
    simp [eval,rootTest,localVar,evalHOLExact,toExact,rootCell,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  rw [shapes.2.1,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite]
  simp only [eval] at read
  rw [read]
  by_cases zero : root=0#64
  · simp only [if_pos zero,show (1#64 : BitVec 64)≠0 from by decide,if_false]
    have stops:=NoFallthrough.sequence copyCall (.return (.const 0#64)) (NoFallthrough.returned _) source
    rw [←shapes.2.2.1] at stops
    rw [←evaluateHOLFiniteState_seq_line780,stopped_sequence_eq source emptyBranch hashCall stops]
  · simp only [if_neg zero,if_pos rfl,evaluateHOLFiniteState_skip]
    rfl

theorem after_root_cost {source : PanSemStateFiniteExact 64 Guest.HostMemory} {m out root heap cursor floor : BitVec 64}
    {lower frontier inputEnd cacheLimit valueLimit : Nat} (data : Entry source m out root heap cursor floor lower frontier inputEnd cacheLimit valueLimit)
    (rootCell : source.locals.lookup (ofString "root")=some (.val (.word root))) :
    source.clock-(evaluateHOLFiniteState source afterRoot).2.clock≤bodyPrice cacheLimit valueLimit := by
  rw [after_root_select source root rootCell]
  by_cases zero : root=0#64
  · rw [if_pos zero]
    exact (empty_cost source.code data.live.code source rfl).trans (by unfold bodyPrice; omega)
  · rw [if_neg zero]
    exact hash_call_cost data zero rootCell

/-- Current mpt_root has a finite complete body allowance at its actual
physical entry, for empty and nonempty indexed roots and every outcome. -/
theorem body_cost {source : PanSemStateFiniteExact 64 Guest.HostMemory} {m out root heap cursor floor : BitVec 64}
    {lower frontier inputEnd cacheLimit valueLimit : Nat} (data : Entry source m out root heap cursor floor lower frontier inputEnd cacheLimit valueLimit) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤bodyPrice cacheLimit valueLimit := by
  have read : eval source rootExpression=some (.val (.word root)):=by
    apply Witness.load_word_read source _ m root _ data.headerMapped data.rootStored
    simp [rootExpression,eval,evalHOLExact,evalListHOLExact,toExact,localVar,data.mCell,valueIsWord,valueWord,wordOpHOL,wordOp]
  rw [shapes.1]
  exact ClockCost.declared_current source "root" rootExpression root afterRoot _ read (after_root_cost data.bindRoot (bind_lookup_same _ _ _))

/-- Price the real mpt_root caller from current header/serializer facts.
Formal m/out bindings are obtained from its actual two-word arguments. -/
theorem call_cost {source : PanSemStateFiniteExact 64 Guest.HostMemory} {m out root heap cursor floor : BitVec 64}
    {lower frontier inputEnd cacheLimit valueLimit : Nat} (data : NodeRlpFill.Persistent source heap lower frontier inputEnd cacheLimit valueLimit)
    (member : data.graph.valid root) (serializable : root≠0#64→wordAt source.memory root≠0#64 ∨ wordAt source.memory (root+24#64)≠0#64)
    (live : Rlp.LiveArena source) (arena : Rlp.Validation.Arena source cursor floor)
    (headerMapped : source.memaddrs m) (rootStored : source.memory m=.word root) (cacheRoom : 251658240≤cacheLimit)
    (destination : Option (Option MlS)) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=some [.val (.word m),.val (.word out)]) :
    source.clock-(evaluateHOLFiniteState source (.call (LocalEffects.callInfo destination) (ofString "mpt_root") arguments)).2.clock≤bodyPrice cacheLimit valueLimit+1 := by
  obtain ⟨callee,called,mCell,outCell⟩:=word_pair_environment source.code.lookup (ofString "mpt_root") (ofString "m") (ofString "out") body .one m out (by decide)
    (original_code source.code live.code)
  let entry : Entry (callEntryStateHOLFinite source callee) m out root heap cursor floor lower frontier inputEnd cacheLimit valueLimit:={
    persistent:=data.call callee,live:=live.of_frame rfl,arena:=arena.of_fields source _ cursor floor rfl rfl,
    mCell:=mCell,outCell:=outCell,headerMapped:=headerMapped,rootStored:=rootStored,member:=member,serializable:=serializable,cacheRoom:=cacheRoom}
  exact ClockCost.call_current source destination (ofString "mpt_root") arguments _ body callee .one (bodyPrice cacheLimit valueLimit) args called (body_cost entry)

/-- Exact local source allowance at the persistent cache and input caps. -/
theorem bodyPrice_at_window : bodyPrice 251658240 268435456=858256895957420 := by decide

end Root
end InitECandidate.Solver.Mpt.CurrentTrieRoot

#print axioms InitECandidate.Solver.Mpt.CurrentTrieRoot.NodeRlp.original_code
#print axioms InitECandidate.Solver.Mpt.CurrentTrieRoot.NodeRlp.Entry.bindCached
#print axioms InitECandidate.Solver.Mpt.CurrentTrieRoot.NodeRlp.Entry.field_read
#print axioms InitECandidate.Solver.Mpt.CurrentTrieRoot.NodeRlp.after_tag_selected
#print axioms InitECandidate.Solver.Mpt.CurrentTrieRoot.NodeRlp.fill_tail_cost
#print axioms InitECandidate.Solver.Mpt.CurrentTrieRoot.NodeRlp.after_cache_cost
#print axioms InitECandidate.Solver.Mpt.CurrentTrieRoot.NodeRlp.body_cost
#print axioms InitECandidate.Solver.Mpt.CurrentTrieRoot.NodeHash.original_code
#print axioms InitECandidate.Solver.Mpt.CurrentTrieRoot.Root.original_code

#print axioms InitECandidate.Solver.Mpt.CurrentTrieRoot.NodeRlp.field_read
#print axioms InitECandidate.Solver.Mpt.CurrentTrieRoot.NodeRlp.Output.of_frame
#print axioms InitECandidate.Solver.Mpt.CurrentTrieRoot.NodeRlp.pair_return_normal
#print axioms InitECandidate.Solver.Mpt.CurrentTrieRoot.NodeRlp.after_cache_normal
#print axioms InitECandidate.Solver.Mpt.CurrentTrieRoot.NodeRlp.body_normal

#print axioms InitECandidate.Solver.Mpt.CurrentTrieRoot.NodeRlp.Entry.call
#print axioms InitECandidate.Solver.Mpt.CurrentTrieRoot.NodeRlp.call_cost

#print axioms InitECandidate.Solver.Mpt.CurrentTrieRoot.NodeHash.allocation_shape
#print axioms InitECandidate.Solver.Mpt.CurrentTrieRoot.NodeHash.after_rlp_cost
#print axioms InitECandidate.Solver.Mpt.CurrentTrieRoot.NodeHash.rlp_call_cost
#print axioms InitECandidate.Solver.Mpt.CurrentTrieRoot.NodeHash.body_cost

#print axioms InitECandidate.Solver.Mpt.CurrentTrieRoot.Root.copy32_cost
#print axioms InitECandidate.Solver.Mpt.CurrentTrieRoot.Root.empty_cost
#print axioms InitECandidate.Solver.Mpt.CurrentTrieRoot.Root.after_hash_cost
#print axioms InitECandidate.Solver.Mpt.CurrentTrieRoot.Root.hash_call_cost
#print axioms InitECandidate.Solver.Mpt.CurrentTrieRoot.Root.after_root_cost
#print axioms InitECandidate.Solver.Mpt.CurrentTrieRoot.Root.body_cost

#print axioms InitECandidate.Solver.Mpt.CurrentTrieRoot.NodeHash.cache_hit_cost

#print axioms InitECandidate.Solver.Mpt.CurrentTrieRoot.NodeHash.current_body_cost
#print axioms InitECandidate.Solver.Mpt.CurrentTrieRoot.NodeHash.call_cost
#print axioms InitECandidate.Solver.Mpt.CurrentTrieRoot.Root.call_cost

#print axioms InitECandidate.Solver.Mpt.CurrentTrieRoot.Root.bodyPrice_at_window

#print axioms InitECandidate.Solver.Mpt.CurrentTrieRoot.NodeRlp.scoped_normal
