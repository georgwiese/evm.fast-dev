import InitECandidate.Solver.Mpt.NodeRlpBeginHeap
import InitECandidate.Solver.Arenas.ScratchScope
import InitECandidate.Solver.Input.CallPrefixTrace
import InitECandidate.Solver.Rlp.ValidationArena
import InitECandidate.Solver.Input.CallPrefixScopedActual
import InitECandidate.Solver.Input.CallPrefixCommand
import InitECandidate.Solver.WitnessRadix.BindingLookup
import InitECandidate.Solver.WitnessRadix.StoreWord
import InitECandidate.Solver.Mpt.NodeNeedsRlp
import InitECandidate.Solver.Input.AssignedCallData
import InitECandidate.Solver.Input.CounterFlow
import InitECandidate.Solver.Input.ClockCostCurrentLoop
import InitECandidate.Solver.Input.LoopInvariantNoControl
import InitECandidate.Solver.Input.LocalEffectsLoop
import InitECandidate.Solver.Input.LoadWord

namespace InitECandidate.Solver.Mpt.NodeRlpFill
open Input Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

def body : ProgHOL 64:=match Guest.Software.guestFn__node_rlp_fill with | .function fn=>progToHOL fn.body | _=>.skip
def formals : List (MlS×ShapeHOL):=[(ofString "node",.one)]
def afterMark : ProgHOL 64:=match body with | .decCall _ _ _ _ rest=>rest | _=>.skip
def afterFrame : ProgHOL 64:=match afterMark with | .decCall _ _ _ _ rest=>rest | _=>.skip
def afterParent : ProgHOL 64:=match afterFrame with | .seq _ rest=>rest | _=>.skip
def afterNode : ProgHOL 64:=match afterParent with | .seq _ rest=>rest | _=>.skip
def beginAndAfter : ProgHOL 64:=match afterNode with | .seq _ rest=>rest | _=>.skip
def afterBegin : ProgHOL 64:=match beginAndAfter with | .seq _ rest=>rest | _=>.skip
def loopAndAfter : ProgHOL 64:=match afterBegin with | .dec _ _ _ rest=>rest | _=>.skip
def loop : ProgHOL 64:=match loopAndAfter with | .seq first _=>first | _=>.skip
def step : ProgHOL 64:=match loop with | .while _ rest=>rest | _=>.skip
def afterLoop : ProgHOL 64:=match loopAndAfter with | .seq _ rest=>rest | _=>.skip
def test : ExpHOL 64:=.cmp .notEqual (localVar "top") (.const 0#64)
def frameAddress (offset : Nat) : ExpHOL 64:=.op .add [localVar "fr",.const (BitVec.ofNat 64 offset)]
def initialActions : List CallPrefix.Action:=[
  .scoped (ofString "mark") .one (ofString "scratch_mark") [],
  .scoped (ofString "fr") .one (ofString "scratch_alloc") [.const 48#64],
  .command (.store (frameAddress 0) (.const 0#64)),
  .command (.store (frameAddress 8) (localVar "node")),
  .command (.store (frameAddress 16) (.const 0#64))]

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "_node_rlp_fill")=some (formals,body,.one) := by
  have checked:=OriginalCode.indexed code installed 258 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.Software.guestFn__node_rlp_fill) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,body,formals,
    Guest.Software.guestFn__node_rlp_fill,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

set_option maxRecDepth 100000 in
theorem shapes : body=CallPrefix.program initialActions beginAndAfter ∧
    beginAndAfter=.seq (.call (some (none,none)) (ofString "_node_rlp_begin") [localVar "fr",localVar "node"]) afterBegin ∧
    afterBegin=.dec (ofString "top") .one (localVar "fr") loopAndAfter ∧
    loopAndAfter=.seq (.while test step) afterLoop ∧
    afterLoop=.seq (.call (some (none,none)) (ofString "scratch_release") [localVar "mark"]) (.return (.const 0#64)) := by
  simp only [body,afterMark,afterFrame,afterParent,afterNode,beginAndAfter,afterBegin,loopAndAfter,loop,step,afterLoop,test,
    initialActions,CallPrefix.program,frameAddress,localVar,Guest.Software.guestFn__node_rlp_fill,progToHOL,expToHOL,shapeToHOL,
    List.map_cons,List.map_nil,Option.map_some,Option.map_none]
  trivial

/-- Marking, allocating the first48-byte frame and its three stores cost
at most three source ticks on every outcome, including allocation failure. -/
theorem initial_cost (code) (installed : OriginalCode.Installed code) :
    ClockCost.Bound code (CallPrefix.program initialActions .skip) 3 := by
  simp only [initialActions,CallPrefix.program]
  apply ClockCost.scoped_body code _ _ _ _ _ [] (Arenas.markBody .down) .one 0 2
    (Arenas.Scratch.mark_code code installed)
  · rw [Arenas.mark_body]
    exact ClockCost.returned code _
  · apply Arenas.scoped_price code installed .down _ _ _ _ 0
    repeat first
      | apply ClockCost.sequence code _ _ 0 0
      | exact ClockCost.store code _ _
      | exact ClockCost.skip code

theorem initial_never : NoReturn.Never (CallPrefix.program initialActions .skip) := by
  have safe : LocalPrefix (ofString "node") (CallPrefix.program initialActions .skip) := by
    simp only [initialActions,CallPrefix.program]
    repeat first
      | apply LocalPrefix.decCall _ _ _ _ (by decide)
      | apply LocalPrefix.seq
      | exact LocalPrefix.store _ _
      | exact LocalPrefix.skip
  intro F source value
  exact (safe.summary_full source).2.1 value

/-- The real serializer either stops in its first allocation/stores or
reaches its actual begin call with the same lexical action trace. -/
theorem initial_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (installed : OriginalCode.Installed source.code) (outcome : Option (PanSemResultExact 64))
    (run : evaluateHOLFiniteState source body=(outcome,post)) :
    (source.clock-post.clock≤3 ∧ ∀ value,outcome≠some (.returned value)) ∨ ∃ current inner,
      CallPrefix.Execution source initialActions current ∧ current.clock≤source.clock ∧ source.clock-current.clock≤3 ∧
      post.clock=inner.clock ∧ evaluateHOLFiniteState current beginAndAfter=(outcome,inner) := by
  rw [shapes.1] at run
  rcases CallPrefix.priced_trace source post initialActions beginAndAfter 3 (initial_cost source.code installed source rfl) outcome run with stopped|reached
  · exact Or.inl ⟨stopped.1,by intro value; rw [stopped.2]; exact initial_never source value⟩
  · exact Or.inr reached

/-- Actual frame header, with the child cursor range used by the branch
scan. Preparation writes only the other three descriptor fields. -/
structure Header (source : PanSemStateFiniteExact 64 Guest.HostMemory) (frame node parent : BitVec 64) (index : Nat) : Prop where
  arena : AllocatedBytes.Arena frame 48
  aligned : frame.toNat%8=0
  scratch : 2952790016≤frame.toNat
  bounded : index≤16
  parentStored : source.memory frame=.word parent
  nodeStored : source.memory (frame+8#64)=.word node
  indexStored : source.memory (frame+16#64)=.word (BitVec.ofNat 64 index)

theorem Header.after_begin {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    {frame node parent heap : BitVec 64} {index limit allowance : Nat} {value : ValueHOL 64}
    (header : Header source frame node parent index)
    (output : NodeRlpBegin.Output source target node heap frame limit value allowance) : Header target frame node parent index := by
  have different (left right : Nat) (leftInside : left<48) (rightInside : right<48) (unequal : left≠right) :
      frame+BitVec.ofNat 64 left≠frame+BitVec.ofNat 64 right := by
    have first:=byteAddress_toNat frame left (by have upper:=header.arena.upper; omega)
    have second:=byteAddress_toNat frame right (by have upper:=header.arena.upper; omega)
    intro equal
    have number:=congrArg BitVec.toNat equal
    change (byteAddress frame left).toNat=(byteAddress frame right).toNat at number
    rw [first,second] at number
    omega
  have saved (offset : Nat) (inside : offset≤16) : target.memory (frame+BitVec.ofNat 64 offset)=source.memory (frame+BitVec.ofNat 64 offset) := by
    have number:=byteAddress_toNat frame offset (by have upper:=header.arena.upper; omega)
    apply output.outside _
    · change 2952790016≤(byteAddress frame offset).toNat
      rw [number]
      have lower:=header.scratch
      omega
    · exact different offset 24 (by omega) (by decide) (by omega)
    · exact different offset 32 (by omega) (by decide) (by omega)
    · exact different offset 40 (by omega) (by decide) (by omega)
  have parentMemory : target.memory frame=source.memory frame:=by simpa using saved 0 (by decide)
  exact ⟨header.arena,header.aligned,header.scratch,header.bounded,parentMemory.trans header.parentStored,
    (saved 8 (by decide)).trans header.nodeStored,(saved 16 (by decide)).trans header.indexStored⟩

def framePointer (cursor : BitVec 64) : BitVec 64:=Arenas.rounded .down cursor 48#64

theorem allocation_geometry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor floor : BitVec 64)
    (arena : Rlp.Validation.Arena source cursor floor) (room : Arenas.Room .down cursor floor 48#64) :
    AllocatedBytes.Arena (framePointer cursor) 48 ∧ floor.toNat≤(framePointer cursor).toNat ∧
      (framePointer cursor).toNat+48≤cursor.toNat ∧ (framePointer cursor).toNat%8=0 := by
  obtain ⟨first,second,lower,upper,padding,aligned⟩:=Arenas.downward_guards cursor floor 48#64 arena.aligned room
  change floor.toNat≤(framePointer cursor).toNat at lower
  change (framePointer cursor).toNat+48≤cursor.toNat at upper
  exact ⟨⟨by have bound:=arena.lower; omega,by have bound:=arena.upper; omega⟩,lower,upper,aligned⟩

theorem mark_reached (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : BitVec 64)
    (installed : OriginalCode.Installed source.code)
    (scratch : source.globals.lookup (ofString "scratch_ptr")=some (.val (.word cursor)))
    (reached : CallPrefix.Reaches source (.scoped (ofString "mark") .one (ofString "scratch_mark") []) target) :
    target=bind {source with clock:=source.clock-1} "mark" cursor := by
  have code:=Arenas.Scratch.mark_code source.code installed
  have raw : lookupCodeHOLExact source.code.lookup (ofString "scratch_mark") []=
      some (Arenas.markBody .down,(fun _=>none),.one):=by simp [lookupCodeHOLExact,code]
  obtain ⟨callee,called,locals⟩:=CodeEnvironment.finite_lookup source.code.lookup (ofString "scratch_mark") []
    (Arenas.markBody .down) (fun _=>none) .one raw
  obtain ⟨child,value,run,endpoint⟩:=reached.scoped_known (ofString "mark") .one (ofString "scratch_mark") [] []
    (Arenas.markBody .down) callee .one rfl called
  have actual:=Arenas.mark_execute (callEntryStateHOLFinite source callee) .down cursor scratch
  have answer : value=.val (.word cursor):=PanSemResultExact.returned.inj (Option.some.inj (congrArg Prod.fst (run.symm.trans actual)))
  have childEq : child=emptyLocalsHOLFinite (callEntryStateHOLFinite source callee):=congrArg Prod.snd (run.symm.trans actual)
  rw [endpoint,answer,childEq]
  rfl

theorem allocation_reached (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor floor : BitVec 64)
    (installed : OriginalCode.Installed source.code) (arena : Rlp.Validation.Arena source cursor floor)
    (reached : CallPrefix.Reaches source (.scoped (ofString "fr") .one (ofString "scratch_alloc") [.const 48#64]) target) :
    Arenas.Room .down cursor floor 48#64 ∧
      target=bind (Arenas.post {source with clock:=source.clock-1} .down cursor 48#64) "fr" (framePointer cursor) := by
  obtain ⟨callee,called,amountCell⟩:=CallNormal.unary_environment source.code.lookup (ofString "scratch_alloc") "n"
    (Arenas.body .down) 48#64 (Arenas.original_code source.code installed .down)
  obtain ⟨child,value,run,endpoint⟩:=reached.scoped_known (ofString "fr") .one (ofString "scratch_alloc") [.const 48#64]
    [.val (.word 48#64)] (Arenas.body .down) callee .one rfl called
  obtain ⟨room,answer,frame⟩:=Arenas.post_of_normal (callEntryStateHOLFinite source callee) child .down cursor floor 48#64
    amountCell arena.cursorGlobal arena.limitGlobal arena.ordered arena.aligned (Trap.original_code source.code installed) value run
  refine ⟨room,?_⟩
  rw [endpoint,answer]
  have updated:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>
    bind {state with locals:=source.locals} "fr" (framePointer cursor)) frame
  exact updated

def written (source : PanSemStateFiniteExact 64 Guest.HostMemory) (frame : BitVec 64) (offset : Nat) (word : BitVec 64) :=
  {source with memory:=StoreWord.put source.memory (frame+BitVec.ofNat 64 offset) word}

theorem initial_store (source : PanSemStateFiniteExact 64 Guest.HostMemory) (frame word : BitVec 64) (offset : Nat)
    (expression : ExpHOL 64) (inside : offset<48) (aligned : offset%8=0)
    (arena : AllocatedBytes.Arena frame 48) (frameAligned : frame.toNat%8=0)
    (domain : source.memaddrs=InitE.ordinaryDomain)
    (frameCell : source.locals.lookup (ofString "fr")=some (.val (.word frame)))
    (read : eval source expression=some (.val (.word word))) :
    evaluateHOLFiniteState source (.store (frameAddress offset) expression)=(none,written source frame offset word) := by
  have addressRead : eval source (frameAddress offset)=some (.val (.word (frame+BitVec.ofNat 64 offset))):=by
    simp [eval,frameAddress,evalHOLExact,evalListHOLExact,localVar,toExact,frameCell,valueIsWord,valueWord,wordOpHOL,wordOp]
  exact StoreWord.execute source _ _ _ _ addressRead read
    (AllocatedBytes.word_mapped source frame 48 offset domain arena inside frameAligned aligned)

/-- The actually reached five actions derive their first mapped scratch
record. Request room, cursor movement and all three stores come from this
execution; no later begin/finish or body return is an input condition. -/
theorem initial_from_execution (source current : PanSemStateFiniteExact 64 Guest.HostMemory) (node cursor floor : BitVec 64)
    (installed : OriginalCode.Installed source.code) (arena : Rlp.Validation.Arena source cursor floor)
    (floorLower : 2952790016≤floor.toNat)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node)))
    (execution : CallPrefix.Execution source initialActions current) :
    Arenas.Room .down cursor floor 48#64 ∧ Header current (framePointer cursor) node 0#64 0 ∧
      current.locals.lookup (ofString "fr")=some (.val (.word (framePointer cursor))) ∧
      current.locals.lookup (ofString "mark")=some (.val (.word cursor)) ∧
      current.globals.lookup (ofString "scratch_ptr")=some (.val (.word (framePointer cursor))) ∧
      MemoryMetadata.erase {current with globals:=source.globals}=MemoryMetadata.erase source ∧
      (∀ key,key≠ofString "scratch_ptr"→current.globals.lookup key=source.globals.lookup key) ∧
      (∀ query : BitVec 64,query.toNat<(framePointer cursor).toNat ∨ cursor.toNat≤query.toNat→current.memory query=source.memory query) ∧
      current.locals.lookup (ofString "node")=some (.val (.word node)) := by
  rw [initialActions] at execution
  obtain ⟨marked,markReached,afterMarkRun⟩:=execution.head
  have markedEq:=mark_reached source marked cursor installed arena.cursorGlobal markReached
  rw [markedEq] at afterMarkRun
  let marked:=bind {source with clock:=source.clock-1} "mark" cursor
  have markedArena : Rlp.Validation.Arena marked cursor floor:=arena.of_fields source marked cursor floor rfl rfl
  obtain ⟨allocated,allocationReached,stores⟩:=afterMarkRun.head
  obtain ⟨room,allocatedEq⟩:=allocation_reached marked allocated cursor floor installed markedArena allocationReached
  rw [allocatedEq] at stores
  let allocated:=bind (Arenas.post {marked with clock:=marked.clock-1} .down cursor 48#64) "fr" (framePointer cursor)
  obtain ⟨recordArena,aboveFloor,beforeCursor,frameAligned⟩:=allocation_geometry source cursor floor arena room
  have frameCell : allocated.locals.lookup (ofString "fr")=some (.val (.word (framePointer cursor))):=bind_lookup_same _ _ _
  have typedNode : allocated.locals.lookup (ofString "node")=some (.val (.word node)):=
    (bind_lookup_other _ "fr" "node" _ (by decide)).trans ((bind_lookup_other _ "mark" "node" _ (by decide)).trans nodeCell)
  have readNode : eval allocated (localVar "node")=some (.val (.word node)):=by simp [eval,evalHOLExact,localVar,toExact,typedNode]
  let first:=written allocated (framePointer cursor) 0 0#64
  let second:=written first (framePointer cursor) 8 node
  let third:=written second (framePointer cursor) 16 0#64
  have firstRun:=initial_store allocated (framePointer cursor) 0#64 0 (.const 0#64) (by decide) (by decide)
    recordArena frameAligned arena.domain frameCell rfl
  have secondRun:=initial_store first (framePointer cursor) node 8 (localVar "node") (by decide) (by decide)
    recordArena frameAligned arena.domain frameCell readNode
  have thirdRun:=initial_store second (framePointer cursor) 0#64 16 (.const 0#64) (by decide) (by decide)
    recordArena frameAligned arena.domain frameCell rfl
  have finished:=((stores.command_known _ _ firstRun).command_known _ _ secondRun).command_known _ _ thirdRun
  have same : current=third:=by cases finished; rfl
  rw [same]
  have different (left right : Nat) (firstInside : left<48) (secondInside : right<48) (unequal : left≠right) :
      framePointer cursor+BitVec.ofNat 64 left≠framePointer cursor+BitVec.ofNat 64 right:=by
    have firstNumber:=byteAddress_toNat (framePointer cursor) left (by have upper:=recordArena.upper; omega)
    have secondNumber:=byteAddress_toNat (framePointer cursor) right (by have upper:=recordArena.upper; omega)
    intro equal
    have number:=congrArg BitVec.toNat equal
    change (byteAddress (framePointer cursor) left).toNat=(byteAddress (framePointer cursor) right).toNat at number
    rw [firstNumber,secondNumber] at number
    omega
  refine ⟨room,⟨recordArena,frameAligned,Nat.le_trans floorLower aboveFloor,by decide,?_,?_,?_⟩,frameCell,?_,?_,?_,?_,?_,typedNode⟩
  · have awayEight : framePointer cursor≠framePointer cursor+8#64:=by simpa using different 0 8 (by decide) (by decide) (by decide)
    have awaySixteen : framePointer cursor≠framePointer cursor+16#64:=by simpa using different 0 16 (by decide) (by decide) (by decide)
    simp [third,second,first,written,StoreWord.put,awayEight,awaySixteen]
  · have away:=different 8 16 (by decide) (by decide) (by decide)
    simp [third,second,written,StoreWord.put,away]
  · simp [third,written,StoreWord.put]
  · exact (bind_lookup_other _ "fr" "mark" _ (by decide)).trans (bind_lookup_same _ _ _)
  · simp [third,second,first,written,allocated,Arenas.post,Arenas.pointerName,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,framePointer]
  · rfl
  · intro key notScratch
    simp [third,second,first,written,allocated,marked,Arenas.post,Arenas.pointerName,QueryBranch.bind,setVarHOLFinite,
      HolFiniteMapExact.update,FUPDATE,notScratch,Ne.symm notScratch]
  · intro query outside
    have away (offset : Nat) (inside : offset<48) : query≠framePointer cursor+BitVec.ofNat 64 offset := by
      have number:=byteAddress_toNat (framePointer cursor) offset (by have upper:=recordArena.upper; omega)
      intro equal
      have observed:=congrArg BitVec.toNat equal
      change query.toNat=(byteAddress (framePointer cursor) offset).toNat at observed
      rw [number] at observed
      rcases outside with before|after
      · omega
      · omega
    have zeroAway : query≠framePointer cursor:=by simpa using away 0 (by decide)
    simp [third,second,first,written,StoreWord.put,zeroAway,away 8 (by decide),away 16 (by decide)]
    rfl

def recordsLeft (cursor floor : Nat) : Nat:=(cursor-floor)/48
def rank (remaining depth : Nat) : Nat:=2*remaining+depth

theorem push_rank (remaining next depth : Nat) (spent : next+1≤remaining) : rank next (depth+1)<rank remaining depth := by
  simp only [rank]
  omega

theorem pop_rank (remaining depth : Nat) : rank remaining depth<rank remaining (depth+1) := by
  simp only [rank]
  omega

/-- A successful real48-byte downward allocation reduces the remaining
record budget even when its entering cursor needed alignment padding. -/
theorem allocation_budget (cursor floor : BitVec 64) (aligned : floor.toNat%8=0)
    (room : Arenas.Room .down cursor floor 48#64) :
    recordsLeft (Arenas.rounded .down cursor 48#64).toNat floor.toNat+1≤recordsLeft cursor.toNat floor.toNat := by
  obtain ⟨first,second,lower,upper,padding,nextAligned⟩:=Arenas.downward_guards cursor floor 48#64 aligned room
  change (Arenas.rounded .down cursor 48#64).toNat+48≤cursor.toNat at upper
  simp only [recordsLeft]
  omega

theorem initial_rank_bound (cursor floor : BitVec 64) (aligned : floor.toNat%8=0)
    (lower : 2952790016≤floor.toNat) (upper : cursor.toNat≤2965299200)
    (room : Arenas.Room .down cursor floor 48#64) :
    rank (recordsLeft (Arenas.rounded .down cursor 48#64).toNat floor.toNat) 1≤521215 := by
  have spent:=allocation_budget cursor floor aligned room
  simp only [recordsLeft,rank] at *
  omega

/-- The actual reached record retains a current live arena and the
uniform initial traversal rank, with the same saved mark and caller data. -/
theorem initial_live (source current : PanSemStateFiniteExact 64 Guest.HostMemory) (node cursor floor : BitVec 64)
    (live : Rlp.LiveArena source) (arena : Rlp.Validation.Arena source cursor floor)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node)))
    (execution : CallPrefix.Execution source initialActions current) :
    Arenas.Room .down cursor floor 48#64 ∧ Header current (framePointer cursor) node 0#64 0 ∧
      Rlp.Validation.Arena current (framePointer cursor) floor ∧ Rlp.LiveArena current ∧
      current.locals.lookup (ofString "fr")=some (.val (.word (framePointer cursor))) ∧
      current.locals.lookup (ofString "mark")=some (.val (.word cursor)) ∧
      rank (recordsLeft (framePointer cursor).toNat floor.toNat) 1≤521215 ∧
      (∀ query : BitVec 64,query.toNat<(framePointer cursor).toNat ∨ cursor.toNat≤query.toNat→current.memory query=source.memory query) := by
  obtain ⟨floorLower,cursorUpper⟩:=live.bounds arena
  obtain ⟨room,header,frCell,markCell,scratchCell,metadata,others,memory,finalNode⟩:=
    initial_from_execution source current node cursor floor live.code arena floorLower nodeCell execution
  obtain ⟨recordArena,aboveFloor,beforeCursor,frameAligned⟩:=allocation_geometry source cursor floor arena room
  have domain:=congrArg PanSemStateFiniteExact.memaddrs metadata
  have code:=congrArg PanSemStateFiniteExact.code metadata
  change current.memaddrs=source.memaddrs at domain
  change current.code=source.code at code
  have next : Rlp.Validation.Arena current (framePointer cursor) floor:=
    ⟨domain.trans arena.domain,scratchCell,(others _ (by decide)).trans arena.limitGlobal,
      aboveFloor,arena.aligned,arena.lower,by have upper:=arena.upper; omega⟩
  have installed : OriginalCode.Installed current.code:=by rw [code]; exact live.code
  exact ⟨room,header,next,Rlp.LiveArena.of_validation next floorLower (by omega) installed,frCell,markCell,
    initial_rank_bound cursor floor arena.aligned floorLower cursorUpper room,memory⟩

/-- The genuine reached record supplies all operands and the current
physical graph needed by the first begin call. No begin return is assumed. -/
theorem initial_begin_entry (source current : PanSemStateFiniteExact 64 Guest.HostMemory) (node heap cursor floor : BitVec 64)
    (lower limit : Nat) (property : BitVec 64→BitVec 64→Prop)
    (data : NodeRlpBegin.Entry source node heap lower limit property)
    (live : Rlp.LiveArena source) (arena : Rlp.Validation.Arena source cursor floor)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node)))
    (execution : CallPrefix.Execution source initialActions current) :
    Header current (framePointer cursor) node 0#64 0 ∧
      Nonempty (NodeRlpBegin.Entry current node heap lower limit property) ∧
      current.locals.lookup (ofString "node")=some (.val (.word node)) ∧
      current.locals.lookup (ofString "fr")=some (.val (.word (framePointer cursor))) := by
  obtain ⟨floorLower,cursorUpper⟩:=live.bounds arena
  obtain ⟨room,header,frCell,markCell,scratchCell,metadata,others,memory,finalNode⟩:=
    initial_from_execution source current node cursor floor live.code arena floorLower nodeCell execution
  have domain:=congrArg PanSemStateFiniteExact.memaddrs metadata
  change current.memaddrs=source.memaddrs at domain
  have heapCell:=(others _ (by decide)).trans data.heapCell
  have next:=data.of_before domain heapCell (by
    intro query earlier
    apply memory query (Or.inl ?_)
    have upper:=data.heapUpper
    have scratch:=header.scratch
    omega)
  exact ⟨header,next,finalNode,frCell⟩

def afterStepNode : ProgHOL 64:=match step with | .dec _ _ _ rest=>rest | _=>.skip
def afterStepKind : ProgHOL 64:=match afterStepNode with | .dec _ _ _ rest=>rest | _=>.skip
def afterStepChild : ProgHOL 64:=match afterStepKind with | .dec _ _ _ rest=>rest | _=>.skip
def stepTail : ProgHOL 64:=match afterStepChild with | .dec _ _ _ rest=>rest | _=>.skip
def selectChild : ProgHOL 64:=match stepTail with | .seq first _=>first | _=>.skip
def branchChoice : ProgHOL 64:=match selectChild with | .ite _ _ rest=>rest | _=>.skip
def branchScope : ProgHOL 64:=match branchChoice with | .ite _ yes _=>yes | _=>.skip
def scanAndStore : ProgHOL 64:=match branchScope with | .dec _ _ _ rest=>rest | _=>.skip
def branchScan : ProgHOL 64:=match scanAndStore with | .seq first _=>first | _=>.skip
def scanTest : ExpHOL 64:=.op .and [
  .cmp .notEqual (.const 0#64) (.cmp .less (localVar "i") (.const 16#64)),
  .cmp .notEqual (.const 0#64) (.cmp .equal (localVar "found") (.const 0#64))]
def scanChild : ExpHOL 64:=.load .one (.op .add [localVar "nd",.const 32#64,.panop .mul [localVar "i",.const 8#64]])
def scanAssign : ProgHOL 64:=.assign .local (ofString "child") scanChild
def scanIncrement : ProgHOL 64:=.assign .local (ofString "i") (.op .add [localVar "i",.const 1#64])
def scanCall : ProgHOL 64:=.call (some (some (.local,ofString "found"),none)) (ofString "_node_needs_rlp") [localVar "child"]
def scanBody : ProgHOL 64:=.seq scanAssign (.seq scanIncrement scanCall)

set_option maxRecDepth 100000 in
theorem branch_scan_shape : branchScan=.while scanTest scanBody ∧
    scanAndStore=.seq branchScan (.store (.op .add [localVar "top",.const 16#64]) (localVar "i")) ∧
    branchScope=.dec (ofString "i") .one (.load .one (.op .add [localVar "top",.const 16#64])) scanAndStore := by
  simp only [branchScan,scanAndStore,branchScope,branchChoice,selectChild,stepTail,afterStepChild,afterStepKind,afterStepNode,
    step,loop,loopAndAfter,afterBegin,beginAndAfter,afterNode,afterParent,afterFrame,afterMark,body,
    Guest.Software.guestFn__node_rlp_fill,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none,
    scanTest,scanBody,scanAssign,scanChild,scanIncrement,scanCall,localVar]
  trivial

theorem scan_body_safe (key : MlS) (notChild : key≠ofString "child") (notIndex : key≠ofString "i")
    (notFound : key≠ofString "found") : LocalPrefix key scanBody := by
  exact .seq (.assign _ _ notChild) (.seq (.assign _ _ notIndex) (.call (some _) _ _ (by intro name same; cases same; exact notFound)))

theorem scan_body_cost (code) (installed : OriginalCode.Installed code) : ClockCost.Bound code scanBody 1 := by
  exact ClockCost.sequence code _ _ 0 1 (ClockCost.assign code _ _)
    (ClockCost.sequence code _ _ 0 1 (ClockCost.assign code _ _)
      (ClockCost.call_body code (some (some (ofString "found"))) (ofString "_node_needs_rlp") [localVar "child"]
        NodeNeedsRlp.formals NodeNeedsRlp.body .one 0 (NodeNeedsRlp.original_code code installed) (NodeNeedsRlp.body_cost code)))

theorem scan_body_readonly (code) (installed : OriginalCode.Installed code) : LocalEffects.Preserves code scanBody :=
  LocalEffects.sequence code _ _ (LocalEffects.assign code _ _)
    (LocalEffects.sequence code _ _ (LocalEffects.assign code _ _)
      (LocalEffects.call_body code (some (some (ofString "found"))) (ofString "_node_needs_rlp") [localVar "child"]
        NodeNeedsRlp.formals NodeNeedsRlp.body .one (NodeNeedsRlp.original_code code installed) (NodeNeedsRlp.readonly code)))

theorem scan_body_advance : CounterFlow.Advances (ofString "i") 1 scanBody := by
  apply CounterFlow.sequence _ _ _ 0 1
  · exact CounterFlow.preserved _ _ (.assign _ _ (by decide))
  · apply CounterFlow.sequence _ _ _ 1 0
    · exact CounterFlow.increment _
    · exact CounterFlow.preserved _ _ (.call (some _) _ _ (by intro name same; cases same; decide))

/-- An actual continuing needs-RLP call returns a real scalar decision.
The branch scan does not assume a readable child or future helper return. -/
theorem scan_found_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (installed : OriginalCode.Installed source.code) (normal : evaluateHOLFiniteState source scanBody=(none,post)) :
    ∃ word : BitVec 64,post.locals.lookup (ofString "found")=some (.val (.word word)) ∧ (word=0#64 ∨ word=1#64) := by
  obtain ⟨first,firstRun,restRun⟩:=sequence_none source post scanAssign (.seq scanIncrement scanCall) normal
  obtain ⟨second,incrementRun,callRun⟩:=sequence_none first post scanIncrement scanCall restRun
  have installedSecond : OriginalCode.Installed second.code:=by
    rw [(evaluation_fields first second scanIncrement none incrementRun).2.2.2,
      (evaluation_fields source first scanAssign none firstRun).2.2.2]
    exact installed
  obtain ⟨funded,values,actualBody,callee,shape,child,value,args,called,run,checked,endpoint⟩:=
    CallNormal.local_data second post (ofString "found") (ofString "_node_needs_rlp") [localVar "child"] callRun
  have bodyEq:=LocalEffects.lookup_body second.code (ofString "_node_needs_rlp") NodeNeedsRlp.formals NodeNeedsRlp.body .one
    (NodeNeedsRlp.original_code second.code installedSecond) values actualBody callee shape called
  rw [bodyEq] at run
  rcases NodeNeedsRlp.binary (callEntryStateHOLFinite second callee) child value run with zero|one
  · refine ⟨0#64,?_,Or.inl rfl⟩
    rw [endpoint,zero]
    simp [setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
  · refine ⟨1#64,?_,Or.inr rfl⟩
    rw [endpoint,one]
    simp [setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]

def ScanInvariant (source : PanSemStateFiniteExact 64 Guest.HostMemory) : Prop:=
  ∃ index found : BitVec 64,source.locals.lookup (ofString "i")=some (.val (.word index)) ∧
    source.locals.lookup (ofString "found")=some (.val (.word found)) ∧ index.toNat≤16
def scanRank (source : PanSemStateFiniteExact 64 Guest.HostMemory) : Nat:=16-(CounterFlow.counterWord source (ofString "i")).toNat

theorem scan_test_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (index found : BitVec 64)
    (indexCell : source.locals.lookup (ofString "i")=some (.val (.word index)))
    (foundCell : source.locals.lookup (ofString "found")=some (.val (.word found))) (bounded : index.toNat≤16) :
    eval source scanTest=some (.val (.word (if index.toNat<16 ∧ found=0#64 then 1#64 else 0#64))) := by
  have small : index.toNat<9223372036854775808:=by omega
  by_cases active : index.toNat<16 <;> by_cases searching : found=0#64 <;>
    simp [eval,scanTest,evalHOLExact,evalListHOLExact,localVar,toExact,indexCell,foundCell,
      Flapjack.Compiler.Encoders.Asm.wordCmpHOL,Flapjack.Compiler.Encoders.Asm.holAsmSignedLess,small,active,searching,
      valueIsWord,valueWord,wordOpHOL,wordOp] <;> decide

theorem scan_transition (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (installed : OriginalCode.Installed source.code) (valid : ScanInvariant source) (word : BitVec 64)
    (read : evalHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) scanTest=some (.val (.word word)))
    (nonzero : word≠0#64) : 0<scanRank source ∧ ∀ target,
      evaluateHOLFiniteState (decClockHOLFinite source) scanBody=(none,target)→ScanInvariant target ∧ scanRank target<scanRank source := by
  obtain ⟨index,found,indexCell,foundCell,bounded⟩:=valid
  have expected:=scan_test_read source index found indexCell foundCell bounded
  change eval source scanTest=some (.val (.word word)) at read
  have active : index.toNat<16:=by
    by_contra inactive
    rw [if_neg (by intro both; exact inactive both.1)] at expected
    have zero : word=0#64:=by simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using read.symm.trans expected
    exact nonzero zero
  have before : scanRank source=16-index.toNat:=by simp [scanRank,CounterFlow.counterWord,indexCell,valueWord]
  refine ⟨by rw [before]; omega,?_⟩
  intro target bodyRun
  have nextCell:=scan_body_advance (decClockHOLFinite source) target index indexCell bodyRun
  obtain ⟨nextFound,nextFoundCell,binary⟩:=scan_found_normal (decClockHOLFinite source) target installed bodyRun
  have number : (index+1#64).toNat=index.toNat+1:=by
    rw [BitVec.toNat_add_of_lt (by change index.toNat+1<2^64; omega)]
    rfl
  have afterRank : scanRank target=16-(index.toNat+1):=by simp [scanRank,CounterFlow.counterWord,nextCell,valueWord,number]
  exact ⟨⟨index+1#64,nextFound,nextCell,nextFoundCell,by rw [number]; omega⟩,by rw [afterRank,before]; omega⟩

/-- All outcomes of the actual early-exit branch scan cost at most32
source ticks, including failed child loads, callee errors and short clocks. -/
theorem scan_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (installed : OriginalCode.Installed source.code) (valid : ScanInvariant source) :
    source.clock-(evaluateHOLFiniteState source branchScan).2.clock≤32 := by
  rw [branch_scan_shape.1]
  have price:=ClockCost.ranked_loop source.code scanTest scanBody 1 ScanInvariant scanRank (scan_body_cost source.code installed) (by
    intro current codeEq ready word read nonzero
    have currentInstalled : OriginalCode.Installed current.code:=by rw [codeEq]; exact installed
    have progress:=scan_transition current currentInstalled ready word read nonzero
    refine ⟨progress.1,?_⟩
    intro funded
    dsimp only
    intro continuing
    have safe:=(scan_body_safe (ofString "nd") (by decide) (by decide) (by decide)).summary_full (decClockHOLFinite current)
    have normal : (evaluateHOLFiniteState (decClockHOLFinite current) scanBody).1=none:=continuing.resolve_right safe.2.2.2
    exact progress.2 _ (Prod.ext normal rfl)) source rfl valid
  have upper : scanRank source≤16:=Nat.sub_le _ _
  omega

/-- A completed actual scan retains its bounded index/typed decision and
the entire nonlocal state needed by the enclosing serializer frame. -/
theorem scan_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (installed : OriginalCode.Installed source.code) (valid : ScanInvariant source)
    (normal : evaluateHOLFiniteState source branchScan=(none,post)) :
    ScanInvariant post ∧ LocalEffects.erase post=LocalEffects.erase source := by
  rw [branch_scan_shape.1] at normal
  have control (current : PanSemStateFiniteExact 64 Guest.HostMemory):=
    ((scan_body_safe (ofString "nd") (by decide) (by decide) (by decide)).summary_full current).2.2
  have final:=loop_invariant_no_control source.code scanTest scanBody control ScanInvariant (by
    intro current codeEq ready word read nonzero funded target bodyRun
    have currentInstalled : OriginalCode.Installed current.code:=by rw [codeEq]; exact installed
    exact ((scan_transition current currentInstalled ready word read nonzero).2 target bodyRun).1) source post rfl valid normal
  have frame:=LocalEffects.loop source.code scanTest scanBody (scan_body_readonly source.code installed) source rfl
  rw [normal] at frame
  exact ⟨final,frame⟩

def scanIndexExpression : ExpHOL 64:=.load .one (.op .add [localVar "top",.const 16#64])

theorem Header.index_read {source : PanSemStateFiniteExact 64 Guest.HostMemory} {frame node parent : BitVec 64} {index : Nat}
    (header : Header source frame node parent index) (domain : source.memaddrs=InitE.ordinaryDomain)
    (topCell : source.locals.lookup (ofString "top")=some (.val (.word frame))) :
    eval source scanIndexExpression=some (.val (.word (BitVec.ofNat 64 index))) := by
  have topRead : eval source (localVar "top")=some (.val (.word frame)):=by simp [eval,evalHOLExact,localVar,toExact,topCell]
  exact Witness.load_word_read source (Scalar.plus (localVar "top") 16) (frame+16#64) (BitVec.ofNat 64 index)
    (Scalar.plus_read source (localVar "top") frame 16 topRead)
    (AllocatedBytes.word_mapped source frame 48 16 domain header.arena (by decide) header.aligned (by decide)) header.indexStored

/-- The actual frame header supplies the signed scan's bounded initial
counter. Its lexical declaration and final cursor store add no source ticks. -/
theorem branch_scope_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (frame node parent found : BitVec 64) (index : Nat)
    (installed : OriginalCode.Installed source.code) (header : Header source frame node parent index)
    (domain : source.memaddrs=InitE.ordinaryDomain)
    (topCell : source.locals.lookup (ofString "top")=some (.val (.word frame)))
    (foundCell : source.locals.lookup (ofString "found")=some (.val (.word found))) :
    source.clock-(evaluateHOLFiniteState source branchScope).2.clock≤32 := by
  let entered:=bind source "i" (BitVec.ofNat 64 index)
  have valid : ScanInvariant entered:=⟨BitVec.ofNat 64 index,found,bind_lookup_same _ _ _,
    (bind_lookup_other source "i" "found" _ (by decide)).trans foundCell,by change index%2^64≤16; exact (Nat.mod_le _ _).trans header.bounded⟩
  rw [branch_scan_shape.2.2]
  apply ClockCost.declared_current source "i" scanIndexExpression (BitVec.ofNat 64 index) scanAndStore 32 (header.index_read domain topCell)
  rw [branch_scan_shape.2.1]
  exact ClockCost.sequence_current entered _ _ 32 0 (scan_cost entered installed valid) (ClockCost.store entered.code _ _)

/-- The real continuing branch scope writes back its actual bounded scan
cursor. The other header words, all other memory and runtime fields survive. -/
theorem branch_scope_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (frame node parent found : BitVec 64) (index : Nat)
    (installed : OriginalCode.Installed source.code) (header : Header source frame node parent index)
    (domain : source.memaddrs=InitE.ordinaryDomain)
    (topCell : source.locals.lookup (ofString "top")=some (.val (.word frame)))
    (foundCell : source.locals.lookup (ofString "found")=some (.val (.word found)))
    (normal : evaluateHOLFiniteState source branchScope=(none,post)) :
    (∃ nextIndex,Header post frame node parent nextIndex) ∧ MemoryMetadata.erase post=MemoryMetadata.erase source ∧
      ∀ query : BitVec 64,query≠frame+16#64→post.memory query=source.memory query := by
  rw [branch_scan_shape.2.2] at normal
  obtain ⟨inner,tailRun,endpoint⟩:=declaration_none_word source post "i" scanIndexExpression (BitVec.ofNat 64 index) scanAndStore
    (header.index_read domain topCell) normal
  let entered:=bind source "i" (BitVec.ofNat 64 index)
  have valid : ScanInvariant entered:=⟨BitVec.ofNat 64 index,found,bind_lookup_same _ _ _,
    (bind_lookup_other source "i" "found" _ (by decide)).trans foundCell,by change index%2^64≤16; exact (Nat.mod_le _ _).trans header.bounded⟩
  rw [branch_scan_shape.2.1] at tailRun
  obtain ⟨scanned,scanRun,storeRun⟩:=sequence_none entered inner branchScan _ tailRun
  obtain ⟨⟨nextIndex,nextFound,indexCell,nextFoundCell,bounded⟩,frameEq⟩:=scan_normal entered scanned installed valid scanRun
  have memory:=LocalEffects.memory_of_erase entered scanned frameEq
  have scannedDomain:=congrArg PanSemStateFiniteExact.memaddrs frameEq
  change scanned.memaddrs=source.memaddrs at scannedDomain
  have saved:=((LocalPrefix.loop scanTest (scan_body_safe (ofString "top") (by decide) (by decide) (by decide))).summary_full entered)
  unfold LocalSummary at saved
  rw [←branch_scan_shape.1,scanRun] at saved
  have scannedTop : scanned.locals.lookup (ofString "top")=some (.val (.word frame)):=
    (saved.1 rfl).trans ((bind_lookup_other source "i" "top" _ (by decide)).trans topCell)
  have addressRead : eval scanned (.op .add [localVar "top",.const 16#64])=some (.val (.word (frame+16#64))):=by
    simp [eval,evalHOLExact,evalListHOLExact,localVar,toExact,scannedTop,valueIsWord,valueWord,wordOpHOL,wordOp]
  have indexRead : eval scanned (localVar "i")=some (.val (.word nextIndex)):=by simp [eval,evalHOLExact,localVar,toExact,indexCell]
  have actual:=StoreWord.execute scanned _ _ (frame+16#64) nextIndex addressRead indexRead
    (AllocatedBytes.word_mapped scanned frame 48 16 (scannedDomain.trans domain) header.arena (by decide) header.aligned (by decide))
  have innerEq : inner={scanned with memory:=StoreWord.put scanned.memory (frame+16#64) nextIndex}:=congrArg Prod.snd (storeRun.symm.trans actual)
  have kept (query : BitVec 64) (away : query≠frame+16#64) : post.memory query=source.memory query:=by
    rw [endpoint,innerEq]
    exact (if_neg away).trans (congrFun memory query)
  have different (offset : Nat) (inside : offset≤8) : frame+BitVec.ofNat 64 offset≠frame+16#64:=by
    have first:=byteAddress_toNat frame offset (by have upper:=header.arena.upper; omega)
    have second:=byteAddress_toNat frame 16 (by have upper:=header.arena.upper; omega)
    intro equal
    have number:=congrArg BitVec.toNat equal
    change (byteAddress frame offset).toNat=(byteAddress frame 16).toNat at number
    rw [first,second] at number
    omega
  refine ⟨⟨nextIndex.toNat,header.arena,header.aligned,header.scratch,bounded,?_,?_,?_⟩,?_,kept⟩
  · have away : frame≠frame+16#64:=by simpa using different 0 (by decide)
    exact (kept frame away).trans header.parentStored
  · exact (kept (frame+8#64) (different 8 (by decide))).trans header.nodeStored
  · rw [endpoint,innerEq]
    change StoreWord.put scanned.memory (frame+16#64) nextIndex (frame+16#64)=.word (BitVec.ofNat 64 nextIndex.toNat)
    simp [StoreWord.put]
  · have metadata:=MemoryMetadata.of_frame frameEq
    change MemoryMetadata.erase scanned=MemoryMetadata.erase source at metadata
    rw [endpoint,innerEq]
    exact metadata

end InitECandidate.Solver.Mpt.NodeRlpFill

#print axioms InitECandidate.Solver.Mpt.NodeRlpFill.original_code
#print axioms InitECandidate.Solver.Mpt.NodeRlpFill.shapes
#print axioms InitECandidate.Solver.Mpt.NodeRlpFill.initial_cost
#print axioms InitECandidate.Solver.Mpt.NodeRlpFill.initial_trace
#print axioms InitECandidate.Solver.Mpt.NodeRlpFill.Header.after_begin
#print axioms InitECandidate.Solver.Mpt.NodeRlpFill.allocation_geometry
#print axioms InitECandidate.Solver.Mpt.NodeRlpFill.mark_reached
#print axioms InitECandidate.Solver.Mpt.NodeRlpFill.allocation_reached
#print axioms InitECandidate.Solver.Mpt.NodeRlpFill.initial_from_execution
#print axioms InitECandidate.Solver.Mpt.NodeRlpFill.push_rank
#print axioms InitECandidate.Solver.Mpt.NodeRlpFill.pop_rank
#print axioms InitECandidate.Solver.Mpt.NodeRlpFill.allocation_budget
#print axioms InitECandidate.Solver.Mpt.NodeRlpFill.initial_rank_bound
#print axioms InitECandidate.Solver.Mpt.NodeRlpFill.initial_live
#print axioms InitECandidate.Solver.Mpt.NodeRlpFill.initial_begin_entry
#print axioms InitECandidate.Solver.Mpt.NodeRlpFill.branch_scan_shape
#print axioms InitECandidate.Solver.Mpt.NodeRlpFill.scan_body_cost
#print axioms InitECandidate.Solver.Mpt.NodeRlpFill.scan_body_readonly
#print axioms InitECandidate.Solver.Mpt.NodeRlpFill.scan_found_normal
#print axioms InitECandidate.Solver.Mpt.NodeRlpFill.scan_test_read
#print axioms InitECandidate.Solver.Mpt.NodeRlpFill.scan_transition
#print axioms InitECandidate.Solver.Mpt.NodeRlpFill.scan_cost
#print axioms InitECandidate.Solver.Mpt.NodeRlpFill.scan_normal
#print axioms InitECandidate.Solver.Mpt.NodeRlpFill.Header.index_read
#print axioms InitECandidate.Solver.Mpt.NodeRlpFill.branch_scope_cost
#print axioms InitECandidate.Solver.Mpt.NodeRlpFill.branch_scope_normal
