import InitECandidate.Solver.Mpt.NodeRlpFinishCall
import InitECandidate.Solver.Mpt.NodeRlpBeginHeap
import InitECandidate.Solver.Mpt.NodeRlpBeginGraph
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
import InitECandidate.Solver.Input.AssignNormal
import InitECandidate.Solver.Input.AssignedCallKnown
import InitECandidate.Solver.Input.ClockCostCurrentConditional
import InitECandidate.Solver.Input.ScopedCallNone

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

theorem scan_child_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (node index child : BitVec 64)
    (nodeCell : source.locals.lookup (ofString "nd")=some (.val (.word node)))
    (indexCell : source.locals.lookup (ofString "i")=some (.val (.word index)))
    (mapped : source.memaddrs (node+32#64+BitVec.ofNat 64 (index.toNat*8)))
    (stored : source.memory (node+32#64+BitVec.ofNat 64 (index.toNat*8))=.word child) :
    eval source scanChild=some (.val (.word child)) := by
  have product : index*8#64=BitVec.ofNat 64 (index.toNat*8):=by simp [BitVec.ofNat_mul]
  simp [eval,scanChild,evalHOLExact,evalListHOLExact,localVar,toExact,nodeCell,indexCell,
    valueIsWord,valueWord,wordOpHOL,wordOp,panOpHOL,product,memLoadHOLExact,isWfShapeExactHOL,
    ←BitVec.add_assoc,mapped,stored]

/-- The actual load selects the child's real word. The following increment
and assigned decision call preserve that child binding on normal return. -/
theorem scan_body_child_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (child : BitVec 64)
    (read : eval source scanChild=some (.val (.word child)))
    (normal : evaluateHOLFiniteState source scanBody=(none,post)) :
    post.locals.lookup (ofString "child")=some (.val (.word child)) := by
  obtain ⟨first,firstRun,restRun⟩:=sequence_none source post scanAssign (.seq scanIncrement scanCall) normal
  have firstEq:=assign_none source first "child" scanChild child read firstRun
  have safe : LocalPrefix (ofString "child") (.seq scanIncrement scanCall):=
    .seq (.assign _ _ (by decide)) (.call (some _) _ _ (by intro name same; cases same; decide))
  have saved:=safe.summary_full first
  unfold LocalSummary at saved
  rw [restRun] at saved
  exact (saved.1 rfl).trans (by rw [firstEq]; exact bind_lookup_same _ _ _)

/-- A continuing scan selects only registered children from the actual
branch array. Zero iterations retain the incoming registered child. -/
theorem scan_member_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (node initialChild : BitVec 64)
    (installed : OriginalCode.Installed source.code) (valid : ScanInvariant source)
    (member : graph.valid node) (active : node≠0#64)
    (notHash : GasBudget.wordAt source.memory node≠0#64) (notLeaf : GasBudget.wordAt source.memory node≠1#64)
    (notExtension : GasBudget.wordAt source.memory node≠2#64)
    (nodeCell : source.locals.lookup (ofString "nd")=some (.val (.word node)))
    (childCell : source.locals.lookup (ofString "child")=some (.val (.word initialChild)))
    (childMember : graph.valid initialChild)
    (normal : evaluateHOLFiniteState source branchScan=(none,post)) :
    ∃ child,post.locals.lookup (ofString "child")=some (.val (.word child)) ∧ graph.valid child := by
  let invariant (current : PanSemStateFiniteExact 64 Guest.HostMemory) : Prop:=
    ScanInvariant current ∧ LocalEffects.erase current=LocalEffects.erase source ∧
    current.locals.lookup (ofString "nd")=some (.val (.word node)) ∧
    ∃ child,current.locals.lookup (ofString "child")=some (.val (.word child)) ∧ graph.valid child
  have initial : invariant source:=⟨valid,rfl,nodeCell,initialChild,childCell,childMember⟩
  have control (current : PanSemStateFiniteExact 64 Guest.HostMemory):=
    ((scan_body_safe (ofString "nd") (by decide) (by decide) (by decide)).summary_full current).2.2
  rw [branch_scan_shape.1] at normal
  have final:=loop_invariant_no_control source.code scanTest scanBody control invariant (by
    intro current codeEq ready word read nonzero funded target bodyRun
    obtain ⟨currentValid,currentFrame,currentNode,oldChild⟩:=ready
    have currentInstalled : OriginalCode.Installed current.code:=by rw [codeEq]; exact installed
    obtain ⟨index,found,indexCell,foundCell,bounded⟩:=currentValid
    have expected:=scan_test_read current index found indexCell foundCell bounded
    change eval current scanTest=some (.val (.word word)) at read
    have inside : index.toNat<16:=by
      by_contra outside
      rw [if_neg (by intro both; exact outside both.1)] at expected
      have zero : word=0#64:=by simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using read.symm.trans expected
      exact nonzero zero
    let view:=graph.branch node member active notHash notLeaf notExtension index.toNat inside
    have memory:=LocalEffects.memory_of_erase source current currentFrame
    have domain:=congrArg PanSemStateFiniteExact.memaddrs currentFrame
    change current.memaddrs=source.memaddrs at domain
    have loaded:=scan_child_read current node index view.child currentNode indexCell
      (by rw [domain]; exact view.mapped) (by rw [memory]; exact view.stored)
    have nextChild:=scan_body_child_normal (decClockHOLFinite current) target view.child loaded bodyRun
    have nextValid:=((scan_transition current currentInstalled ⟨index,found,indexCell,foundCell,bounded⟩ word read nonzero).2 target bodyRun).1
    have nextFrame:=scan_body_readonly current.code currentInstalled (decClockHOLFinite current) rfl
    rw [bodyRun] at nextFrame
    change LocalEffects.erase target=LocalEffects.erase current at nextFrame
    have saved:=(scan_body_safe (ofString "nd") (by decide) (by decide) (by decide)).summary_full (decClockHOLFinite current)
    unfold LocalSummary at saved
    rw [bodyRun] at saved
    exact ⟨nextValid,nextFrame.trans currentFrame,(saved.1 rfl).trans currentNode,view.child,nextChild,view.member⟩)
    source post rfl initial normal
  exact final.2.2.2

/-- The complete branch scope carries its actual registered selected child
through the cursor store and restoration of the lexical scan variable. -/
theorem branch_scope_member_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (frame node parent found initialChild : BitVec 64) (index : Nat)
    (installed : OriginalCode.Installed source.code) (header : Header source frame node parent index)
    (domain : source.memaddrs=InitE.ordinaryDomain)
    (topCell : source.locals.lookup (ofString "top")=some (.val (.word frame)))
    (foundCell : source.locals.lookup (ofString "found")=some (.val (.word found)))
    (nodeCell : source.locals.lookup (ofString "nd")=some (.val (.word node)))
    (childCell : source.locals.lookup (ofString "child")=some (.val (.word initialChild)))
    (member : graph.valid node) (active : node≠0#64) (childMember : graph.valid initialChild)
    (notHash : GasBudget.wordAt source.memory node≠0#64) (notLeaf : GasBudget.wordAt source.memory node≠1#64)
    (notExtension : GasBudget.wordAt source.memory node≠2#64)
    (normal : evaluateHOLFiniteState source branchScope=(none,post)) :
    ∃ child,post.locals.lookup (ofString "child")=some (.val (.word child)) ∧ graph.valid child := by
  rw [branch_scan_shape.2.2] at normal
  obtain ⟨inner,tailRun,endpoint⟩:=declaration_none_word source post "i" scanIndexExpression (BitVec.ofNat 64 index) scanAndStore
    (header.index_read domain topCell) normal
  let entered:=bind source "i" (BitVec.ofNat 64 index)
  have valid : ScanInvariant entered:=⟨BitVec.ofNat 64 index,found,bind_lookup_same _ _ _,
    (bind_lookup_other source "i" "found" _ (by decide)).trans foundCell,
    by change index%2^64≤16; exact (Nat.mod_le _ _).trans header.bounded⟩
  rw [branch_scan_shape.2.1] at tailRun
  obtain ⟨scanned,scanRun,storeRun⟩:=sequence_none entered inner branchScan _ tailRun
  obtain ⟨child,scannedChild,selected⟩:=scan_member_normal entered scanned graph node initialChild installed valid member active
    notHash notLeaf notExtension ((bind_lookup_other source "i" "nd" _ (by decide)).trans nodeCell)
    ((bind_lookup_other source "i" "child" _ (by decide)).trans childCell) childMember scanRun
  have safe : LocalPrefix (ofString "child") (.store (.op .add [localVar "top",.const 16#64]) (localVar "i")):=.store _ _
  have saved:=safe.summary_full scanned
  unfold LocalSummary at saved
  rw [storeRun] at saved
  refine ⟨child,?_,selected⟩
  rw [endpoint]
  exact (restore_lookup_other source inner "i" "child" (by decide)).trans ((saved.1 rfl).trans scannedChild)

/-- An actual positive assigned decision supplies the next begin call's
nonnull/non-hash facts. Its callee and result are derived from this call. -/
theorem scan_call_positive (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (child tag found : BitVec 64)
    (installed : OriginalCode.Installed source.code)
    (childCell : source.locals.lookup (ofString "child")=some (.val (.word child)))
    (header : child≠0#64→source.memaddrs child ∧ source.memory child=.word tag)
    (normal : evaluateHOLFiniteState source scanCall=(none,post))
    (foundCell : post.locals.lookup (ofString "found")=some (.val (.word found))) (positive : found≠0#64) :
    child≠0#64 ∧ tag≠0#64 := by
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) [localVar "child"]=
      some [.val (.word child)]:=by simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,childCell]
  obtain ⟨callee,called,calleeChild⟩:=NodeNeedsRlp.environment source.code.lookup child (NodeNeedsRlp.original_code source.code installed)
  obtain ⟨funded,target,returned,run,endpoint⟩:=CallNormal.local_known source post (ofString "found") (ofString "_node_needs_rlp")
    [localVar "child"] [.val (.word child)] NodeNeedsRlp.body callee .one args called normal
  have assigned : post.locals.lookup (ofString "found")=some returned:=by
    rw [endpoint]
    simp [setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
  have answer : returned=.val (.word found):=Option.some.inj (assigned.symm.trans foundCell)
  rw [answer] at run
  have one : found=1#64:=by
    rcases NodeNeedsRlp.binary (callEntryStateHOLFinite source callee) target (.val (.word found)) run with zero|one
    · have zeroWord : found=0#64:=by simpa only [ValueHOL.val.injEq,HolWordLab.word.injEq] using zero
      exact (positive zeroWord).elim
    · simpa only [ValueHOL.val.injEq,HolWordLab.word.injEq] using one
  rw [one] at run
  have active:=NodeNeedsRlp.one_active (callEntryStateHOLFinite source callee) target child calleeChild run
  obtain ⟨mapped,stored⟩:=header active
  exact ⟨active,NodeNeedsRlp.one_non_hash (callEntryStateHOLFinite source callee) target child tag calleeChild mapped stored run⟩

def extensionChoice : ProgHOL 64:=match selectChild with | .ite _ yes _=>yes | _=>.skip
def extensionChild : ExpHOL 64:=.load .one (.op .add [localVar "nd",.const 48#64])

set_option maxRecDepth 100000 in
theorem selection_shapes :
    selectChild=.ite (.cmp .equal (localVar "k") (.const 2#64)) extensionChoice branchChoice ∧
    branchChoice=.ite (.cmp .equal (localVar "k") (.const 3#64)) branchScope .skip ∧
    extensionChoice=.ite (.cmp .equal scanIndexExpression (.const 0#64))
      (.seq (.store (.op .add [localVar "top",.const 16#64]) (.const 1#64))
        (.seq (.assign .local (ofString "child") extensionChild) scanCall)) .skip := by
  simp only [extensionChoice,extensionChild,scanIndexExpression,scanCall,branchScope,branchChoice,selectChild,stepTail,
    afterStepChild,afterStepKind,afterStepNode,step,loop,loopAndAfter,afterBegin,beginAndAfter,afterNode,afterParent,
    afterFrame,afterMark,body,Guest.Software.guestFn__node_rlp_fill,progToHOL,expToHOL,shapeToHOL,
    List.map_cons,List.map_nil,Option.map_some,Option.map_none,localVar]
  trivial

/-- The real extension selection has only one possible helper call. -/
theorem extension_choice_cost (code) (installed : OriginalCode.Installed code) : ClockCost.Bound code extensionChoice 1 := by
  rw [selection_shapes.2.2]
  apply ClockCost.conditional code _ _ _ 1 0
  · exact ClockCost.sequence code _ _ 0 1 (ClockCost.store code _ _)
      (ClockCost.sequence code _ _ 0 1 (ClockCost.assign code _ _)
        (ClockCost.call_body code (some (some (ofString "found"))) (ofString "_node_needs_rlp") [localVar "child"]
          NodeNeedsRlp.formals NodeNeedsRlp.body .one 0 (NodeNeedsRlp.original_code code installed) (NodeNeedsRlp.body_cost code)))
  · exact ClockCost.skip code

/-- Actual extension selection either retains its existing index or stores
one, while its child assignment/helper call retain all nonlocal fields. -/
theorem extension_choice_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (frame node parent : BitVec 64) (index : Nat)
    (installed : OriginalCode.Installed source.code) (header : Header source frame node parent index)
    (domain : source.memaddrs=InitE.ordinaryDomain)
    (topCell : source.locals.lookup (ofString "top")=some (.val (.word frame)))
    (normal : evaluateHOLFiniteState source extensionChoice=(none,post)) :
    (∃ nextIndex,Header post frame node parent nextIndex) ∧ MemoryMetadata.erase post=MemoryMetadata.erase source ∧
      ∀ query : BitVec 64,query≠frame+16#64 → post.memory query=source.memory query := by
  have indexRead:=header.index_read domain topCell
  simp only [eval] at indexRead
  by_cases zero : index=0
  · have selected : evaluateHOLFiniteState source extensionChoice=evaluateHOLFiniteState source
        (.seq (.store (.op .add [localVar "top",.const 16#64]) (.const 1#64)) (.seq (.assign .local (ofString "child") extensionChild) scanCall)):=by
      rw [selection_shapes.2.2,evaluateHOLFiniteState_ite]
      simp [evalHOLExact,toExact,indexRead,zero,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    rw [selected] at normal
    have stored:=StoreWord.execute source (.op .add [localVar "top",.const 16#64]) (.const 1#64) (frame+16#64) 1#64
      (by simp [eval,evalHOLExact,evalListHOLExact,toExact,localVar,topCell,valueIsWord,valueWord,wordOpHOL,wordOp]) rfl
      (AllocatedBytes.word_mapped source frame 48 16 domain header.arena (by decide) header.aligned (by decide))
    rw [evaluateHOLFiniteState_seq_line780,stored] at normal
    let next:=written source frame 16 1#64
    change evaluateHOLFiniteState next (.seq (.assign .local (ofString "child") extensionChild) scanCall)=(none,post) at normal
    have pureTail : LocalEffects.Preserves source.code (.seq (.assign .local (ofString "child") extensionChild) scanCall):=
      LocalEffects.sequence source.code _ _ (LocalEffects.assign source.code _ _)
        (LocalEffects.call_body source.code (some (some (ofString "found"))) (ofString "_node_needs_rlp") [localVar "child"]
          NodeNeedsRlp.formals NodeNeedsRlp.body .one (NodeNeedsRlp.original_code source.code installed) (NodeNeedsRlp.readonly source.code))
    have frameEq:=pureTail next rfl
    rw [normal] at frameEq
    have memory:=LocalEffects.memory_of_erase next post frameEq
    have kept (query : BitVec 64) (away : query≠frame+16#64) : post.memory query=source.memory query:=by
      exact (congrFun memory query).trans (if_neg away)
    have parentAway : frame≠frame+16#64:=by
      simpa only [BitVec.add_zero] using GasBudget.offsets_ne frame 0#64 16#64 (by decide)
    refine ⟨⟨1,header.arena,header.aligned,header.scratch,by decide,(kept frame parentAway).trans header.parentStored,
      (kept (frame+8#64) (GasBudget.offsets_ne frame 8#64 16#64 (by decide))).trans header.nodeStored,?_⟩,(MemoryMetadata.of_frame frameEq).trans (show MemoryMetadata.erase next=MemoryMetadata.erase source from rfl),kept⟩
    change post.memory (frame+16#64)=.word 1#64
    exact (congrFun memory _).trans (if_pos rfl)
  · have nonzero : (BitVec.ofNat 64 index)≠0#64:=by
      intro equal
      have numeric:=congrArg BitVec.toNat equal
      rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by have bound:=header.bounded; omega)] at numeric
      exact zero numeric
    have skipped : evaluateHOLFiniteState source extensionChoice=(none,source):=by
      rw [selection_shapes.2.2,evaluateHOLFiniteState_ite]
      simp [evalHOLExact,toExact,indexRead,nonzero,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,evaluateHOLFiniteState_skip]
    have same : post=source:=congrArg Prod.snd (normal.symm.trans skipped)
    subst post
    exact ⟨⟨index,header⟩,rfl,by intros; rfl⟩

/-- The complete actual selector retains all words except its real index16,
and returns a bounded current linked header at the same observed endpoint. -/
theorem select_child_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (frame node parent tag found : BitVec 64) (index : Nat)
    (installed : OriginalCode.Installed source.code) (header : Header source frame node parent index) (domain : source.memaddrs=InitE.ordinaryDomain)
    (topCell : source.locals.lookup (ofString "top")=some (.val (.word frame)))
    (tagCell : source.locals.lookup (ofString "k")=some (.val (.word tag)))
    (foundCell : source.locals.lookup (ofString "found")=some (.val (.word found)))
    (normal : evaluateHOLFiniteState source selectChild=(none,post)) :
    (∃ nextIndex,Header post frame node parent nextIndex) ∧ MemoryMetadata.erase post=MemoryMetadata.erase source ∧
      ∀ query : BitVec 64,query≠frame+16#64 → post.memory query=source.memory query := by
  have selected : evaluateHOLFiniteState source selectChild=if tag=2#64 then evaluateHOLFiniteState source extensionChoice else evaluateHOLFiniteState source branchChoice:=by
    rw [selection_shapes.1,evaluateHOLFiniteState_ite]
    simp [evalHOLExact,toExact,localVar,tagCell,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  rw [selected] at normal
  by_cases extension : tag=2#64
  · rw [if_pos extension] at normal
    exact extension_choice_normal source post frame node parent index installed header domain topCell normal
  · rw [if_neg extension] at normal
    have branchSelected : evaluateHOLFiniteState source branchChoice=if tag=3#64 then evaluateHOLFiniteState source branchScope else (none,source):=by
      rw [selection_shapes.2.1,evaluateHOLFiniteState_ite]
      simp [evalHOLExact,toExact,localVar,tagCell,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,evaluateHOLFiniteState_skip]
    rw [branchSelected] at normal
    by_cases branch : tag=3#64
    · rw [if_pos branch] at normal
      exact branch_scope_normal source post frame node parent found index installed header domain topCell foundCell normal
    · rw [if_neg branch] at normal
      have same : post=source:=congrArg Prod.snd normal.symm
      subst post
      exact ⟨⟨index,header⟩,rfl,by intros; rfl⟩

/-- Every actual child-selection outcome is covered, including extension,
branch, leaf and failed conditions. No subsequent push or pop is assumed. -/
theorem select_child_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (frame node parent found : BitVec 64) (index : Nat)
    (installed : OriginalCode.Installed source.code) (header : Header source frame node parent index)
    (domain : source.memaddrs=InitE.ordinaryDomain)
    (topCell : source.locals.lookup (ofString "top")=some (.val (.word frame)))
    (foundCell : source.locals.lookup (ofString "found")=some (.val (.word found))) :
    source.clock-(evaluateHOLFiniteState source selectChild).2.clock≤32 := by
  have branchPrice : source.clock-(evaluateHOLFiniteState source branchChoice).2.clock≤32:=by
    rw [selection_shapes.2.1]
    exact ClockCost.conditional_current source _ _ _ 32 0
      (branch_scope_cost source frame node parent found index installed header domain topCell foundCell)
      (ClockCost.skip source.code source rfl)
  rw [selection_shapes.1]
  exact ClockCost.conditional_current source _ _ _ 1 32 (extension_choice_cost source.code installed source rfl) branchPrice

/-- The loaded child and its positive decision belong to the same actual
scan iteration, including the intervening counter update. -/
theorem scan_body_positive (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (child tag found : BitVec 64)
    (installed : OriginalCode.Installed source.code)
    (read : eval source scanChild=some (.val (.word child)))
    (header : child≠0#64→source.memaddrs child ∧ source.memory child=.word tag)
    (normal : evaluateHOLFiniteState source scanBody=(none,post))
    (foundCell : post.locals.lookup (ofString "found")=some (.val (.word found))) (positive : found≠0#64) :
    child≠0#64 ∧ tag≠0#64 := by
  obtain ⟨first,firstRun,restRun⟩:=sequence_none source post scanAssign (.seq scanIncrement scanCall) normal
  obtain ⟨second,incrementRun,callRun⟩:=sequence_none first post scanIncrement scanCall restRun
  have firstEq:=assign_none source first "child" scanChild child read firstRun
  have frame:=LocalEffects.assign first.code (ofString "i") (.op .add [localVar "i",.const 1#64]) first rfl
  change LocalEffects.erase (evaluateHOLFiniteState first scanIncrement).2=LocalEffects.erase first at frame
  rw [incrementRun] at frame
  have memory : second.memory=source.memory:=by rw [LocalEffects.memory_of_erase first second frame,firstEq]; rfl
  have domain:=congrArg PanSemStateFiniteExact.memaddrs frame
  change second.memaddrs=first.memaddrs at domain
  rw [firstEq] at domain
  have secondInstalled : OriginalCode.Installed second.code:=by rw [LocalEffects.code_of_erase first second frame,firstEq]; exact installed
  have safe : LocalPrefix (ofString "child") scanIncrement:=.assign _ _ (by decide)
  have saved:=safe.summary_full first
  unfold LocalSummary at saved
  rw [incrementRun] at saved
  have secondChild : second.locals.lookup (ofString "child")=some (.val (.word child)):=
    (saved.1 rfl).trans (by rw [firstEq]; exact bind_lookup_same _ _ _)
  exact scan_call_positive second post child tag found secondInstalled secondChild
    (by intro active; obtain ⟨mapped,stored⟩:=header active; exact ⟨by rw [domain]; exact mapped,by rw [memory]; exact stored⟩)
    callRun foundCell positive

/-- Starting from the literal found0 initializer, every actual completed
scan's positive decision refers to its same registered nonnull/non-hash
child. Zero iterations cannot invent a positive decision. -/
theorem scan_descent_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (node : BitVec 64)
    (installed : OriginalCode.Installed source.code) (valid : ScanInvariant source)
    (member : graph.valid node) (active : node≠0#64)
    (notHash : GasBudget.wordAt source.memory node≠0#64) (notLeaf : GasBudget.wordAt source.memory node≠1#64)
    (notExtension : GasBudget.wordAt source.memory node≠2#64)
    (nodeCell : source.locals.lookup (ofString "nd")=some (.val (.word node)))
    (childCell : source.locals.lookup (ofString "child")=some (.val (.word 0#64)))
    (foundCell : source.locals.lookup (ofString "found")=some (.val (.word 0#64)))
    (normal : evaluateHOLFiniteState source branchScan=(none,post)) :
    ∃ child found,post.locals.lookup (ofString "child")=some (.val (.word child)) ∧
      post.locals.lookup (ofString "found")=some (.val (.word found)) ∧ graph.valid child ∧
      (found≠0#64→child≠0#64 ∧ GasBudget.wordAt source.memory child≠0#64) := by
  let sound (current : PanSemStateFiniteExact 64 Guest.HostMemory) : Prop:=
    ∀ child found,current.locals.lookup (ofString "child")=some (.val (.word child))→
      current.locals.lookup (ofString "found")=some (.val (.word found))→found≠0#64→
      child≠0#64 ∧ GasBudget.wordAt source.memory child≠0#64
  let invariant (current : PanSemStateFiniteExact 64 Guest.HostMemory) : Prop:=
    ScanInvariant current ∧ LocalEffects.erase current=LocalEffects.erase source ∧
    current.locals.lookup (ofString "nd")=some (.val (.word node)) ∧ sound current
  have initial : invariant source:=⟨valid,rfl,nodeCell,by
    intro child found childRead foundRead positive
    have zero : found=0#64:=by simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using foundRead.symm.trans foundCell
    exact (positive zero).elim⟩
  have control (current : PanSemStateFiniteExact 64 Guest.HostMemory):=
    ((scan_body_safe (ofString "nd") (by decide) (by decide) (by decide)).summary_full current).2.2
  have loopRun:=normal
  rw [branch_scan_shape.1] at loopRun
  have final:=loop_invariant_no_control source.code scanTest scanBody control invariant (by
    intro current codeEq ready word read nonzero funded target bodyRun
    obtain ⟨currentValid,currentFrame,currentNode,oldSound⟩:=ready
    have currentInstalled : OriginalCode.Installed current.code:=by rw [codeEq]; exact installed
    obtain ⟨index,found,indexCell,foundCell,bounded⟩:=currentValid
    have expected:=scan_test_read current index found indexCell foundCell bounded
    change eval current scanTest=some (.val (.word word)) at read
    have inside : index.toNat<16:=by
      by_contra outside
      rw [if_neg (by intro both; exact outside both.1)] at expected
      have zero : word=0#64:=by simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using read.symm.trans expected
      exact nonzero zero
    let view:=graph.branch node member active notHash notLeaf notExtension index.toNat inside
    have memory:=LocalEffects.memory_of_erase source current currentFrame
    have domain:=congrArg PanSemStateFiniteExact.memaddrs currentFrame
    change current.memaddrs=source.memaddrs at domain
    have loaded:=scan_child_read current node index view.child currentNode indexCell
      (by rw [domain]; exact view.mapped) (by rw [memory]; exact view.stored)
    have nextChild:=scan_body_child_normal (decClockHOLFinite current) target view.child loaded bodyRun
    have nextValid:=((scan_transition current currentInstalled ⟨index,found,indexCell,foundCell,bounded⟩ word read nonzero).2 target bodyRun).1
    have nextFrame:=scan_body_readonly current.code currentInstalled (decClockHOLFinite current) rfl
    rw [bodyRun] at nextFrame
    change LocalEffects.erase target=LocalEffects.erase current at nextFrame
    have saved:=(scan_body_safe (ofString "nd") (by decide) (by decide) (by decide)).summary_full (decClockHOLFinite current)
    unfold LocalSummary at saved
    rw [bodyRun] at saved
    refine ⟨nextValid,nextFrame.trans currentFrame,(saved.1 rfl).trans currentNode,?_⟩
    intro selected decision selectedCell decisionCell positive
    have same : selected=view.child:=by simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using selectedCell.symm.trans nextChild
    subst selected
    exact scan_body_positive (decClockHOLFinite current) target view.child (GasBudget.wordAt source.memory view.child) decision currentInstalled loaded
      (by intro childActive; obtain ⟨mapped,stored⟩:=graph.header view.child view.member childActive
          exact ⟨by change current.memaddrs view.child; rw [domain]; exact mapped,
            by change current.memory view.child=_; rw [memory]; exact stored⟩)
      bodyRun decisionCell positive) source post rfl initial loopRun
  obtain ⟨child,selected,childMember⟩:=scan_member_normal source post graph node 0#64 installed valid member active notHash notLeaf notExtension
    nodeCell childCell graph.null normal
  obtain ⟨index,found,indexCell,decisionCell,bounded⟩:=final.1
  exact ⟨child,found,selected,decisionCell,childMember,final.2.2.2 child found selected decisionCell⟩

/-- The positive-decision/child relation survives the complete actual
branch scope, including the stored cursor and restored scan binding. -/
theorem branch_scope_descent_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (frame node parent : BitVec 64) (index : Nat)
    (installed : OriginalCode.Installed source.code) (header : Header source frame node parent index)
    (domain : source.memaddrs=InitE.ordinaryDomain)
    (topCell : source.locals.lookup (ofString "top")=some (.val (.word frame)))
    (nodeCell : source.locals.lookup (ofString "nd")=some (.val (.word node)))
    (childCell : source.locals.lookup (ofString "child")=some (.val (.word 0#64)))
    (foundCell : source.locals.lookup (ofString "found")=some (.val (.word 0#64)))
    (member : graph.valid node) (active : node≠0#64)
    (notHash : GasBudget.wordAt source.memory node≠0#64) (notLeaf : GasBudget.wordAt source.memory node≠1#64)
    (notExtension : GasBudget.wordAt source.memory node≠2#64)
    (normal : evaluateHOLFiniteState source branchScope=(none,post)) :
    ∃ child found,post.locals.lookup (ofString "child")=some (.val (.word child)) ∧
      post.locals.lookup (ofString "found")=some (.val (.word found)) ∧ graph.valid child ∧
      (found≠0#64→child≠0#64 ∧ GasBudget.wordAt source.memory child≠0#64) := by
  rw [branch_scan_shape.2.2] at normal
  obtain ⟨inner,tailRun,endpoint⟩:=declaration_none_word source post "i" scanIndexExpression (BitVec.ofNat 64 index) scanAndStore
    (header.index_read domain topCell) normal
  let entered:=bind source "i" (BitVec.ofNat 64 index)
  have enteredFound : entered.locals.lookup (ofString "found")=some (.val (.word 0#64)):=
    (bind_lookup_other source "i" "found" _ (by decide)).trans foundCell
  have valid : ScanInvariant entered:=⟨BitVec.ofNat 64 index,0#64,bind_lookup_same _ _ _,enteredFound,
    by change index%2^64≤16; exact (Nat.mod_le _ _).trans header.bounded⟩
  rw [branch_scan_shape.2.1] at tailRun
  obtain ⟨scanned,scanRun,storeRun⟩:=sequence_none entered inner branchScan _ tailRun
  obtain ⟨child,found,scannedChild,scannedFound,selected,sound⟩:=scan_descent_normal entered scanned graph node installed valid member active
    notHash notLeaf notExtension ((bind_lookup_other source "i" "nd" _ (by decide)).trans nodeCell)
    ((bind_lookup_other source "i" "child" _ (by decide)).trans childCell) enteredFound scanRun
  have stored (key : MlS) : inner.locals.lookup key=scanned.locals.lookup key:=by
    have safe : LocalPrefix key (.store (.op .add [localVar "top",.const 16#64]) (localVar "i")):=.store _ _
    have saved:=safe.summary_full scanned
    unfold LocalSummary at saved
    rw [storeRun] at saved
    exact saved.1 rfl
  refine ⟨child,found,?_,?_,selected,sound⟩
  · rw [endpoint]
    exact (restore_lookup_other source inner "i" "child" (by decide)).trans ((stored _).trans scannedChild)
  · rw [endpoint]
    exact (restore_lookup_other source inner "i" "found" (by decide)).trans ((stored _).trans scannedFound)

def pushChoice : ProgHOL 64:=match stepTail with | .seq _ rest=>rest | _=>.skip
def pushBranch : ProgHOL 64:=match pushChoice with | .ite _ yes _=>yes | _=>.skip
def pushActions : List CallPrefix.Action:=[
  .scoped (ofString "cf") .one (ofString "scratch_alloc") [.const 48#64],
  .command (.store (.op .add [localVar "cf",.const 0#64]) (localVar "top")),
  .command (.store (.op .add [localVar "cf",.const 8#64]) (localVar "child")),
  .command (.store (.op .add [localVar "cf",.const 16#64]) (.const 0#64))]
def pushTail : ProgHOL 64:=.seq (.call (some (none,none)) (ofString "_node_rlp_begin") [localVar "cf",localVar "child"])
  (.assign .local (ofString "top") (localVar "cf"))

set_option maxRecDepth 100000 in
theorem push_shape : pushBranch=CallPrefix.program pushActions pushTail := by
  simp only [pushBranch,pushChoice,stepTail,afterStepChild,afterStepKind,afterStepNode,step,loop,loopAndAfter,
    afterBegin,beginAndAfter,afterNode,afterParent,afterFrame,afterMark,body,pushActions,pushTail,CallPrefix.program,
    Guest.Software.guestFn__node_rlp_fill,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none,localVar]

theorem push_prefix_cost (code) (installed : OriginalCode.Installed code) : ClockCost.Bound code (CallPrefix.program pushActions .skip) 2 := by
  simp only [pushActions,CallPrefix.program]
  apply Arenas.scoped_price code installed .down _ _ _ _ 0
  repeat first
    | apply ClockCost.sequence code _ _ 0 0
    | exact ClockCost.store code _ _
    | exact ClockCost.skip code

theorem push_prefix_never : NoReturn.Never (CallPrefix.program pushActions .skip) := by
  have safe : LocalPrefix (ofString "top") (CallPrefix.program pushActions .skip):=by
    simp only [pushActions,CallPrefix.program]
    repeat first
      | apply LocalPrefix.decCall _ _ _ _ (by decide)
      | apply LocalPrefix.seq
      | exact LocalPrefix.store _ _
      | exact LocalPrefix.skip
  intro F source value
  exact (safe.summary_full source).2.1 value

/-- Every actual push either stops in its allocation/stores or reaches
the same real begin-and-install-top suffix within two source ticks. -/
theorem push_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (installed : OriginalCode.Installed source.code) (outcome : Option (PanSemResultExact 64))
    (run : evaluateHOLFiniteState source pushBranch=(outcome,post)) :
    (source.clock-post.clock≤2 ∧ ∀ value,outcome≠some (.returned value)) ∨ ∃ current inner,
      CallPrefix.Execution source pushActions current ∧ current.clock≤source.clock ∧ source.clock-current.clock≤2 ∧
      post.clock=inner.clock ∧ evaluateHOLFiniteState current pushTail=(outcome,inner) := by
  rw [push_shape] at run
  rcases CallPrefix.priced_trace source post pushActions pushTail 2 (push_prefix_cost source.code installed source rfl) outcome run with stopped|reached
  · exact Or.inl ⟨stopped.1,by intro value; rw [stopped.2]; exact push_prefix_never source value⟩
  · exact Or.inr reached

theorem allocation_reached_named (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor floor : BitVec 64) (name : String)
    (installed : OriginalCode.Installed source.code) (arena : Rlp.Validation.Arena source cursor floor)
    (reached : CallPrefix.Reaches source (.scoped (ofString name) .one (ofString "scratch_alloc") [.const 48#64]) target) :
    Arenas.Room .down cursor floor 48#64 ∧
      target=bind (Arenas.post {source with clock:=source.clock-1} .down cursor 48#64) name (framePointer cursor) := by
  obtain ⟨callee,called,amountCell⟩:=CallNormal.unary_environment source.code.lookup (ofString "scratch_alloc") "n"
    (Arenas.body .down) 48#64 (Arenas.original_code source.code installed .down)
  obtain ⟨child,value,run,endpoint⟩:=reached.scoped_known (ofString name) .one (ofString "scratch_alloc") [.const 48#64]
    [.val (.word 48#64)] (Arenas.body .down) callee .one rfl called
  obtain ⟨room,answer,frame⟩:=Arenas.post_of_normal (callEntryStateHOLFinite source callee) child .down cursor floor 48#64
    amountCell arena.cursorGlobal arena.limitGlobal arena.ordered arena.aligned (Trap.original_code source.code installed) value run
  refine ⟨room,?_⟩
  rw [endpoint,answer]
  have updated:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>
    bind {state with locals:=source.locals} name (framePointer cursor)) frame
  exact updated

theorem record_store (source : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String)
    (frame word : BitVec 64) (offset : Nat) (expression : ExpHOL 64) (inside : offset<48) (aligned : offset%8=0)
    (arena : AllocatedBytes.Arena frame 48) (frameAligned : frame.toNat%8=0)
    (domain : source.memaddrs=InitE.ordinaryDomain)
    (frameCell : source.locals.lookup (ofString name)=some (.val (.word frame)))
    (read : eval source expression=some (.val (.word word))) :
    evaluateHOLFiniteState source (.store (.op .add [localVar name,.const (BitVec.ofNat 64 offset)]) expression)=
      (none,written source frame offset word) := by
  have addressRead : eval source (.op .add [localVar name,.const (BitVec.ofNat 64 offset)])=some (.val (.word (frame+BitVec.ofNat 64 offset))):=by
    simp [eval,evalHOLExact,evalListHOLExact,localVar,toExact,frameCell,valueIsWord,valueWord,wordOpHOL,wordOp]
  exact StoreWord.execute source _ _ _ _ addressRead read
    (AllocatedBytes.word_mapped source frame 48 offset domain arena inside frameAligned aligned)

/-- The actual push prefix constructs its linked scratch record. Its
allocation room and parent/child/index stores are derived from this same
execution, and every old stack word at or above the old cursor survives. -/
theorem push_from_execution (source current : PanSemStateFiniteExact 64 Guest.HostMemory) (parent child cursor floor : BitVec 64)
    (installed : OriginalCode.Installed source.code) (arena : Rlp.Validation.Arena source cursor floor)
    (floorLower : 2952790016≤floor.toNat)
    (topCell : source.locals.lookup (ofString "top")=some (.val (.word parent)))
    (childCell : source.locals.lookup (ofString "child")=some (.val (.word child)))
    (execution : CallPrefix.Execution source pushActions current) :
    Arenas.Room .down cursor floor 48#64 ∧ Header current (framePointer cursor) child parent 0 ∧
      current.locals.lookup (ofString "cf")=some (.val (.word (framePointer cursor))) ∧
      current.locals.lookup (ofString "top")=some (.val (.word parent)) ∧
      current.locals.lookup (ofString "child")=some (.val (.word child)) ∧
      current.globals.lookup (ofString "scratch_ptr")=some (.val (.word (framePointer cursor))) ∧
      MemoryMetadata.erase {current with globals:=source.globals}=MemoryMetadata.erase source ∧
      (∀ key,key≠ofString "scratch_ptr"→current.globals.lookup key=source.globals.lookup key) ∧
      (∀ query : BitVec 64,query.toNat<(framePointer cursor).toNat ∨ cursor.toNat≤query.toNat→current.memory query=source.memory query) := by
  rw [pushActions] at execution
  obtain ⟨allocated,allocationReached,stores⟩:=execution.head
  obtain ⟨room,allocatedEq⟩:=allocation_reached_named source allocated cursor floor "cf" installed arena allocationReached
  rw [allocatedEq] at stores
  let allocated:=bind (Arenas.post {source with clock:=source.clock-1} .down cursor 48#64) "cf" (framePointer cursor)
  obtain ⟨recordArena,aboveFloor,beforeCursor,frameAligned⟩:=allocation_geometry source cursor floor arena room
  have frameCell : allocated.locals.lookup (ofString "cf")=some (.val (.word (framePointer cursor))):=bind_lookup_same _ _ _
  have parentCell : allocated.locals.lookup (ofString "top")=some (.val (.word parent)):=
    (bind_lookup_other _ "cf" "top" _ (by decide)).trans topCell
  have selectedCell : allocated.locals.lookup (ofString "child")=some (.val (.word child)):=
    (bind_lookup_other _ "cf" "child" _ (by decide)).trans childCell
  have readParent : eval allocated (localVar "top")=some (.val (.word parent)):=by simp [eval,evalHOLExact,localVar,toExact,parentCell]
  have readChild : eval allocated (localVar "child")=some (.val (.word child)):=by simp [eval,evalHOLExact,localVar,toExact,selectedCell]
  let first:=written allocated (framePointer cursor) 0 parent
  let second:=written first (framePointer cursor) 8 child
  let third:=written second (framePointer cursor) 16 0#64
  have firstRun:=record_store allocated "cf" (framePointer cursor) parent 0 (localVar "top") (by decide) (by decide)
    recordArena frameAligned arena.domain frameCell readParent
  have secondRun:=record_store first "cf" (framePointer cursor) child 8 (localVar "child") (by decide) (by decide)
    recordArena frameAligned arena.domain frameCell readChild
  have thirdRun:=record_store second "cf" (framePointer cursor) 0#64 16 (.const 0#64) (by decide) (by decide)
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
  refine ⟨room,⟨recordArena,frameAligned,Nat.le_trans floorLower aboveFloor,by decide,?_,?_,?_⟩,
    frameCell,parentCell,selectedCell,?_,?_,?_,?_⟩
  · have awayEight : framePointer cursor≠framePointer cursor+8#64:=by simpa using different 0 8 (by decide) (by decide) (by decide)
    have awaySixteen : framePointer cursor≠framePointer cursor+16#64:=by simpa using different 0 16 (by decide) (by decide) (by decide)
    simp [third,second,first,written,StoreWord.put,awayEight,awaySixteen]
  · have away:=different 8 16 (by decide) (by decide) (by decide)
    simp [third,second,written,StoreWord.put,away]
  · simp [third,written,StoreWord.put]
  · simp [third,second,first,written,allocated,Arenas.post,Arenas.pointerName,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,framePointer]
  · rfl
  · intro key notScratch
    simp [third,second,first,written,allocated,Arenas.post,Arenas.pointerName,QueryBranch.bind,setVarHOLFinite,
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

/-- Memory agreement above an old cursor retains an old stack header. -/
theorem Header.of_after_memory {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    {frame node parent : BitVec 64} {index cursor : Nat} (header : Header source frame node parent index)
    (above : cursor≤frame.toNat)
    (memory : ∀ query : BitVec 64,cursor≤query.toNat→target.memory query=source.memory query) :
    Header target frame node parent index := by
  have saved (offset : Nat) (inside : offset≤16) : target.memory (frame+BitVec.ofNat 64 offset)=source.memory (frame+BitVec.ofNat 64 offset):=by
    apply memory
    have number:=byteAddress_toNat frame offset (by have upper:=header.arena.upper; omega)
    change cursor≤(byteAddress frame offset).toNat
    rw [number]
    omega
  have parentMemory : target.memory frame=source.memory frame:=by simpa using saved 0 (by decide)
  exact ⟨header.arena,header.aligned,header.scratch,header.bounded,parentMemory.trans header.parentStored,
    (saved 8 (by decide)).trans header.nodeStored,(saved 16 (by decide)).trans header.indexStored⟩

structure StackFrame where
  address : BitVec 64
  node : BitVec 64
  index : Nat

def stackTop : List StackFrame→BitVec 64
  | []=>0#64
  | frame::_=>frame.address

/-- The concrete linked headers are ordered in their real downward
allocation order. Each retained older record begins after the newer record. -/
inductive HeaderStack (source : PanSemStateFiniteExact 64 Guest.HostMemory) : Nat→List StackFrame→Prop where
  | nil (cursor : Nat) : HeaderStack source cursor []
  | cons {cursor : Nat} (frame : StackFrame) (rest : List StackFrame)
      (above : cursor≤frame.address.toNat)
      (header : Header source frame.address frame.node (stackTop rest) frame.index)
      (tail : HeaderStack source (frame.address.toNat+48) rest) : HeaderStack source cursor (frame::rest)

theorem HeaderStack.weaken {source : PanSemStateFiniteExact 64 Guest.HostMemory} {cursor next : Nat} {frames : List StackFrame}
    (stack : HeaderStack source cursor frames) (lower : next≤cursor) : HeaderStack source next frames := by
  cases stack with
  | nil=>exact .nil _
  | cons frame rest above header tail=>exact .cons frame rest (lower.trans above) header tail

theorem HeaderStack.of_memory {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {cursor : Nat} {frames : List StackFrame}
    (stack : HeaderStack source cursor frames)
    (memory : ∀ query : BitVec 64,cursor≤query.toNat→target.memory query=source.memory query) : HeaderStack target cursor frames := by
  induction stack generalizing target with
  | nil cursor=>exact .nil cursor
  | @cons cursor frame rest above header tail ih=>
    refine .cons frame rest above (header.of_after_memory above memory) ?_
    exact ih (by intro query afterFrame; exact memory query (by omega))

/-- Every retained real header supplies its own allocated high scratch frame. -/
theorem HeaderStack.arenas {source : PanSemStateFiniteExact 64 Guest.HostMemory} {cursor : Nat} {frames : List StackFrame}
    (stack : HeaderStack source cursor frames) (current : StackFrame) (member : current∈frames) :
    AllocatedBytes.Arena current.address 48 ∧ 2952790016≤current.address.toNat := by
  induction stack with
  | nil=>cases member
  | cons frame rest above header tail ih=>
    rcases List.mem_cons.mp member with equal|inside
    · subst current
      exact ⟨header.arena,header.scratch⟩
    · exact ih inside

theorem HeaderStack.frame_before {source : PanSemStateFiniteExact 64 Guest.HostMemory} {cursor : Nat} {frames : List StackFrame}
    (stack : HeaderStack source cursor frames) (current : StackFrame) (member : current∈frames) : cursor≤current.address.toNat := by
  induction stack with
  | nil=>cases member
  | cons frame rest above header tail ih=>
    rcases List.mem_cons.mp member with equal|inside
    · subst current
      exact above
    · have afterFrame:=ih inside
      omega

/-- The saved descriptors and genuine size decisions for each active
linked frame, independently of its changing child-selection index. -/
def PreparedStack (source : PanSemStateFiniteExact 64 Guest.HostMemory) (valid : BitVec 64 → Prop)
    (lower upper : Nat) (frames : List StackFrame) : Prop :=
  ∀ current,current∈frames → valid current.node ∧ current.node≠0#64 ∧ Nonempty (NodeRlpFinish.Prepared source current.address current.node lower upper)

theorem PreparedStack.nil (source : PanSemStateFiniteExact 64 Guest.HostMemory) (valid : BitVec 64 → Prop) (lower upper : Nat) :
    PreparedStack source valid lower upper [] := by
  intro current impossible
  cases impossible

theorem PreparedStack.cons {source : PanSemStateFiniteExact 64 Guest.HostMemory} {valid : BitVec 64 → Prop} {lower upper : Nat} {rest : List StackFrame}
    (current : StackFrame) (member : valid current.node) (active : current.node≠0#64)
    (prepared : NodeRlpFinish.Prepared source current.address current.node lower upper) (tail : PreparedStack source valid lower upper rest) :
    PreparedStack source valid lower upper (current::rest) := by
  intro frame inside
  rcases List.mem_cons.mp inside with equal|inside
  · subst frame
    exact ⟨member,active,⟨prepared⟩⟩
  · exact tail frame inside

theorem PreparedStack.tail {source : PanSemStateFiniteExact 64 Guest.HostMemory} {valid : BitVec 64 → Prop} {lower upper : Nat} {current : StackFrame} {rest : List StackFrame}
    (stack : PreparedStack source valid lower upper (current::rest)) : PreparedStack source valid lower upper rest :=
  fun frame inside=>stack frame (List.mem_cons.mpr (Or.inr inside))

theorem PreparedStack.weaken {source : PanSemStateFiniteExact 64 Guest.HostMemory} {valid : BitVec 64 → Prop} {lower upper smaller larger : Nat} {frames : List StackFrame}
    (stack : PreparedStack source valid lower upper frames) (first : smaller≤lower) (last : upper≤larger) : PreparedStack source valid smaller larger frames := by
  intro current member
  obtain ⟨valid,active,⟨prepared⟩⟩:=stack current member
  exact ⟨valid,active,⟨prepared.weaken first last⟩⟩

theorem PreparedStack.of_frame {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {valid : BitVec 64 → Prop} {lower upper : Nat} {frames : List StackFrame}
    (stack : PreparedStack source valid lower upper frames) (same : LocalEffects.erase target=LocalEffects.erase source) : PreparedStack target valid lower upper frames := by
  intro current member
  obtain ⟨valid,active,⟨prepared⟩⟩:=stack current member
  exact ⟨valid,active,⟨prepared.of_frame same⟩⟩

/-- Partial physical agreement is enough to transport the saved stack.
The actual index16 words do not belong to these preparation footprints. -/
theorem PreparedStack.of_bands {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {heap : BitVec 64}
    {frontier cursor : Nat} {frames : List StackFrame} (graph : TrieWalk.Graph source.memory source.memaddrs)
    (lower upper inputEnd limit cut : Nat) (regions : graph.Regions lower upper) (beforeHeap : upper≤heap.toNat)
    (values : TrieWalk.Values graph limit (fun pointer length=>pointer.toNat+length.toNat≤inputEnd)) (inputBefore : inputEnd≤heap.toNat)
    (headers : HeaderStack source cursor frames) (afterFrames : ∀ current,current∈frames → cut≤current.address.toNat+24)
    (stack : PreparedStack source graph.valid frontier heap.toNat frames)
    (domain : target.memaddrs=source.memaddrs) (endian : target.be=source.be)
    (memory : ∀ query,query.toNat<heap.toNat ∨ cut≤query.toNat → target.memory query=source.memory query) :
    PreparedStack target graph.valid frontier heap.toNat frames := by
  intro current member
  obtain ⟨valid,active,⟨prepared⟩⟩:=stack current member
  obtain ⟨arena,_scratch⟩:=headers.arenas current member
  exact ⟨valid,active,⟨prepared.of_memory domain endian (fun query required=>memory query
    (prepared.footprint_bands graph valid active lower upper inputEnd limit cut regions beforeHeap values inputBefore arena (afterFrames current member) query required))⟩⟩

theorem PreparedStack.with_index {source : PanSemStateFiniteExact 64 Guest.HostMemory} {valid : BitVec 64 → Prop}
    {lower upper : Nat} {current : StackFrame} {rest : List StackFrame}
    (stack : PreparedStack source valid lower upper (current::rest)) (index : Nat) :
    PreparedStack source valid lower upper ({current with index:=index}::rest) := by
  intro frame member
  rcases List.mem_cons.mp member with equal|inside
  · subst frame
    exact stack current (List.mem_cons.mpr (Or.inl rfl))
  · exact stack frame (List.mem_cons.mpr (Or.inr inside))

/-- The real top-frame index16 store cannot affect any active record's
saved preparation words or any earlier persistent sizing decision. -/
theorem PreparedStack.after_index_frame {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {heap : BitVec 64}
    {frontier cursor : Nat} {current : StackFrame} {rest : List StackFrame} (graph : TrieWalk.Graph source.memory source.memaddrs)
    (lower upper inputEnd limit : Nat) (regions : graph.Regions lower upper) (beforeHeap : upper≤heap.toNat) (heapUpper : heap.toNat≤2952790016)
    (values : TrieWalk.Values graph limit (fun pointer length=>pointer.toNat+length.toNat≤inputEnd)) (inputBefore : inputEnd≤heap.toNat)
    (headers : HeaderStack source cursor (current::rest)) (prepared : PreparedStack source graph.valid frontier heap.toNat (current::rest))
    (domain : target.memaddrs=source.memaddrs) (endian : target.be=source.be)
    (memory : ∀ query,query≠current.address+16#64 → target.memory query=source.memory query) :
    PreparedStack target graph.valid frontier heap.toNat (current::rest) := by
  have atHead : HeaderStack source current.address.toNat (current::rest):=by
    cases headers with
    | cons frame rest above header tail=>exact .cons _ _ (Nat.le_refl _) header tail
  obtain ⟨arena,scratch⟩:=headers.arenas current (List.mem_cons.mpr (Or.inl rfl))
  have number : (current.address+16#64).toNat=current.address.toNat+16:=byteAddress_toNat current.address 16 (by have room:=arena.upper; omega)
  apply PreparedStack.of_bands graph lower upper inputEnd limit (current.address.toNat+24) regions beforeHeap values inputBefore headers
    (by intro frame member; have afterHead:=atHead.frame_before frame member; omega) prepared domain endian
  intro query required
  apply memory query
  intro equal
  have numeric:=congrArg BitVec.toNat equal
  rw [number] at numeric
  rcases required with older|afterRecord
  · omega
  · omega

/-- A real normal branch scan/index store updates its linked head header
and retains every active saved preparation at that same execution endpoint. -/
theorem branch_scope_prepared (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64)
    (cursor frontier lower upper inputEnd limit : Nat) (current : StackFrame) (rest : List StackFrame) (found : BitVec 64)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (regions : graph.Regions lower upper) (beforeHeap : upper≤heap.toNat) (heapUpper : heap.toNat≤2952790016)
    (values : TrieWalk.Values graph limit (fun pointer length=>pointer.toNat+length.toNat≤inputEnd)) (inputBefore : inputEnd≤heap.toNat)
    (headers : HeaderStack source cursor (current::rest)) (prepared : PreparedStack source graph.valid frontier heap.toNat (current::rest))
    (installed : OriginalCode.Installed source.code) (domain : source.memaddrs=InitE.ordinaryDomain)
    (topCell : source.locals.lookup (ofString "top")=some (.val (.word current.address)))
    (foundCell : source.locals.lookup (ofString "found")=some (.val (.word found)))
    (normal : evaluateHOLFiniteState source branchScope=(none,post)) :
    ∃ nextIndex,HeaderStack post cursor ({current with index:=nextIndex}::rest) ∧
      PreparedStack post graph.valid frontier heap.toNat ({current with index:=nextIndex}::rest) ∧ MemoryMetadata.erase post=MemoryMetadata.erase source := by
  have originalHeaders:=headers
  cases headers with
  | cons frame rest above header tail=>
    obtain ⟨⟨nextIndex,nextHeader⟩,fields,memory⟩:=branch_scope_normal source post current.address current.node (stackTop rest) found current.index installed header domain topCell foundCell normal
    have retainedPrepared:=PreparedStack.after_index_frame graph lower upper inputEnd limit regions beforeHeap heapUpper values inputBefore
      originalHeaders prepared (MemoryMetadata.domain fields) (MemoryMetadata.endian fields) memory
    have number : (current.address+16#64).toNat=current.address.toNat+16:=byteAddress_toNat current.address 16 (by have room:=header.arena.upper; omega)
    have retainedHeaders:=tail.of_memory (target:=post) (by
      intro query afterFrame
      apply memory query
      intro equal
      have numeric:=congrArg BitVec.toNat equal
      rw [number] at numeric
      omega)
    exact ⟨nextIndex,.cons _ rest above nextHeader retainedHeaders,retainedPrepared.with_index nextIndex,fields⟩

/-- The full actual selector preserves the ordered prepared stack while
updating its head index to the value actually stored by its selected branch. -/
theorem select_child_prepared (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64)
    (cursor frontier lower upper inputEnd limit : Nat) (current : StackFrame) (rest : List StackFrame) (tag found : BitVec 64)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (regions : graph.Regions lower upper) (beforeHeap : upper≤heap.toNat) (heapUpper : heap.toNat≤2952790016)
    (values : TrieWalk.Values graph limit (fun pointer length=>pointer.toNat+length.toNat≤inputEnd)) (inputBefore : inputEnd≤heap.toNat)
    (headers : HeaderStack source cursor (current::rest)) (prepared : PreparedStack source graph.valid frontier heap.toNat (current::rest))
    (installed : OriginalCode.Installed source.code) (domain : source.memaddrs=InitE.ordinaryDomain)
    (topCell : source.locals.lookup (ofString "top")=some (.val (.word current.address)))
    (tagCell : source.locals.lookup (ofString "k")=some (.val (.word tag)))
    (foundCell : source.locals.lookup (ofString "found")=some (.val (.word found)))
    (normal : evaluateHOLFiniteState source selectChild=(none,post)) :
    ∃ nextIndex,HeaderStack post cursor ({current with index:=nextIndex}::rest) ∧
      PreparedStack post graph.valid frontier heap.toNat ({current with index:=nextIndex}::rest) ∧ MemoryMetadata.erase post=MemoryMetadata.erase source := by
  have originalHeaders:=headers
  cases headers with
  | cons frame rest above header tail=>
    obtain ⟨⟨nextIndex,nextHeader⟩,fields,memory⟩:=select_child_normal source post current.address current.node (stackTop rest) tag found current.index installed header domain topCell tagCell foundCell normal
    have retainedPrepared:=PreparedStack.after_index_frame graph lower upper inputEnd limit regions beforeHeap heapUpper values inputBefore
      originalHeaders prepared (MemoryMetadata.domain fields) (MemoryMetadata.endian fields) memory
    have number : (current.address+16#64).toNat=current.address.toNat+16:=byteAddress_toNat current.address 16 (by have room:=header.arena.upper; omega)
    have retainedHeaders:=tail.of_memory (target:=post) (by
      intro query afterFrame
      apply memory query
      intro equal
      have numeric:=congrArg BitVec.toNat equal
      rw [number] at numeric
      omega)
    exact ⟨nextIndex,.cons _ rest above nextHeader retainedHeaders,retainedPrepared.with_index nextIndex,fields⟩

/-- Every actual high linked header survives the real persistent finish writes. -/
theorem HeaderStack.after_finish {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {cursor : Nat} {frames : List StackFrame}
    {node heap : BitVec 64} {bytes : Nat} {keep : BitVec 64 → Prop}
    (stack : HeaderStack source cursor frames) (high : 2952790016≤cursor)
    (output : NodeRlpFinish.FinishOutput source target node heap bytes keep) : HeaderStack target cursor frames :=
  stack.of_memory (fun query afterCursor=>output.scratch query (high.trans afterCursor))

/-- The actual child finish retains the complete saved preparation for all
active frames. Advancing the heap may then weaken their shared upper bound. -/
theorem PreparedStack.after_finish {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    {node heap frame : BitVec 64} {lower upper inputEnd cacheLimit valueLimit bytes cursor : Nat} {frames : List StackFrame}
    (data : NodeRlpFinish.Entry source node heap frame lower upper inputEnd cacheLimit valueLimit)
    (headers : HeaderStack source cursor frames) (stack : PreparedStack source data.graph.valid upper heap.toNat frames)
    (output : NodeRlpFinish.FinishOutput source target node heap bytes (NodeRlpFinish.WithBand (NodeRlpFinish.SerializerQueries data.graph inputEnd) upper heap.toNat)) :
    PreparedStack target data.graph.valid upper heap.toNat frames := by
  intro current member
  obtain ⟨valid,active,⟨prepared⟩⟩:=stack current member
  obtain ⟨arena,scratch⟩:=headers.arenas current member
  exact ⟨valid,active,⟨prepared.after_finish data valid active arena scratch output⟩⟩

/-- The actual ignored first begin followed by the literal top declaration. -/
def prepareActions : List CallPrefix.Action:=[
  .command (.call (some (none,none)) (ofString "_node_rlp_begin") [localVar "fr",localVar "node"]),
  .declare (ofString "top") .one (localVar "fr")]

theorem prepare_shape : beginAndAfter=CallPrefix.program prepareActions loopAndAfter := by
  rw [shapes.2.1,shapes.2.2.1]
  rfl

/-- The actual first preparation constructs the singleton linked/prepared
stack at the real while-loop entry. No begin return or later room is assumed. -/
theorem prepare_normal (source current : PanSemStateFiniteExact 64 Guest.HostMemory) (node heap frame : BitVec 64)
    (lower frontier inputEnd limit : Nat)
    (data : NodeRlpBegin.Entry source node heap lower limit (fun pointer length=>pointer.toNat+length.toNat≤inputEnd))
    (beforeHeap : frontier≤heap.toNat) (inputBefore : inputEnd≤heap.toNat)
    (header : Header source frame node 0#64 0) (valueFits : limit+19≤2^63) (installed : OriginalCode.Installed source.code)
    (frameCell : source.locals.lookup (ofString "fr")=some (.val (.word frame)))
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node)))
    (trace : CallPrefix.Execution source prepareActions current) :
    HeaderStack current frame.toNat [{address:=frame,node:=node,index:=0}] ∧
      PreparedStack current data.graph.valid frontier (NodeRlpBegin.outputHeap source node heap).toNat [{address:=frame,node:=node,index:=0}] ∧
      current.locals.lookup (ofString "top")=some (.val (.word frame)) ∧
      current.globals.lookup (ofString "heap_ptr")=some (.val (.word (NodeRlpBegin.outputHeap source node heap))) ∧
      heap.toNat≤(NodeRlpBegin.outputHeap source node heap).toNat ∧ (NodeRlpBegin.outputHeap source node heap).toNat≤2952790016 ∧
      (NodeRlpBegin.outputHeap source node heap).toNat%8=0 ∧
      source.clock-current.clock≤NodeRlpBegin.bodyAllowance source.memory node+1 := by
  unfold prepareActions at trace
  obtain ⟨begun,reached,rest⟩:=trace.head
  have beginRun : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "_node_rlp_begin") [localVar "fr",localVar "node"])=(none,begun):=by
    cases reached with
    | command _ _ run=>exact run
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) [localVar "fr",localVar "node"]=
      some [.val (.word frame),.val (.word node)]:=by simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,frameCell,nodeCell]
  obtain ⟨locals,⟨output⟩⟩:=NodeRlpBegin.call_normal source begun node heap frame lower limit _ data valueFits installed [localVar "fr",localVar "node"] args beginRun
  obtain ⟨ready,declared,last⟩:=rest.head
  have currentEq : current=ready:=by cases last; rfl
  subst current
  have read : eval begun (localVar "fr")=some (.val (.word frame)):=by simp [eval,evalHOLExact,toExact,localVar,locals,frameCell]
  have endpoint:=declared.declare_target (.val (.word frame)) read
  have fields : LocalEffects.erase ready=LocalEffects.erase begun:=by rw [endpoint]; rfl
  have heapFacts:=output.heap data
  let record : StackFrame:={address:=frame,node:=node,index:=0}
  have begunHeaders : HeaderStack begun frame.toNat [record]:=
    .cons record [] (Nat.le_refl _) (header.after_begin output) (.nil (frame.toNat+48))
  let fresh:=NodeRlpFinish.Prepared.of_begin output data valueFits header.arena header.scratch (data.value_byte_low (inputBefore.trans data.heapUpper))
  have begunPrepared : PreparedStack begun data.graph.valid frontier (NodeRlpBegin.outputHeap source node heap).toNat [record]:=
    PreparedStack.cons record data.member data.active (fresh.weaken beforeHeap (Nat.le_refl _)) (PreparedStack.nil _ _ _ _)
  have memory:=LocalEffects.memory_of_erase begun ready fields
  have globals:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>state.globals.lookup (ofString "heap_ptr")) fields
  refine ⟨begunHeaders.of_memory (fun query _=>congrFun memory query),begunPrepared.of_frame fields,?_,globals.trans heapFacts.1,heapFacts.2.1,heapFacts.2.2.1,heapFacts.2.2.2,?_⟩
  · rw [endpoint]
    exact bind_lookup_same _ _ _
  · have clock : ready.clock=begun.clock:=by rw [endpoint]; rfl
    rw [clock]
    exact output.price

/-- A real continuing push retains the live physical arena and spends at
least one available record, giving the strict outer-rank decrease on push. -/
theorem push_live (source current : PanSemStateFiniteExact 64 Guest.HostMemory) (parent child cursor floor : BitVec 64) (depth : Nat)
    (live : Rlp.LiveArena source) (arena : Rlp.Validation.Arena source cursor floor)
    (topCell : source.locals.lookup (ofString "top")=some (.val (.word parent)))
    (childCell : source.locals.lookup (ofString "child")=some (.val (.word child)))
    (execution : CallPrefix.Execution source pushActions current) :
    Arenas.Room .down cursor floor 48#64 ∧ Header current (framePointer cursor) child parent 0 ∧
      Rlp.Validation.Arena current (framePointer cursor) floor ∧ Rlp.LiveArena current ∧
      current.locals.lookup (ofString "cf")=some (.val (.word (framePointer cursor))) ∧
      current.locals.lookup (ofString "child")=some (.val (.word child)) ∧
      rank (recordsLeft (framePointer cursor).toNat floor.toNat) (depth+1)<rank (recordsLeft cursor.toNat floor.toNat) depth ∧
      (∀ query : BitVec 64,query.toNat<(framePointer cursor).toNat ∨ cursor.toNat≤query.toNat→current.memory query=source.memory query) := by
  obtain ⟨floorLower,cursorUpper⟩:=live.bounds arena
  obtain ⟨room,header,cfCell,finalTop,finalChild,scratchCell,metadata,others,memory⟩:=
    push_from_execution source current parent child cursor floor live.code arena floorLower topCell childCell execution
  obtain ⟨recordArena,aboveFloor,beforeCursor,frameAligned⟩:=allocation_geometry source cursor floor arena room
  have domain:=congrArg PanSemStateFiniteExact.memaddrs metadata
  have code:=congrArg PanSemStateFiniteExact.code metadata
  change current.memaddrs=source.memaddrs at domain
  change current.code=source.code at code
  have next : Rlp.Validation.Arena current (framePointer cursor) floor:=
    ⟨domain.trans arena.domain,scratchCell,(others _ (by decide)).trans arena.limitGlobal,
      aboveFloor,arena.aligned,arena.lower,by have upper:=arena.upper; omega⟩
  have installed : OriginalCode.Installed current.code:=by rw [code]; exact live.code
  exact ⟨room,header,next,Rlp.LiveArena.of_validation next floorLower (by omega) installed,cfCell,finalChild,
    push_rank _ _ depth (allocation_budget cursor floor arena.aligned room),memory⟩

/-- The actually constructed fresh frame links to the old top and keeps
every older linked header. This is the prefix before begin installs top. -/
theorem push_prefix_stack (source current : PanSemStateFiniteExact 64 Guest.HostMemory) (child cursor floor : BitVec 64)
    (frames : List StackFrame) (live : Rlp.LiveArena source) (arena : Rlp.Validation.Arena source cursor floor)
    (stack : HeaderStack source cursor.toNat frames)
    (topCell : source.locals.lookup (ofString "top")=some (.val (.word (stackTop frames))))
    (childCell : source.locals.lookup (ofString "child")=some (.val (.word child)))
    (execution : CallPrefix.Execution source pushActions current) :
    HeaderStack current (framePointer cursor).toNat ({address:=framePointer cursor,node:=child,index:=0}::frames) ∧
      rank (recordsLeft (framePointer cursor).toNat floor.toNat) (frames.length+1)<rank (recordsLeft cursor.toNat floor.toNat) frames.length := by
  obtain ⟨room,header,next,nextLive,cfCell,finalChild,decreased,memory⟩:=
    push_live source current (stackTop frames) child cursor floor frames.length live arena topCell childCell execution
  have retained:=stack.of_memory (target:=current) (fun query afterCursor=>memory query (Or.inr afterCursor))
  have geometry:=allocation_geometry source cursor floor arena room
  exact ⟨.cons _ frames (Nat.le_refl _) header (retained.weaken geometry.2.2.1),decreased⟩

/-- The real push prefix transports the selected child's incoming graph
to the actual begin call, protecting all registered fields below the heap. -/
theorem push_begin_entry (source current : PanSemStateFiniteExact 64 Guest.HostMemory) (parent child heap cursor floor : BitVec 64)
    (lower limit : Nat) (property : BitVec 64→BitVec 64→Prop)
    (data : NodeRlpBegin.Entry source child heap lower limit property)
    (live : Rlp.LiveArena source) (arena : Rlp.Validation.Arena source cursor floor)
    (topCell : source.locals.lookup (ofString "top")=some (.val (.word parent)))
    (childCell : source.locals.lookup (ofString "child")=some (.val (.word child)))
    (execution : CallPrefix.Execution source pushActions current) :
    Header current (framePointer cursor) child parent 0 ∧
      Nonempty (NodeRlpBegin.Entry current child heap lower limit property) ∧
      current.locals.lookup (ofString "child")=some (.val (.word child)) ∧
      current.locals.lookup (ofString "cf")=some (.val (.word (framePointer cursor))) := by
  obtain ⟨floorLower,cursorUpper⟩:=live.bounds arena
  obtain ⟨room,header,cfCell,finalTop,finalChild,scratchCell,metadata,others,memory⟩:=
    push_from_execution source current parent child cursor floor live.code arena floorLower topCell childCell execution
  have domain:=congrArg PanSemStateFiniteExact.memaddrs metadata
  change current.memaddrs=source.memaddrs at domain
  have next:=data.of_before domain ((others _ (by decide)).trans data.heapCell) (by
    intro query earlier
    apply memory query (Or.inl ?_)
    have upper:=data.heapUpper
    have scratch:=header.scratch
    omega)
  exact ⟨header,next,finalChild,cfCell⟩

/-- A genuine continuing push derives its actual four-action prefix,
begin/install-top suffix and final lexical restoration. -/
theorem push_normal_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (installed : OriginalCode.Installed source.code)
    (normal : evaluateHOLFiniteState source pushBranch=(none,post)) :
    ∃ current inner,CallPrefix.Execution source pushActions current ∧
      evaluateHOLFiniteState current pushTail=(none,inner) ∧ post=restore source "cf" inner := by
  let stores:=CallPrefix.program pushActions.tail pushTail
  have shape : pushBranch=.decCall (ofString "cf") .one (ofString "scratch_alloc") [.const 48#64] stores:=by rw [push_shape]; rfl
  rw [shape] at normal
  obtain ⟨callee,called,amountCell⟩:=CallNormal.unary_environment source.code.lookup (ofString "scratch_alloc") "n"
    (Arenas.body .down) 48#64 (Arenas.original_code source.code installed .down)
  obtain ⟨funded,child,returned,inner,run,checked,continued,endpoint⟩:=CallNormal.scoped_none source post "cf" .one
    (ofString "scratch_alloc") [.const 48#64] [.val (.word 48#64)] (Arenas.body .down) stores callee .one rfl called normal
  let allocated:=CallNormal.continuationEntry source child "cf" returned
  have reached : CallPrefix.Reaches source (.scoped (ofString "cf") .one (ofString "scratch_alloc") [.const 48#64]) allocated:=
    .scoped source (ofString "cf") .one (ofString "scratch_alloc") [.const 48#64] [.val (.word 48#64)] (Arenas.body .down) callee .one
      returned child rfl called (by omega) run checked
  let storeParent : ProgHOL 64:=.store (.op .add [localVar "cf",.const 0#64]) (localVar "top")
  let storeChild : ProgHOL 64:=.store (.op .add [localVar "cf",.const 8#64]) (localVar "child")
  let storeIndex : ProgHOL 64:=.store (.op .add [localVar "cf",.const 16#64]) (.const 0#64)
  change evaluateHOLFiniteState allocated (.seq storeParent (.seq storeChild (.seq storeIndex pushTail)))=(none,inner) at continued
  obtain ⟨first,firstRun,restRun⟩:=sequence_none allocated inner storeParent _ continued
  obtain ⟨second,secondRun,lastRun⟩:=sequence_none first inner storeChild _ restRun
  obtain ⟨current,thirdRun,tailRun⟩:=sequence_none second inner storeIndex pushTail lastRun
  exact ⟨current,inner,.step reached (.step (.command _ _ _ firstRun)
    (.step (.command _ _ _ secondRun) (.step (.command _ _ _ thirdRun) (.done current)))),tailRun,endpoint⟩

structure PushOutput (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (child heap cursor floor : BitVec 64)
    (lower limit : Nat) (property : BitVec 64→BitVec 64→Prop) (frames : List StackFrame) where
  current : PanSemStateFiniteExact 64 Guest.HostMemory
  begun : PanSemStateFiniteExact 64 Guest.HostMemory
  execution : CallPrefix.Execution source pushActions current
  entry : NodeRlpBegin.Entry current child heap lower limit property
  output : NodeRlpBegin.Output current begun child heap (framePointer cursor) limit (.val (.word 0#64))
    (NodeRlpBegin.bodyAllowance current.memory child+1)
  frame : LocalEffects.erase post=LocalEffects.erase begun
  topCell : post.locals.lookup (ofString "top")=some (.val (.word (framePointer cursor)))
  stack : HeaderStack post (framePointer cursor).toNat ({address:=framePointer cursor,node:=child,index:=0}::frames)
  arena : Rlp.Validation.Arena post (framePointer cursor) floor
  live : Rlp.LiveArena post
  decreased : rank (recordsLeft (framePointer cursor).toNat floor.toNat) (frames.length+1)<rank (recordsLeft cursor.toNat floor.toNat) frames.length

/-- The complete actual normal push installs its real new top, retains
the whole linked stack and live arena, and strictly decreases the rank.
No completed begin call or future room is supplied by the caller. -/
theorem push_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (child heap cursor floor : BitVec 64)
    (lower limit : Nat) (property : BitVec 64→BitVec 64→Prop) (frames : List StackFrame)
    (data : NodeRlpBegin.Entry source child heap lower limit property)
    (live : Rlp.LiveArena source) (arena : Rlp.Validation.Arena source cursor floor)
    (stack : HeaderStack source cursor.toNat frames) (valueFits : limit+19≤2^63)
    (topCell : source.locals.lookup (ofString "top")=some (.val (.word (stackTop frames))))
    (childCell : source.locals.lookup (ofString "child")=some (.val (.word child)))
    (normal : evaluateHOLFiniteState source pushBranch=(none,post)) :
    Nonempty (PushOutput source post child heap cursor floor lower limit property frames) := by
  obtain ⟨current,inner,execution,tailRun,endpoint⟩:=push_normal_trace source post live.code normal
  obtain ⟨room,header,next,nextLive,cfCell,finalChild,decreased,memory⟩:=
    push_live source current (stackTop frames) child cursor floor frames.length live arena topCell childCell execution
  obtain ⟨freshStack,_rank⟩:=push_prefix_stack source current child cursor floor frames live arena stack topCell childCell execution
  obtain ⟨_header,⟨entry⟩,_child,_cf⟩:=push_begin_entry source current (stackTop frames) child heap cursor floor lower limit property data live arena topCell childCell execution
  obtain ⟨begun,beginRun,assignRun⟩:=sequence_none current inner _ _ tailRun
  have args : evalListHOLFinite current (h:=fun query=>Classical.propDecidable (current.memaddrs query)) [localVar "cf",localVar "child"]=
      some [.val (.word (framePointer cursor)),.val (.word child)]:=by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,cfCell,finalChild]
  obtain ⟨localsEq,⟨output⟩⟩:=NodeRlpBegin.call_normal current begun child heap (framePointer cursor) lower limit property entry valueFits nextLive.code
    [localVar "cf",localVar "child"] args beginRun
  have cfRead : eval begun (localVar "cf")=some (.val (.word (framePointer cursor))):=by simp [eval,evalHOLExact,localVar,toExact,localsEq,cfCell]
  have innerEq:=assign_none begun inner "top" (localVar "cf") (framePointer cursor) cfRead assignRun
  have finalFrame : LocalEffects.erase post=LocalEffects.erase begun:=by rw [endpoint,innerEq]; rfl
  have begunLive:=nextLive.of_cursors output.domain output.code (output.heap_globals _ (by decide)) (output.heap_globals _ (by decide))
  have begunArena : Rlp.Validation.Arena begun (framePointer cursor) floor:=
    ⟨output.domain.trans next.domain,(output.heap_globals _ (by decide)).trans next.cursorGlobal,
      (output.heap_globals _ (by decide)).trans next.limitGlobal,next.ordered,next.aligned,next.lower,next.upper⟩
  have begunStack : HeaderStack begun (framePointer cursor).toNat ({address:=framePointer cursor,node:=child,index:=0}::frames):=by
    cases freshStack with
    | cons frame rest above freshHeader tail=>
      exact .cons _ _ above (freshHeader.after_begin output)
        (tail.of_memory (fun query afterFrame=>output.after_frame header.arena header.scratch query afterFrame))
  have finalMemory:=LocalEffects.memory_of_erase begun post finalFrame
  have finalGlobals:=congrArg PanSemStateFiniteExact.globals finalFrame
  have finalDomain:=congrArg PanSemStateFiniteExact.memaddrs finalFrame
  refine ⟨{
    current:=current,begun:=begun,execution:=execution,entry:=entry,output:=output,frame:=finalFrame,
    topCell:=?_,stack:=begunStack.of_memory (fun query _=>congrFun finalMemory query),
    arena:=begunArena.of_fields begun post (framePointer cursor) floor finalDomain finalGlobals,
    live:=begunLive.of_frame finalFrame,decreased:=decreased }⟩
  rw [endpoint,innerEq]
  exact (restore_lookup_other source _ "cf" "top" (by decide)).trans (bind_lookup_same _ _ _)

/-- An actual continuing push installs a genuinely prepared new frame and
retains every older saved preparation. The two physical query bands are
transported through the same scratch stores and real child begin call. -/
theorem push_prepared_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (child heap cursor floor : BitVec 64)
    (lower frontier inputEnd limit : Nat) (frames : List StackFrame)
    (data : NodeRlpBegin.Entry source child heap lower limit (fun pointer length=>pointer.toNat+length.toNat≤inputEnd))
    (regions : data.graph.Regions lower frontier) (beforeHeap : frontier≤heap.toNat) (inputBefore : inputEnd≤heap.toNat)
    (live : Rlp.LiveArena source) (arena : Rlp.Validation.Arena source cursor floor)
    (headers : HeaderStack source cursor.toNat frames) (prepared : PreparedStack source data.graph.valid frontier heap.toNat frames)
    (valueFits : limit+19≤2^63)
    (topCell : source.locals.lookup (ofString "top")=some (.val (.word (stackTop frames))))
    (childCell : source.locals.lookup (ofString "child")=some (.val (.word child)))
    (normal : evaluateHOLFiniteState source pushBranch=(none,post)) :
    ∃ result : PushOutput source post child heap cursor floor lower limit (fun pointer length=>pointer.toNat+length.toNat≤inputEnd) frames,
      PreparedStack post data.graph.valid frontier (NodeRlpBegin.outputHeap result.current child heap).toNat
        ({address:=framePointer cursor,node:=child,index:=0}::frames) ∧
      post.globals.lookup (ofString "heap_ptr")=some (.val (.word (NodeRlpBegin.outputHeap result.current child heap))) ∧
      heap.toNat≤(NodeRlpBegin.outputHeap result.current child heap).toNat ∧
      (NodeRlpBegin.outputHeap result.current child heap).toNat≤2952790016 ∧
      (NodeRlpBegin.outputHeap result.current child heap).toNat%8=0 := by
  obtain ⟨result⟩:=push_normal source post child heap cursor floor lower limit _ frames data live arena headers valueFits topCell childCell normal
  obtain ⟨room,header,_next,_nextLive,_cf,_child,_rank,prefixMemory⟩:=
    push_live source result.current (stackTop frames) child cursor floor frames.length live arena topCell childCell result.execution
  have geometry:=allocation_geometry source cursor floor arena room
  have memory (query : BitVec 64) (required : query.toNat<heap.toNat ∨ cursor.toNat≤query.toNat) :
      result.begun.memory query=source.memory query:=by
    rcases required with old|afterCursor
    · exact (result.output.before_heap header.arena header.scratch data.heapUpper query old).trans
        (prefixMemory query (Or.inl (by have bound:=data.heapUpper; have scratch:=header.scratch; omega)))
    · exact (result.output.after_frame header.arena header.scratch query (geometry.2.2.1.trans afterCursor)).trans
        (prefixMemory query (Or.inr afterCursor))
  have retained:=PreparedStack.of_bands data.graph lower frontier inputEnd limit cursor.toNat regions beforeHeap data.values inputBefore headers
    (by intro current member; have afterCursor:=headers.frame_before current member; omega) prepared
    (result.output.domain.trans result.execution.runtime.1) (result.output.endian.trans result.execution.runtime.2.1) memory
  have heapFacts:=result.output.heap result.entry
  have valueLow:=result.entry.value_byte_low (inputBefore.trans data.heapUpper)
  let fresh:=NodeRlpFinish.Prepared.of_begin result.output result.entry valueFits header.arena header.scratch valueLow
  have begunPrepared : PreparedStack result.begun data.graph.valid frontier (NodeRlpBegin.outputHeap result.current child heap).toNat
      ({address:=framePointer cursor,node:=child,index:=0}::frames):=
    PreparedStack.cons _ data.member data.active (fresh.weaken beforeHeap (Nat.le_refl _)) (retained.weaken (Nat.le_refl _) heapFacts.2.1)
  have globals:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>state.globals.lookup (ofString "heap_ptr")) result.frame
  refine ⟨result,begunPrepared.of_frame result.frame,globals.trans heapFacts.1,heapFacts.2⟩

/-- The actual push stores are above the old heap and therefore retain
the selected child's original preparation allowance. -/
theorem push_allowance (source current : PanSemStateFiniteExact 64 Guest.HostMemory) (parent child heap cursor floor : BitVec 64)
    (lower limit : Nat) (property : BitVec 64→BitVec 64→Prop)
    (data : NodeRlpBegin.Entry source child heap lower limit property)
    (live : Rlp.LiveArena source) (arena : Rlp.Validation.Arena source cursor floor)
    (topCell : source.locals.lookup (ofString "top")=some (.val (.word parent)))
    (childCell : source.locals.lookup (ofString "child")=some (.val (.word child)))
    (execution : CallPrefix.Execution source pushActions current) :
    NodeRlpBegin.bodyAllowance current.memory child=NodeRlpBegin.bodyAllowance source.memory child := by
  obtain ⟨floorLower,cursorUpper⟩:=live.bounds arena
  obtain ⟨room,header,cfCell,finalTop,finalChild,scratchCell,metadata,others,memory⟩:=
    push_from_execution source current parent child cursor floor live.code arena floorLower topCell childCell execution
  have agree (query : BitVec 64) (older : query.toNat<heap.toNat) : current.memory query=source.memory query:=by
    apply memory query (Or.inl ?_)
    have heapUpper:=data.heapUpper
    have scratch:=header.scratch
    omega
  have tagEq:=congrArg MemoryBytes.wordBits (agree child
    (data.graph.footprint_bounds lower heap.toNat data.regions child (.header child data.member data.active)).2)
  change GasBudget.wordAt current.memory child=GasBudget.wordAt source.memory child at tagEq
  by_cases branch : GasBudget.wordAt source.memory child=3#64
  · simp [NodeRlpBegin.bodyAllowance,tagEq,branch]
  · have pathTag : GasBudget.wordAt source.memory child=1#64 ∨ GasBudget.wordAt source.memory child=2#64:=by
      rcases NodeRlpBegin.tag_cases source child heap lower limit property data with leaf|extension|isBranch
      · exact Or.inl leaf
      · exact Or.inr extension
      · exact (branch isBranch).elim
    have sizeEq:=congrArg MemoryBytes.wordBits (agree (child+40#64)
      (data.graph.footprint_bounds lower heap.toNat data.regions _ (.size child data.member data.active pathTag)).2)
    change GasBudget.wordAt current.memory (child+40#64)=GasBudget.wordAt source.memory (child+40#64) at sizeEq
    simp [NodeRlpBegin.bodyAllowance,tagEq,sizeEq,branch]

/-- All actual push outcomes, including failed preparation and allocation,
cost at most the original child's begin allowance plus three source ticks. -/
theorem push_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (parent child heap cursor floor : BitVec 64)
    (lower limit : Nat) (property : BitVec 64→BitVec 64→Prop)
    (data : NodeRlpBegin.Entry source child heap lower limit property)
    (live : Rlp.LiveArena source) (arena : Rlp.Validation.Arena source cursor floor) (valueFits : limit+19≤2^63)
    (topCell : source.locals.lookup (ofString "top")=some (.val (.word parent)))
    (childCell : source.locals.lookup (ofString "child")=some (.val (.word child))) :
    source.clock-(evaluateHOLFiniteState source pushBranch).2.clock≤NodeRlpBegin.bodyAllowance source.memory child+3 := by
  let output:=evaluateHOLFiniteState source pushBranch
  rcases push_trace source output.2 live.code output.1 rfl with stopped|reached
  · have price:=stopped.1
    change source.clock-output.2.clock≤_
    omega
  · obtain ⟨current,inner,execution,forward,spent,clockEq,tailRun⟩:=reached
    obtain ⟨header,⟨entry⟩,selectedCell,cfCell⟩:=push_begin_entry source current parent child heap cursor floor lower limit property
      data live arena topCell childCell execution
    have currentInstalled : OriginalCode.Installed current.code:=by rw [execution.runtime.2.2.2.1]; exact live.code
    have args : evalListHOLFinite current (h:=fun query=>Classical.propDecidable (current.memaddrs query)) [localVar "cf",localVar "child"]=
        some [.val (.word (framePointer cursor)),.val (.word child)]:=by
      simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,cfCell,selectedCell]
    have tailPrice:=ClockCost.sequence_current current _ _ (NodeRlpBegin.bodyAllowance current.memory child+1) 0
      (NodeRlpBegin.call_cost current child heap (framePointer cursor) lower limit property entry valueFits currentInstalled (some none)
        [localVar "cf",localVar "child"] args) (ClockCost.assign current.code (ofString "top") (localVar "cf"))
    change current.clock-(evaluateHOLFiniteState current pushTail).2.clock≤NodeRlpBegin.bodyAllowance current.memory child+1 at tailPrice
    rw [tailRun] at tailPrice
    rw [push_allowance source current parent child heap cursor floor lower limit property data live arena topCell childCell execution] at tailPrice
    change current.clock-inner.clock≤NodeRlpBegin.bodyAllowance source.memory child+1 at tailPrice
    have afterClock:=evaluateHOLFiniteState_clock_le current pushTail
    rw [tailRun] at afterClock
    change inner.clock≤current.clock at afterClock
    change source.clock-output.2.clock≤_
    rw [clockEq]
    omega


def popBranch : ProgHOL 64:=match pushChoice with | .ite _ _ no=>no | _=>.skip
def finishArguments : List (ExpHOL 64):=[localVar "top",localVar "nd"]
def parentExpression : ExpHOL 64:=.load .one (.op .add [localVar "top",.const 0#64])

set_option maxRecDepth 100000 in
theorem pop_shape : popBranch=.seq (.call (some (none,none)) (ofString "_node_rlp_finish") finishArguments)
    (.assign .local (ofString "top") parentExpression) := by
  simp only [popBranch,pushChoice,stepTail,afterStepChild,afterStepKind,afterStepNode,step,loop,loopAndAfter,
    afterBegin,beginAndAfter,afterNode,afterParent,afterFrame,afterMark,body,finishArguments,parentExpression,
    Guest.Software.guestFn__node_rlp_fill,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none,localVar]

theorem finish_arguments (source : PanSemStateFiniteExact 64 Guest.HostMemory) (frame node : BitVec 64)
    (topCell : source.locals.lookup (ofString "top")=some (.val (.word frame)))
    (nodeCell : source.locals.lookup (ofString "nd")=some (.val (.word node))) :
    evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) finishArguments=some [.val (.word frame),.val (.word node)] := by
  simp [finishArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,topCell,nodeCell]

/-- All real pop outcomes add no source ticks beyond the actual finish call. -/
theorem pop_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (node heap frame : BitVec 64)
    (lower upper inputEnd cacheLimit valueLimit : Nat) (data : NodeRlpFinish.Entry source node heap frame lower upper inputEnd cacheLimit valueLimit)
    (topCell : source.locals.lookup (ofString "top")=some (.val (.word frame)))
    (nodeCell : source.locals.lookup (ofString "nd")=some (.val (.word node))) :
    source.clock-(evaluateHOLFiniteState source popBranch).2.clock≤NodeRlpFinish.finishAllowance data.prepared.tag data.prepared.length cacheLimit valueLimit+1 := by
  have price:=NodeRlpFinish.call_cost source node heap frame lower upper inputEnd cacheLimit valueLimit data (some none) finishArguments
    (finish_arguments source frame node topCell nodeCell)
  rw [pop_shape]
  have total:=ClockCost.sequence_current source (.call (some (none,none)) (ofString "_node_rlp_finish") finishArguments)
    (.assign .local (ofString "top") parentExpression) _ 0 price (ClockCost.assign source.code (ofString "top") parentExpression)
  simpa only [Nat.add_zero] using total

/-- A genuine normal pop finishes the same current node, retains its full
physical result and reads the actual saved high-frame parent pointer. -/
theorem pop_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (node heap frame parent : BitVec 64) (index : Nat)
    (lower upper inputEnd cacheLimit valueLimit : Nat) (data : NodeRlpFinish.Entry source node heap frame lower upper inputEnd cacheLimit valueLimit)
    (header : Header source frame node parent index)
    (topCell : source.locals.lookup (ofString "top")=some (.val (.word frame)))
    (nodeCell : source.locals.lookup (ofString "nd")=some (.val (.word node)))
    (normal : evaluateHOLFiniteState source popBranch=(none,post)) :
    ∃ bytes,bytes≤2952790016 ∧ NodeRlpFinish.FinishOutput source post node heap bytes
      (NodeRlpFinish.WithBand (NodeRlpFinish.SerializerQueries data.graph inputEnd) upper heap.toNat) ∧
      post.locals.lookup (ofString "top")=some (.val (.word parent)) ∧
      (∀ key : MlS,key≠ofString "top" → post.locals.lookup key=source.locals.lookup key) := by
  rw [pop_shape] at normal
  obtain ⟨finished,finishRun,assignRun⟩:=sequence_none source post _ _ normal
  obtain ⟨locals,bytes,bound,output⟩:=NodeRlpFinish.call_normal_band source finished node heap frame lower upper inputEnd cacheLimit valueLimit data finishArguments
    (finish_arguments source frame node topCell nodeCell) finishRun
  have finishedTop : finished.locals.lookup (ofString "top")=some (.val (.word frame)):=by rw [locals]; exact topCell
  have mapped : finished.memaddrs frame:=by
    rw [output.runtime.1]
    simpa only [byteAddress,BitVec.add_zero] using AllocatedBytes.word_mapped source frame 48 0 data.environment.domain header.arena (by decide) header.aligned (by decide)
  have stored : finished.memory frame=.word parent:=(output.scratch frame header.scratch).trans header.parentStored
  have read : eval finished parentExpression=some (.val (.word parent)):=by
    simp [parentExpression,eval,evalHOLExact,evalListHOLExact,toExact,localVar,finishedTop,valueIsWord,valueWord,wordOpHOL,wordOp,
      memLoadHOLExact,isWfShapeExactHOL,mapped,stored]
  have endpoint:=assign_none finished post "top" parentExpression parent read assignRun
  have frameResult : LocalEffects.erase post=LocalEffects.erase finished:=by rw [endpoint]; rfl
  refine ⟨bytes,bound,output.reframe rfl frameResult,?_,?_⟩
  · rw [endpoint]
    exact bind_lookup_same _ _ _
  · intro key different
    rw [endpoint]
    simp [QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,Ne.symm different,locals]


theorem pop_safe (key : MlS) (different : key≠ofString "top") : LocalPrefix key popBranch := by
  rw [pop_shape]
  exact .seq (.call none (ofString "_node_rlp_finish") finishArguments (by intro name impossible; cases impossible))
    (.assign _ _ different)

/-- The actual normal pop removes precisely the active linked frame,
retains every older header/preparation, derives its true next heap and
strictly decreases the same finite traversal rank. -/
theorem pop_stack_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (heap cursor floor : BitVec 64)
    (lower upper inputEnd cacheLimit valueLimit : Nat) (current : StackFrame) (rest : List StackFrame)
    (data : NodeRlpFinish.Entry source current.node heap current.address lower upper inputEnd cacheLimit valueLimit)
    (headers : HeaderStack source cursor.toNat (current::rest))
    (prepared : PreparedStack source data.graph.valid upper heap.toNat (current::rest))
    (topCell : source.locals.lookup (ofString "top")=some (.val (.word current.address)))
    (nodeCell : source.locals.lookup (ofString "nd")=some (.val (.word current.node)))
    (normal : evaluateHOLFiniteState source popBranch=(none,post)) :
    ∃ bytes nextHeap,NodeRlpFinish.FinishOutput source post current.node heap bytes
        (NodeRlpFinish.WithBand (NodeRlpFinish.SerializerQueries data.graph inputEnd) upper heap.toNat) ∧
      post.globals.lookup (ofString "heap_ptr")=some (.val (.word nextHeap)) ∧ nextHeap.toNat≤2952790016 ∧ nextHeap.toNat%8=0 ∧
      heap.toNat≤nextHeap.toNat ∧ HeaderStack post cursor.toNat rest ∧ PreparedStack post data.graph.valid upper nextHeap.toNat rest ∧
      post.locals.lookup (ofString "top")=some (.val (.word (stackTop rest))) ∧
      rank (recordsLeft cursor.toNat floor.toNat) rest.length<rank (recordsLeft cursor.toNat floor.toNat) (current::rest).length := by
  have originalHeaders:=headers
  cases headers with
  | cons frame rest above header tail=>
    obtain ⟨bytes,_bound,output,topAfter,_locals⟩:=pop_normal source post current.node heap current.address (stackTop rest) current.index lower upper inputEnd cacheLimit valueLimit
      data header topCell nodeCell normal
    obtain ⟨nextHeap,heapCell,heapUpper,heapAligned,heapFloor⟩:=output.heap
    have grows : heap.toNat≤nextHeap.toNat:=by omega
    have retainedHeaders:=tail.of_memory (target:=post) (fun query afterFrame=>output.scratch query (by have high:=header.scratch; omega))
    have retainedPrepared:=(PreparedStack.after_finish data originalHeaders prepared output).tail
    exact ⟨bytes,nextHeap,output,heapCell,heapUpper,heapAligned,grows,retainedHeaders.weaken (by omega),
      retainedPrepared.weaken (Nat.le_refl _) grows,topAfter,by simpa only [List.length_cons] using pop_rank (recordsLeft cursor.toNat floor.toNat) rest.length⟩

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
#print axioms InitECandidate.Solver.Mpt.NodeRlpFill.scan_child_read
#print axioms InitECandidate.Solver.Mpt.NodeRlpFill.scan_body_child_normal
#print axioms InitECandidate.Solver.Mpt.NodeRlpFill.scan_member_normal
#print axioms InitECandidate.Solver.Mpt.NodeRlpFill.branch_scope_member_normal
#print axioms InitECandidate.Solver.Mpt.NodeRlpFill.scan_call_positive
#print axioms InitECandidate.Solver.Mpt.NodeRlpFill.selection_shapes
#print axioms InitECandidate.Solver.Mpt.NodeRlpFill.extension_choice_cost
#print axioms InitECandidate.Solver.Mpt.NodeRlpFill.select_child_cost
#print axioms InitECandidate.Solver.Mpt.NodeRlpFill.scan_body_positive
#print axioms InitECandidate.Solver.Mpt.NodeRlpFill.scan_descent_normal
#print axioms InitECandidate.Solver.Mpt.NodeRlpFill.branch_scope_descent_normal
#print axioms InitECandidate.Solver.Mpt.NodeRlpFill.push_shape
#print axioms InitECandidate.Solver.Mpt.NodeRlpFill.push_prefix_cost
#print axioms InitECandidate.Solver.Mpt.NodeRlpFill.push_trace
#print axioms InitECandidate.Solver.Mpt.NodeRlpFill.allocation_reached_named
#print axioms InitECandidate.Solver.Mpt.NodeRlpFill.record_store
#print axioms InitECandidate.Solver.Mpt.NodeRlpFill.push_from_execution
#print axioms InitECandidate.Solver.Mpt.NodeRlpFill.Header.of_after_memory
#print axioms InitECandidate.Solver.Mpt.NodeRlpFill.HeaderStack.weaken
#print axioms InitECandidate.Solver.Mpt.NodeRlpFill.HeaderStack.of_memory
#print axioms InitECandidate.Solver.Mpt.NodeRlpFill.push_live
#print axioms InitECandidate.Solver.Mpt.NodeRlpFill.push_prefix_stack
#print axioms InitECandidate.Solver.Mpt.NodeRlpFill.push_begin_entry
#print axioms InitECandidate.Solver.Mpt.NodeRlpFill.push_normal_trace
#print axioms InitECandidate.Solver.Mpt.NodeRlpFill.push_normal
#print axioms InitECandidate.Solver.Mpt.NodeRlpFill.push_allowance
#print axioms InitECandidate.Solver.Mpt.NodeRlpFill.push_cost

#print axioms InitECandidate.Solver.Mpt.NodeRlpFill.HeaderStack.arenas

#print axioms InitECandidate.Solver.Mpt.NodeRlpFill.PreparedStack.nil

#print axioms InitECandidate.Solver.Mpt.NodeRlpFill.PreparedStack.cons

#print axioms InitECandidate.Solver.Mpt.NodeRlpFill.PreparedStack.tail

#print axioms InitECandidate.Solver.Mpt.NodeRlpFill.PreparedStack.weaken

#print axioms InitECandidate.Solver.Mpt.NodeRlpFill.PreparedStack.of_frame

#print axioms InitECandidate.Solver.Mpt.NodeRlpFill.HeaderStack.after_finish

#print axioms InitECandidate.Solver.Mpt.NodeRlpFill.PreparedStack.after_finish

#print axioms InitECandidate.Solver.Mpt.NodeRlpFill.pop_shape

#print axioms InitECandidate.Solver.Mpt.NodeRlpFill.finish_arguments

#print axioms InitECandidate.Solver.Mpt.NodeRlpFill.pop_cost

#print axioms InitECandidate.Solver.Mpt.NodeRlpFill.pop_normal

#print axioms InitECandidate.Solver.Mpt.NodeRlpFill.pop_safe

#print axioms InitECandidate.Solver.Mpt.NodeRlpFill.pop_stack_normal

#print axioms InitECandidate.Solver.Mpt.NodeRlpFill.HeaderStack.frame_before

#print axioms InitECandidate.Solver.Mpt.NodeRlpFill.PreparedStack.of_bands

#print axioms InitECandidate.Solver.Mpt.NodeRlpFill.push_prepared_normal

#print axioms InitECandidate.Solver.Mpt.NodeRlpFill.prepare_shape

#print axioms InitECandidate.Solver.Mpt.NodeRlpFill.prepare_normal

#print axioms InitECandidate.Solver.Mpt.NodeRlpFill.PreparedStack.with_index

#print axioms InitECandidate.Solver.Mpt.NodeRlpFill.PreparedStack.after_index_frame

#print axioms InitECandidate.Solver.Mpt.NodeRlpFill.branch_scope_prepared

#print axioms InitECandidate.Solver.Mpt.NodeRlpFill.extension_choice_normal

#print axioms InitECandidate.Solver.Mpt.NodeRlpFill.select_child_normal

#print axioms InitECandidate.Solver.Mpt.NodeRlpFill.select_child_prepared
