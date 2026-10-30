import InitECandidate.Solver.Input.CurrentVerify.TransactionData

namespace InitECandidate.Solver.Input.CurrentVerify.ExecuteBlock
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

/-- The unchanged block executor and its actual two opening declarations. -/
def body : ProgHOL 64:=match Guest.Software.guestFn_execute_block with | .function fn=>progToHOL fn.body | _=>.skip
def afterPayload : ProgHOL 64:=match body with | .dec _ _ _ rest=>rest | _=>.skip
def afterCount : ProgHOL 64:=match afterPayload with | .dec _ _ _ rest=>rest | _=>.skip
def payloadExpression : ExpHOL 64:=.load .one (Scalar.plus (localVar "si") 0)
def countExpression : ExpHOL 64:=.load .one (Scalar.plus (localVar "pl") 40)
def arguments : List (ExpHOL 64):=[localVar "si",localVar "hdr"]
def declarationEntry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (record : BitVec 64) :=
  QueryBranch.bind (QueryBranch.bind source "pl" record) "ntx" 0#64

theorem shapes : body=.dec (ofString "pl") .one payloadExpression afterPayload ∧
    afterPayload=.dec (ofString "ntx") .one countExpression afterCount := by
  simp only [body,afterPayload,afterCount,payloadExpression,countExpression,
    Guest.Software.guestFn_execute_block,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,
    Option.map_some,Option.map_none,Scalar.plus,localVar]
  trivial

theorem original_code (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "execute_block")=some ([(ofString "si",.one),(ofString "hdr",.one)],body,.one) := by
  have found:=OriginalCode.indexed code installed 802
    (GasBudget.OriginalCodeEnvironment.originalEntry Guest.Software.guestFn_execute_block) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,body,
    Guest.Software.guestFn_execute_block,paramToHOL,shapeToHOL,List.map_cons,List.map_nil] using found

/-- Both loads use the already decoded and mapped records. In particular the
transaction count is the actual payload word at offset40, with value zero. -/
theorem declaration_reads {input : Guest.InputBlob} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord : BitVec 64} {boundary : Nat}
    (data : Data input source pointer si record gasWord boundary)
    (zero : VarList.decodedCount input (62+Guest.GasLimit.le32 input 566)
      (Guest.GasLimit.le32 input 570-Guest.GasLimit.le32 input 566)=0) :
    eval source payloadExpression=some (.val (.word record)) ∧
      eval (QueryBranch.bind source "pl" record) countExpression=some (.val (.word 0#64)) := by
  have siRead : eval source (localVar "si")=some (.val (.word si)):=by
    simp [eval,evalHOLExact,toExact,localVar,data.siLocal]
  have payloadRead : eval source payloadExpression=some (.val (.word record)):=
    Witness.load_word_read source _ (si+0#64) record (Scalar.plus_read source (localVar "si") si 0 siRead)
      (AllocatedBytes.word_mapped source si 96 0 data.arena.domain data.siArena (by decide) data.siAligned (by decide))
      (by simpa using data.payloadCell)
  obtain ⟨array,length,start,size,payload,arrayBefore,countBound,byteBound⟩:=data.payload
  have countZero : VarList.decodedCount input start size=0:=by
    rw [payload.transactions.startEq,payload.transactions.sizeEq]
    exact zero
  let next:=QueryBranch.bind source "pl" record
  have plRead : eval next (localVar "pl")=some (.val (.word record)):=by
    simp [eval,evalHOLExact,toExact,localVar,next,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
  refine ⟨payloadRead,?_⟩
  exact Witness.load_word_read next _ (record+40#64) 0#64 (Scalar.plus_read next (localVar "pl") record 40 plRead)
    (AllocatedBytes.word_mapped next record 136 40 data.arena.domain data.recordArena (by decide) data.recordAligned (by decide))
    (by have cell:=payload.transactions.count; rw [countZero] at cell; exact cell)

/-- Every actual executor outcome reaches its initialization after the two
real loads. These declarations spend no source ticks and restore their own
caller bindings on all outcomes, including exceptions and short clocks. -/
theorem declarations_trace {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord : BitVec 64} {boundary : Nat}
    (data : Data input source pointer si record gasWord boundary)
    (zero : VarList.decodedCount input (62+Guest.GasLimit.le32 input 566)
      (Guest.GasLimit.le32 input 570-Guest.GasLimit.le32 input 566)=0)
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source body=(outcome,post)) :
    ∃ inner,evaluateHOLFiniteState (declarationEntry source record) afterCount=(outcome,inner) ∧
      post=QueryBranch.restore source "pl" (QueryBranch.restore (QueryBranch.bind source "pl" record) "ntx" inner) := by
  obtain ⟨payloadRead,countRead⟩:=declaration_reads data zero
  rw [shapes.1] at run
  obtain ⟨middle,continued,endpoint⟩:=ScalarScope.declare_trace source post "pl" payloadExpression record afterPayload outcome payloadRead run
  rw [shapes.2] at continued
  obtain ⟨inner,rest,restored⟩:=ScalarScope.declare_trace (QueryBranch.bind source "pl" record) middle "ntx" countExpression 0#64 afterCount outcome countRead continued
  exact ⟨inner,rest,by rw [endpoint,restored]⟩

/-- Main's same actual SI/HDR arguments determine the original executor ABI.
After its real opening declarations, full earlier physical facts and the
owned block environment survive with the genuine zero transaction local. -/
theorem call_entry {input : Guest.InputBlob} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord header be : BitVec 64} {boundary encoded : Nat}
    (ready : RunAttempt.BlockEnvBuffer input source pointer si record gasWord header be boundary encoded) :
    ∃ callee,evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=
      some [.val (.word si),.val (.word header)] ∧
      lookupCodeHOLFinite source.code.lookup (ofString "execute_block") [.val (.word si),.val (.word header)]=some (body,callee,.one) ∧
      Data input (callEntryStateHOLFinite source callee) pointer si record gasWord boundary ∧
      RunAttempt.BlockEnvBuffer input (declarationEntry (callEntryStateHOLFinite source callee) record)
        pointer si record gasWord header be boundary encoded ∧
      (declarationEntry (callEntryStateHOLFinite source callee) record).locals.lookup (ofString "ntx")=some (.val (.word 0#64)) := by
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=
      some [.val (.word si),.val (.word header)]:=by
    simp [arguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,ready.physical.data.siLocal,ready.physical.headerCell]
  obtain ⟨callee,called,siCell,hdrCell⟩:=word_pair_environment source.code.lookup (ofString "execute_block") (ofString "si") (ofString "hdr")
    body .one si header (by decide) (original_code source.code ready.physical.data.arena.code)
  have data:=ready.physical.data.of_frame (post:=callEntryStateHOLFinite source callee) rfl siCell
  let current:=declarationEntry (callEntryStateHOLFinite source callee) record
  have currentSi : current.locals.lookup (ofString "si")=some (.val (.word si)):=
    (bind_lookup_other _ "ntx" "si" 0#64 (by decide)).trans ((bind_lookup_other _ "pl" "si" record (by decide)).trans siCell)
  have currentHdr : current.locals.lookup (ofString "hdr")=some (.val (.word header)):=
    (bind_lookup_other _ "ntx" "hdr" 0#64 (by decide)).trans ((bind_lookup_other _ "pl" "hdr" record (by decide)).trans hdrCell)
  have currentPl : current.locals.lookup (ofString "pl")=some (.val (.word record)):=
    (bind_lookup_other _ "ntx" "pl" 0#64 (by decide)).trans (bind_lookup_same _ _ _)
  have physical:=ready.physical.of_frame (target:=current) rfl currentSi currentHdr currentPl
  exact ⟨callee,args,called,data,⟨physical,ready.cell,ready.arena,ready.aligned,ready.before,ready.heapAfter⟩,bind_lookup_same _ _ _⟩

end InitECandidate.Solver.Input.CurrentVerify.ExecuteBlock

#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecuteBlock.shapes
#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecuteBlock.original_code
#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecuteBlock.declaration_reads
#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecuteBlock.declarations_trace
#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecuteBlock.call_entry

namespace InitECandidate.Solver.Input.CurrentVerify.ExecuteBlock
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

def outputAllocation : ProgHOL 64:=.call (some (some (.global,ofString "bo"),none)) (ofString "alloc") [.const 88#64]
def outputZero : ProgHOL 64:=.call (some (none,none)) (ofString "memzero") [.var .global (ofString "bo"),.const 88#64]
def outputActions : List CallPrefix.Action:=[.command outputAllocation,.command outputZero]
def beforeArrays : ProgHOL 64:=(CallPrefix.cutAt 2 afterCount).2

theorem output_shape : afterCount=CallPrefix.program outputActions beforeArrays := by
  simp only [afterCount,afterPayload,body,Guest.Software.guestFn_execute_block,progToHOL,expToHOL,shapeToHOL,
    List.map_cons,List.map_nil,Option.map_some,Option.map_none,CallPrefix.cutAt,CallPrefix.cut,↓reduceIte,
    beforeArrays,CallPrefix.program,outputActions,outputAllocation,outputZero]

/-- The real first output allocation/zero pair costs at most115source ticks
on every state with the original code. No successful read/store is assumed. -/
theorem output_cost (code) (installed : OriginalCode.Installed code) :
    ClockCost.Bound code (CallPrefix.program outputActions .skip) 115 := by
  have allocation : ClockCost.Bound code outputAllocation 2:=by
    intro source sameCode
    have sourceInstalled : OriginalCode.Installed source.code:=by rw [sameCode]; exact installed
    obtain ⟨callee,called,amount⟩:=PersistentAlloc.environment source.code.lookup 88#64 (PersistentAlloc.original_code source.code sourceInstalled)
    exact ClockCost.assigned_current source (some (.global,ofString "bo")) (ofString "alloc") [.const 88#64] (PersistentAlloc.values 88#64)
      PersistentAlloc.body callee .one 1 rfl called (PersistentAlloc.body_price source.code sourceInstalled (callEntryStateHOLFinite source callee) rfl)
  have zero : ClockCost.Bound code outputZero 113:=by
    intro source sameCode
    have sourceInstalled : OriginalCode.Installed source.code:=by rw [sameCode]; exact installed
    exact ZeroAny.dynamic_call_cost source (.var .global (ofString "bo")) 88 (by decide) (Zero.original_code source.code sourceInstalled)
  exact ClockCost.sequence code _ _ 2 113 allocation
    (ClockCost.sequence code _ _ 113 0 zero (ClockCost.skip code))

end InitECandidate.Solver.Input.CurrentVerify.ExecuteBlock

#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecuteBlock.output_shape
#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecuteBlock.output_cost

namespace InitECandidate.Solver.Input.CurrentVerify.ExecuteBlock
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch RunAttempt PayloadHeaderEntry

/-- Original output ownership, together with the same earlier environment
and actual zero transaction local. Future helper success is not a premise. -/
structure OutputBuffer (input : Guest.InputBlob) (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer si record gasWord header be bo : BitVec 64) (boundary encoded : Nat) : Prop where
  environment : BlockEnvBuffer input source pointer si record gasWord header be boundary encoded
  cell : source.globals.lookup (ofString "bo")=some (.val (.word bo))
  arena : AllocatedBytes.Arena bo 88
  aligned : bo.toNat%8=0
  before : be.toNat+120≤bo.toNat
  heapAfter : NormalHeapEffects.AtLeast (bo.toNat+88) source
  count : source.locals.lookup (ofString "ntx")=some (.val (.word 0#64))

/-- The actual normal allocation supplies its own room and new heap. In
particular it follows the earlier120byte block environment in memory. -/
theorem output_allocated {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord header be : BitVec 64} {boundary encoded : Nat}
    (ready : BlockEnvBuffer input source pointer si record gasWord header be boundary encoded)
    (count : source.locals.lookup (ofString "ntx")=some (.val (.word 0#64)))
    (normal : evaluateHOLFiniteState source outputAllocation=(none,post)) :
    ∃ bo,OutputBuffer input post pointer si record gasWord header be bo boundary encoded := by
  obtain ⟨heap,cell,lower,bounded,aligned⟩:=ready.heapAfter
  obtain ⟨room,funded,endpoint⟩:=PersistentAlloc.global_call_normal_any source post "bo" heap 88#64 [.const 88#64] rfl
    (PersistentAlloc.original_code source.code ready.physical.data.arena.code)
    (Trap.original_code source.code ready.physical.data.arena.code) cell bounded normal
  let raw:=PersistentAlloc.post {source with clock:=source.clock-1} heap 88#64
  let current:=putGlobal raw "bo" heap
  have guards:=PersistentAlloc.guards heap 88#64 room
  have rawGlobals : HeapGlobals source raw:=by
    intro key different
    simp [raw,PersistentAlloc.post,HolFiniteMapExact.update,FUPDATE,different,Ne.symm different]
  have rawHeap : raw.globals.lookup (ofString "heap_ptr")=some (.val (.word (PersistentAlloc.rounded heap 88#64))):=by
    simp [raw,PersistentAlloc.post,HolFiniteMapExact.update,FUPDATE]
  have beforeHeader : (headerFrontier header).toNat+16≤heap.toNat:=by have earlier:=ready.before; omega
  have rawAfter : NormalHeapEffects.AtLeast ((headerFrontier header).toNat+16) raw:=
    ⟨PersistentAlloc.rounded heap 88#64,rawHeap,by have advanced:=guards.2.2.1; omega,guards.2.2.2.1,guards.2.2.2.2⟩
  have rawPhysical:=ready.physical.of_older_output (target:=raw) heap beforeHeader rfl rfl rfl rawGlobals rawAfter
    ready.physical.data.siLocal ready.physical.headerCell ready.physical.payloadCell (by intros; rfl)
  have currentPhysical : AfterHeader input current pointer si record gasWord header boundary encoded:=by
    apply rawPhysical.with_globals current.globals
    intro key member
    have different : key≠ofString "bo":=by
      intro equal
      rw [equal] at member
      have absent : ofString "bo"∉dataGlobals:=by decide
      exact absent member
    exact putGlobal.lookup_other raw "bo" heap key different
  have currentHeap : current.globals.lookup (ofString "heap_ptr")=some (.val (.word (PersistentAlloc.rounded heap 88#64))):=
    (putGlobal.lookup_other raw "bo" heap (ofString "heap_ptr") (by decide)).trans rawHeap
  have environmentAfter : NormalHeapEffects.AtLeast (be.toNat+120) current:=
    ⟨PersistentAlloc.rounded heap 88#64,currentHeap,by have advanced:=guards.2.2.1; omega,guards.2.2.2.1,guards.2.2.2.2⟩
  have outputAfter : NormalHeapEffects.AtLeast (heap.toNat+88) current:=
    ⟨PersistentAlloc.rounded heap 88#64,currentHeap,by have advanced:=guards.2.2.1; change heap.toNat+88≤_ at advanced; exact advanced,
      guards.2.2.2.1,guards.2.2.2.2⟩
  have beCell : current.globals.lookup (ofString "be")=some (.val (.word be)):=
    (putGlobal.lookup_other raw "bo" heap (ofString "be") (by decide)).trans ((rawGlobals _ (by decide)).trans ready.cell)
  have heapLower : 2701131776≤heap.toNat:=by have before:=ready.arena.lower; omega
  rw [endpoint]
  exact ⟨heap,⟨currentPhysical,beCell,ready.arena,ready.aligned,ready.before,environmentAfter⟩,
    putGlobal.lookup_same raw "bo" heap,⟨heapLower,by change heap.toNat+88≤2952790016 at room; omega⟩,
    aligned,lower,outputAfter,count⟩

/-- Actual zeroing protects the entire preceding input/header/environment
and preserves the real heap and zero transaction local. -/
theorem output_zeroed {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord header be bo : BitVec 64} {boundary encoded : Nat}
    (ready : OutputBuffer input source pointer si record gasWord header be bo boundary encoded)
    (normal : evaluateHOLFiniteState source outputZero=(none,post)) :
    OutputBuffer input post pointer si record gasWord header be bo boundary encoded := by
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) [.var .global (ofString "bo"),.const 88#64]=
      some (Zero.values bo 88):=by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,ready.cell,Zero.values]
  have globals (key : MlS) : post.globals.lookup key=source.globals.lookup key:=by
    have frame:=CurrentKeccak.Hash.zero_call_globals key source.code ready.environment.physical.data.arena.code
      [.var .global (ofString "bo"),.const 88#64] source rfl
    change GlobalEffects.erase key (evaluateHOLFiniteState source outputZero).2=GlobalEffects.erase key source at frame
    rw [normal] at frame
    exact congrArg Prod.snd frame
  have memory (query : BitVec 64) (before : query.toNat<bo.toNat) : post.memory query=source.memory query:=by
    have away:=CopyGeneral.Away.after_floor bo query 88 bo.toNat ready.aligned (Nat.le_refl _) (by have room:=ready.arena.upper; omega) before
    exact (CurrentKeccak.Hash.zero_frame source post 2701132160#64 2701132360#64 bo query 88 ready.environment.physical.data.keccak _ args ready.arena ready.aligned
      (by decide) (fun offset inside=>(away offset inside).1) normal).memory
  have heaps (floor : Nat) (old : NormalHeapEffects.AtLeast floor source) : NormalHeapEffects.AtLeast floor post:=by
    obtain ⟨heap,cell,lower,bounded,aligned⟩:=old
    exact ⟨heap,(globals _).trans cell,lower,bounded,aligned⟩
  have saved (name : String) : post.locals.lookup (ofString name)=source.locals.lookup (ofString name):=
    CallNormal.ignored_lookup source post (ofString name) (ofString "memzero") [.var .global (ofString "bo"),.const 88#64] normal
  have runtime:=evaluation_fields source post outputZero none normal
  have beforeHeader : (headerFrontier header).toNat+16≤bo.toNat:=by
    have earlier:=ready.environment.before
    have later:=ready.before
    omega
  have physical:=ready.environment.physical.of_older_output bo beforeHeader runtime.1 runtime.2.1 runtime.2.2.2
    (fun key different=>globals key) (heaps _ ready.environment.physical.heapAfter)
    ((saved "si").trans ready.environment.physical.data.siLocal) ((saved "hdr").trans ready.environment.physical.headerCell)
    ((saved "pl").trans ready.environment.physical.payloadCell) memory
  exact ⟨⟨physical,(globals _).trans ready.environment.cell,ready.environment.arena,ready.environment.aligned,
    ready.environment.before,heaps _ ready.environment.heapAfter⟩,
    (globals _).trans ready.cell,ready.arena,ready.aligned,ready.before,heaps _ ready.heapAfter,(saved "ntx").trans ready.count⟩

/-- Only real normal prefix executions supply the output ownership frame. -/
theorem output_reached {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord header be : BitVec 64} {boundary encoded : Nat}
    (ready : BlockEnvBuffer input source pointer si record gasWord header be boundary encoded)
    (count : source.locals.lookup (ofString "ntx")=some (.val (.word 0#64)))
    (execution : CallPrefix.Execution source outputActions post) :
    ∃ bo,OutputBuffer input post pointer si record gasWord header be bo boundary encoded := by
  cases execution with
  | step first next=>
    cases first with
    | command allocated command allocationRun=>
      obtain ⟨bo,allocatedReady⟩:=output_allocated ready count allocationRun
      have last:=next.singleton
      cases last with
      | command zeroed command zeroRun=>exact ⟨bo,output_zeroed allocatedReady zeroRun⟩

/-- Every actual initialization outcome either stops within115source ticks
or reaches the original array allocations with all physical facts retained. -/
theorem output_trace {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord header be : BitVec 64} {boundary encoded : Nat}
    (ready : BlockEnvBuffer input source pointer si record gasWord header be boundary encoded)
    (count : source.locals.lookup (ofString "ntx")=some (.val (.word 0#64)))
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source afterCount=(outcome,post)) :
    source.clock-post.clock≤115 ∨ ∃ current inner bo,OutputBuffer input current pointer si record gasWord header be bo boundary encoded ∧
      current.clock≤source.clock ∧ source.clock-current.clock≤115 ∧ CallPrefix.ScopeFrame post inner ∧
      evaluateHOLFiniteState current beforeArrays=(outcome,inner) := by
  rw [output_shape] at run
  rcases CallPrefix.priced_frame_trace source post outputActions beforeArrays 115
    (output_cost source.code ready.physical.data.arena.code source rfl) outcome run with stopped|reached
  · exact Or.inl stopped.1
  · obtain ⟨current,inner,execution,forward,price,endpoint,continued⟩:=reached
    obtain ⟨bo,currentReady⟩:=output_reached ready count execution
    exact Or.inr ⟨current,inner,bo,currentReady,forward,price,endpoint,continued⟩

end InitECandidate.Solver.Input.CurrentVerify.ExecuteBlock

#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecuteBlock.output_allocated
#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecuteBlock.output_zeroed
#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecuteBlock.output_reached
#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecuteBlock.output_trace

namespace InitECandidate.Solver.Input.CurrentVerify.ExecuteBlock
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

/-- Complete original executor prefix through the two actual declarations,
output allocation and zero. No fresh restriction is placed on its input. -/
theorem body_output_trace {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord header be : BitVec 64} {boundary encoded : Nat}
    (data : Data input source pointer si record gasWord boundary)
    (ready : RunAttempt.BlockEnvBuffer input (declarationEntry source record) pointer si record gasWord header be boundary encoded)
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source body=(outcome,post)) :
    source.clock-post.clock≤115 ∨ ∃ current inner bo,OutputBuffer input current pointer si record gasWord header be bo boundary encoded ∧
      current.clock≤source.clock ∧ source.clock-current.clock≤115 ∧ post.clock=inner.clock ∧
      evaluateHOLFiniteState current beforeArrays=(outcome,inner) := by
  obtain ⟨target,continued,endpoint⟩:=declarations_trace data ready.physical.transactionsZero outcome run
  have clock : post.clock=target.clock:=by rw [endpoint]; rfl
  have entryClock : (declarationEntry source record).clock=source.clock:=rfl
  rcases output_trace ready (bind_lookup_same _ _ _) outcome continued with stopped|reached
  · exact Or.inl (by rw [clock]; simpa only [entryClock] using stopped)
  · obtain ⟨current,inner,bo,physical,forward,price,scope,rest⟩:=reached
    exact Or.inr ⟨current,inner,bo,physical,by simpa only [entryClock] using forward,
      by simpa only [entryClock] using price,clock.trans scope.clock,rest⟩

end InitECandidate.Solver.Input.CurrentVerify.ExecuteBlock

#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecuteBlock.body_output_trace

namespace InitECandidate.Solver.Input.CurrentVerify.ExecuteBlock
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

/-- All-outcome body pricing also covers global-result assignments, with
arbitrary actual argument expressions and failed ABI lookup included. -/
theorem assigned_body_cost (code) (destination : Option (VarKind×MlS)) (function : MlS) (arguments : List (ExpHOL 64))
    (formals : List (MlS×ShapeHOL)) (program : ProgHOL 64) (shape : ShapeHOL) (price : Nat)
    (entry : code.lookup function=some (formals,program,shape)) (priced : ClockCost.Bound code program price) :
    ClockCost.Bound code (.call (some (destination,none)) function arguments) (price+1) := by
  intro source sameCode
  cases args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments with
  | none=>rw [evaluateHOLFiniteState_call,args]; simp
  | some values=>
    cases called : lookupCodeHOLFinite source.code.lookup function values with
    | none=>rw [evaluateHOLFiniteState_call]; simp only [args,called]; omega
    | some triple=>
      obtain ⟨actual,callee,actualShape⟩:=triple
      have sourceEntry : source.code.lookup function=some (formals,program,shape):=by rw [sameCode]; exact entry
      have bodyEq:=LocalEffects.lookup_body source.code function formals program shape sourceEntry values actual callee actualShape called
      exact ClockCost.assigned_current source destination function arguments values actual callee actualShape price args called
        (by rw [bodyEq]; exact priced _ sameCode)

def listBody : ProgHOL 64:=match Guest.Software.guestFn_lst_new with | .function fn=>progToHOL fn.body | _=>.skip
def listFormals : List (MlS×ShapeHOL):=[(ofString "esz",.one),(ofString "cap",.one)]

theorem list_code (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "lst_new")=some (listFormals,listBody,.one) := by
  have found:=OriginalCode.indexed code installed 369
    (GasBudget.OriginalCodeEnvironment.originalEntry Guest.Software.guestFn_lst_new) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,listBody,listFormals,
    Guest.Software.guestFn_lst_new,paramToHOL,shapeToHOL,List.map_cons,List.map_nil] using found

/-- The original persistent list has two allocation calls and three stores;
its all-outcome body bound needs no element-size/capacity or memory image. -/
theorem list_cost (code) (installed : OriginalCode.Installed code) : ClockCost.Bound code listBody 4 := by
  simp only [listBody,Guest.Software.guestFn_lst_new,progToHOL,shapeToHOL]
  apply PersistentAlloc.scoped_price (tailPrice:=2) code installed
  apply PersistentAlloc.scoped_price (tailPrice:=0) code installed
  apply ClockCost.sequence (firstPrice:=0) (secondPrice:=0)
  · exact ClockCost.store code _ _
  · apply ClockCost.sequence (firstPrice:=0) (secondPrice:=0)
    · exact ClockCost.store code _ _
    · apply ClockCost.sequence (firstPrice:=0) (secondPrice:=0)
      · exact ClockCost.store code _ _
      · exact ClockCost.returned code _

def balBody : ProgHOL 64:=match Guest.Software.guestFn_bal_init with | .function fn=>progToHOL fn.body | _=>.skip

theorem bal_code (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "bal_init")=some ([],balBody,.one) := by
  have found:=OriginalCode.indexed code installed 372
    (GasBudget.OriginalCodeEnvironment.originalEntry Guest.Software.guestFn_bal_init) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,balBody,
    Guest.Software.guestFn_bal_init,paramToHOL,shapeToHOL,List.map_cons,List.map_nil] using found

/-- The unchanged BAL initializer uses three real Patricia constructors
(8body ticks each), one allocation, a scalar global assignment and return. -/
theorem bal_cost (code) (installed : OriginalCode.Installed code) : ClockCost.Bound code balBody 29 := by
  have table (destination : Option (VarKind×MlS)) (arguments : List (ExpHOL 64)) :
      ClockCost.Bound code (.call (some (destination,none)) (ofString "htab_new") arguments) 9:=
    assigned_body_cost code destination (ofString "htab_new") arguments CurrentTable.New.formals CurrentTable.New.body .one 8
      (CurrentTable.New.original_code code installed) (CurrentTable.New.body_cost code installed)
  have allocation (destination : Option (VarKind×MlS)) (arguments : List (ExpHOL 64)) :
      ClockCost.Bound code (.call (some (destination,none)) (ofString "alloc") arguments) 2:=
    assigned_body_cost code destination (ofString "alloc") arguments PersistentAlloc.formals PersistentAlloc.body .one 1
      (PersistentAlloc.original_code code installed) (PersistentAlloc.body_price code installed)
  simp only [balBody,Guest.Software.guestFn_bal_init,progToHOL]
  apply ClockCost.sequence (firstPrice:=9) (secondPrice:=20)
  · exact table _ _
  · apply ClockCost.sequence (firstPrice:=9) (secondPrice:=11)
    · exact table _ _
    · apply ClockCost.sequence (firstPrice:=9) (secondPrice:=2)
      · exact table _ _
      · apply ClockCost.sequence (firstPrice:=2) (secondPrice:=0)
        · exact allocation _ _
        · apply ClockCost.sequence (firstPrice:=0) (secondPrice:=0)
          · exact ClockCost.of_quiet code _ (QuietClock.assign_kind code .global _ _)
          · exact ClockCost.returned code _

end InitECandidate.Solver.Input.CurrentVerify.ExecuteBlock

#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecuteBlock.assigned_body_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecuteBlock.list_code
#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecuteBlock.list_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecuteBlock.bal_code
#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecuteBlock.bal_cost

namespace InitECandidate.Solver.Input.CurrentVerify.ExecuteBlock
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

/-- Cut the actual lexical prefix immediately before the first mandatory
system transaction, retaining its declarations rather than flattening them. -/
def initialActions : List CallPrefix.Action:=(CallPrefix.cutAt 17 body).1
def beforeFirstSystem : ProgHOL 64:=(CallPrefix.cutAt 17 body).2

theorem initial_shape : body=CallPrefix.program initialActions beforeFirstSystem:=
  (CallPrefix.reconstructAt 17 body).symm

theorem first_system_shape : ∃ tail,beforeFirstSystem=.seq
    (.call (some (none,none)) (ofString "process_unchecked_system_transaction")
      [.var .global (ofString "beacon_roots_address"),.load .one (Scalar.plus (localVar "si") 24),.const 32#64]) tail := by
  simp only [beforeFirstSystem,body,Guest.Software.guestFn_execute_block,progToHOL,CallPrefix.cutAt,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,Scalar.plus,localVar]
  exact ⟨_,rfl⟩

/-- All original arrays, empty lists, output zeroing and BAL initialization
are included. Failed expressions, allocation guards and stores are covered;
no count, memory image, room or future normal return is assumed. -/
theorem initial_cost (code) (installed : OriginalCode.Installed code) :
    ClockCost.Bound code (CallPrefix.program initialActions .skip) 161 := by
  have allocation (destination : Option (VarKind×MlS)) (arguments : List (ExpHOL 64)) :
      ClockCost.Bound code (.call (some (destination,none)) (ofString "alloc") arguments) 2:=
    assigned_body_cost code destination (ofString "alloc") arguments PersistentAlloc.formals PersistentAlloc.body .one 1
      (PersistentAlloc.original_code code installed) (PersistentAlloc.body_price code installed)
  have zero : ClockCost.Bound code outputZero 113:=by
    intro source sameCode
    have sourceInstalled : OriginalCode.Installed source.code:=by rw [sameCode]; exact installed
    exact ZeroAny.dynamic_call_cost source (.var .global (ofString "bo")) 88 (by decide) (Zero.original_code source.code sourceInstalled)
  have bal : ClockCost.Bound code (.call (some (none,none)) (ofString "bal_init") []) 30:=
    assigned_body_cost code none (ofString "bal_init") [] [] balBody .one 29 (bal_code code installed) (bal_cost code installed)
  simp only [initialActions,body,Guest.Software.guestFn_execute_block,progToHOL,CallPrefix.cutAt,CallPrefix.program,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none]
  apply ClockCost.declared
  apply ClockCost.declared
  apply ClockCost.sequence (firstPrice:=2) (secondPrice:=159)
  · exact allocation _ _
  · apply ClockCost.sequence (firstPrice:=113) (secondPrice:=46)
    · exact zero
    · apply PersistentAlloc.scoped_price (tailPrice:=44) code installed
      apply ClockCost.sequence (firstPrice:=0) (secondPrice:=44)
      · exact ClockCost.store code _ _
      · apply PersistentAlloc.scoped_price (tailPrice:=42) code installed
        apply ClockCost.sequence (firstPrice:=0) (secondPrice:=42)
        · exact ClockCost.store code _ _
        · apply ClockCost.scoped_body (calleePrice:=4) (continuationPrice:=37) (formals:=listFormals) (body:=listBody)
            (returnShape:=.one) (entry:=list_code code installed) (calleeBound:=list_cost code installed)
          apply ClockCost.sequence (firstPrice:=0) (secondPrice:=37)
          · exact ClockCost.store code _ _
          · apply PersistentAlloc.scoped_price (tailPrice:=35) code installed
            apply ClockCost.sequence (firstPrice:=0) (secondPrice:=35)
            · exact ClockCost.store code _ _
            · apply ClockCost.scoped_body (calleePrice:=4) (continuationPrice:=30) (formals:=listFormals) (body:=listBody)
                (returnShape:=.one) (entry:=list_code code installed) (calleeBound:=list_cost code installed)
              apply ClockCost.sequence (firstPrice:=0) (secondPrice:=30)
              · exact ClockCost.store code _ _
              · apply ClockCost.sequence (firstPrice:=0) (secondPrice:=30)
                · exact ClockCost.store code _ _
                · apply ClockCost.sequence (firstPrice:=30) (secondPrice:=0)
                  · exact bal
                  · exact ClockCost.sequence code .skip .skip 0 0 (ClockCost.skip code) (ClockCost.skip code)

/-- Every actual executor outcome either stops during initialization within
161source ticks or reaches its genuine first system-transaction continuation.
The actual normal prefix is retained for subsequent state/table proofs. -/
theorem initial_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (installed : OriginalCode.Installed source.code) (outcome : Option (PanSemResultExact 64))
    (run : evaluateHOLFiniteState source body=(outcome,post)) :
    source.clock-post.clock≤161 ∨ ∃ current inner,CallPrefix.Execution source initialActions current ∧
      current.clock≤source.clock ∧ source.clock-current.clock≤161 ∧ CallPrefix.ScopeFrame post inner ∧
      evaluateHOLFiniteState current beforeFirstSystem=(outcome,inner) := by
  rw [initial_shape] at run
  rcases CallPrefix.priced_frame_trace source post initialActions beforeFirstSystem 161
    (initial_cost source.code installed source rfl) outcome run with stopped|reached
  · exact Or.inl stopped.1
  · exact Or.inr reached

end InitECandidate.Solver.Input.CurrentVerify.ExecuteBlock

#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecuteBlock.initial_shape
#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecuteBlock.first_system_shape
#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecuteBlock.initial_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecuteBlock.initial_trace

namespace InitECandidate.Solver.Input.CurrentVerify.ExecuteBlock
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

def listAfterHeader : ProgHOL 64:=match listBody with | .decCall _ _ _ _ rest=>rest | _=>.skip
def listTail : ProgHOL 64:=match listAfterHeader with | .decCall _ _ _ _ rest=>rest | _=>.skip
def listAmount : ExpHOL 64:=.panop .mul [localVar "esz",localVar "cap"]
def listFields (buffer cap : BitVec 64) : List FieldStores.Field:=
  [⟨0,.saved "p" buffer⟩,⟨8,.literal 0#64⟩,⟨16,.saved "cap" cap⟩]
def listFirst (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64):=
  QueryBranch.bind (PersistentAlloc.post {source with clock:=source.clock-1} heap 24#64) "l" heap

theorem list_shapes (buffer cap : BitVec 64) :
    listBody=.decCall (ofString "l") .one (ofString "alloc") [.const 24#64] listAfterHeader ∧
    listAfterHeader=.decCall (ofString "p") .one (ofString "alloc") [listAmount] listTail ∧
    listTail=FieldStores.program "l" "unused" (listFields buffer cap) (.return (localVar "l")) := by
  simp only [listBody,listAfterHeader,listTail,listAmount,listFields,Guest.Software.guestFn_lst_new,
    progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,FieldStores.program,
    FieldStores.address,FieldStores.Value.expression,localVar,addConst]
  trivial

theorem list_writes_distinct (heap buffer cap : BitVec 64) :
    ((FieldStores.writes heap (listFields buffer cap)).map Prod.fst).Nodup := by
  change (([0#64,8#64,16#64] : List (BitVec 64)).map (fun offset=>heap+offset)).Nodup
  exact List.Nodup.map (fun left right same=>(BitVec.add_right_inj heap).mp same) (by decide)

/-- The three original header writes need only their actual locals and
owned header. Backing bytes are not read while the returned list is empty. -/
theorem list_stores_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap buffer cap : BitVec 64)
    (domain : source.memaddrs=InitE.ordinaryDomain) (arena : AllocatedBytes.Arena heap 24) (aligned : heap.toNat%8=0)
    (headerCell : source.locals.lookup (ofString "l")=some (.val (.word heap)))
    (bufferCell : source.locals.lookup (ofString "p")=some (.val (.word buffer)))
    (capCell : source.locals.lookup (ofString "cap")=some (.val (.word cap))) :
    evaluateHOLFiniteState source listTail=
      (some (.returned (.val (.word heap))),emptyLocalsHOLFinite
        {source with memory:=WordWrites.write source.memory (FieldStores.writes heap (listFields buffer cap))}) := by
  have reads : ∀ field∈listFields buffer cap,field.value.Ready source "unused" 0#64:=by
    intro field member
    simp only [listFields,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl
    · exact bufferCell
    · trivial
    · exact capCell
  have mapped : ∀ field∈listFields buffer cap,source.memaddrs (heap+BitVec.ofNat 64 field.offset):=by
    intro field member
    simp only [listFields,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl
    all_goals exact AllocatedBytes.word_mapped source heap 24 _ domain arena (by dsimp <;> decide) aligned (by dsimp <;> decide)
  have separate : ∀ reader∈listFields buffer cap,∀ writer∈listFields buffer cap,
      reader.value.Avoid 0#64 (heap+BitVec.ofNat 64 writer.offset):=by
    intro reader member writer other
    simp only [listFields,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl <;> trivial
  rw [(list_shapes buffer cap).2.2,FieldStores.execute source "l" "unused" heap 0#64 (listFields buffer cap)
    headerCell reads mapped separate (.return (localVar "l"))]
  simp [evaluateHOLFiniteState_return,localVar,evalHOLExact,toExact,headerCell,shapeOfHOLExact,sizeOfShapeWithContextHOL]

/-- A genuine normal persistent-list return derives both allocation rooms,
its empty header and a complete frame for all earlier memory. The element
size/capacity may be arbitrary words; their actual wrapped product is used. -/
theorem list_body_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (heap size cap : BitVec 64)
    (sizeCell : source.locals.lookup (ofString "esz")=some (.val (.word size)))
    (capCell : source.locals.lookup (ofString "cap")=some (.val (.word cap)))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (heapBound : heap.toNat≤2952790016) (heapAligned : heap.toNat%8=0)
    (domain : source.memaddrs=InitE.ordinaryDomain) (installed : OriginalCode.Installed source.code)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source listBody=(some (.returned value),post)) :
    value=.val (.word heap) ∧ AllocatedBytes.Arena heap 24 ∧ PersistentNormalFrame source post heap ∧
      ∃ buffer,AllocatedBytes.Arena buffer (size*cap).toNat ∧ heap.toNat+24≤buffer.toNat ∧
        NormalHeapEffects.AtLeast (buffer.toNat+(size*cap).toNat) post ∧ post.memory heap=.word buffer ∧ post.memory (heap+8#64)=.word 0#64 ∧ post.memory (heap+16#64)=.word cap := by
  rw [(list_shapes 0#64 cap).1] at normal
  rcases CurrentAlloc.scoped_classified source post "l" [.const 24#64] listAfterHeader heap 24#64 rfl installed heapCell heapBound _ normal with stopped|reached
  · exact (stopped.2 value rfl).elim
  · obtain ⟨funded,headerRoom,middle,continued,endpoint⟩:=reached
    let first:=listFirst source heap
    let buffer:=PersistentAlloc.rounded heap 24#64
    let amount:=size*cap
    change evaluateHOLFiniteState first listAfterHeader=(some (.returned value),middle) at continued
    have headerGuards:=PersistentAlloc.guards heap 24#64 headerRoom
    have headerArena : AllocatedBytes.Arena heap 24:=⟨heapArena.lower,by change heap.toNat+24≤2952790016 at headerRoom; omega⟩
    have bufferCell : first.globals.lookup (ofString "heap_ptr")=some (.val (.word buffer)):=by
      simp [first,listFirst,QueryBranch.bind,setVarHOLFinite,PersistentAlloc.post,HolFiniteMapExact.update,FUPDATE,buffer]
    have firstSize : first.locals.lookup (ofString "esz")=some (.val (.word size)):=
      (bind_lookup_other _ "l" "esz" heap (by decide)).trans sizeCell
    have firstCap : first.locals.lookup (ofString "cap")=some (.val (.word cap)):=
      (bind_lookup_other _ "l" "cap" heap (by decide)).trans capCell
    have amountRead : evalListHOLFinite first (h:=fun query=>Classical.propDecidable (first.memaddrs query)) [listAmount]=some (PersistentAlloc.values amount):=by
      simp [listAmount,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,firstSize,firstCap,
        PersistentAlloc.values,amount,valueIsWord,valueWord,panOpHOL]
    rw [(list_shapes buffer cap).2.1] at continued
    rcases CurrentAlloc.scoped_classified first middle "p" [listAmount] listTail buffer amount amountRead installed bufferCell
      headerGuards.2.2.2.1 _ continued with stopped|reached
    · exact (stopped.2 value rfl).elim
    · obtain ⟨secondFunded,bufferRoom,target,tailRun,secondEndpoint⟩:=reached
      let ready:=QueryBranch.bind (PersistentAlloc.post {first with clock:=first.clock-1} buffer amount) "p" buffer
      change evaluateHOLFiniteState ready listTail=(some (.returned value),target) at tailRun
      have listCell : ready.locals.lookup (ofString "l")=some (.val (.word heap)):=
        (bind_lookup_other _ "p" "l" buffer (by decide)).trans (bind_lookup_same _ _ _)
      have actualBuffer : ready.locals.lookup (ofString "p")=some (.val (.word buffer)):=bind_lookup_same _ _ _
      have actualCap : ready.locals.lookup (ofString "cap")=some (.val (.word cap)):=
        (bind_lookup_other _ "p" "cap" buffer (by decide)).trans firstCap
      rw [list_stores_execute ready heap buffer cap domain headerArena heapAligned listCell actualBuffer actualCap] at tailRun
      have answer : value=.val (.word heap):=by
        simpa only [Option.some.injEq,PanSemResultExact.returned.injEq] using (congrArg Prod.fst tailRun).symm
      have targetEq:=congrArg Prod.snd tailRun
      dsimp only at targetEq
      let writes:=FieldStores.writes heap (listFields buffer cap)
      have memoryEq : post.memory=WordWrites.write source.memory writes:=by
        rw [endpoint,secondEndpoint,←targetEq]
        rfl
      have bufferGuards:=PersistentAlloc.guards buffer amount bufferRoom
      have beforeBuffer : heap.toNat+24≤buffer.toNat:=headerGuards.2.2.1
      have backingArena : AllocatedBytes.Arena buffer amount.toNat:=
        ⟨by have lower:=heapArena.lower; omega,by omega⟩
      let next:=PersistentAlloc.rounded buffer amount
      have nextCell : post.globals.lookup (ofString "heap_ptr")=some (.val (.word next)):=by
        rw [endpoint,secondEndpoint,←targetEq]
        simp [ready,PersistentAlloc.post,QueryBranch.bind,QueryBranch.restore,emptyLocalsHOLFinite,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,next]
      have nextLower : 2701131776≤next.toNat:=by
        have lower:=heapArena.lower
        have advanced:=bufferGuards.2.2.1
        change buffer.toNat+amount.toNat≤next.toNat at advanced
        omega
      have frame : PersistentNormalFrame source post heap:=by
        refine ⟨⟨next,nextCell,⟨nextLower,by have bound:=bufferGuards.2.2.2.1; change next.toNat≤2952790016 at bound; omega⟩,
          bufferGuards.2.2.2.1,bufferGuards.2.2.2.2,by have advanced:=bufferGuards.2.2.1; change buffer.toNat+amount.toNat≤next.toNat at advanced; omega⟩,?_,?_,?_⟩
        · rw [endpoint,secondEndpoint,←targetEq]
          rfl
        · intro key other
          rw [endpoint,secondEndpoint,←targetEq]
          simp [ready,first,listFirst,PersistentAlloc.post,QueryBranch.bind,QueryBranch.restore,emptyLocalsHOLFinite,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,other,Ne.symm other]
        · intro query before
          rw [memoryEq]
          apply WordWrites.write_away
          intro member
          have addresses : writes.map Prod.fst=([0#64,8#64,16#64] : List (BitVec 64)).map (fun offset=>heap+offset):=rfl
          rw [addresses] at member
          obtain ⟨offset,member,same⟩:=List.mem_map.mp member
          have small : offset.toNat<24:=by
            simp only [List.mem_cons,List.not_mem_nil,or_false] at member
            rcases member with rfl|rfl|rfl <;> decide
          have number : (heap+offset).toNat=heap.toNat+offset.toNat:=BitVec.toNat_add_of_lt (by have room:=headerArena.upper; omega)
          have equal:=congrArg BitVec.toNat same
          rw [number] at equal
          omega
      have fields (entry : BitVec 64×BitVec 64) (member : entry∈writes) : post.memory entry.1=.word entry.2:=by
        rw [memoryEq]
        exact WordWrites.write_unique source.memory writes entry (list_writes_distinct heap buffer cap) member
      exact ⟨answer,headerArena,frame,buffer,backingArena,beforeBuffer,
        ⟨next,nextCell,bufferGuards.2.2.1,bufferGuards.2.2.2.1,bufferGuards.2.2.2.2⟩,
        by simpa using fields (heap+0#64,buffer) (by simp [writes,FieldStores.writes,listFields,FieldStores.Value.word]),
        fields (heap+8#64,0#64) (by simp [writes,FieldStores.writes,listFields,FieldStores.Value.word]),
        fields (heap+16#64,cap) (by simp [writes,FieldStores.writes,listFields,FieldStores.Value.word])⟩

end InitECandidate.Solver.Input.CurrentVerify.ExecuteBlock

#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecuteBlock.list_shapes
#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecuteBlock.list_writes_distinct
#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecuteBlock.list_stores_execute
#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecuteBlock.list_body_normal

namespace InitECandidate.Solver.Input.CurrentVerify.ExecuteBlock
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

/-- A real reached original list call installs its returned header in the
caller, retains every other caller binding and supplies the actual empty
header/backing ownership and the complete persistent memory frame. -/
theorem list_scoped_reached (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String)
    (heap size cap : BitVec 64) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=
      some [.val (.word size),.val (.word cap)])
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (heapBound : heap.toNat≤2952790016) (heapAligned : heap.toNat%8=0)
    (arena : CurrentStartup.ArenaState source)
    (reached : CallPrefix.Reaches source (.scoped (ofString name) .one (ofString "lst_new") arguments) post) :
    post.locals.lookup (ofString name)=some (.val (.word heap)) ∧
      (∀ key : MlS,key≠ofString name→post.locals.lookup key=source.locals.lookup key) ∧
      AllocatedBytes.Arena heap 24 ∧ PersistentNormalFrame source post heap ∧
      ∃ buffer,AllocatedBytes.Arena buffer (size*cap).toNat ∧ heap.toNat+24≤buffer.toNat ∧
        NormalHeapEffects.AtLeast (buffer.toNat+(size*cap).toNat) post ∧ post.memory heap=.word buffer ∧ post.memory (heap+8#64)=.word 0#64 ∧ post.memory (heap+16#64)=.word cap := by
  obtain ⟨callee,called,sizeCell,capCell⟩:=word_pair_environment source.code.lookup (ofString "lst_new") (ofString "esz") (ofString "cap")
    listBody .one size cap (by decide) (list_code source.code arena.code)
  obtain ⟨child,value,normal,endpoint⟩:=reached.scoped_known (ofString name) .one (ofString "lst_new") arguments _ listBody callee .one args called
  obtain ⟨answer,headerArena,frame,buffer,backingArena,before,extent,first,count,capacity⟩:=list_body_normal (callEntryStateHOLFinite source callee)
    child heap size cap sizeCell capCell heapCell heapArena heapBound heapAligned arena.domain arena.code value normal
  have callerFrame : PersistentNormalFrame source post heap:=frame.of_erase _ _ source post heap rfl (by rw [endpoint]; rfl)
  have memory : post.memory=child.memory:=by rw [endpoint]; rfl
  have callerExtent : NormalHeapEffects.AtLeast (buffer.toNat+(size*cap).toNat) post:=by
    obtain ⟨next,cell,lower,bounded,aligned⟩:=extent
    exact ⟨next,by rw [endpoint]; exact cell,lower,bounded,aligned⟩
  refine ⟨?_,?_,headerArena,callerFrame,buffer,backingArena,before,callerExtent,?_,?_,?_⟩
  · rw [endpoint,answer]
    simp [setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
  · intro key other
    rw [endpoint]
    simp [setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,other,Ne.symm other]
  · rw [memory]; exact first
  · rw [memory]; exact count
  · rw [memory]; exact capacity

/-- Any genuine persistent helper frame protects all earlier executor
inputs, header and block environment. The supplied caller bindings are
obtained from that helper's own ordinary/scoped return interface. -/
theorem OutputBuffer.of_persistent {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord header be bo heap : BitVec 64} {boundary encoded : Nat}
    (ready : OutputBuffer input source pointer si record gasWord header be bo boundary encoded)
    (beforeHeap : bo.toNat+88≤heap.toNat) (frame : PersistentNormalFrame source post heap)
    (siCell : post.locals.lookup (ofString "si")=some (.val (.word si)))
    (headerCell : post.locals.lookup (ofString "hdr")=some (.val (.word header)))
    (payloadCell : post.locals.lookup (ofString "pl")=some (.val (.word record)))
    (countCell : post.locals.lookup (ofString "ntx")=some (.val (.word 0#64))) :
    OutputBuffer input post pointer si record gasWord header be bo boundary encoded := by
  obtain ⟨next,nextCell,nextArena,nextBound,nextAligned,advanced⟩:=frame.nextHeap
  have afterHeader : NormalHeapEffects.AtLeast ((PayloadHeaderEntry.headerFrontier header).toNat+16) post:=
    ⟨next,nextCell,by have first:=ready.environment.before; have second:=ready.before; omega,nextBound,nextAligned⟩
  have oldBefore : (PayloadHeaderEntry.headerFrontier header).toNat+16≤heap.toNat:=by
    have first:=ready.environment.before
    have second:=ready.before
    omega
  have domain : post.memaddrs=source.memaddrs:=MemoryMetadata.domain (target:={post with globals:=source.globals}) frame.metadata
  have endian : post.be=source.be:=MemoryMetadata.endian (target:={post with globals:=source.globals}) frame.metadata
  have code : post.code=source.code:=MemoryMetadata.code (target:={post with globals:=source.globals}) frame.metadata
  have physical:=ready.environment.physical.of_older_output (target:=post) heap oldBefore
    domain endian code
    frame.globals afterHeader siCell headerCell payloadCell frame.memory
  have environmentAfter : NormalHeapEffects.AtLeast (be.toNat+120) post:=
    ⟨next,nextCell,by have earlier:=ready.before; omega,nextBound,nextAligned⟩
  have outputAfter : NormalHeapEffects.AtLeast (bo.toNat+88) post:=⟨next,nextCell,by omega,nextBound,nextAligned⟩
  exact ⟨⟨physical,(frame.globals _ (by decide)).trans ready.environment.cell,ready.environment.arena,ready.environment.aligned,
    ready.environment.before,environmentAfter⟩,
    (frame.globals _ (by decide)).trans ready.cell,ready.arena,ready.aligned,ready.before,outputAfter,countCell⟩

end InitECandidate.Solver.Input.CurrentVerify.ExecuteBlock

#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecuteBlock.list_scoped_reached
#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecuteBlock.OutputBuffer.of_persistent

namespace InitECandidate.Solver.Input.CurrentVerify.ExecuteBlock
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

/-- Real scoped array allocation supplies its owned extent and next heap,
without requiring room or a successful future call at the source. -/
theorem allocation_scoped_reached (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String)
    (heap amount : BitVec 64) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=
      some (PersistentAlloc.values amount))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (heapBound : heap.toNat≤2952790016)
    (installed : OriginalCode.Installed source.code)
    (reached : CallPrefix.Reaches source (.scoped (ofString name) .one (ofString "alloc") arguments) post) :
    post.locals.lookup (ofString name)=some (.val (.word heap)) ∧
      (∀ key : MlS,key≠ofString name→post.locals.lookup key=source.locals.lookup key) ∧
      AllocatedBytes.Arena heap amount.toNat ∧ PersistentNormalFrame source post heap ∧
      NormalHeapEffects.AtLeast (heap.toNat+amount.toNat) post := by
  obtain ⟨room,endpoint⟩:=reached.alloc_target (ofString name) arguments heap amount installed args heapCell heapBound
  have guards:=PersistentAlloc.guards heap amount room
  have rawFrame:=PersistentAlloc.post_persistent_frame {source with clock:=source.clock-1} heap amount heapArena room
  have frame : PersistentNormalFrame source post heap:=rawFrame.of_erase _ _ source post heap rfl (by rw [endpoint]; rfl)
  refine ⟨?_,?_,⟨heapArena.lower,by omega⟩,frame,PersistentAlloc.rounded heap amount,?_,guards.2.2.1,guards.2.2.2.1,guards.2.2.2.2⟩
  · rw [endpoint]
    simp [setVarHOLFinite,PersistentAlloc.post,HolFiniteMapExact.update,FUPDATE]
  · intro key other
    rw [endpoint]
    simp [setVarHOLFinite,PersistentAlloc.post,HolFiniteMapExact.update,FUPDATE,other,Ne.symm other]
  · rw [endpoint]
    simp [setVarHOLFinite,PersistentAlloc.post,HolFiniteMapExact.update,FUPDATE]

end InitECandidate.Solver.Input.CurrentVerify.ExecuteBlock

#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecuteBlock.allocation_scoped_reached

namespace InitECandidate.Solver.Input.CurrentVerify.ExecuteBlock
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

def outputAddress (offset : Nat) : ExpHOL 64:=Scalar.plus (.var .global (ofString "bo")) offset

theorem OutputBuffer.with_memory {input : Guest.InputBlob} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord header be bo : BitVec 64} {boundary encoded : Nat}
    (ready : OutputBuffer input source pointer si record gasWord header be bo boundary encoded)
    (memory : BitVec 64→HolWordLab 64)
    (earlier : ∀ query : BitVec 64,query.toNat<bo.toNat→memory query=source.memory query) :
    OutputBuffer input {source with memory:=memory} pointer si record gasWord header be bo boundary encoded := by
  have beforeHeader : (PayloadHeaderEntry.headerFrontier header).toNat+16≤bo.toNat:=by
    have first:=ready.environment.before
    have second:=ready.before
    omega
  have physical:=ready.environment.physical.of_older_output (target:={source with memory:=memory}) bo beforeHeader
    rfl rfl rfl (by intro key different; rfl) ready.environment.physical.heapAfter
    ready.environment.physical.data.siLocal ready.environment.physical.headerCell ready.environment.physical.payloadCell earlier
  exact ⟨⟨physical,ready.environment.cell,ready.environment.arena,ready.environment.aligned,ready.environment.before,ready.environment.heapAfter⟩,
    ready.cell,ready.arena,ready.aligned,ready.before,ready.heapAfter,ready.count⟩

/-- A real scalar output store has exactly one written word. This retains
older input and protects newly allocated list headers at other addresses. -/
theorem output_word_store {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord header be bo : BitVec 64} {boundary encoded : Nat}
    (ready : OutputBuffer input source pointer si record gasWord header be bo boundary encoded)
    (offset : Nat) (expression : ExpHOL 64) (value : BitVec 64) (inside : offset<88) (aligned : offset%8=0)
    (read : eval source expression=some (.val (.word value)))
    (normal : evaluateHOLFiniteState source (.store (outputAddress offset) expression)=(none,post)) :
    OutputBuffer input post pointer si record gasWord header be bo boundary encoded ∧ post.locals=source.locals ∧ post.globals=source.globals ∧
      post.memory (bo+BitVec.ofNat 64 offset)=.word value ∧
      ∀ query : BitVec 64,query≠bo+BitVec.ofNat 64 offset→post.memory query=source.memory query := by
  have boRead : eval source (.var .global (ofString "bo"))=some (.val (.word bo)):=by
    simp [eval,evalHOLExact,toExact,ready.cell]
  have destination:=Scalar.plus_read source (.var .global (ofString "bo")) bo offset boRead
  have mapped:=AllocatedBytes.word_mapped source bo 88 offset ready.environment.physical.data.arena.domain ready.arena inside ready.aligned aligned
  have actual:=StoreWord.execute source (outputAddress offset) expression (bo+BitVec.ofNat 64 offset) value destination read mapped
  have endpoint : post={source with memory:=StoreWord.put source.memory (bo+BitVec.ofNat 64 offset) value}:=
    congrArg Prod.snd (normal.symm.trans actual)
  have earlier (query : BitVec 64) (before : query.toNat<bo.toNat) :
      StoreWord.put source.memory (bo+BitVec.ofNat 64 offset) value query=source.memory query:=by
    have number : (bo+BitVec.ofNat 64 offset).toNat=bo.toNat+offset:=
      byteAddress_toNat bo offset (by have upper:=ready.arena.upper; omega)
    have different : query≠bo+BitVec.ofNat 64 offset:=by
      intro same
      have equal:=congrArg BitVec.toNat same
      rw [number] at equal
      omega
    simp [StoreWord.put,different]
  rw [endpoint]
  refine ⟨ready.with_memory _ earlier,rfl,rfl,?_,?_⟩
  · simp [StoreWord.put]
  · intro query different
    simp [StoreWord.put,different]

/-- Instantiate actual array returns in this executor while retaining its
physical inputs and zero count. Only the four preserved caller names are
excluded from the new binding. Actual room/extent follow from the call. -/
theorem output_allocation_reached {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord header be bo : BitVec 64} {boundary encoded : Nat}
    (ready : OutputBuffer input source pointer si record gasWord header be bo boundary encoded)
    (name : String) (amount : BitVec 64) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=some (PersistentAlloc.values amount))
    (distinct : ofString "si"≠ofString name ∧ ofString "hdr"≠ofString name ∧ ofString "pl"≠ofString name ∧ ofString "ntx"≠ofString name)
    (reached : CallPrefix.Reaches source (.scoped (ofString name) .one (ofString "alloc") arguments) post) :
    ∃ heap,source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)) ∧
      OutputBuffer input post pointer si record gasWord header be bo boundary encoded ∧
      post.locals.lookup (ofString name)=some (.val (.word heap)) ∧
      (∀ key : MlS,key≠ofString name→post.locals.lookup key=source.locals.lookup key) ∧
      AllocatedBytes.Arena heap amount.toNat ∧ heap.toNat%8=0 ∧ bo.toNat+88≤heap.toNat ∧
      PersistentNormalFrame source post heap ∧ NormalHeapEffects.AtLeast (heap.toNat+amount.toNat) post := by
  obtain ⟨heap,cell,lower,bounded,aligned⟩:=ready.heapAfter
  have heapArena : AllocatedBytes.Arena heap 0:=⟨by have before:=ready.arena.lower; omega,by omega⟩
  obtain ⟨bound,other,owned,frame,extent⟩:=allocation_scoped_reached source post name heap amount arguments args cell heapArena bounded
    ready.environment.physical.data.arena.code reached
  have physical:=ready.of_persistent lower frame
    ((other _ distinct.1).trans ready.environment.physical.data.siLocal)
    ((other _ distinct.2.1).trans ready.environment.physical.headerCell)
    ((other _ distinct.2.2.1).trans ready.environment.physical.payloadCell)
    ((other _ distinct.2.2.2).trans ready.count)
  exact ⟨heap,cell,physical,bound,other,owned,aligned,lower,frame,extent⟩

def arrayAmount : ExpHOL 64:=.op .add [.panop .mul [localVar "ntx",.const 16#64],.const 16#64]

theorem array_amount_read (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (count : source.locals.lookup (ofString "ntx")=some (.val (.word 0#64))) :
    evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) [arrayAmount]=some (PersistentAlloc.values 16#64) := by
  simp [arrayAmount,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,count,PersistentAlloc.values,
    valueIsWord,valueWord,panOpHOL,wordOpHOL,wordOp]

end InitECandidate.Solver.Input.CurrentVerify.ExecuteBlock

#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecuteBlock.OutputBuffer.with_memory
#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecuteBlock.output_word_store
#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecuteBlock.output_allocation_reached
#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecuteBlock.array_amount_read

namespace InitECandidate.Solver.Input.CurrentVerify.ExecuteBlock
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

def arrayActions : List CallPrefix.Action:=
  [.scoped (ofString "txs") .one (ofString "alloc") [arrayAmount],
   .command (.store (outputAddress 24) (localVar "txs")),
   .scoped (ofString "rcs") .one (ofString "alloc") [arrayAmount],
   .command (.store (outputAddress 32) (localVar "rcs"))]
def beforeLogs : ProgHOL 64:=(CallPrefix.cutAt 4 beforeArrays).2

theorem arrays_shape : beforeArrays=CallPrefix.program arrayActions beforeLogs := by
  simp only [beforeArrays,afterCount,afterPayload,body,Guest.Software.guestFn_execute_block,progToHOL,
    expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,CallPrefix.cutAt,CallPrefix.program,
    arrayActions,beforeLogs,arrayAmount,outputAddress,Scalar.plus,localVar] <;> trivial

structure Arrays (input : Guest.InputBlob) (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer si record gasWord header be bo txs rcs : BitVec 64) (boundary encoded : Nat) : Prop where
  output : OutputBuffer input source pointer si record gasWord header be bo boundary encoded
  txsCell : source.locals.lookup (ofString "txs")=some (.val (.word txs))
  rcsCell : source.locals.lookup (ofString "rcs")=some (.val (.word rcs))
  txsArena : AllocatedBytes.Arena txs 16
  rcsArena : AllocatedBytes.Arena rcs 16
  txsAligned : txs.toNat%8=0
  rcsAligned : rcs.toNat%8=0
  beforeTxs : bo.toNat+88≤txs.toNat
  beforeRcs : txs.toNat+16≤rcs.toNat
  heapAfter : NormalHeapEffects.AtLeast (rcs.toNat+16) source
  txsField : source.memory (bo+24#64)=.word txs
  rcsField : source.memory (bo+32#64)=.word rcs

/-- The original two array callers/stores derive their own16byte extents
from the real zero count. The output's actual pointer cells, caller locals,
disjoint aligned arrays and frontier are retained from this same execution. -/
theorem arrays_reached {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord header be bo : BitVec 64} {boundary encoded : Nat}
    (ready : OutputBuffer input source pointer si record gasWord header be bo boundary encoded)
    (execution : CallPrefix.Execution source arrayActions post) :
    ∃ txs rcs,Arrays input post pointer si record gasWord header be bo txs rcs boundary encoded := by
  change CallPrefix.Execution source
    (.scoped (ofString "txs") .one (ofString "alloc") [arrayAmount]::
      .command (.store (outputAddress 24) (localVar "txs"))::
      .scoped (ofString "rcs") .one (ofString "alloc") [arrayAmount]::
      [.command (.store (outputAddress 32) (localVar "rcs"))]) post at execution
  obtain ⟨txAllocated,txAllocation,remaining⟩:=execution.head
  obtain ⟨txs,txIncoming,txReady,txCell,txOther,txArena,txAligned,txBefore,txFrame,txExtent⟩:=
    output_allocation_reached ready "txs" 16#64 [arrayAmount] (array_amount_read source ready.count) (by decide) txAllocation
  obtain ⟨txStored,txStore,afterTxStore⟩:=remaining.head
  have txStoreRun : evaluateHOLFiniteState txAllocated (.store (outputAddress 24) (localVar "txs"))=(none,txStored):=by
    cases txStore with | command _ _ run=>exact run
  have txRead : eval txAllocated (localVar "txs")=some (.val (.word txs)):=by
    simp [eval,evalHOLExact,toExact,localVar,txCell]
  obtain ⟨storedReady,txLocals,txGlobals,txField,txAway⟩:=output_word_store txReady 24 (localVar "txs") txs (by decide) (by decide) txRead txStoreRun
  have txStoredCell : txStored.locals.lookup (ofString "txs")=some (.val (.word txs)):=by rw [txLocals]; exact txCell
  have txStoredExtent : NormalHeapEffects.AtLeast (txs.toNat+16) txStored:=by
    obtain ⟨heap,cell,lower,bounded,aligned⟩:=txExtent
    exact ⟨heap,by rw [txGlobals]; exact cell,lower,bounded,aligned⟩
  obtain ⟨rcsAllocated,rcsAllocation,last⟩:=afterTxStore.head
  obtain ⟨rcs,rcsIncoming,rcsReady,rcsCell,rcsOther,rcsArena,rcsAligned,rcsBefore,rcsFrame,rcsExtent⟩:=
    output_allocation_reached storedReady "rcs" 16#64 [arrayAmount] (array_amount_read txStored storedReady.count) (by decide) rcsAllocation
  have arraysBefore : txs.toNat+16≤rcs.toNat:=by
    obtain ⟨heap,cell,lower,bounded,aligned⟩:=txStoredExtent
    have same : heap=rcs:=by
      have equal:=Option.some.inj (cell.symm.trans rcsIncoming)
      cases equal
      rfl
    simpa only [same] using lower
  have earlierField : (bo+24#64).toNat<rcs.toNat:=by
    have number : (bo+24#64).toNat=bo.toNat+24:=byteAddress_toNat bo 24 (by have bound:=ready.arena.upper; omega)
    rw [number]
    omega
  have keptTxField : rcsAllocated.memory (bo+24#64)=.word txs:=(rcsFrame.memory _ earlierField).trans txField
  have rcsStoreRun : evaluateHOLFiniteState rcsAllocated (.store (outputAddress 32) (localVar "rcs"))=(none,post):=by
    have reached:=last.singleton
    cases reached with | command _ _ run=>exact run
  have rcsRead : eval rcsAllocated (localVar "rcs")=some (.val (.word rcs)):=by
    simp [eval,evalHOLExact,toExact,localVar,rcsCell]
  obtain ⟨finalReady,rcsLocals,rcsGlobals,rcsField,rcsAway⟩:=output_word_store rcsReady 32 (localVar "rcs") rcs (by decide) (by decide) rcsRead rcsStoreRun
  have finalExtent : NormalHeapEffects.AtLeast (rcs.toNat+16) post:=by
    obtain ⟨heap,cell,lower,bounded,aligned⟩:=rcsExtent
    exact ⟨heap,by rw [rcsGlobals]; exact cell,lower,bounded,aligned⟩
  have different : bo+24#64≠bo+32#64:=by
    intro same
    have impossible : (24#64 : BitVec 64)=32#64:=(BitVec.add_right_inj bo).mp same
    exact (by decide : (24#64 : BitVec 64)≠32#64) impossible
  exact ⟨txs,rcs,finalReady,
    by rw [rcsLocals]; exact (rcsOther _ (by decide)).trans txStoredCell,
    by rw [rcsLocals]; exact rcsCell,
    txArena,rcsArena,txAligned,rcsAligned,txBefore,arraysBefore,finalExtent,
    (rcsAway _ different).trans keptTxField,rcsField⟩

theorem arrays_cost (code) (installed : OriginalCode.Installed code) :
    ClockCost.Bound code (CallPrefix.program arrayActions .skip) 4 := by
  simp only [arrayActions,CallPrefix.program]
  apply PersistentAlloc.scoped_price (tailPrice:=2) code installed
  apply ClockCost.sequence (firstPrice:=0) (secondPrice:=2)
  · exact ClockCost.store code _ _
  · apply PersistentAlloc.scoped_price (tailPrice:=0) code installed
    exact ClockCost.sequence code _ _ 0 0 (ClockCost.store code _ _) (ClockCost.skip code)

/-- Every actual array-prefix outcome is covered, including stopped helpers,
failed stores and short clocks. Reached outcomes supply the genuine arrays. -/
theorem arrays_trace {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord header be bo : BitVec 64} {boundary encoded : Nat}
    (ready : OutputBuffer input source pointer si record gasWord header be bo boundary encoded)
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source beforeArrays=(outcome,post)) :
    source.clock-post.clock≤4 ∨ ∃ current inner txs rcs,Arrays input current pointer si record gasWord header be bo txs rcs boundary encoded ∧
      current.clock≤source.clock ∧ source.clock-current.clock≤4 ∧ CallPrefix.ScopeFrame post inner ∧
      evaluateHOLFiniteState current beforeLogs=(outcome,inner) := by
  rw [arrays_shape] at run
  rcases CallPrefix.priced_frame_trace source post arrayActions beforeLogs 4
    (arrays_cost source.code ready.environment.physical.data.arena.code source rfl) outcome run with stopped|reached
  · exact Or.inl stopped.1
  · obtain ⟨current,inner,execution,forward,price,scope,rest⟩:=reached
    obtain ⟨txs,rcs,physical⟩:=arrays_reached ready execution
    exact Or.inr ⟨current,inner,txs,rcs,physical,forward,price,scope,rest⟩

theorem body_arrays_trace {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord header be : BitVec 64} {boundary encoded : Nat}
    (data : Data input source pointer si record gasWord boundary)
    (ready : RunAttempt.BlockEnvBuffer input (declarationEntry source record) pointer si record gasWord header be boundary encoded)
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source body=(outcome,post)) :
    source.clock-post.clock≤119 ∨ ∃ current inner bo txs rcs,Arrays input current pointer si record gasWord header be bo txs rcs boundary encoded ∧
      current.clock≤source.clock ∧ source.clock-current.clock≤119 ∧ post.clock=inner.clock ∧
      evaluateHOLFiniteState current beforeLogs=(outcome,inner) := by
  rcases body_output_trace data ready outcome run with stopped|reached
  · exact Or.inl (by omega)
  · obtain ⟨before,target,bo,output,forward,price,endpoint,continued⟩:=reached
    rcases arrays_trace output outcome continued with stopped|reached
    · exact Or.inl (by rw [endpoint]; omega)
    · obtain ⟨current,inner,txs,rcs,physical,arrayForward,arrayPrice,scope,rest⟩:=reached
      exact Or.inr ⟨current,inner,bo,txs,rcs,physical,by omega,by omega,endpoint.trans scope.clock,rest⟩

end InitECandidate.Solver.Input.CurrentVerify.ExecuteBlock

#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecuteBlock.arrays_shape
#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecuteBlock.arrays_reached
#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecuteBlock.arrays_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecuteBlock.arrays_trace
#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecuteBlock.body_arrays_trace

namespace InitECandidate.Solver.Input.CurrentVerify.ExecuteBlock
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

/-- Later real persistent helpers retain both earlier array pointer cells
and their owned extents. Their actual preserved caller bindings are explicit. -/
theorem Arrays.of_persistent {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord header be bo txs rcs heap : BitVec 64} {boundary encoded : Nat}
    (ready : Arrays input source pointer si record gasWord header be bo txs rcs boundary encoded)
    (beforeHeap : rcs.toNat+16≤heap.toNat) (frame : PersistentNormalFrame source post heap)
    (siCell : post.locals.lookup (ofString "si")=some (.val (.word si)))
    (headerCell : post.locals.lookup (ofString "hdr")=some (.val (.word header)))
    (payloadCell : post.locals.lookup (ofString "pl")=some (.val (.word record)))
    (countCell : post.locals.lookup (ofString "ntx")=some (.val (.word 0#64)))
    (txsCell : post.locals.lookup (ofString "txs")=some (.val (.word txs)))
    (rcsCell : post.locals.lookup (ofString "rcs")=some (.val (.word rcs))) :
    Arrays input post pointer si record gasWord header be bo txs rcs boundary encoded := by
  have outputBefore : bo.toNat+88≤heap.toNat:=by
    have first:=ready.beforeTxs
    have second:=ready.beforeRcs
    omega
  have output:=ready.output.of_persistent outputBefore frame siCell headerCell payloadCell countCell
  obtain ⟨next,nextCell,nextArena,nextBound,nextAligned,advanced⟩:=frame.nextHeap
  have afterRcs : NormalHeapEffects.AtLeast (rcs.toNat+16) post:=⟨next,nextCell,by omega,nextBound,nextAligned⟩
  have earlier (offset : Nat) (inside : offset<88) : (bo+BitVec.ofNat 64 offset).toNat<heap.toNat:=by
    have number:=byteAddress_toNat bo offset (by have upper:=ready.output.arena.upper; omega)
    change (bo+BitVec.ofNat 64 offset).toNat=bo.toNat+offset at number
    rw [number]
    omega
  exact ⟨output,txsCell,rcsCell,ready.txsArena,ready.rcsArena,ready.txsAligned,ready.rcsAligned,
    ready.beforeTxs,ready.beforeRcs,afterRcs,(frame.memory _ (earlier 24 (by decide))).trans ready.txsField,
    (frame.memory _ (earlier 32 (by decide))).trans ready.rcsField⟩

/-- Exact normal store observations lift the physical array contract.
Only the two actual protected pointer cells need memory transport. -/
theorem Arrays.of_store_frame {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord header be bo txs rcs : BitVec 64} {boundary encoded : Nat}
    (ready : Arrays input source pointer si record gasWord header be bo txs rcs boundary encoded)
    (output : OutputBuffer input post pointer si record gasWord header be bo boundary encoded)
    (locals : post.locals=source.locals) (globals : post.globals=source.globals)
    (txsMemory : post.memory (bo+24#64)=source.memory (bo+24#64))
    (rcsMemory : post.memory (bo+32#64)=source.memory (bo+32#64)) :
    Arrays input post pointer si record gasWord header be bo txs rcs boundary encoded := by
  obtain ⟨heap,cell,lower,bounded,aligned⟩:=ready.heapAfter
  exact ⟨output,by rw [locals]; exact ready.txsCell,by rw [locals]; exact ready.rcsCell,
    ready.txsArena,ready.rcsArena,ready.txsAligned,ready.rcsAligned,ready.beforeTxs,ready.beforeRcs,
    ⟨heap,by rw [globals]; exact cell,lower,bounded,aligned⟩,txsMemory.trans ready.txsField,rcsMemory.trans ready.rcsField⟩

def logActions : List CallPrefix.Action:=
  [.scoped (ofString "logs") .one (ofString "lst_new") [.const 8#64,.const 16#64],
   .command (.store (outputAddress 40) (localVar "logs"))]
def beforeRequests : ProgHOL 64:=(CallPrefix.cutAt 2 beforeLogs).2

theorem logs_shape : beforeLogs=CallPrefix.program logActions beforeRequests := by
  simp only [beforeLogs,beforeArrays,afterCount,afterPayload,body,Guest.Software.guestFn_execute_block,progToHOL,
    expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,CallPrefix.cutAt,CallPrefix.program,
    logActions,beforeRequests,outputAddress,Scalar.plus,localVar] <;> trivial

structure Logs (input : Guest.InputBlob) (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer si record gasWord header be bo txs rcs logs buffer : BitVec 64) (boundary encoded : Nat) : Prop where
  arrays : Arrays input source pointer si record gasWord header be bo txs rcs boundary encoded
  cell : source.locals.lookup (ofString "logs")=some (.val (.word logs))
  arena : AllocatedBytes.Arena logs 24
  aligned : logs.toNat%8=0
  backing : AllocatedBytes.Arena buffer 128
  before : rcs.toNat+16≤logs.toNat
  headerBefore : logs.toNat+24≤buffer.toNat
  heapAfter : NormalHeapEffects.AtLeast (buffer.toNat+128) source
  pointerField : source.memory logs=.word buffer
  countField : source.memory (logs+8#64)=.word 0#64
  capacityField : source.memory (logs+16#64)=.word 16#64
  outputField : source.memory (bo+40#64)=.word logs

/-- The original log constructor and output store retain the real empty
list, its backing extent and heap, all earlier arrays and input/header data. -/
theorem logs_reached {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord header be bo txs rcs : BitVec 64} {boundary encoded : Nat}
    (ready : Arrays input source pointer si record gasWord header be bo txs rcs boundary encoded)
    (execution : CallPrefix.Execution source logActions post) :
    ∃ logs buffer,Logs input post pointer si record gasWord header be bo txs rcs logs buffer boundary encoded := by
  change CallPrefix.Execution source
    (.scoped (ofString "logs") .one (ofString "lst_new") [.const 8#64,.const 16#64]::
      [.command (.store (outputAddress 40) (localVar "logs"))]) post at execution
  obtain ⟨allocated,allocation,last⟩:=execution.head
  obtain ⟨logs,heapCell,lower,bounded,aligned⟩:=ready.heapAfter
  have cursorArena : AllocatedBytes.Arena logs 0:=⟨by have low:=ready.rcsArena.lower; omega,by omega⟩
  obtain ⟨cell,other,headerArena,frame,buffer,backingArena,headerBefore,extent,pointerCell,countCell,capacityCell⟩:=
    list_scoped_reached source allocated "logs" logs 8#64 16#64 [.const 8#64,.const 16#64] rfl
      heapCell cursorArena bounded aligned ready.output.environment.physical.data.arena allocation
  change AllocatedBytes.Arena buffer 128 at backingArena
  change NormalHeapEffects.AtLeast (buffer.toNat+128) allocated at extent
  have arrays:=ready.of_persistent lower frame
    ((other _ (by decide)).trans ready.output.environment.physical.data.siLocal)
    ((other _ (by decide)).trans ready.output.environment.physical.headerCell)
    ((other _ (by decide)).trans ready.output.environment.physical.payloadCell)
    ((other _ (by decide)).trans ready.output.count)
    ((other _ (by decide)).trans ready.txsCell) ((other _ (by decide)).trans ready.rcsCell)
  have storeRun : evaluateHOLFiniteState allocated (.store (outputAddress 40) (localVar "logs"))=(none,post):=by
    have reached:=last.singleton
    cases reached with | command _ _ run=>exact run
  have read : eval allocated (localVar "logs")=some (.val (.word logs)):=by
    simp [eval,evalHOLExact,toExact,localVar,cell]
  obtain ⟨output,locals,globals,outputField,away⟩:=output_word_store arrays.output 40 (localVar "logs") logs (by decide) (by decide) read storeRun
  have different (offset : BitVec 64) (distinct : offset≠40#64) : bo+offset≠bo+40#64:=by
    intro same
    exact distinct ((BitVec.add_right_inj bo).mp same)
  have finalArrays:=arrays.of_store_frame output locals globals (away _ (different 24#64 (by decide))) (away _ (different 32#64 (by decide)))
  have headerAway (offset : Nat) (inside : offset<24) : logs+BitVec.ofNat 64 offset≠bo+40#64:=by
    have headerNumber : (logs+BitVec.ofNat 64 offset).toNat=logs.toNat+offset:=byteAddress_toNat logs offset (by have upper:=headerArena.upper; omega)
    have outputNumber : (bo+40#64).toNat=bo.toNat+40:=byteAddress_toNat bo 40 (by have upper:=ready.output.arena.upper; omega)
    have first:=ready.beforeTxs
    have second:=ready.beforeRcs
    intro same
    have equal:=congrArg BitVec.toNat same
    rw [headerNumber,outputNumber] at equal
    omega
  have finalExtent : NormalHeapEffects.AtLeast (buffer.toNat+128) post:=by
    obtain ⟨heap,cell,low,bound,align⟩:=extent
    exact ⟨heap,by rw [globals]; exact cell,low,bound,align⟩
  exact ⟨logs,buffer,finalArrays,by rw [locals]; exact cell,headerArena,aligned,backingArena,lower,headerBefore,finalExtent,
    (away _ (by simpa using headerAway 0 (by decide))).trans pointerCell,
    (away _ (headerAway 8 (by decide))).trans countCell,(away _ (headerAway 16 (by decide))).trans capacityCell,outputField⟩

end InitECandidate.Solver.Input.CurrentVerify.ExecuteBlock

#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecuteBlock.Arrays.of_persistent
#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecuteBlock.Arrays.of_store_frame
#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecuteBlock.logs_shape
#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecuteBlock.logs_reached

namespace InitECandidate.Solver.Input.CurrentVerify.ExecuteBlock
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

/-- Full list caller and its actual output store, with every failed/short
outcome included in the original five-tick caller allowance. -/
theorem logs_cost (code) (installed : OriginalCode.Installed code) :
    ClockCost.Bound code (CallPrefix.program logActions .skip) 5 := by
  simp only [logActions,CallPrefix.program]
  apply ClockCost.scoped_body (calleePrice:=4) (continuationPrice:=0) (formals:=listFormals) (body:=listBody)
    (returnShape:=.one) (entry:=list_code code installed) (calleeBound:=list_cost code installed)
  exact ClockCost.sequence code _ _ 0 0 (ClockCost.store code _ _) (ClockCost.skip code)

/-- The real log prefix either stops within five source ticks or supplies
its empty list and both earlier arrays at the original request allocation. -/
theorem logs_trace {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord header be bo txs rcs : BitVec 64} {boundary encoded : Nat}
    (ready : Arrays input source pointer si record gasWord header be bo txs rcs boundary encoded)
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source beforeLogs=(outcome,post)) :
    source.clock-post.clock≤5 ∨ ∃ current inner logs buffer,Logs input current pointer si record gasWord header be bo txs rcs logs buffer boundary encoded ∧
      current.clock≤source.clock ∧ source.clock-current.clock≤5 ∧ CallPrefix.ScopeFrame post inner ∧
      evaluateHOLFiniteState current beforeRequests=(outcome,inner) := by
  rw [logs_shape] at run
  rcases CallPrefix.priced_frame_trace source post logActions beforeRequests 5
    (logs_cost source.code ready.output.environment.physical.data.arena.code source rfl) outcome run with stopped|reached
  · exact Or.inl stopped.1
  · obtain ⟨current,inner,execution,forward,price,scope,rest⟩:=reached
    obtain ⟨logs,buffer,physical⟩:=logs_reached ready execution
    exact Or.inr ⟨current,inner,logs,buffer,physical,forward,price,scope,rest⟩

/-- Entire actual original executor prefix through log-list initialization,
retaining its empty header/backing and every earlier physical input fact. -/
theorem body_logs_trace {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord header be : BitVec 64} {boundary encoded : Nat}
    (data : Data input source pointer si record gasWord boundary)
    (ready : RunAttempt.BlockEnvBuffer input (declarationEntry source record) pointer si record gasWord header be boundary encoded)
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source body=(outcome,post)) :
    source.clock-post.clock≤124 ∨ ∃ current inner bo txs rcs logs buffer,
      Logs input current pointer si record gasWord header be bo txs rcs logs buffer boundary encoded ∧
      current.clock≤source.clock ∧ source.clock-current.clock≤124 ∧ post.clock=inner.clock ∧
      evaluateHOLFiniteState current beforeRequests=(outcome,inner) := by
  rcases body_arrays_trace data ready outcome run with stopped|reached
  · exact Or.inl (by omega)
  · obtain ⟨before,target,bo,txs,rcs,arrays,forward,price,endpoint,continued⟩:=reached
    rcases logs_trace arrays outcome continued with stopped|reached
    · exact Or.inl (by rw [endpoint]; omega)
    · obtain ⟨current,inner,logs,buffer,physical,logForward,logPrice,scope,rest⟩:=reached
      exact Or.inr ⟨current,inner,bo,txs,rcs,logs,buffer,physical,by omega,by omega,endpoint.trans scope.clock,rest⟩

end InitECandidate.Solver.Input.CurrentVerify.ExecuteBlock

#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecuteBlock.logs_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecuteBlock.logs_trace
#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecuteBlock.body_logs_trace

namespace InitECandidate.Solver.Input.CurrentVerify.ExecuteBlock
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

def keptLogNames : List MlS:=[ofString "si",ofString "hdr",ofString "pl",ofString "ntx",ofString "txs",ofString "rcs",ofString "logs"]

/-- Later real persistent calls retain the complete initial log image,
owned backing and earlier arrays, using their genuine caller-name frame. -/
theorem Logs.of_persistent {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord header be bo txs rcs logs buffer heap : BitVec 64} {boundary encoded : Nat}
    (ready : Logs input source pointer si record gasWord header be bo txs rcs logs buffer boundary encoded)
    (beforeHeap : buffer.toNat+128≤heap.toNat) (frame : PersistentNormalFrame source post heap)
    (locals : ∀ key∈keptLogNames,post.locals.lookup key=source.locals.lookup key) :
    Logs input post pointer si record gasWord header be bo txs rcs logs buffer boundary encoded := by
  have afterRcs : rcs.toNat+16≤heap.toNat:=by
    have first:=ready.before
    have second:=ready.headerBefore
    omega
  have arrays:=ready.arrays.of_persistent afterRcs frame
    ((locals _ (by simp [keptLogNames])).trans ready.arrays.output.environment.physical.data.siLocal)
    ((locals _ (by simp [keptLogNames])).trans ready.arrays.output.environment.physical.headerCell)
    ((locals _ (by simp [keptLogNames])).trans ready.arrays.output.environment.physical.payloadCell)
    ((locals _ (by simp [keptLogNames])).trans ready.arrays.output.count)
    ((locals _ (by simp [keptLogNames])).trans ready.arrays.txsCell)
    ((locals _ (by simp [keptLogNames])).trans ready.arrays.rcsCell)
  have earlier (offset : Nat) (inside : offset<24) : (logs+BitVec.ofNat 64 offset).toNat<heap.toNat:=by
    have number:=byteAddress_toNat logs offset (by have upper:=ready.arena.upper; omega)
    change (logs+BitVec.ofNat 64 offset).toNat=logs.toNat+offset at number
    rw [number]
    have before:=ready.headerBefore
    omega
  have outputBefore : (bo+40#64).toNat<heap.toNat:=by
    have number : (bo+40#64).toNat=bo.toNat+40:=byteAddress_toNat bo 40 (by have upper:=ready.arrays.output.arena.upper; omega)
    rw [number]
    have first:=ready.arrays.beforeTxs
    have second:=ready.arrays.beforeRcs
    omega
  obtain ⟨next,cell,arena,bound,aligned,advanced⟩:=frame.nextHeap
  exact ⟨arrays,(locals _ (by simp [keptLogNames])).trans ready.cell,ready.arena,ready.aligned,ready.backing,ready.before,ready.headerBefore,
    ⟨next,cell,by omega,bound,aligned⟩,
    by simpa using (frame.memory _ (earlier 0 (by decide))).trans (by simpa using ready.pointerField),
    (frame.memory _ (earlier 8 (by decide))).trans ready.countField,
    (frame.memory _ (earlier 16 (by decide))).trans ready.capacityField,(frame.memory _ outputBefore).trans ready.outputField⟩

/-- Words in an owned header beyond the output are distinct from every
scalar output destination, without wrapping across the ordinary domain. -/
theorem output_header_distinct (bo header : BitVec 64) (outputArena : AllocatedBytes.Arena bo 88)
    (headerArena : AllocatedBytes.Arena header 24) (before : bo.toNat+88≤header.toNat)
    (destination offset : Nat) (destinationInside : destination<88) (inside : offset<24) :
    header+BitVec.ofNat 64 offset≠bo+BitVec.ofNat 64 destination := by
  have headerNumber:=byteAddress_toNat header offset (by have upper:=headerArena.upper; omega)
  have outputNumber:=byteAddress_toNat bo destination (by have upper:=outputArena.upper; omega)
  change (header+BitVec.ofNat 64 offset).toNat=header.toNat+offset at headerNumber
  change (bo+BitVec.ofNat 64 destination).toNat=bo.toNat+destination at outputNumber
  intro same
  have equal:=congrArg BitVec.toNat same
  rw [headerNumber,outputNumber] at equal
  omega

/-- A real scalar output store at a different field retains the entire
empty-log contract. The exact store's memory frame supplies every read. -/
theorem Logs.of_output_store {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord header be bo txs rcs logs buffer : BitVec 64} {boundary encoded : Nat}
    (ready : Logs input source pointer si record gasWord header be bo txs rcs logs buffer boundary encoded)
    (offset : Nat) (inside : offset<88)
    (distinct : (24#64 : BitVec 64)≠BitVec.ofNat 64 offset ∧ (32#64 : BitVec 64)≠BitVec.ofNat 64 offset ∧ (40#64 : BitVec 64)≠BitVec.ofNat 64 offset)
    (output : OutputBuffer input post pointer si record gasWord header be bo boundary encoded)
    (locals : post.locals=source.locals) (globals : post.globals=source.globals)
    (memory : ∀ query : BitVec 64,query≠bo+BitVec.ofNat 64 offset→post.memory query=source.memory query) :
    Logs input post pointer si record gasWord header be bo txs rcs logs buffer boundary encoded := by
  have different (value : BitVec 64) (other : value≠BitVec.ofNat 64 offset) : bo+value≠bo+BitVec.ofNat 64 offset:=by
    intro same
    exact other ((BitVec.add_right_inj bo).mp same)
  have arrays:=ready.arrays.of_store_frame output locals globals (memory _ (different 24#64 distinct.1)) (memory _ (different 32#64 distinct.2.1))
  have headerBefore : bo.toNat+88≤logs.toNat:=by
    have first:=ready.arrays.beforeTxs
    have second:=ready.arrays.beforeRcs
    have third:=ready.before
    omega
  have away (field : Nat) (fieldInside : field<24) := output_header_distinct bo logs ready.arrays.output.arena ready.arena headerBefore offset field inside fieldInside
  obtain ⟨heap,cell,lower,bound,aligned⟩:=ready.heapAfter
  exact ⟨arrays,by rw [locals]; exact ready.cell,ready.arena,ready.aligned,ready.backing,ready.before,ready.headerBefore,
    ⟨heap,by rw [globals]; exact cell,lower,bound,aligned⟩,
    (memory _ (by simpa using away 0 (by decide))).trans ready.pointerField,
    (memory _ (away 8 (by decide))).trans ready.countField,(memory _ (away 16 (by decide))).trans ready.capacityField,
    (memory _ (different 40#64 distinct.2.2)).trans ready.outputField⟩

end InitECandidate.Solver.Input.CurrentVerify.ExecuteBlock

#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecuteBlock.Logs.of_persistent
#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecuteBlock.output_header_distinct
#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecuteBlock.Logs.of_output_store

namespace InitECandidate.Solver.Input.CurrentVerify.ExecuteBlock
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

def requestArguments : List (ExpHOL 64):=[.panop .mul [.const 8#64,.const 16#64]]
def requestActions : List CallPrefix.Action:=
  [.scoped (ofString "reqs") .one (ofString "alloc") requestArguments,
   .command (.store (outputAddress 56) (localVar "reqs"))]
def beforeReturnList : ProgHOL 64:=(CallPrefix.cutAt 2 beforeRequests).2

theorem requests_shape : beforeRequests=CallPrefix.program requestActions beforeReturnList := by
  simp only [beforeRequests,beforeLogs,beforeArrays,afterCount,afterPayload,body,Guest.Software.guestFn_execute_block,progToHOL,
    expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,CallPrefix.cutAt,CallPrefix.program,
    requestActions,requestArguments,beforeReturnList,outputAddress,Scalar.plus,localVar] <;> trivial

structure Requests (input : Guest.InputBlob) (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer si record gasWord header be bo txs rcs logs buffer reqs : BitVec 64) (boundary encoded : Nat) : Prop where
  logs : Logs input source pointer si record gasWord header be bo txs rcs logs buffer boundary encoded
  cell : source.locals.lookup (ofString "reqs")=some (.val (.word reqs))
  arena : AllocatedBytes.Arena reqs 128
  aligned : reqs.toNat%8=0
  before : buffer.toNat+128≤reqs.toNat
  heapAfter : NormalHeapEffects.AtLeast (reqs.toNat+128) source
  outputField : source.memory (bo+56#64)=.word reqs

/-- The original request allocation/store supplies its real128byte extent
and output pointer, beyond the entire existing log backing. All earlier
empty-list/array/input facts survive this same actual prefix execution. -/
theorem requests_reached {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord header be bo txs rcs logs buffer : BitVec 64} {boundary encoded : Nat}
    (ready : Logs input source pointer si record gasWord header be bo txs rcs logs buffer boundary encoded)
    (execution : CallPrefix.Execution source requestActions post) :
    ∃ reqs,Requests input post pointer si record gasWord header be bo txs rcs logs buffer reqs boundary encoded := by
  change CallPrefix.Execution source
    (.scoped (ofString "reqs") .one (ofString "alloc") requestArguments::
      [.command (.store (outputAddress 56) (localVar "reqs"))]) post at execution
  obtain ⟨allocated,allocation,last⟩:=execution.head
  obtain ⟨reqs,heapCell,lower,bounded,aligned⟩:=ready.heapAfter
  have cursorArena : AllocatedBytes.Arena reqs 0:=⟨by have low:=ready.backing.lower; omega,by omega⟩
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) requestArguments=some (PersistentAlloc.values 128#64):=by
    simp [requestArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,panOpHOL,valueIsWord,valueWord,PersistentAlloc.values]
  obtain ⟨cell,other,owned,frame,extent⟩:=allocation_scoped_reached source allocated "reqs" reqs 128#64 requestArguments args
    heapCell cursorArena bounded ready.arrays.output.environment.physical.data.arena.code allocation
  have logReady:=ready.of_persistent lower frame (by
    intro key member
    apply other
    intro same
    rw [same] at member
    exact (by decide : ofString "reqs"∉keptLogNames) member)
  have storeRun : evaluateHOLFiniteState allocated (.store (outputAddress 56) (localVar "reqs"))=(none,post):=by
    have reached:=last.singleton
    cases reached with | command _ _ run=>exact run
  have read : eval allocated (localVar "reqs")=some (.val (.word reqs)):=by
    simp [eval,evalHOLExact,toExact,localVar,cell]
  obtain ⟨output,locals,globals,outputField,away⟩:=output_word_store logReady.arrays.output 56 (localVar "reqs") reqs (by decide) (by decide) read storeRun
  have finalLogs:=logReady.of_output_store 56 (by decide) (by decide) output locals globals away
  have finalExtent : NormalHeapEffects.AtLeast (reqs.toNat+128) post:=by
    obtain ⟨heap,cell,low,bound,align⟩:=extent
    exact ⟨heap,by rw [globals]; exact cell,low,bound,align⟩
  exact ⟨reqs,finalLogs,by rw [locals]; exact cell,owned,aligned,lower,finalExtent,outputField⟩

theorem requests_cost (code) (installed : OriginalCode.Installed code) :
    ClockCost.Bound code (CallPrefix.program requestActions .skip) 2 := by
  simp only [requestActions,CallPrefix.program]
  apply PersistentAlloc.scoped_price (tailPrice:=0) code installed
  exact ClockCost.sequence code _ _ 0 0 (ClockCost.store code _ _) (ClockCost.skip code)

/-- Actual request-array outcomes stop within two source ticks or reach
the original return-list constructor with every physical fact retained. -/
theorem requests_trace {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord header be bo txs rcs logs buffer : BitVec 64} {boundary encoded : Nat}
    (ready : Logs input source pointer si record gasWord header be bo txs rcs logs buffer boundary encoded)
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source beforeRequests=(outcome,post)) :
    source.clock-post.clock≤2 ∨ ∃ current inner reqs,Requests input current pointer si record gasWord header be bo txs rcs logs buffer reqs boundary encoded ∧
      current.clock≤source.clock ∧ source.clock-current.clock≤2 ∧ CallPrefix.ScopeFrame post inner ∧
      evaluateHOLFiniteState current beforeReturnList=(outcome,inner) := by
  rw [requests_shape] at run
  rcases CallPrefix.priced_frame_trace source post requestActions beforeReturnList 2
    (requests_cost source.code ready.arrays.output.environment.physical.data.arena.code source rfl) outcome run with stopped|reached
  · exact Or.inl stopped.1
  · obtain ⟨current,inner,execution,forward,price,scope,rest⟩:=reached
    obtain ⟨reqs,physical⟩:=requests_reached ready execution
    exact Or.inr ⟨current,inner,reqs,physical,forward,price,scope,rest⟩

theorem body_requests_trace {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord header be : BitVec 64} {boundary encoded : Nat}
    (data : Data input source pointer si record gasWord boundary)
    (ready : RunAttempt.BlockEnvBuffer input (declarationEntry source record) pointer si record gasWord header be boundary encoded)
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source body=(outcome,post)) :
    source.clock-post.clock≤126 ∨ ∃ current inner bo txs rcs logs buffer reqs,
      Requests input current pointer si record gasWord header be bo txs rcs logs buffer reqs boundary encoded ∧
      current.clock≤source.clock ∧ source.clock-current.clock≤126 ∧ post.clock=inner.clock ∧
      evaluateHOLFiniteState current beforeReturnList=(outcome,inner) := by
  rcases body_logs_trace data ready outcome run with stopped|reached
  · exact Or.inl (by omega)
  · obtain ⟨before,target,bo,txs,rcs,logs,buffer,physical,forward,price,endpoint,continued⟩:=reached
    rcases requests_trace physical outcome continued with stopped|reached
    · exact Or.inl (by rw [endpoint]; omega)
    · obtain ⟨current,inner,reqs,physical,requestForward,requestPrice,scope,rest⟩:=reached
      exact Or.inr ⟨current,inner,bo,txs,rcs,logs,buffer,reqs,physical,by omega,by omega,endpoint.trans scope.clock,rest⟩

end InitECandidate.Solver.Input.CurrentVerify.ExecuteBlock

#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecuteBlock.requests_shape
#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecuteBlock.requests_reached
#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecuteBlock.requests_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecuteBlock.requests_trace
#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecuteBlock.body_requests_trace

namespace InitECandidate.Solver.Input.CurrentVerify.ExecuteBlock
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

def keptRequestNames : List MlS:=keptLogNames++[ofString "reqs"]

/-- Later actual persistent calls retain the request extent and its output
pointer as well as every earlier empty-log/array/input fact. -/
theorem Requests.of_persistent {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord header be bo txs rcs logs buffer reqs heap : BitVec 64} {boundary encoded : Nat}
    (ready : Requests input source pointer si record gasWord header be bo txs rcs logs buffer reqs boundary encoded)
    (beforeHeap : reqs.toNat+128≤heap.toNat) (frame : PersistentNormalFrame source post heap)
    (locals : ∀ key∈keptRequestNames,post.locals.lookup key=source.locals.lookup key) :
    Requests input post pointer si record gasWord header be bo txs rcs logs buffer reqs boundary encoded := by
  have logBefore : buffer.toNat+128≤heap.toNat:=by have before:=ready.before; omega
  have logState:=ready.logs.of_persistent logBefore frame (by
    intro key member
    apply locals
    simp only [keptRequestNames,List.mem_append]
    exact Or.inl member)
  have outputBefore : (bo+56#64).toNat<heap.toNat:=by
    have number : (bo+56#64).toNat=bo.toNat+56:=byteAddress_toNat bo 56 (by have upper:=ready.logs.arrays.output.arena.upper; omega)
    rw [number]
    have first:=ready.logs.arrays.beforeTxs
    have second:=ready.logs.arrays.beforeRcs
    have third:=ready.logs.before
    have fourth:=ready.logs.headerBefore
    have fifth:=ready.before
    omega
  obtain ⟨next,cell,arena,bound,aligned,advanced⟩:=frame.nextHeap
  exact ⟨logState,(locals _ (by simp [keptRequestNames])).trans ready.cell,ready.arena,ready.aligned,ready.before,
    ⟨next,cell,by omega,bound,aligned⟩,(frame.memory _ outputBefore).trans ready.outputField⟩

/-- Exact stores in different output fields retain the complete request
and empty-log images, including the live backing and heap frontier. -/
theorem Requests.of_output_store {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord header be bo txs rcs logs buffer reqs : BitVec 64} {boundary encoded : Nat}
    (ready : Requests input source pointer si record gasWord header be bo txs rcs logs buffer reqs boundary encoded)
    (offset : Nat) (inside : offset<88)
    (distinct : (24#64 : BitVec 64)≠BitVec.ofNat 64 offset ∧ (32#64 : BitVec 64)≠BitVec.ofNat 64 offset ∧
      (40#64 : BitVec 64)≠BitVec.ofNat 64 offset ∧ (56#64 : BitVec 64)≠BitVec.ofNat 64 offset)
    (output : OutputBuffer input post pointer si record gasWord header be bo boundary encoded)
    (locals : post.locals=source.locals) (globals : post.globals=source.globals)
    (memory : ∀ query : BitVec 64,query≠bo+BitVec.ofNat 64 offset→post.memory query=source.memory query) :
    Requests input post pointer si record gasWord header be bo txs rcs logs buffer reqs boundary encoded := by
  have logState:=ready.logs.of_output_store offset inside ⟨distinct.1,distinct.2.1,distinct.2.2.1⟩ output locals globals memory
  have different : bo+56#64≠bo+BitVec.ofNat 64 offset:=by
    intro same
    exact distinct.2.2.2 ((BitVec.add_right_inj bo).mp same)
  obtain ⟨heap,cell,lower,bound,aligned⟩:=ready.heapAfter
  exact ⟨logState,by rw [locals]; exact ready.cell,ready.arena,ready.aligned,ready.before,
    ⟨heap,by rw [globals]; exact cell,lower,bound,aligned⟩,(memory _ different).trans ready.outputField⟩

end InitECandidate.Solver.Input.CurrentVerify.ExecuteBlock

#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecuteBlock.Requests.of_persistent
#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecuteBlock.Requests.of_output_store

namespace InitECandidate.Solver.Input.CurrentVerify.ExecuteBlock
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

def returnActions : List CallPrefix.Action:=
  [.scoped (ofString "rls") .one (ofString "lst_new") [.const 8#64,.const 16#64],
   .command (.store (outputAddress 72) (localVar "rls")),
   .command (.store (outputAddress 80) (localVar "ntx"))]
def beforeBalInit : ProgHOL 64:=(CallPrefix.cutAt 3 beforeReturnList).2

theorem return_list_shape : beforeReturnList=CallPrefix.program returnActions beforeBalInit := by
  simp only [beforeReturnList,beforeRequests,beforeLogs,beforeArrays,afterCount,afterPayload,body,
    Guest.Software.guestFn_execute_block,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,
    Option.map_none,CallPrefix.cutAt,CallPrefix.program,returnActions,beforeBalInit,outputAddress,Scalar.plus,localVar] <;> trivial

structure ReturnList (input : Guest.InputBlob) (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer si record gasWord header be bo txs rcs logs buffer reqs rls returnBuffer : BitVec 64) (boundary encoded : Nat) : Prop where
  requests : Requests input source pointer si record gasWord header be bo txs rcs logs buffer reqs boundary encoded
  cell : source.locals.lookup (ofString "rls")=some (.val (.word rls))
  arena : AllocatedBytes.Arena rls 24
  aligned : rls.toNat%8=0
  backing : AllocatedBytes.Arena returnBuffer 128
  before : reqs.toNat+128≤rls.toNat
  headerBefore : rls.toNat+24≤returnBuffer.toNat
  heapAfter : NormalHeapEffects.AtLeast (returnBuffer.toNat+128) source
  pointerField : source.memory rls=.word returnBuffer
  countField : source.memory (rls+8#64)=.word 0#64
  capacityField : source.memory (rls+16#64)=.word 16#64
  outputField : source.memory (bo+72#64)=.word rls
  countOutputField : source.memory (bo+80#64)=.word 0#64

/-- The actual original return-list call and both scalar stores supply its
empty header/backing and the genuine zero output transaction count. Every
previous request/log/array/input fact survives the same real prefix. -/
theorem return_list_reached {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord header be bo txs rcs logs buffer reqs : BitVec 64} {boundary encoded : Nat}
    (ready : Requests input source pointer si record gasWord header be bo txs rcs logs buffer reqs boundary encoded)
    (execution : CallPrefix.Execution source returnActions post) :
    ∃ rls returnBuffer,ReturnList input post pointer si record gasWord header be bo txs rcs logs buffer reqs rls returnBuffer boundary encoded := by
  change CallPrefix.Execution source
    (.scoped (ofString "rls") .one (ofString "lst_new") [.const 8#64,.const 16#64]::
      .command (.store (outputAddress 72) (localVar "rls"))::
      [.command (.store (outputAddress 80) (localVar "ntx"))]) post at execution
  obtain ⟨allocated,allocation,remaining⟩:=execution.head
  obtain ⟨rls,heapCell,lower,bounded,aligned⟩:=ready.heapAfter
  have cursorArena : AllocatedBytes.Arena rls 0:=⟨by have low:=ready.arena.lower; omega,by omega⟩
  obtain ⟨cell,other,headerArena,frame,returnBuffer,backingArena,headerBefore,extent,pointerCell,countCell,capacityCell⟩:=
    list_scoped_reached source allocated "rls" rls 8#64 16#64 [.const 8#64,.const 16#64] rfl
      heapCell cursorArena bounded aligned ready.logs.arrays.output.environment.physical.data.arena allocation
  change AllocatedBytes.Arena returnBuffer 128 at backingArena
  change NormalHeapEffects.AtLeast (returnBuffer.toNat+128) allocated at extent
  have requests:=ready.of_persistent lower frame (by
    intro key member
    apply other
    intro same
    rw [same] at member
    exact (by decide : ofString "rls"∉keptRequestNames) member)
  obtain ⟨stored,store72,last⟩:=remaining.head
  have store72Run : evaluateHOLFiniteState allocated (.store (outputAddress 72) (localVar "rls"))=(none,stored):=by
    cases store72 with | command _ _ run=>exact run
  have readRls : eval allocated (localVar "rls")=some (.val (.word rls)):=by
    simp [eval,evalHOLExact,toExact,localVar,cell]
  obtain ⟨output72,locals72,globals72,field72,away72⟩:=output_word_store requests.logs.arrays.output 72 (localVar "rls") rls (by decide) (by decide) readRls store72Run
  have after72:=requests.of_output_store 72 (by decide) (by decide) output72 locals72 globals72 away72
  have store80Run : evaluateHOLFiniteState stored (.store (outputAddress 80) (localVar "ntx"))=(none,post):=by
    have reached:=last.singleton
    cases reached with | command _ _ run=>exact run
  have readCount : eval stored (localVar "ntx")=some (.val (.word 0#64)):=by
    simp [eval,evalHOLExact,toExact,localVar,after72.logs.arrays.output.count]
  obtain ⟨output80,locals80,globals80,field80,away80⟩:=output_word_store after72.logs.arrays.output 80 (localVar "ntx") 0#64 (by decide) (by decide) readCount store80Run
  have finalRequests:=after72.of_output_store 80 (by decide) (by decide) output80 locals80 globals80 away80
  have beforeHeader : bo.toNat+88≤rls.toNat:=by
    have first:=ready.logs.arrays.beforeTxs
    have second:=ready.logs.arrays.beforeRcs
    have third:=ready.logs.before
    have fourth:=ready.logs.headerBefore
    have fifth:=ready.before
    omega
  have headerAway (destination offset : Nat) (destinationInside : destination<88) (inside : offset<24) :=
    output_header_distinct bo rls ready.logs.arrays.output.arena headerArena beforeHeader destination offset destinationInside inside
  have finalExtent : NormalHeapEffects.AtLeast (returnBuffer.toNat+128) post:=by
    obtain ⟨heap,cell,low,bound,align⟩:=extent
    exact ⟨heap,by rw [globals80,globals72]; exact cell,low,bound,align⟩
  have outputAway : bo+72#64≠bo+80#64:=by
    intro same
    exact (by decide : (72#64 : BitVec 64)≠80#64) ((BitVec.add_right_inj bo).mp same)
  exact ⟨rls,returnBuffer,finalRequests,by rw [locals80,locals72]; exact cell,headerArena,aligned,backingArena,lower,headerBefore,finalExtent,
    (away80 _ (by simpa using headerAway 80 0 (by decide) (by decide))).trans
      ((away72 _ (by simpa using headerAway 72 0 (by decide) (by decide))).trans pointerCell),
    (away80 _ (headerAway 80 8 (by decide) (by decide))).trans ((away72 _ (headerAway 72 8 (by decide) (by decide))).trans countCell),
    (away80 _ (headerAway 80 16 (by decide) (by decide))).trans ((away72 _ (headerAway 72 16 (by decide) (by decide))).trans capacityCell),
    (away80 _ outputAway).trans field72,field80⟩

/-- Full actual return-list caller and both output stores, on every outcome. -/
theorem return_list_cost (code) (installed : OriginalCode.Installed code) :
    ClockCost.Bound code (CallPrefix.program returnActions .skip) 5 := by
  simp only [returnActions,CallPrefix.program]
  apply ClockCost.scoped_body (calleePrice:=4) (continuationPrice:=0) (formals:=listFormals) (body:=listBody)
    (returnShape:=.one) (entry:=list_code code installed) (calleeBound:=list_cost code installed)
  exact ClockCost.sequence code _ _ 0 0 (ClockCost.store code _ _)
    (ClockCost.sequence code _ _ 0 0 (ClockCost.store code _ _) (ClockCost.skip code))

/-- Actual return-list outcomes either stop within five source ticks or
reach the original BAL initializer with all physical facts retained. -/
theorem return_list_trace {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord header be bo txs rcs logs buffer reqs : BitVec 64} {boundary encoded : Nat}
    (ready : Requests input source pointer si record gasWord header be bo txs rcs logs buffer reqs boundary encoded)
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source beforeReturnList=(outcome,post)) :
    source.clock-post.clock≤5 ∨ ∃ current inner rls returnBuffer,
      ReturnList input current pointer si record gasWord header be bo txs rcs logs buffer reqs rls returnBuffer boundary encoded ∧
      current.clock≤source.clock ∧ source.clock-current.clock≤5 ∧ CallPrefix.ScopeFrame post inner ∧
      evaluateHOLFiniteState current beforeBalInit=(outcome,inner) := by
  rw [return_list_shape] at run
  rcases CallPrefix.priced_frame_trace source post returnActions beforeBalInit 5
    (return_list_cost source.code ready.logs.arrays.output.environment.physical.data.arena.code source rfl) outcome run with stopped|reached
  · exact Or.inl stopped.1
  · obtain ⟨current,inner,execution,forward,price,scope,rest⟩:=reached
    obtain ⟨rls,returnBuffer,physical⟩:=return_list_reached ready execution
    exact Or.inr ⟨current,inner,rls,returnBuffer,physical,forward,price,scope,rest⟩

theorem body_return_list_trace {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord header be : BitVec 64} {boundary encoded : Nat}
    (data : Data input source pointer si record gasWord boundary)
    (ready : RunAttempt.BlockEnvBuffer input (declarationEntry source record) pointer si record gasWord header be boundary encoded)
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source body=(outcome,post)) :
    source.clock-post.clock≤131 ∨ ∃ current inner bo txs rcs logs buffer reqs rls returnBuffer,
      ReturnList input current pointer si record gasWord header be bo txs rcs logs buffer reqs rls returnBuffer boundary encoded ∧
      current.clock≤source.clock ∧ source.clock-current.clock≤131 ∧ post.clock=inner.clock ∧
      evaluateHOLFiniteState current beforeBalInit=(outcome,inner) := by
  rcases body_requests_trace data ready outcome run with stopped|reached
  · exact Or.inl (by omega)
  · obtain ⟨before,target,bo,txs,rcs,logs,buffer,reqs,physical,forward,price,endpoint,continued⟩:=reached
    rcases return_list_trace physical outcome continued with stopped|reached
    · exact Or.inl (by rw [endpoint]; omega)
    · obtain ⟨current,inner,rls,returnBuffer,physical,returnForward,returnPrice,scope,rest⟩:=reached
      exact Or.inr ⟨current,inner,bo,txs,rcs,logs,buffer,reqs,rls,returnBuffer,physical,by omega,by omega,endpoint.trans scope.clock,rest⟩

end InitECandidate.Solver.Input.CurrentVerify.ExecuteBlock

#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecuteBlock.return_list_shape
#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecuteBlock.return_list_reached
#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecuteBlock.return_list_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecuteBlock.return_list_trace
#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecuteBlock.body_return_list_trace
