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

namespace InitECandidate.Solver.Input.CurrentVerify.ExecuteBlock
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

def keptReturnNames : List MlS:=keptRequestNames++[ofString "rls"]
def keptExecutionGlobals : List MlS:=dataGlobals++[ofString "be",ofString "bo"]

/-- Actual later persistent helpers retain both complete empty lists,
request/array extents, output cells and all earlier physical input facts. -/
theorem ReturnList.of_persistent {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord header be bo txs rcs logs buffer reqs rls returnBuffer heap : BitVec 64} {boundary encoded : Nat}
    (ready : ReturnList input source pointer si record gasWord header be bo txs rcs logs buffer reqs rls returnBuffer boundary encoded)
    (beforeHeap : returnBuffer.toNat+128≤heap.toNat) (frame : PersistentNormalFrame source post heap)
    (locals : ∀ key∈keptReturnNames,post.locals.lookup key=source.locals.lookup key) :
    ReturnList input post pointer si record gasWord header be bo txs rcs logs buffer reqs rls returnBuffer boundary encoded := by
  have afterReqs : reqs.toNat+128≤heap.toNat:=by
    have first:=ready.before
    have second:=ready.headerBefore
    omega
  have requests:=ready.requests.of_persistent afterReqs frame (by
    intro key member
    apply locals
    simp only [keptReturnNames,List.mem_append]
    exact Or.inl member)
  have earlier (offset : Nat) (inside : offset<24) : (rls+BitVec.ofNat 64 offset).toNat<heap.toNat:=by
    have number:=byteAddress_toNat rls offset (by have upper:=ready.arena.upper; omega)
    change (rls+BitVec.ofNat 64 offset).toNat=rls.toNat+offset at number
    rw [number]
    have before:=ready.headerBefore
    omega
  have outputBefore (offset : Nat) (inside : offset<88) : (bo+BitVec.ofNat 64 offset).toNat<heap.toNat:=by
    have number:=byteAddress_toNat bo offset (by have upper:=ready.requests.logs.arrays.output.arena.upper; omega)
    change (bo+BitVec.ofNat 64 offset).toNat=bo.toNat+offset at number
    rw [number]
    have first:=ready.requests.logs.arrays.beforeTxs
    have second:=ready.requests.logs.arrays.beforeRcs
    have third:=ready.requests.logs.before
    have fourth:=ready.requests.logs.headerBefore
    have fifth:=ready.requests.before
    omega
  obtain ⟨next,cell,arena,bound,aligned,advanced⟩:=frame.nextHeap
  exact ⟨requests,(locals _ (by simp [keptReturnNames])).trans ready.cell,ready.arena,ready.aligned,ready.backing,ready.before,ready.headerBefore,
    ⟨next,cell,by omega,bound,aligned⟩,
    (frame.memory _ (by simpa using earlier 0 (by decide))).trans ready.pointerField,
    (frame.memory _ (earlier 8 (by decide))).trans ready.countField,
    (frame.memory _ (earlier 16 (by decide))).trans ready.capacityField,
    (frame.memory _ (outputBefore 72 (by decide))).trans ready.outputField,
    (frame.memory _ (outputBefore 80 (by decide))).trans ready.countOutputField⟩

/-- BAL may initialize its own globals while retaining every global used
by the current input/environment contract. Memory and caller locals are
unchanged by this update; all live heap frontiers are explicitly retained. -/
theorem ReturnList.with_globals {input : Guest.InputBlob} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord header be bo txs rcs logs buffer reqs rls returnBuffer : BitVec 64} {boundary encoded : Nat}
    (ready : ReturnList input source pointer si record gasWord header be bo txs rcs logs buffer reqs rls returnBuffer boundary encoded)
    (globals : HolFiniteMapExact MlS (ValueHOL 64))
    (kept : ∀ key∈keptExecutionGlobals,globals.lookup key=source.globals.lookup key) :
    ReturnList input {source with globals:=globals} pointer si record gasWord header be bo txs rcs logs buffer reqs rls returnBuffer boundary encoded := by
  have keptData : ∀ key∈dataGlobals,globals.lookup key=source.globals.lookup key:=by
    intro key member
    exact kept key (List.mem_append.mpr (Or.inl member))
  have heaps (floor : Nat) (old : NormalHeapEffects.AtLeast floor source) : NormalHeapEffects.AtLeast floor {source with globals:=globals}:=by
    obtain ⟨heap,cell,lower,bound,aligned⟩:=old
    exact ⟨heap,(keptData _ (by simp [dataGlobals])).trans cell,lower,bound,aligned⟩
  let oldOutput:=ready.requests.logs.arrays.output
  have physical:=oldOutput.environment.physical.with_globals globals keptData
  have environment : RunAttempt.BlockEnvBuffer input {source with globals:=globals} pointer si record gasWord header be boundary encoded:=
    {oldOutput.environment with physical:=physical,cell:=(kept _ (by simp [keptExecutionGlobals])).trans oldOutput.environment.cell, heapAfter:=heaps _ oldOutput.environment.heapAfter}
  have output : OutputBuffer input {source with globals:=globals} pointer si record gasWord header be bo boundary encoded:=
    {oldOutput with environment:=environment,cell:=(kept _ (by simp [keptExecutionGlobals])).trans oldOutput.cell, heapAfter:=heaps _ oldOutput.heapAfter}
  have arrays : Arrays input {source with globals:=globals} pointer si record gasWord header be bo txs rcs boundary encoded:=
    {ready.requests.logs.arrays with output:=output,heapAfter:=heaps _ ready.requests.logs.arrays.heapAfter}
  have logState : Logs input {source with globals:=globals} pointer si record gasWord header be bo txs rcs logs buffer boundary encoded:=
    {ready.requests.logs with arrays:=arrays,heapAfter:=heaps _ ready.requests.logs.heapAfter}
  have requests : Requests input {source with globals:=globals} pointer si record gasWord header be bo txs rcs logs buffer reqs boundary encoded:=
    {ready.requests with logs:=logState,heapAfter:=heaps _ ready.requests.heapAfter}
  exact {ready with requests:=requests,heapAfter:=heaps _ ready.heapAfter}

/-- The current constructor's post-header syntax only advances the actual
heap through allocation calls; failed/error outcomes remain unrestricted. -/
theorem table_after_header_heap (code) (installed : OriginalCode.Installed code) :
    NormalHeapEffects.Preserves code CurrentTable.New.afterTable := by
  have allocation : NormalHeapEffects.Returning code PersistentAlloc.body:=by
    have pure:=CurrentStartup.HeapMonotone.alloc code installed
    have same : CurrentStartup.Code.body .alloc=PersistentAlloc.body:=by
      simp only [CurrentStartup.Code.body,CurrentStartup.Code.entry,CurrentStartup.Code.declaration,
        GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,Guest.Software.guestFn_alloc,PersistentAlloc.body]
    rw [same] at pure
    exact pure
  simp only [CurrentTable.New.afterTable,CurrentTable.New.body,Guest.Software.guestFn_htab_new,progToHOL]
  repeat first
    | apply NormalHeapEffects.declared
    | apply NormalHeapEffects.sequence
    | apply NormalHeapEffects.conditional
    | exact NormalHeapEffects.assign code _ _
    | exact NormalHeapEffects.store code _ _
    | exact NormalHeapEffects.skip code
    | exact NormalHeapEffects.returned code _
    | apply NormalHeapEffects.scoped_body (formals:=PersistentAlloc.formals) (body:=PersistentAlloc.body) (returnShape:=.one)
        (entry:=PersistentAlloc.original_code code installed) (pureBody:=allocation)

/-- A genuine normal constructor derives the heap beyond its full header,
including arbitrary scalar key/capacity reads in the later continuation. -/
theorem table_body_header_extent (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (bounded : heap.toNat≤2952790016) (installed : OriginalCode.Installed source.code)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source CurrentTable.New.body=(some (.returned value),post)) :
    NormalHeapEffects.AtLeast (heap.toNat+88) post := by
  rw [CurrentTable.New.shapes.1] at normal
  rcases CurrentAlloc.scoped_classified source post "t" [.const 88#64] CurrentTable.New.afterTable heap 88#64 rfl installed heapCell bounded _ normal with stopped|reached
  · exact (stopped.2 value rfl).elim
  · obtain ⟨funded,room,middle,continued,endpoint⟩:=reached
    let entered:=CurrentTable.New.tableEntry source heap
    have guards:=PersistentAlloc.guards heap 88#64 room
    have cell : entered.globals.lookup (ofString "heap_ptr")=some (.val (.word (PersistentAlloc.rounded heap 88#64))):=by
      simp [entered,CurrentTable.New.tableEntry,QueryBranch.bind,setVarHOLFinite,PersistentAlloc.post,HolFiniteMapExact.update,FUPDATE]
    have initial : NormalHeapEffects.AtLeast (heap.toNat+88) entered:=
      ⟨PersistentAlloc.rounded heap 88#64,cell,guards.2.2.1,guards.2.2.2.1,guards.2.2.2.2⟩
    change evaluateHOLFiniteState entered CurrentTable.New.afterTable=(some (.returned value),middle) at continued
    have after:=table_after_header_heap source.code installed entered rfl (heap.toNat+88) initial (by rw [continued]; trivial)
    rw [continued] at after
    rw [endpoint]
    exact after

/-- A real global-result call to the current Patricia constructor supplies
its own88byte header and persistent callee frame before the actual global
assignment. No old destination value/shape or allocation room is assumed. -/
theorem table_global_normal_frame (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (name : String) (key cap heap : BitVec 64) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=
      some [.val (.word key),.val (.word cap)]) (atLeastTwo : 2≤cap.toNat)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (heapBound : heap.toNat≤2952790016) (heapAligned : heap.toNat%8=0)
    (arena : CurrentStartup.ArenaState source)
    (normal : evaluateHOLFiniteState source (.call (some (some (.global,ofString name),none)) (ofString "htab_new") arguments)=(none,post)) :
    ∃ raw,post=putGlobal raw name heap ∧ raw.locals=source.locals ∧ AllocatedBytes.Arena heap 88 ∧ PersistentNormalFrame source raw heap ∧
      NormalHeapEffects.AtLeast (heap.toNat+88) raw := by
  obtain ⟨callee,called,keyCell,capCell⟩:=word_pair_environment source.code.lookup (ofString "htab_new") (ofString "key_len") (ofString "cap")
    CurrentTable.New.body .one key cap (by decide) (CurrentTable.New.original_code source.code arena.code)
  obtain ⟨funded,child,value,bodyRun⟩:=CallNormal.assigned_callee_return source post (some (.global,ofString name)) (ofString "htab_new") arguments _
    CurrentTable.New.body callee .one args called normal
  obtain ⟨answer,owned,frame⟩:=CurrentTable.New.body_scalar_normal_frame (callEntryStateHOLFinite source callee) child heap key cap
    keyCell capCell atLeastTwo heapCell heapArena heapBound heapAligned (arena.of_frame rfl) value bodyRun
  have extent:=table_body_header_extent (callEntryStateHOLFinite source callee) child heap heapCell heapBound arena.code value bodyRun
  let raw:={child with locals:=source.locals}
  have callerFrame : PersistentNormalFrame source raw heap:=frame.of_erase _ _ source raw heap rfl rfl
  rw [answer] at bodyRun
  rw [evaluateHOLFiniteState_call,args] at normal
  simp only [called,if_neg (show source.clock≠0 by omega),bodyRun,shapeOfHOLExact,shapeEqHOL,↓reduceIte] at normal
  split at normal
  · have endpoint:=(congrArg Prod.snd normal).symm
    change post=setKvarHOLFinite .global (ofString name) (.val (.word heap)) raw at endpoint
    exact ⟨raw,endpoint,rfl,owned,callerFrame,extent⟩
  · cases normal

end InitECandidate.Solver.Input.CurrentVerify.ExecuteBlock

#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecuteBlock.ReturnList.of_persistent
#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecuteBlock.ReturnList.with_globals
#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecuteBlock.table_after_header_heap
#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecuteBlock.table_body_header_extent
#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecuteBlock.table_global_normal_frame

namespace InitECandidate.Solver.Input.CurrentVerify.ExecuteBlock
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

/-- A genuine unrelated global assignment preserves all live executor
physical data. Its normal scalar update is established by the call/command,
not assumed as a future execution at entry. -/
theorem ReturnList.put_global {input : Guest.InputBlob} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord header be bo txs rcs logs buffer reqs rls returnBuffer : BitVec 64} {boundary encoded : Nat}
    (ready : ReturnList input source pointer si record gasWord header be bo txs rcs logs buffer reqs rls returnBuffer boundary encoded)
    (name : String) (word : BitVec 64) (unrelated : ofString name∉keptExecutionGlobals) :
    ReturnList input (putGlobal source name word) pointer si record gasWord header be bo txs rcs logs buffer reqs rls returnBuffer boundary encoded := by
  apply ready.with_globals (putGlobal source name word).globals
  intro key member
  apply putGlobal.lookup_other source name word key
  intro same
  rw [same] at member
  exact unrelated member

/-- A real callee may initialize its own globals and use its own locals.
After the ordinary call restores the observed caller bindings, its genuine
memory/heap frame and retained input globals recover the full executor state. -/
theorem ReturnList.of_memory_frame {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord header be bo txs rcs logs buffer reqs rls returnBuffer heap : BitVec 64} {boundary encoded : Nat}
    (ready : ReturnList input source pointer si record gasWord header be bo txs rcs logs buffer reqs rls returnBuffer boundary encoded)
    (beforeHeap : returnBuffer.toNat+128≤heap.toNat) (frame : PersistentMemoryFrame source post heap)
    (kept : ∀ key∈keptExecutionGlobals,key≠ofString "heap_ptr"→post.globals.lookup key=source.globals.lookup key)
    (locals : ∀ key∈keptReturnNames,post.locals.lookup key=source.locals.lookup key) :
    ReturnList input post pointer si record gasWord header be bo txs rcs logs buffer reqs rls returnBuffer boundary encoded := by
  obtain ⟨next,cell,arena,bound,aligned,advanced⟩:=frame.nextHeap
  let raw:={post with globals:=source.globals.update (ofString "heap_ptr",.val (.word next))}
  have rawCell : raw.globals.lookup (ofString "heap_ptr")=some (.val (.word next)):=by
    simp [raw,HolFiniteMapExact.update,FUPDATE]
  have rawFrame : PersistentNormalFrame source raw heap:=by
    refine ⟨⟨next,rawCell,arena,bound,aligned,advanced⟩,frame.metadata,?_,frame.memory⟩
    intro key different
    simp [raw,HolFiniteMapExact.update,FUPDATE,different,Ne.symm different]
  have rawReady:=ready.of_persistent beforeHeap rawFrame locals
  have actual:=rawReady.with_globals post.globals (by
    intro key member
    by_cases same : key=ofString "heap_ptr"
    · subst key
      exact cell.trans rawCell.symm
    · exact (kept key member same).trans (rawFrame.globals key same).symm)
  exact actual

end InitECandidate.Solver.Input.CurrentVerify.ExecuteBlock

#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecuteBlock.ReturnList.put_global
#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecuteBlock.ReturnList.of_memory_frame

namespace InitECandidate.Solver.Input.CurrentVerify.ExecuteBlock
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

/-- Callee-scope interface for each current BAL table assignment. It needs
only the actual runtime arena and incoming heap, not main's caller locals.
Normal execution derives the global header, owned extent and advanced heap,
complete older-memory frame and exactly retained unrelated globals. -/
theorem table_global_memory_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (name : String) (key cap heap : BitVec 64) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=
      some [.val (.word key),.val (.word cap)]) (atLeastTwo : 2≤cap.toNat)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (heapBound : heap.toNat≤2952790016) (heapAligned : heap.toNat%8=0)
    (arena : CurrentStartup.ArenaState source)
    (different : ofString "heap_ptr"≠ofString name ∧ ofString "scratch_ptr"≠ofString name ∧ ofString "frame_mem_ptr"≠ofString name)
    (normal : evaluateHOLFiniteState source (.call (some (some (.global,ofString name),none)) (ofString "htab_new") arguments)=(none,post)) :
    post.locals=source.locals ∧ post.globals.lookup (ofString name)=some (.val (.word heap)) ∧
      AllocatedBytes.Arena heap 88 ∧ CurrentStartup.ArenaState post ∧ PersistentMemoryFrame source post heap ∧
      NormalHeapEffects.AtLeast (heap.toNat+88) post ∧
      ∀ global : MlS,global≠ofString name→global≠ofString "heap_ptr"→post.globals.lookup global=source.globals.lookup global := by
  obtain ⟨raw,endpoint,locals,owned,frame,extent⟩:=table_global_normal_frame source post name key cap heap arguments args atLeastTwo
    heapCell heapArena heapBound heapAligned arena normal
  have rawArena:=frame.current_arena arena
  have resultArena : CurrentStartup.ArenaState (putGlobal raw name heap):=
    ⟨(putGlobal.lookup_other raw name heap _ different.2.1).trans rawArena.scratch,
      (putGlobal.lookup_other raw name heap _ different.2.2).trans rawArena.frame,rawArena.domain,rawArena.code⟩
  have memoryFrame:=frame.memory_frame.put_global source raw heap name heap different.1
  have resultExtent : NormalHeapEffects.AtLeast (heap.toNat+88) (putGlobal raw name heap):=by
    obtain ⟨next,cell,lower,bound,aligned⟩:=extent
    exact ⟨next,(putGlobal.lookup_other raw name heap _ different.1).trans cell,lower,bound,aligned⟩
  rw [endpoint]
  refine ⟨locals,putGlobal.lookup_same raw name heap,owned,resultArena,memoryFrame,resultExtent,?_⟩
  intro global notName notHeap
  exact (putGlobal.lookup_other raw name heap global notName).trans (frame.globals global notHeap)

end InitECandidate.Solver.Input.CurrentVerify.ExecuteBlock

#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecuteBlock.table_global_memory_normal

namespace InitECandidate.Solver.Input.CurrentVerify.ExecuteBlock
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

/-- Current allocation with a genuine global result, in BAL's own scope. -/
theorem allocation_global_memory_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (name : String) (heap amount : BitVec 64) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=some (PersistentAlloc.values amount))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (heapBound : heap.toNat≤2952790016)
    (arena : CurrentStartup.ArenaState source)
    (different : ofString "heap_ptr"≠ofString name ∧ ofString "scratch_ptr"≠ofString name ∧ ofString "frame_mem_ptr"≠ofString name)
    (normal : evaluateHOLFiniteState source (.call (some (some (.global,ofString name),none)) (ofString "alloc") arguments)=(none,post)) :
    post.locals=source.locals ∧ post.globals.lookup (ofString name)=some (.val (.word heap)) ∧
      AllocatedBytes.Arena heap amount.toNat ∧ CurrentStartup.ArenaState post ∧ PersistentMemoryFrame source post heap ∧
      NormalHeapEffects.AtLeast (heap.toNat+amount.toNat) post ∧
      ∀ global : MlS,global≠ofString name→global≠ofString "heap_ptr"→post.globals.lookup global=source.globals.lookup global := by
  obtain ⟨room,funded,endpoint⟩:=PersistentAlloc.global_call_normal_any source post name heap amount arguments args
    (PersistentAlloc.original_code source.code arena.code) (Trap.original_code source.code arena.code) heapCell heapBound normal
  let raw:=PersistentAlloc.post {source with clock:=source.clock-1} heap amount
  have frame : PersistentNormalFrame source raw heap:=
    (PersistentAlloc.post_persistent_frame {source with clock:=source.clock-1} heap amount heapArena room).of_erase _ _ source raw heap rfl rfl
  have rawArena:=frame.current_arena arena
  have resultArena : CurrentStartup.ArenaState (putGlobal raw name heap):=
    ⟨(putGlobal.lookup_other raw name heap _ different.2.1).trans rawArena.scratch,
      (putGlobal.lookup_other raw name heap _ different.2.2).trans rawArena.frame,rawArena.domain,rawArena.code⟩
  have guards:=PersistentAlloc.guards heap amount room
  have rawCell : raw.globals.lookup (ofString "heap_ptr")=some (.val (.word (PersistentAlloc.rounded heap amount))):=by
    simp [raw,PersistentAlloc.post,HolFiniteMapExact.update,FUPDATE]
  have extent : NormalHeapEffects.AtLeast (heap.toNat+amount.toNat) (putGlobal raw name heap):=
    ⟨PersistentAlloc.rounded heap amount,(putGlobal.lookup_other raw name heap _ different.1).trans rawCell,
      guards.2.2.1,guards.2.2.2.1,guards.2.2.2.2⟩
  rw [endpoint]
  refine ⟨rfl,putGlobal.lookup_same raw name heap,⟨heapArena.lower,by omega⟩,resultArena,
    frame.memory_frame.put_global source raw heap name heap different.1,extent,?_⟩
  intro global notName notHeap
  exact (putGlobal.lookup_other raw name heap global notName).trans (frame.globals global notHeap)

structure BalHeap (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64) : Prop where
  runtime : CurrentStartup.ArenaState source
  cell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap))
  arena : AllocatedBytes.Arena heap 0
  bounded : heap.toNat≤2952790016
  aligned : heap.toNat%8=0

theorem BalHeap.of_extent (source : PanSemStateFiniteExact 64 Guest.HostMemory) (floor : Nat)
    (runtime : CurrentStartup.ArenaState source) (lower : 2701131776≤floor)
    (extent : NormalHeapEffects.AtLeast floor source) :
    ∃ heap,BalHeap source heap ∧ floor≤heap.toNat := by
  obtain ⟨heap,cell,before,bounded,aligned⟩:=extent
  exact ⟨heap,⟨runtime,cell,⟨by omega,by omega⟩,bounded,aligned⟩,before⟩

def balTableCall (name : String) (key : BitVec 64) : ProgHOL 64:=
  .call (some (some (.global,ofString name),none)) (ofString "htab_new") [.const key,.const 64#64]
def balBufferCall : ProgHOL 64:=.call (some (some (.global,ofString "bal_key_buf"),none)) (ofString "alloc") [.const 64#64]
def balZero : ProgHOL 64:=.assign .global (ofString "bal_index") (.const 0#64)
def balActions : List CallPrefix.Action:=
  [.command (balTableCall "bal_accounts" 20#64),.command (balTableCall "bal_idx_accts" 28#64),
   .command (balTableCall "bal_idx_stor" 60#64),.command balBufferCall,.command balZero]
def balReturn : ProgHOL 64:=.return (.const 0#64)
def balGlobals : List MlS:=[ofString "bal_accounts",ofString "bal_idx_accts",ofString "bal_idx_stor",ofString "bal_key_buf",ofString "bal_index"]

theorem bal_body_shape : balBody=CallPrefix.program balActions balReturn := by
  simp only [balBody,Guest.Software.guestFn_bal_init,progToHOL,expToHOL,List.map_cons,List.map_nil,
    Option.map_some,Option.map_none,balActions,balTableCall,balBufferCall,balZero,balReturn,CallPrefix.program]

theorem bal_prefix_never : NoReturn.Never (CallPrefix.program balActions .skip) := by
  have safe : LocalPrefix (ofString "_") (CallPrefix.program balActions .skip):=by
    simp only [balActions,CallPrefix.program,balTableCall,balBufferCall,balZero]
    exact .seq (.globalCall _ _ _) (.seq (.globalCall _ _ _) (.seq (.globalCall _ _ _) (.seq (.globalCall _ _ _) (.seq (.globalAssign _ _) .skip))))
  intro F source value
  exact (safe.summary source).2 value

structure BalCells (source : PanSemStateFiniteExact 64 Guest.HostMemory) (accounts accountIndex storageIndex keyBuffer : BitVec 64) : Prop where
  accountsCell : source.globals.lookup (ofString "bal_accounts")=some (.val (.word accounts))
  accountIndexCell : source.globals.lookup (ofString "bal_idx_accts")=some (.val (.word accountIndex))
  storageIndexCell : source.globals.lookup (ofString "bal_idx_stor")=some (.val (.word storageIndex))
  keyBufferCell : source.globals.lookup (ofString "bal_key_buf")=some (.val (.word keyBuffer))
  indexCell : source.globals.lookup (ofString "bal_index")=some (.val (.word 0#64))
  accountsArena : AllocatedBytes.Arena accounts 88
  accountIndexArena : AllocatedBytes.Arena accountIndex 88
  storageIndexArena : AllocatedBytes.Arena storageIndex 88
  keyBufferArena : AllocatedBytes.Arena keyBuffer 64
  accountsAligned : accounts.toNat%8=0
  accountIndexAligned : accountIndex.toNat%8=0
  storageIndexAligned : storageIndex.toNat%8=0
  keyBufferAligned : keyBuffer.toNat%8=0
  beforeAccountIndex : accounts.toNat+88≤accountIndex.toNat
  beforeStorageIndex : accountIndex.toNat+88≤storageIndex.toNat
  beforeKeyBuffer : storageIndex.toNat+88≤keyBuffer.toNat
  heapAfter : NormalHeapEffects.AtLeast (keyBuffer.toNat+64) source

end InitECandidate.Solver.Input.CurrentVerify.ExecuteBlock

#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecuteBlock.allocation_global_memory_normal
#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecuteBlock.BalHeap.of_extent
#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecuteBlock.bal_body_shape
#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecuteBlock.bal_prefix_never

namespace InitECandidate.Solver.Input.CurrentVerify.ExecuteBlock
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

/-- Replay the five actual normal BAL commands in their own callee scope.
Each next frontier and allocation room follows from the same observed call;
all final globals and disjoint owned extents are conclusions. -/
theorem bal_execution (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64)
    (context : BalHeap source heap) (execution : CallPrefix.Execution source balActions post) :
    CurrentStartup.ArenaState post ∧ PersistentMemoryFrame source post heap ∧ post.locals=source.locals ∧
      (∃ accountIndex storageIndex keyBuffer,BalCells post heap accountIndex storageIndex keyBuffer) ∧
      ∀ key : MlS,key∉balGlobals→key≠ofString "heap_ptr"→post.globals.lookup key=source.globals.lookup key := by
  change CallPrefix.Execution source
    (.command (balTableCall "bal_accounts" 20#64)::.command (balTableCall "bal_idx_accts" 28#64)::
      .command (balTableCall "bal_idx_stor" 60#64)::.command balBufferCall::[.command balZero]) post at execution
  obtain ⟨one,first,rest⟩:=execution.head
  have run1 : evaluateHOLFiniteState source (balTableCall "bal_accounts" 20#64)=(none,one):=by
    cases first with | command _ _ run=>exact run
  obtain ⟨locals1,accounts,owned1,runtime1,frame1,extent1,globals1⟩:=table_global_memory_normal source one "bal_accounts" 20#64 64#64 heap
    [.const 20#64,.const 64#64] rfl (by decide) context.cell context.arena context.bounded context.aligned context.runtime (by decide) run1
  obtain ⟨accountIndex,context1,before1⟩:=BalHeap.of_extent one (heap.toNat+88) runtime1 (by have low:=context.arena.lower; omega) extent1
  obtain ⟨two,second,rest⟩:=rest.head
  have run2 : evaluateHOLFiniteState one (balTableCall "bal_idx_accts" 28#64)=(none,two):=by
    cases second with | command _ _ run=>exact run
  obtain ⟨locals2,indexAccounts,owned2,runtime2,frame2,extent2,globals2⟩:=table_global_memory_normal one two "bal_idx_accts" 28#64 64#64 accountIndex
    [.const 28#64,.const 64#64] rfl (by decide) context1.cell context1.arena context1.bounded context1.aligned context1.runtime (by decide) run2
  obtain ⟨storageIndex,context2,before2⟩:=BalHeap.of_extent two (accountIndex.toNat+88) runtime2 (by have low:=context1.arena.lower; omega) extent2
  obtain ⟨three,third,rest⟩:=rest.head
  have run3 : evaluateHOLFiniteState two (balTableCall "bal_idx_stor" 60#64)=(none,three):=by
    cases third with | command _ _ run=>exact run
  obtain ⟨locals3,indexStorage,owned3,runtime3,frame3,extent3,globals3⟩:=table_global_memory_normal two three "bal_idx_stor" 60#64 64#64 storageIndex
    [.const 60#64,.const 64#64] rfl (by decide) context2.cell context2.arena context2.bounded context2.aligned context2.runtime (by decide) run3
  obtain ⟨keyBuffer,context3,before3⟩:=BalHeap.of_extent three (storageIndex.toNat+88) runtime3 (by have low:=context2.arena.lower; omega) extent3
  obtain ⟨four,fourth,last⟩:=rest.head
  have run4 : evaluateHOLFiniteState three balBufferCall=(none,four):=by
    cases fourth with | command _ _ run=>exact run
  obtain ⟨locals4,bufferCell,owned4,runtime4,frame4,extent4,globals4⟩:=allocation_global_memory_normal three four "bal_key_buf" keyBuffer 64#64
    [.const 64#64] rfl context3.cell context3.arena context3.bounded context3.runtime (by decide) run4
  have run5 : evaluateHOLFiniteState four balZero=(none,post):=by
    have last:=last.singleton
    cases last with | command _ _ run=>exact run
  have endpoint : post=putGlobal four "bal_index" 0#64:=global_assign_none four post "bal_index" (.const 0#64) 0#64 rfl run5
  have indexOther (key : MlS) (different : key≠ofString "bal_index") : post.globals.lookup key=four.globals.lookup key:=by
    rw [endpoint]
    exact putGlobal.lookup_other four "bal_index" 0#64 key different
  have runtime : CurrentStartup.ArenaState post:=by
    rw [endpoint]
    exact ⟨(putGlobal.lookup_other four "bal_index" 0#64 _ (by decide)).trans runtime4.scratch,
      (putGlobal.lookup_other four "bal_index" 0#64 _ (by decide)).trans runtime4.frame,runtime4.domain,runtime4.code⟩
  have total12:=frame1.trans source one two heap accountIndex frame2 (by omega)
  have total123:=total12.trans source two three heap storageIndex frame3 (by omega)
  have total1234:=total123.trans source three four heap keyBuffer frame4 (by omega)
  have total : PersistentMemoryFrame source post heap:=by
    rw [endpoint]
    exact total1234.put_global source four heap "bal_index" 0#64 (by decide)
  have extent : NormalHeapEffects.AtLeast (keyBuffer.toNat+64) post:=by
    obtain ⟨next,cell,lower,bound,aligned⟩:=extent4
    exact ⟨next,(indexOther _ (by decide)).trans cell,lower,bound,aligned⟩
  have cells : BalCells post heap accountIndex storageIndex keyBuffer:=by
    refine ⟨?_,?_,?_,?_,?_,owned1,owned2,owned3,owned4,context.aligned,context1.aligned,context2.aligned,context3.aligned,
      before1,before2,before3,extent⟩
    · exact (indexOther _ (by decide)).trans ((globals4 _ (by decide) (by decide)).trans
        ((globals3 _ (by decide) (by decide)).trans ((globals2 _ (by decide) (by decide)).trans accounts)))
    · exact (indexOther _ (by decide)).trans ((globals4 _ (by decide) (by decide)).trans ((globals3 _ (by decide) (by decide)).trans indexAccounts))
    · exact (indexOther _ (by decide)).trans ((globals4 _ (by decide) (by decide)).trans indexStorage)
    · exact (indexOther _ (by decide)).trans bufferCell
    · rw [endpoint]; exact putGlobal.lookup_same four "bal_index" 0#64
  refine ⟨runtime,total,?_,⟨accountIndex,storageIndex,keyBuffer,cells⟩,?_⟩
  · rw [endpoint]
    exact locals4.trans (locals3.trans (locals2.trans locals1))
  · intro key outside notHeap
    have different (name : MlS) (member : name∈balGlobals) : key≠name:=by
      intro same
      apply outside
      rw [same]
      exact member
    exact (indexOther _ (different _ (by simp [balGlobals]))).trans
      ((globals4 _ (different _ (by simp [balGlobals])) notHeap).trans
        ((globals3 _ (different _ (by simp [balGlobals])) notHeap).trans
          ((globals2 _ (different _ (by simp [balGlobals])) notHeap).trans
            (globals1 _ (different _ (by simp [balGlobals])) notHeap))))

end InitECandidate.Solver.Input.CurrentVerify.ExecuteBlock

#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecuteBlock.bal_execution

namespace InitECandidate.Solver.Input.CurrentVerify.ExecuteBlock
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

theorem BalCells.of_globals {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {accounts accountIndex storageIndex keyBuffer : BitVec 64}
    (ready : BalCells source accounts accountIndex storageIndex keyBuffer) (globals : post.globals=source.globals) :
    BalCells post accounts accountIndex storageIndex keyBuffer := by
  have cells (key : MlS) : post.globals.lookup key=source.globals.lookup key:=by rw [globals]
  obtain ⟨heap,cell,lower,bound,aligned⟩:=ready.heapAfter
  exact {ready with accountsCell:=(cells _).trans ready.accountsCell,accountIndexCell:=(cells _).trans ready.accountIndexCell, storageIndexCell:=(cells _).trans ready.storageIndexCell,keyBufferCell:=(cells _).trans ready.keyBufferCell, indexCell:=(cells _).trans ready.indexCell,heapAfter:=⟨heap,(cells _).trans cell,lower,bound,aligned⟩}

/-- Complete real BAL body return, including its actual five commands,
zero returned word, all assigned globals and complete older-memory frame. -/
theorem bal_body_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64)
    (context : BalHeap source heap) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source balBody=(some (.returned value),post)) :
    value=.val (.word 0#64) ∧ CurrentStartup.ArenaState post ∧ PersistentMemoryFrame source post heap ∧
      (∃ accountIndex storageIndex keyBuffer,BalCells post heap accountIndex storageIndex keyBuffer) ∧
      ∀ key : MlS,key∉balGlobals→key≠ofString "heap_ptr"→post.globals.lookup key=source.globals.lookup key := by
  rw [bal_body_shape] at normal
  obtain ⟨current,inner,execution,clock,continued⟩:=CallPrefix.normal_trace source post balActions balReturn value bal_prefix_never normal
  obtain ⟨runtime,frame,locals,⟨accountIndex,storageIndex,keyBuffer,cells⟩,kept⟩:=bal_execution source current heap context execution
  have returned : evaluateHOLFiniteState current balReturn=(some (.returned (.val (.word 0#64))),emptyLocalsHOLFinite current):=by
    simp [balReturn,evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact,sizeOfShapeWithContextHOL]
  have answer : value=.val (.word 0#64):=by
    simpa only [Option.some.injEq,PanSemResultExact.returned.injEq] using congrArg Prod.fst (continued.symm.trans returned)
  have physical:=execution.erase balReturn
  rw [normal,returned] at physical
  change LocalEffects.erase post=LocalEffects.erase current at physical
  have globals:=congrArg PanSemStateFiniteExact.globals physical
  change post.globals=current.globals at globals
  exact ⟨answer,runtime.of_frame physical,frame.of_erase source current source post heap rfl physical,
    ⟨accountIndex,storageIndex,keyBuffer,cells.of_globals globals⟩,by intro key outside notHeap; rw [globals]; exact kept key outside notHeap⟩

structure BalReady (input : Guest.InputBlob) (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer si record gasWord header be bo txs rcs logs buffer reqs rls returnBuffer accounts accountIndex storageIndex keyBuffer : BitVec 64)
    (boundary encoded : Nat) : Prop where
  physical : ReturnList input source pointer si record gasWord header be bo txs rcs logs buffer reqs rls returnBuffer boundary encoded
  cells : BalCells source accounts accountIndex storageIndex keyBuffer
  before : returnBuffer.toNat+128≤accounts.toNat

/-- None of BAL's five actual destination names belongs to the input,
heap or block-environment/output globals retained by the physical contract. -/
theorem protected_globals_outside_bal (key : MlS) (member : key∈keptExecutionGlobals) : key∉balGlobals := by
  simp only [keptExecutionGlobals,dataGlobals,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with (rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl)|(rfl|rfl)
  all_goals decide

/-- Actual ordinary BAL return restores the executor's own locals and
retains its full earlier state with the newly initialized BAL globals. -/
theorem bal_call_normal {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord header be bo txs rcs logs buffer reqs rls returnBuffer : BitVec 64} {boundary encoded : Nat}
    (ready : ReturnList input source pointer si record gasWord header be bo txs rcs logs buffer reqs rls returnBuffer boundary encoded)
    (normal : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "bal_init") [])=(none,post)) :
    ∃ accounts accountIndex storageIndex keyBuffer,
      BalReady input post pointer si record gasWord header be bo txs rcs logs buffer reqs rls returnBuffer accounts accountIndex storageIndex keyBuffer boundary encoded := by
  obtain ⟨heap,heapCell,lower,bound,aligned⟩:=ready.heapAfter
  have heapArena : AllocatedBytes.Arena heap 0:=⟨by have low:=ready.backing.lower; omega,by omega⟩
  let arena:=ready.requests.logs.arrays.output.environment.physical.data.arena
  obtain ⟨funded,values,actual,callee,shape,target,value,args,called,bodyRun,checked,endpoint,fields⟩:=CallNormal.ignored_data source post (ofString "bal_init") [] normal
  have valuesEq : values=[]:=by
    change some ([] : List (ValueHOL 64))=some values at args
    exact Option.some.inj args.symm
  subst values
  have bodyEq:=LocalEffects.lookup_body source.code (ofString "bal_init") [] balBody .one (bal_code source.code arena.code) [] actual callee shape called
  rw [bodyEq] at bodyRun
  have context : BalHeap (callEntryStateHOLFinite source callee) heap:=⟨arena.of_frame rfl,heapCell,heapArena,bound,aligned⟩
  obtain ⟨answer,runtime,frame,⟨accountIndex,storageIndex,keyBuffer,cells⟩,kept⟩:=bal_body_normal (callEntryStateHOLFinite source callee) target heap context value bodyRun
  have callerFrame : PersistentMemoryFrame source post heap:=frame.of_erase _ _ source post heap rfl (by rw [endpoint]; rfl)
  have globals : post.globals=target.globals:=by rw [endpoint]
  have physical:=ready.of_memory_frame lower callerFrame (by
    intro key member notHeap
    rw [globals]
    exact kept key (protected_globals_outside_bal key member) notHeap) (by
    intro key member
    rw [endpoint])
  exact ⟨heap,accountIndex,storageIndex,keyBuffer,physical,cells.of_globals globals,lower⟩

end InitECandidate.Solver.Input.CurrentVerify.ExecuteBlock

#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecuteBlock.BalCells.of_globals
#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecuteBlock.bal_body_normal
#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecuteBlock.protected_globals_outside_bal
#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecuteBlock.bal_call_normal

namespace InitECandidate.Solver.Input.CurrentVerify.ExecuteBlock
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

def balCaller : ProgHOL 64:=.call (some (none,none)) (ofString "bal_init") []
def balCallerActions : List CallPrefix.Action:=[.command balCaller,.command .skip]

theorem bal_caller_shape : beforeBalInit=CallPrefix.program balCallerActions beforeFirstSystem := by
  simp only [beforeBalInit,beforeReturnList,beforeRequests,beforeLogs,beforeArrays,afterCount,afterPayload,body,
    Guest.Software.guestFn_execute_block,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,
    CallPrefix.cutAt,CallPrefix.program,beforeFirstSystem,balCallerActions,balCaller] <;> trivial

theorem bal_caller_cost (code) (installed : OriginalCode.Installed code) :
    ClockCost.Bound code (CallPrefix.program balCallerActions .skip) 30 := by
  have callCost : ClockCost.Bound code balCaller 30:=assigned_body_cost code none (ofString "bal_init") [] [] balBody .one 29
    (bal_code code installed) (bal_cost code installed)
  exact ClockCost.sequence code _ _ 30 0 callCost
    (ClockCost.sequence code .skip .skip 0 0 (ClockCost.skip code) (ClockCost.skip code))

/-- Only real normal BAL/skip executions supply the final initialized state. -/
theorem bal_caller_reached {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord header be bo txs rcs logs buffer reqs rls returnBuffer : BitVec 64} {boundary encoded : Nat}
    (ready : ReturnList input source pointer si record gasWord header be bo txs rcs logs buffer reqs rls returnBuffer boundary encoded)
    (execution : CallPrefix.Execution source balCallerActions post) :
    ∃ accounts accountIndex storageIndex keyBuffer,
      BalReady input post pointer si record gasWord header be bo txs rcs logs buffer reqs rls returnBuffer accounts accountIndex storageIndex keyBuffer boundary encoded := by
  change CallPrefix.Execution source [.command balCaller,.command .skip] post at execution
  obtain ⟨current,call,remaining⟩:=execution.head
  have normal : evaluateHOLFiniteState source balCaller=(none,current):=by
    cases call with | command _ _ run=>exact run
  obtain ⟨accounts,accountIndex,storageIndex,keyBuffer,physical⟩:=bal_call_normal ready normal
  have skipped : evaluateHOLFiniteState current .skip=(none,post):=by
    have reached:=remaining.singleton
    cases reached with | command _ _ run=>exact run
  have same : post=current:=by simpa only [evaluateHOLFiniteState_skip] using (congrArg Prod.snd skipped).symm
  rw [same]
  exact ⟨accounts,accountIndex,storageIndex,keyBuffer,physical⟩

/-- Every actual BAL caller outcome either stops within30source ticks or
reaches the first mandatory system call with the complete physical result. -/
theorem bal_caller_trace {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord header be bo txs rcs logs buffer reqs rls returnBuffer : BitVec 64} {boundary encoded : Nat}
    (ready : ReturnList input source pointer si record gasWord header be bo txs rcs logs buffer reqs rls returnBuffer boundary encoded)
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source beforeBalInit=(outcome,post)) :
    source.clock-post.clock≤30 ∨ ∃ current inner accounts accountIndex storageIndex keyBuffer,
      BalReady input current pointer si record gasWord header be bo txs rcs logs buffer reqs rls returnBuffer accounts accountIndex storageIndex keyBuffer boundary encoded ∧
      current.clock≤source.clock ∧ source.clock-current.clock≤30 ∧ CallPrefix.ScopeFrame post inner ∧
      evaluateHOLFiniteState current beforeFirstSystem=(outcome,inner) := by
  rw [bal_caller_shape] at run
  rcases CallPrefix.priced_frame_trace source post balCallerActions beforeFirstSystem 30
    (bal_caller_cost source.code ready.requests.logs.arrays.output.environment.physical.data.arena.code source rfl) outcome run with stopped|reached
  · exact Or.inl stopped.1
  · obtain ⟨current,inner,execution,forward,price,scope,rest⟩:=reached
    obtain ⟨accounts,accountIndex,storageIndex,keyBuffer,physical⟩:=bal_caller_reached ready execution
    exact Or.inr ⟨current,inner,accounts,accountIndex,storageIndex,keyBuffer,physical,forward,price,scope,rest⟩

/-- Entire unchanged executor initialization, connected through the actual
first system-call continuation with complete input, list and BAL ownership. -/
theorem body_bal_ready_trace {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord header be : BitVec 64} {boundary encoded : Nat}
    (data : Data input source pointer si record gasWord boundary)
    (ready : RunAttempt.BlockEnvBuffer input (declarationEntry source record) pointer si record gasWord header be boundary encoded)
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source body=(outcome,post)) :
    source.clock-post.clock≤161 ∨ ∃ current inner bo txs rcs logs buffer reqs rls returnBuffer accounts accountIndex storageIndex keyBuffer,
      BalReady input current pointer si record gasWord header be bo txs rcs logs buffer reqs rls returnBuffer accounts accountIndex storageIndex keyBuffer boundary encoded ∧
      current.clock≤source.clock ∧ source.clock-current.clock≤161 ∧ post.clock=inner.clock ∧
      evaluateHOLFiniteState current beforeFirstSystem=(outcome,inner) := by
  rcases body_return_list_trace data ready outcome run with stopped|reached
  · exact Or.inl (by omega)
  · obtain ⟨before,target,bo,txs,rcs,logs,buffer,reqs,rls,returnBuffer,physical,forward,price,endpoint,continued⟩:=reached
    rcases bal_caller_trace physical outcome continued with stopped|reached
    · exact Or.inl (by rw [endpoint]; omega)
    · obtain ⟨current,inner,accounts,accountIndex,storageIndex,keyBuffer,physical,balForward,balPrice,scope,rest⟩:=reached
      exact Or.inr ⟨current,inner,bo,txs,rcs,logs,buffer,reqs,rls,returnBuffer,accounts,accountIndex,storageIndex,keyBuffer,
        physical,by omega,by omega,endpoint.trans scope.clock,rest⟩

end InitECandidate.Solver.Input.CurrentVerify.ExecuteBlock

#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecuteBlock.bal_caller_shape
#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecuteBlock.bal_caller_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecuteBlock.bal_caller_reached
#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecuteBlock.bal_caller_trace
#print axioms InitECandidate.Solver.Input.CurrentVerify.ExecuteBlock.body_bal_ready_trace
