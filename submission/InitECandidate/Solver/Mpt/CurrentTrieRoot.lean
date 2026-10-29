import InitECandidate.Solver.Arenas.MarkCost
import InitECandidate.Solver.Arenas.ScratchScope
import InitECandidate.Solver.Input.CurrentDomain
import InitECandidate.Solver.Input.OriginalEntry
import InitECandidate.Solver.Input.OriginalCode
import InitECandidate.Solver.Input.CurrentStartup.ArenaState
import InitECandidate.Solver.Input.ClockCostCurrentCall
import InitECandidate.Solver.Input.IgnoredCallNormal
import InitECandidate.Solver.Mpt.Fail
import InitECandidate.Solver.Input.ClockCostDeclaredReached
import InitECandidate.Solver.Input.NoReturnIgnored
import InitECandidate.Solver.Input.NormalWordDeclaration
import InitECandidate.Solver.Input.ClockCostScopedReached
import InitECandidate.Solver.Input.WordEnvironment
import InitECandidate.Solver.Mpt.TrieCacheMutation
import InitECandidate.Solver.WitnessRadix.CopyGeneralCost
import InitECandidate.Solver.Input.WordPairEnvironment
import InitECandidate.Solver.Input.NoFallthrough
import InitECandidate.Solver.WitnessRadix.CopyNormalCall
import InitECandidate.Solver.Input.MemoryMetadata
import InitECandidate.Solver.Input.SequenceReturned
import InitECandidate.Solver.Input.ReturnNormal

namespace InitECandidate.Solver.Mpt.CurrentNodeRlpFill
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix Input
open Flapjack.Basis.Pure.MlString QueryBranch

def body : ProgHOL 64:=match Guest.Software.guestFn__node_rlp_fill with | .function fn=>progToHOL fn.body | _=>.skip
def formals : List (MlS×ShapeHOL):=[(ofString "node",.one)]
def afterMark : ProgHOL 64:=match body with | .decCall _ _ _ _ rest=>rest | _=>.skip
def afterFrame : ProgHOL 64:=match afterMark with | .decCall _ _ _ _ rest=>rest | _=>.skip
def afterFirstStore : ProgHOL 64:=match afterFrame with | .seq _ rest=>rest | _=>.skip
def firstAddress : ExpHOL 64:=.op .add [localVar "fr",.const 0#64]

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "_node_rlp_fill")=some (formals,body,.one) := by
  have checked:=OriginalCode.indexed code installed 258 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.Software.guestFn__node_rlp_fill) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,formals,body,
    Guest.Software.guestFn__node_rlp_fill,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

set_option maxRecDepth 100000 in
theorem body_shape : body=.decCall (ofString "mark") .one (ofString "scratch_mark") [] afterMark := by
  simp only [body,afterMark,Guest.Software.guestFn__node_rlp_fill,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil]

set_option maxRecDepth 100000 in
theorem after_mark_shape : afterMark=.decCall (ofString "fr") .one (ofString "scratch_alloc") [.const 48#64] afterFrame := by
  simp only [body,afterMark,afterFrame,Guest.Software.guestFn__node_rlp_fill,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil]

set_option maxRecDepth 100000 in
theorem first_store_shape : afterFrame=.seq (.store firstAddress (.const 0#64)) afterFirstStore := by
  simp only [body,afterMark,afterFrame,afterFirstStore,firstAddress,addConst,localVar,
    Guest.Software.guestFn__node_rlp_fill,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil]

/-- This actual helper's first frame store lies below the compiler's
ordinary memory domain. The rest of the encoder is therefore unreachable
from the real startup scratch cursor. -/
theorem frame_error (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (domain : source.memaddrs=InitE.ordinaryDomain)
    (fr : source.locals.lookup (ofString "fr")=some (.val (.word 2701127632#64))) :
    evaluateHOLFiniteState source afterFrame=(some .error,source) := by
  have addressRead : eval source firstAddress=some (.val (.word 2701127632#64)):=by
    simp [eval,firstAddress,addConst,localVar,evalHOLExact,evalListHOLExact,toExact,fr,valueIsWord,valueWord,wordOpHOL,wordOp]
  have store:=CurrentDomain.store_below_base_error source firstAddress (.const 0#64) 2701127632#64 0#64 domain (by decide) addressRead rfl
  rw [first_store_shape,evaluateHOLFiniteState_seq_line780,store]

theorem after_mark_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (installed : OriginalCode.Installed source.code) (domain : source.memaddrs=InitE.ordinaryDomain)
    (scratch : source.globals.lookup (ofString "scratch_ptr")=some (.val (.word 2701127680#64)))
    (frame : source.globals.lookup (ofString "frame_mem_ptr")=some (.val (.word 2688618496#64))) :
    (evaluateHOLFiniteState source afterMark).1=some (if source.clock=0 then .timeOut else .error) ∧
      (evaluateHOLFiniteState source afterMark).2.clock=source.clock-1 := by
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) [.const 48#64]=some [.val (.word 48#64)]:=rfl
  obtain ⟨callee,called,nCell⟩:=CallNormal.unary_environment source.code.lookup (ofString "scratch_alloc") "n" (Arenas.body .down) 48#64 (Arenas.original_code source.code installed .down)
  by_cases zero : source.clock=0
  · rw [after_mark_shape,evaluateHOLFiniteState_decCall_fixClockRewrite]
    simp only [args,called,if_pos zero]
    exact ⟨trivial,by change source.clock=source.clock-1; omega⟩
  · have executed:=Arenas.call_execute source .down "fr" [.const 48#64] afterFrame 2701127680#64 2688618496#64 48#64
      args (Arenas.original_code source.code installed .down) scratch frame (by decide) (by change 2688618496+48≤2701127680; decide) (by omega)
    let ready:=bind (Arenas.post {source with clock:=source.clock-1} .down 2701127680#64 48#64) "fr" 2701127632#64
    have calledEq : Arenas.resultWord .down 2701127680#64 48#64=2701127632#64:=by decide
    simp only [calledEq] at executed
    change evaluateHOLFiniteState source (.decCall (ofString "fr") .one (ofString "scratch_alloc") [.const 48#64] afterFrame)=
      (let output:=evaluateHOLFiniteState ready afterFrame;(output.1,restore source "fr" output.2)) at executed
    have failed:=frame_error ready domain (bind_lookup_same _ _ _)
    simp only [Arenas.functionName] at executed
    rw [after_mark_shape,executed,failed,if_neg zero]
    exact ⟨rfl,rfl⟩

/-- All clocks and outcomes are included. The actual mark/allocation
prefix costs at most two source ticks and never returns an encoded node. -/
theorem body_stops (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (installed : OriginalCode.Installed source.code) (domain : source.memaddrs=InitE.ordinaryDomain)
    (scratch : source.globals.lookup (ofString "scratch_ptr")=some (.val (.word 2701127680#64)))
    (frame : source.globals.lookup (ofString "frame_mem_ptr")=some (.val (.word 2688618496#64))) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤2 ∧
      ∀ value,(evaluateHOLFiniteState source body).1≠some (.returned value) := by
  by_cases zero : source.clock=0
  · have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) []=some []:=rfl
    have lookup:=Arenas.Scratch.mark_code source.code installed
    obtain ⟨callee,called,locals⟩:=CodeEnvironment.finite_lookup source.code.lookup (ofString "scratch_mark") [] (Arenas.markBody .down) (fun _=>none) .one
      (by simp [lookupCodeHOLExact,lookup])
    rw [body_shape,evaluateHOLFiniteState_decCall_fixClockRewrite]
    simp only [args,called,if_pos zero]
    exact ⟨by change source.clock-source.clock≤2; omega,by intro value equal; cases equal⟩
  · let ready:=bind {source with clock:=source.clock-1} "mark" 2701127680#64
    have marked:=Arenas.mark_call source .down "mark" 2701127680#64 afterMark (Arenas.Scratch.mark_code source.code installed) scratch (by omega)
    simp only [Arenas.markName] at marked
    have tail:=after_mark_execute ready installed domain scratch frame
    rw [body_shape,marked]
    refine ⟨?_,?_⟩
    · change source.clock-(evaluateHOLFiniteState ready afterMark).2.clock≤2
      rw [tail.2]
      change source.clock-(source.clock-1-1)≤2
      omega
    · intro value
      change (evaluateHOLFiniteState ready afterMark).1≠some (.returned value)
      rw [tail.1]
      split <;> simp

theorem call_stops (source : PanSemStateFiniteExact 64 Guest.HostMemory) (node : BitVec 64)
    (arguments : List (ExpHOL 64)) (arena : CurrentStartup.ArenaState source)
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=some [.val (.word node)]) :
    source.clock-(evaluateHOLFiniteState source (.call (some (none,none)) (ofString "_node_rlp_fill") arguments)).2.clock≤3 ∧
      (evaluateHOLFiniteState source (.call (some (none,none)) (ofString "_node_rlp_fill") arguments)).1≠none := by
  obtain ⟨callee,called,nodeCell⟩:=CallNormal.unary_environment source.code.lookup (ofString "_node_rlp_fill") "node" body node (original_code source.code arena.code)
  have stopped:=body_stops (callEntryStateHOLFinite source callee) arena.code arena.domain arena.scratch arena.frame
  refine ⟨ClockCost.call_current source (some none) (ofString "_node_rlp_fill") arguments _ body callee .one 2 args called stopped.1,?_⟩
  intro normal
  obtain ⟨funded,target,returned,run⟩:=CallNormal.ignored_callee_return source _ (ofString "_node_rlp_fill") arguments _ body callee .one args called (Prod.ext normal rfl)
  exact stopped.2 returned (congrArg Prod.fst run)

end InitECandidate.Solver.Mpt.CurrentNodeRlpFill

#print axioms InitECandidate.Solver.Mpt.CurrentNodeRlpFill.original_code
#print axioms InitECandidate.Solver.Mpt.CurrentNodeRlpFill.frame_error
#print axioms InitECandidate.Solver.Mpt.CurrentNodeRlpFill.after_mark_execute
#print axioms InitECandidate.Solver.Mpt.CurrentNodeRlpFill.body_stops
#print axioms InitECandidate.Solver.Mpt.CurrentNodeRlpFill.call_stops

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

theorem fill_tail_stops (source : PanSemStateFiniteExact 64 Guest.HostMemory) (node : BitVec 64)
    (arena : CurrentStartup.ArenaState source)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node))) :
    source.clock-(evaluateHOLFiniteState source fillAndReturn).2.clock≤3 ∧
      ∀ value,(evaluateHOLFiniteState source fillAndReturn).1≠some (.returned value) := by
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) [localVar "node"]=some [.val (.word node)]:=by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,nodeCell]
  have stops:=CurrentNodeRlpFill.call_stops source node [localVar "node"] arena args
  change source.clock-(evaluateHOLFiniteState source fillCall).2.clock≤3 ∧ (evaluateHOLFiniteState source fillCall).1≠none at stops
  rw [shapes.2.2,stopped_sequence_eq source fillCall returnFooter stops.2]
  exact ⟨stops.1,fun value=>NoReturn.ignored_call _ _ source value⟩

theorem after_cache_stops (source : PanSemStateFiniteExact 64 Guest.HostMemory) (node tag : BitVec 64)
    (arena : CurrentStartup.ArenaState source)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node)))
    (cached : source.locals.lookup (ofString "cached")=some (.val (.word 0#64)))
    (mapped : source.memaddrs node) (stored : source.memory node=.word tag) :
    source.clock-(evaluateHOLFiniteState source afterCache).2.clock≤3 ∧
      ∀ value,(evaluateHOLFiniteState source afterCache).1≠some (.returned value) := by
  have tagRead : eval source tagTest=some (.val (.word (if tag=0#64 then 1#64 else 0#64))):=by
    simp [eval,tagTest,nodeField,localVar,evalHOLExact,evalListHOLExact,toExact,nodeCell,valueIsWord,valueWord,wordOpHOL,wordOp,
      memLoadHOLExact,isWfShapeExactHOL,mapped,stored,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  have failStops : (evaluateHOLFiniteState source failCall).1≠none:=by
    intro normal
    exact Fail.call_not_normal source _ arena.code [.const 2#64] (Prod.ext normal rfl)
  have failPrice:=Fail.call_price source.code arena.code [.const 2#64] source rfl
  rw [after_cache_selected source cached,shapes.2.1]
  by_cases zero : tag=0#64
  · have guard : evaluateHOLFiniteState source (.ite tagTest failCall .skip)=evaluateHOLFiniteState source failCall:=by
      rw [evaluateHOLFiniteState_ite]
      simp only [eval] at tagRead
      rw [tagRead,if_pos zero]
      simp
    have selected : evaluateHOLFiniteState source (.seq (.ite tagTest failCall .skip) fillAndReturn)=evaluateHOLFiniteState source (.seq failCall fillAndReturn):=by
      rw [evaluateHOLFiniteState_seq_line780,guard,←evaluateHOLFiniteState_seq_line780]
    rw [selected,stopped_sequence_eq source failCall fillAndReturn failStops]
    exact ⟨Nat.le_trans failPrice (by decide),fun value=>NoReturn.ignored_call _ _ source value⟩
  · have guard : evaluateHOLFiniteState source (.ite tagTest failCall .skip)=(none,source):=by
      rw [evaluateHOLFiniteState_ite]
      simp only [eval] at tagRead
      rw [tagRead,if_neg zero]
      simp [evaluateHOLFiniteState_skip]
    rw [evaluateHOLFiniteState_seq_line780,guard]
    exact fill_tail_stops source node arena nodeCell

/-- At a true uncached node, the actual encoder either rejects its hash
tag or reaches the short, failing scratch-frame prefix. There is no encoding
or future successful helper hypothesis. -/
theorem body_stops (source : PanSemStateFiniteExact 64 Guest.HostMemory) (node tag : BitVec 64)
    (arena : CurrentStartup.ArenaState source)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node)))
    (mapped : source.memaddrs node) (stored : source.memory node=.word tag)
    (cacheMapped : source.memaddrs (node+8#64)) (cacheZero : source.memory (node+8#64)=.word 0#64) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤3 ∧
      ∀ value,(evaluateHOLFiniteState source body).1≠some (.returned value) := by
  have read : eval source (nodeField 8#64)=some (.val (.word 0#64)):=by
    simp [eval,nodeField,localVar,evalHOLExact,evalListHOLExact,toExact,nodeCell,valueIsWord,valueWord,wordOpHOL,wordOp,
      memLoadHOLExact,isWfShapeExactHOL,cacheMapped,cacheZero]
  let ready:=WitnessRadix.QueryBranch.bind source "cached" 0#64
  have readyNode : ready.locals.lookup (ofString "node")=some (.val (.word node)):=
    (bind_lookup_other source "cached" "node" 0#64 (by decide)).trans nodeCell
  have tail:=after_cache_stops ready node tag ⟨arena.scratch,arena.frame,arena.domain,arena.code⟩ readyNode (bind_lookup_same _ _ _) mapped stored
  refine ⟨?_,?_⟩
  · rw [shapes.1]
    exact ClockCost.declared_current source "cached" (nodeField 8#64) 0#64 afterCache 3 read tail.1
  · intro value normal
    obtain ⟨inner,continued,endpoint⟩:=declaration_return_word source (evaluateHOLFiniteState source body).2 "cached" (nodeField 8#64) 0#64 afterCache value read
      (by rw [←shapes.1]; exact Prod.ext normal rfl)
    exact tail.2 value (congrArg Prod.fst continued)

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

theorem rlp_call_stops (source : PanSemStateFiniteExact 64 Guest.HostMemory) (node tag : BitVec 64)
    (arena : CurrentStartup.ArenaState source)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node)))
    (mapped : source.memaddrs node) (stored : source.memory node=.word tag)
    (cacheMapped : source.memaddrs (node+8#64)) (cacheZero : source.memory (node+8#64)=.word 0#64) :
    source.clock-(evaluateHOLFiniteState source rlpCall).2.clock≤4 ∧
      ∀ value,(evaluateHOLFiniteState source rlpCall).1≠some (.returned value) := by
  obtain ⟨callee,called,nodeLocal⟩:=word_environment source.code.lookup (ofString "node_rlp") (ofString "node") NodeRlp.body (.comb [.one,.one]) node (NodeRlp.original_code source.code arena.code)
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) [localVar "node"]=some [.val (.word node)]:=by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,nodeCell]
  have stopped:=NodeRlp.body_stops (callEntryStateHOLFinite source callee) node tag ⟨arena.scratch,arena.frame,arena.domain,arena.code⟩ nodeLocal mapped stored cacheMapped cacheZero
  rw [shapes.2]
  refine ⟨?_,?_⟩
  · exact ClockCost.scoped_reached_current source "r" (.comb [.one,.one]) (ofString "node_rlp") [localVar "node"] _
      NodeRlp.body afterRlp callee (.comb [.one,.one]) 3 0 args called stopped.1
      (by intro target returned run checked; exact (stopped.2 returned (congrArg Prod.fst run)).elim)
  · intro value normal
    obtain ⟨funded,target,returned,inner,run,checked,continued,endpoint⟩:=CallNormal.scoped_normal source _ "r" (.comb [.one,.one])
      (ofString "node_rlp") [localVar "node"] _ NodeRlp.body afterRlp callee (.comb [.one,.one]) args called value (Prod.ext normal rfl)
    exact stopped.2 returned (congrArg Prod.fst run)

/-- The actual node_hash never reaches allocation or Keccak on the
uncached root returned by the real insertion loop. -/
theorem body_stops (source : PanSemStateFiniteExact 64 Guest.HostMemory) (node tag : BitVec 64)
    (arena : CurrentStartup.ArenaState source)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node)))
    (mapped : source.memaddrs node) (stored : source.memory node=.word tag)
    (rlpMapped : source.memaddrs (node+8#64)) (rlpZero : source.memory (node+8#64)=.word 0#64)
    (hashMapped : source.memaddrs (node+24#64)) (hashZero : source.memory (node+24#64)=.word 0#64) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤4 ∧
      ∀ value,(evaluateHOLFiniteState source body).1≠some (.returned value) := by
  have read : eval source (NodeRlp.nodeField 24#64)=some (.val (.word 0#64)):=by
    simp [eval,NodeRlp.nodeField,localVar,evalHOLExact,evalListHOLExact,toExact,nodeCell,valueIsWord,valueWord,wordOpHOL,wordOp,
      memLoadHOLExact,isWfShapeExactHOL,hashMapped,hashZero]
  let ready:=WitnessRadix.QueryBranch.bind source "cached" 0#64
  have readyNode : ready.locals.lookup (ofString "node")=some (.val (.word node)):=
    (bind_lookup_other source "cached" "node" 0#64 (by decide)).trans nodeCell
  have tail:=rlp_call_stops ready node tag ⟨arena.scratch,arena.frame,arena.domain,arena.code⟩ readyNode mapped stored rlpMapped rlpZero
  have selected:=after_cache_selected ready (bind_lookup_same _ _ _)
  rw [←selected] at tail
  refine ⟨?_,?_⟩
  · rw [shapes.1]
    exact ClockCost.declared_current source "cached" (NodeRlp.nodeField 24#64) 0#64 afterCache 4 read tail.1
  · intro value normal
    obtain ⟨inner,continued,endpoint⟩:=declaration_return_word source (evaluateHOLFiniteState source body).2 "cached" (NodeRlp.nodeField 24#64) 0#64 afterCache value read
      (by rw [←shapes.1]; exact Prod.ext normal rfl)
    exact tail.2 value (congrArg Prod.fst continued)

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

/-- Actual scalar root entry, owned output/empty-hash buffers and the
same retained physical graph. Caller reachability must establish these facts. -/
structure Entry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (m out empty root : BitVec 64) (lower upper : Nat) where
  arena : CurrentStartup.ArenaState source
  mCell : source.locals.lookup (ofString "m")=some (.val (.word m))
  outCell : source.locals.lookup (ofString "out")=some (.val (.word out))
  headerMapped : source.memaddrs m
  rootStored : source.memory m=.word root
  emptyGlobal : source.globals.lookup (ofString "empty_trie_root")=some (.val (.word empty))
  emptyArena : AllocatedBytes.Arena empty 32
  outArena : AllocatedBytes.Arena out 32
  graph : TrieWalk.Graph source.memory source.memaddrs
  member : graph.valid root
  regions : graph.Regions lower upper
  uncached : TrieWalk.Uncached source.memory root

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

def Entry.after_root {source : PanSemStateFiniteExact 64 Guest.HostMemory} {m out empty root : BitVec 64} {lower upper : Nat}
    (data : Entry source m out empty root lower upper) : Entry (WitnessRadix.QueryBranch.bind source "root" root) m out empty root lower upper := by
  exact {data with
    arena:=⟨data.arena.scratch,data.arena.frame,data.arena.domain,data.arena.code⟩
    mCell:=(bind_lookup_other source "root" "m" root (by decide)).trans data.mCell
    outCell:=(bind_lookup_other source "root" "out" root (by decide)).trans data.outCell }

theorem empty_cost {source : PanSemStateFiniteExact 64 Guest.HostMemory} {m out empty root : BitVec 64} {lower upper : Nat}
    (data : Entry source m out empty root lower upper) :
    source.clock-(evaluateHOLFiniteState source emptyBranch).2.clock≤5 := by
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) copyArguments=some (CopyGeneral.values out empty 32):=by
    simp [copyArguments,CopyGeneral.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,data.outCell,data.emptyGlobal]
  have price:=CopyGeneral.call_cost_arena source copyArguments empty out 32 args (CopyGeneral.original_code source.code data.arena.code)
    data.arena.domain data.emptyArena data.outArena
  have bound:=CopyGeneral.cost_word_multiple empty out 32 (by decide)
  have copied : source.clock-(evaluateHOLFiniteState source copyCall).2.clock≤5:=by
    change source.clock-(evaluateHOLFiniteState source copyCall).2.clock≤CopyGeneral.cost empty out 32+1 at price
    omega
  rw [shapes.2.2.1]
  exact ClockCost.sequence_current source copyCall (.return (.const 0#64)) 5 0 copied (ClockCost.returned source.code _)

theorem hash_call_stops {source : PanSemStateFiniteExact 64 Guest.HostMemory} {m out empty root : BitVec 64} {lower upper : Nat}
    (data : Entry source m out empty root lower upper) (active : root≠0#64)
    (rootCell : source.locals.lookup (ofString "root")=some (.val (.word root))) :
    source.clock-(evaluateHOLFiniteState source hashCall).2.clock≤5 ∧
      ∀ value,(evaluateHOLFiniteState source hashCall).1≠some (.returned value) := by
  obtain ⟨mapped,stored⟩:=data.graph.header root data.member active
  obtain ⟨above,allocation,aligned,before⟩:=data.regions root data.member active
  have size:=TrieWalk.nodeBytes_bounds (wordAt source.memory root)
  obtain clean|⟨rlpZero,hashZero⟩:=data.uncached
  · exact (active clean).elim
  have rlpMapped : source.memaddrs (root+8#64):=AllocatedBytes.word_mapped source root _ 8 data.arena.domain allocation (by omega) aligned (by decide)
  have hashMapped : source.memaddrs (root+24#64):=AllocatedBytes.word_mapped source root _ 24 data.arena.domain allocation (by omega) aligned (by decide)
  obtain ⟨callee,called,nodeLocal⟩:=CallNormal.unary_environment source.code.lookup (ofString "node_hash") "node" NodeHash.body root (NodeHash.original_code source.code data.arena.code)
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) [localVar "root"]=some [.val (.word root)]:=by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,rootCell]
  have stopped:=NodeHash.body_stops (callEntryStateHOLFinite source callee) root (wordAt source.memory root)
    ⟨data.arena.scratch,data.arena.frame,data.arena.domain,data.arena.code⟩ nodeLocal mapped stored rlpMapped rlpZero hashMapped hashZero
  rw [shapes.2.2.2]
  refine ⟨?_,?_⟩
  · exact ClockCost.scoped_reached_current source "h" .one (ofString "node_hash") [localVar "root"] _ NodeHash.body afterHash callee .one 4 0 args called stopped.1
      (by intro target returned run checked; exact (stopped.2 returned (congrArg Prod.fst run)).elim)
  · intro value normal
    obtain ⟨funded,target,returned,inner,run,checked,continued,endpoint⟩:=CallNormal.scoped_normal source _ "h" .one
      (ofString "node_hash") [localVar "root"] _ NodeHash.body afterHash callee .one args called value (Prod.ext normal rfl)
    exact stopped.2 returned (congrArg Prod.fst run)

theorem after_root_cost {source : PanSemStateFiniteExact 64 Guest.HostMemory} {m out empty root : BitVec 64} {lower upper : Nat}
    (data : Entry source m out empty root lower upper)
    (rootCell : source.locals.lookup (ofString "root")=some (.val (.word root))) :
    source.clock-(evaluateHOLFiniteState source afterRoot).2.clock≤5 := by
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
    exact empty_cost data
  · simp only [if_neg zero,if_pos rfl,evaluateHOLFiniteState_skip]
    exact (hash_call_stops data zero rootCell).1

/-- Both real branches, every clock and stopped outcome of current265.
This local physical-entry bound is five body source ticks. -/
theorem body_cost {source : PanSemStateFiniteExact 64 Guest.HostMemory} {m out empty root : BitVec 64} {lower upper : Nat}
    (data : Entry source m out empty root lower upper) : source.clock-(evaluateHOLFiniteState source body).2.clock≤5 := by
  have read : eval source rootExpression=some (.val (.word root)):=by
    simp [eval,rootExpression,localVar,evalHOLExact,evalListHOLExact,toExact,data.mCell,valueIsWord,valueWord,wordOpHOL,wordOp,
      memLoadHOLExact,isWfShapeExactHOL,data.headerMapped,data.rootStored]
  rw [shapes.1]
  exact ClockCost.declared_current source "root" rootExpression root afterRoot 5 read (after_root_cost data.after_root (bind_lookup_same _ _ _))

theorem after_root_select (source : PanSemStateFiniteExact 64 Guest.HostMemory) (root : BitVec 64)
    (rootCell : source.locals.lookup (ofString "root")=some (.val (.word root))) :
    evaluateHOLFiniteState source afterRoot=
      (if root=0#64 then evaluateHOLFiniteState source emptyBranch else evaluateHOLFiniteState source hashCall) := by
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

/-- Every actual normal root return comes from the empty-root copy and
retains the real nonlocal state and all words outside its owned destination.
The observed run, rather than a future success premise, selects that branch. -/
theorem body_normal {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {m out empty root : BitVec 64} {lower upper : Nat}
    (data : Entry source m out empty root lower upper) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source body=(some (.returned value),target)) :
    root=0#64 ∧ value=.val (.word 0#64) ∧ MemoryMetadata.erase target=MemoryMetadata.erase source ∧
      ∀ query : BitVec 64,CopyGeneral.Away out query 32→target.memory query=source.memory query := by
  have read : eval source rootExpression=some (.val (.word root)):=by
    simp [eval,rootExpression,localVar,evalHOLExact,evalListHOLExact,toExact,data.mCell,valueIsWord,valueWord,wordOpHOL,wordOp,
      memLoadHOLExact,isWfShapeExactHOL,data.headerMapped,data.rootStored]
  rw [shapes.1] at normal
  obtain ⟨inner,continued,endpoint⟩:=declaration_return_word source target "root" rootExpression root afterRoot value read normal
  let ready:=WitnessRadix.QueryBranch.bind source "root" root
  have readyData:=data.after_root
  have rootCell : ready.locals.lookup (ofString "root")=some (.val (.word root)):=bind_lookup_same _ _ _
  have zero : root=0#64:=by
    by_contra active
    have stopped:=hash_call_stops readyData active rootCell
    rw [after_root_select ready root rootCell,if_neg active] at continued
    exact stopped.2 value (congrArg Prod.fst continued)
  rw [after_root_select ready root rootCell,if_pos zero,shapes.2.2.1] at continued
  obtain ⟨copied,copyRun,footerRun⟩:=sequence_returned ready inner copyCall (.return (.const 0#64)) value
    (fun returned=>NoReturn.ignored_call (ofString "memcpy") copyArguments ready returned) continued
  obtain ⟨observed,innerEq⟩:=return_normal copied inner (.const 0#64) value footerRun
  have answer : value=.val (.word 0#64):=Option.some.inj (observed.symm.trans rfl)
  have args : evalListHOLFinite ready (h:=fun query=>Classical.propDecidable (ready.memaddrs query)) copyArguments=some (CopyGeneral.values out empty 32):=by
    have outCell : ready.locals.lookup (ofString "out")=some (.val (.word out)):=readyData.outCell
    have emptyCell : ready.globals.lookup (ofString "empty_trie_root")=some (.val (.word empty)):=readyData.emptyGlobal
    simp [copyArguments,CopyGeneral.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,outCell,emptyCell]
  have copiedNormal:=CopyGeneral.call_normal ready copied copyArguments empty out 32 args (CopyGeneral.original_code ready.code readyData.arena.code)
    (AllocatedBytes.copy_mapped ready empty out 32 readyData.arena.domain data.emptyArena data.outArena) (by decide) copyRun
  refine ⟨zero,answer,?_,?_⟩
  · rw [endpoint,innerEq,copiedNormal.2.2]
    rfl
  · intro query away
    rw [endpoint,innerEq,copiedNormal.2.2]
    exact CopyGeneral.call_memory_away ready empty out query 32 away

end Root
end InitECandidate.Solver.Mpt.CurrentTrieRoot

#print axioms InitECandidate.Solver.Mpt.CurrentTrieRoot.NodeRlp.original_code
#print axioms InitECandidate.Solver.Mpt.CurrentTrieRoot.NodeRlp.fill_tail_stops
#print axioms InitECandidate.Solver.Mpt.CurrentTrieRoot.NodeRlp.after_cache_stops
#print axioms InitECandidate.Solver.Mpt.CurrentTrieRoot.NodeRlp.body_stops
#print axioms InitECandidate.Solver.Mpt.CurrentTrieRoot.NodeHash.original_code
#print axioms InitECandidate.Solver.Mpt.CurrentTrieRoot.NodeHash.rlp_call_stops
#print axioms InitECandidate.Solver.Mpt.CurrentTrieRoot.NodeHash.body_stops
#print axioms InitECandidate.Solver.Mpt.CurrentTrieRoot.Root.original_code
#print axioms InitECandidate.Solver.Mpt.CurrentTrieRoot.Root.hash_call_stops
#print axioms InitECandidate.Solver.Mpt.CurrentTrieRoot.Root.body_cost
#print axioms InitECandidate.Solver.Mpt.CurrentTrieRoot.Root.body_normal
