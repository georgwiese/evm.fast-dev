import InitECandidate.Solver.Mpt.FailGuardReturn
import InitECandidate.Solver.CurrentKeccak.Cost
import InitECandidate.Solver.CurrentKeccak.Call
import InitECandidate.Solver.WitnessRadix.AllocationCallNormal
import InitECandidate.Solver.WitnessRadix.AllocationCost
import InitECandidate.Solver.Input.ClockCostSequenceReached
import InitECandidate.Solver.Input.NormalWordDeclaration
import InitECandidate.Solver.Input.WordPairEnvironment
import InitECandidate.Solver.Input.LoadWord
import InitECandidate.Solver.WitnessRadix.BindingLookup
import InitECandidate.Solver.Input.ReturnFactsScalar
import InitECandidate.Solver.Input.ReturnFactsScopedAny
import InitECandidate.Solver.Input.ByteStoreClock

namespace InitECandidate.Solver.Mpt.NodeHashCached
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix Input
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def body : ProgHOL 64:=match Guest.Software.guestFn_node_hash_cached with | .function fn=>progToHOL fn.body | _=>.skip
def formals : List (MlS×ShapeHOL):=[(ofString "node",.one)]
def readAt (offset : Nat) : ExpHOL 64:=.load .one (.op .add [localVar "node",.const (BitVec.ofNat 64 offset)])
def afterCached : ProgHOL 64:=match body with | .dec _ _ _ rest=>rest | _=>.skip
def cachedGuard : ProgHOL 64:=match afterCached with | .seq first _=>first | _=>.skip
def afterGuard : ProgHOL 64:=match afterCached with | .seq _ rest=>rest | _=>.skip
def missingTest : ExpHOL 64:=.cmp .equal (readAt 8) (.const 0#64)
def allocation : ProgHOL 64:=match afterGuard with | .seq _ rest=>rest | _=>.skip
def afterAllocation : ProgHOL 64:=match allocation with | .decCall _ _ _ _ rest=>rest | _=>.skip
def hashArguments : List (ExpHOL 64):=[readAt 8,readAt 16,localVar "h"]
def hashCall : ProgHOL 64:=.call (some (none,none)) (ofString "keccak256") hashArguments
def footer : ProgHOL 64:=.seq (.store (.op .add [localVar "node",.const 24#64]) (localVar "h")) (.return (localVar "h"))

set_option maxRecDepth 100000 in
theorem shapes : body=.dec (ofString "cached") .one (readAt 24) afterCached ∧
    afterCached=.seq cachedGuard afterGuard ∧
    cachedGuard=.ite (.cmp .notEqual (localVar "cached") (.const 0#64)) (.return (localVar "cached")) .skip ∧
    afterGuard=.seq (.ite missingTest (.call (some (none,none)) (ofString "mpt_fail") [.const 13#64]) .skip) allocation ∧
    allocation=.decCall (ofString "h") .one (ofString "alloc") [.const 32#64] afterAllocation ∧
    afterAllocation=.seq hashCall footer := by
  simp only [body,afterCached,cachedGuard,afterGuard,allocation,afterAllocation,readAt,missingTest,hashCall,hashArguments,footer,
    Guest.Software.guestFn_node_hash_cached,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none,localVar]
  trivial

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "node_hash_cached")=some (formals,body,.one) := by
  have checked:=OriginalCode.indexed code installed 262 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.Software.guestFn_node_hash_cached) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,body,formals,Guest.Software.guestFn_node_hash_cached,
    shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

/-- Incoming node cache words and the actual persistent frontier. No
allocation room, successful hash, or future helper return is assumed. -/
structure Data (source : PanSemStateFiniteExact 64 Guest.HostMemory) (node heap pointer : BitVec 64) (length : Nat) : Prop where
  installed : OriginalCode.Installed source.code
  pointerMapped : source.memaddrs (node+8#64)
  pointerStored : source.memory (node+8#64)=.word pointer
  lengthMapped : source.memaddrs (node+16#64)
  lengthStored : source.memory (node+16#64)=.word (BitVec.ofNat 64 length)
  heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap))
  heapUpper : heap.toNat≤2952790016
  small : length+136<2^64

structure Entry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (node heap pointer : BitVec 64) (length : Nat)
    extends Data source node heap pointer length : Prop where
  nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node))

theorem Data.of_frame {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {node heap pointer : BitVec 64} {length : Nat}
    (data : Data source node heap pointer length) (frame : LocalEffects.erase target=LocalEffects.erase source) : Data target node heap pointer length := by
  have code:=LocalEffects.code_of_erase source target frame
  have memory:=LocalEffects.memory_of_erase source target frame
  have domain:=congrArg PanSemStateFiniteExact.memaddrs frame
  have globals:=congrArg PanSemStateFiniteExact.globals frame
  change target.memaddrs=source.memaddrs at domain
  change target.globals=source.globals at globals
  exact ⟨by rw [code]; exact data.installed,by rw [domain]; exact data.pointerMapped,by rw [memory]; exact data.pointerStored,
    by rw [domain]; exact data.lengthMapped,by rw [memory]; exact data.lengthStored,by rw [globals]; exact data.heapCell,data.heapUpper,data.small⟩

def Entry.bind_cached {source : PanSemStateFiniteExact 64 Guest.HostMemory} {node heap pointer : BitVec 64} {length : Nat}
    (data : Entry source node heap pointer length) (word : BitVec 64) : Entry (bind source "cached" word) node heap pointer length:={
  data with nodeCell:=(bind_lookup_other source "cached" "node" word (by decide)).trans data.nodeCell }

theorem field_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (node word : BitVec 64) (offset : Nat)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node)))
    (mapped : source.memaddrs (node+BitVec.ofNat 64 offset)) (stored : source.memory (node+BitVec.ofNat 64 offset)=.word word) :
    eval source (readAt offset)=some (.val (.word word)) := by
  simp [eval,readAt,evalHOLExact,evalListHOLExact,toExact,localVar,nodeCell,valueIsWord,valueWord,wordOpHOL,wordOp,
    memLoadHOLExact,isWfShapeExactHOL,mapped,stored]

theorem cached_guard_cost (code) : ClockCost.Bound code cachedGuard 0 := by
  rw [shapes.2.2.1]
  exact ClockCost.conditional code _ _ _ 0 0 (ClockCost.returned code _) (ClockCost.skip code)

theorem cached_guard_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (cached : BitVec 64)
    (cell : source.locals.lookup (ofString "cached")=some (.val (.word cached)))
    (normal : evaluateHOLFiniteState source cachedGuard=(none,post)) : post=source := by
  by_cases zero : cached=0#64
  · simpa [shapes.2.2.1,evaluateHOLFiniteState_ite,evaluateHOLFiniteState_skip,evalHOLExact,toExact,localVar,cell,zero,
      Flapjack.Compiler.Encoders.Asm.wordCmpHOL] using (congrArg Prod.snd normal).symm
  · simp [shapes.2.2.1,evaluateHOLFiniteState_ite,evaluateHOLFiniteState_return,evalHOLExact,toExact,localVar,cell,zero,
      Flapjack.Compiler.Encoders.Asm.wordCmpHOL,shapeOfHOLExact,sizeOfShapeWithContextHOL] at normal

theorem footer_cost (code) : ClockCost.Bound code footer 0:=
  ClockCost.sequence code _ _ 0 0 (ClockCost.store code _ _) (ClockCost.returned code _)

set_option maxRecDepth 100000 in
/-- Only an actual alloc return enters the hash suffix. Its exact state
preserves the original cache words and supplies the fresh output pointer. -/
theorem allocation_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (node heap pointer : BitVec 64) (length : Nat)
    (data : Entry source node heap pointer length) :
    source.clock-(evaluateHOLFiniteState source allocation).2.clock≤CurrentKeccak.Hash.bodyPrice length+3 := by
  obtain ⟨callee,called,amountCell⟩:=PersistentAlloc.environment source.code.lookup 32#64 (PersistentAlloc.original_code source.code data.installed)
  rw [shapes.2.2.2.2.1]
  have priced:=ClockCost.scoped_reached_current source "h" .one (ofString "alloc") [.const 32#64] (PersistentAlloc.values 32#64)
    PersistentAlloc.body afterAllocation callee .one 1 (CurrentKeccak.Hash.bodyPrice length+1) rfl called
    (PersistentAlloc.body_price source.code data.installed (callEntryStateHOLFinite source callee) rfl) (by
      intro target returned run checked
      obtain ⟨answer,room,frame⟩:=PersistentAlloc.post_of_normal (callEntryStateHOLFinite source callee) target heap 32#64 amountCell
        data.heapCell data.heapUpper (Trap.original_code source.code data.installed) returned run
      let ready:=CallNormal.continuationEntry source target "h" returned
      have readyEq : ready=bind (PersistentAlloc.post {source with clock:=source.clock-1} heap 32#64) "h" heap:=by
        change setVarHOLFinite (ofString "h") returned {target with locals:=source.locals}=_
        rw [answer]
        exact congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>bind {state with locals:=source.locals} "h" heap) frame
      have nextNode : ready.locals.lookup (ofString "node")=some (.val (.word node)):=by
        rw [readyEq]
        exact (bind_lookup_other _ "h" "node" heap (by decide)).trans data.nodeCell
      have nextPointer : eval ready (readAt 8)=some (.val (.word pointer)):=
        field_read ready node pointer 8 nextNode (by rw [readyEq]; exact data.pointerMapped) (by rw [readyEq]; exact data.pointerStored)
      have nextLength : eval ready (readAt 16)=some (.val (.word (BitVec.ofNat 64 length))):=
        field_read ready node (BitVec.ofNat 64 length) 16 nextNode (by rw [readyEq]; exact data.lengthMapped) (by rw [readyEq]; exact data.lengthStored)
      have hCell : ready.locals.lookup (ofString "h")=some (.val (.word heap)):=by rw [readyEq]; exact bind_lookup_same _ _ _
      have args : evalListHOLFinite ready (h:=fun query=>Classical.propDecidable (ready.memaddrs query)) hashArguments=
          some (CurrentKeccak.Hash.values pointer heap length):=by
        simp only [eval] at nextPointer nextLength
        simp [hashArguments,CurrentKeccak.Hash.values,evalListHOLFinite,evalListHOLExact,nextPointer,nextLength,evalHOLExact,toExact,localVar,hCell]
      have nextInstalled : OriginalCode.Installed ready.code:=by rw [readyEq]; exact data.installed
      have hashPrice:=CurrentKeccak.Hash.call_cost ready hashArguments pointer heap length data.small nextInstalled args
      have suffix:=ClockCost.sequence_current ready hashCall footer (CurrentKeccak.Hash.bodyPrice length+1) 0 hashPrice (footer_cost ready.code)
      change ready.clock-(evaluateHOLFiniteState ready afterAllocation).2.clock≤CurrentKeccak.Hash.bodyPrice length+1
      simpa only [shapes.2.2.2.2.2,Nat.add_zero] using suffix)
  have sum : 1+(CurrentKeccak.Hash.bodyPrice length+1)+1=CurrentKeccak.Hash.bodyPrice length+3:=by omega
  rw [sum] at priced
  exact priced

set_option maxRecDepth 100000 in
theorem body_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (node heap pointer : BitVec 64) (length : Nat)
    (data : Entry source node heap pointer length) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤CurrentKeccak.Hash.bodyPrice length+3 := by
  rw [shapes.1]
  apply ClockCost.scalar_declaration_current source (ofString "cached") (readAt 24) afterCached (CurrentKeccak.Hash.bodyPrice length+3)
  intro word
  let ready:=bind source "cached" word
  change ready.clock-(evaluateHOLFiniteState ready afterCached).2.clock≤CurrentKeccak.Hash.bodyPrice length+3
  have next:=data.bind_cached word
  have tailPrice : ready.clock-(evaluateHOLFiniteState ready afterGuard).2.clock≤CurrentKeccak.Hash.bodyPrice length+3:=by
    rw [shapes.2.2.2.1]
    have cost:=Fail.guard_reached_cost ready missingTest 13#64 allocation (CurrentKeccak.Hash.bodyPrice length+3) next.installed
      (fun _=>allocation_cost ready node heap pointer length next)
    have positive : 1≤CurrentKeccak.Hash.bodyPrice length+3:=by omega
    simpa only [Nat.max_eq_right positive] using cost
  rw [shapes.2.1]
  have result:=ClockCost.sequence_reached_current ready cachedGuard afterGuard 0 (CurrentKeccak.Hash.bodyPrice length+3)
    (cached_guard_cost ready.code ready rfl) (by
      intro middle normal
      have same:=cached_guard_normal ready middle word (bind_lookup_same _ _ _) normal
      rw [same]
      exact tailPrice)
  simpa only [ready,QueryBranch.bind,Nat.zero_add] using result

end InitECandidate.Solver.Mpt.NodeHashCached

#print axioms InitECandidate.Solver.Mpt.NodeHashCached.shapes
#print axioms InitECandidate.Solver.Mpt.NodeHashCached.original_code
#print axioms InitECandidate.Solver.Mpt.NodeHashCached.field_read
#print axioms InitECandidate.Solver.Mpt.NodeHashCached.cached_guard_cost
#print axioms InitECandidate.Solver.Mpt.NodeHashCached.cached_guard_normal
#print axioms InitECandidate.Solver.Mpt.NodeHashCached.allocation_cost
#print axioms InitECandidate.Solver.Mpt.NodeHashCached.body_cost

namespace InitECandidate.Solver.Mpt.NodeWriteRef
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix Input
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def body : ProgHOL 64:=match Guest.Software.guestFn_node_write_ref with | .function fn=>progToHOL fn.body | _=>.skip
def formals : List (MlS×ShapeHOL):=[(ofString "child",.one),(ofString "dst",.one)]
def readAt (offset : Nat) : ExpHOL 64:=.load .one (.op .add [localVar "child",.const (BitVec.ofNat 64 offset)])
def nextByte : ExpHOL 64:=.op .add [localVar "dst",.const 1#64]
def nullTest : ExpHOL 64:=.cmp .equal (localVar "child") (.const 0#64)
def hashTest : ExpHOL 64:=.cmp .equal (readAt 0) (.const 0#64)
def missingTest : ExpHOL 64:=.cmp .equal (readAt 8) (.const 0#64)
def shortTest : ExpHOL 64:=.cmp .lower (localVar "rl") (.const 32#64)
def nullBranch : ProgHOL 64:=.seq (.storeByte (localVar "dst") (.const 128#64)) (.return (.const 1#64))
def hashCopy : ProgHOL 64:=.call (some (none,none)) (ofString "memcpy") [nextByte,readAt 24,.const 32#64]
def hashBranch : ProgHOL 64:=.seq (.storeByte (localVar "dst") (.const 160#64)) (.seq hashCopy (.return (.const 33#64)))
def shortCopy : ProgHOL 64:=.call (some (none,none)) (ofString "memcpy") [localVar "dst",localVar "rp",localVar "rl"]
def shortBranch : ProgHOL 64:=.seq shortCopy (.return (localVar "rl"))
def digestCopy : ProgHOL 64:=.call (some (none,none)) (ofString "memcpy") [nextByte,localVar "h",.const 32#64]
def digestBranch : ProgHOL 64:=.seq (.storeByte (localVar "dst") (.const 160#64)) (.seq digestCopy (.return (.const 33#64)))
def digestScope : ProgHOL 64:=.decCall (ofString "h") .one (ofString "node_hash_cached") [localVar "child"] digestBranch
def lengthTail : ProgHOL 64:=.seq (.ite shortTest shortBranch .skip) digestScope
def afterPointer : ProgHOL 64:=.dec (ofString "rl") .one (readAt 16) lengthTail
def afterCache : ProgHOL 64:=.dec (ofString "rp") .one (readAt 8) afterPointer
def afterHash : ProgHOL 64:=.seq (.ite missingTest (.call (some (none,none)) (ofString "mpt_fail") [.const 13#64]) .skip) afterCache
def afterNull : ProgHOL 64:=.seq (.ite hashTest hashBranch .skip) afterHash

set_option maxRecDepth 100000 in
theorem body_shape : body=.seq (.ite nullTest nullBranch .skip) afterNull := by
  simp only [body,nullTest,nullBranch,afterNull,afterHash,afterCache,afterPointer,lengthTail,digestScope,digestBranch,digestCopy,
    shortTest,shortBranch,shortCopy,hashTest,hashBranch,hashCopy,missingTest,nextByte,readAt,
    Guest.Software.guestFn_node_write_ref,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none,localVar]

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "node_write_ref")=some (formals,body,.one) := by
  have checked:=OriginalCode.indexed code installed 263 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.Software.guestFn_node_write_ref) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,body,formals,Guest.Software.guestFn_node_write_ref,
    shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

def Bounded (value : ValueHOL 64) : Prop:=∃ word : BitVec 64,value=.val (.word word) ∧ word.toNat≤33

theorem literal_bound (source : PanSemStateFiniteExact 64 Guest.HostMemory) (word : BitVec 64) (small : word.toNat≤33) :
    ReturnFacts.Returns source (.return (.const word)) Bounded:=ReturnFacts.returned source _ (.val (.word word)) Bounded rfl ⟨word,rfl,small⟩

theorem null_branch_bound (source : PanSemStateFiniteExact 64 Guest.HostMemory) : ReturnFacts.Returns source nullBranch Bounded:=
  ReturnFacts.sequence source _ _ Bounded (ReturnFacts.local_prefix source (ofString "child") _ (.storeByte _ _) Bounded)
    (fun current _=>literal_bound current 1#64 (by decide))

theorem hash_branch_bound (source : PanSemStateFiniteExact 64 Guest.HostMemory) : ReturnFacts.Returns source hashBranch Bounded:=
  ReturnFacts.sequence source _ _ Bounded (ReturnFacts.local_prefix source (ofString "child") _ (.storeByte _ _) Bounded)
    (fun current _=>ReturnFacts.sequence current _ _ Bounded
      (ReturnFacts.local_prefix current (ofString "child") _ (.call none _ _ (by intro name same; cases same)) Bounded)
      (fun target _=>literal_bound target 33#64 (by decide)))

theorem digest_scope_bound (source : PanSemStateFiniteExact 64 Guest.HostMemory) : ReturnFacts.Returns source digestScope Bounded:=
  ReturnFacts.scoped_any source "h" .one (ofString "node_hash_cached") [localVar "child"] digestBranch Bounded (fun ready=>
    ReturnFacts.sequence ready _ _ Bounded (ReturnFacts.local_prefix ready (ofString "child") _ (.storeByte _ _) Bounded)
      (fun current _=>ReturnFacts.sequence current _ _ Bounded
        (ReturnFacts.local_prefix current (ofString "child") _ (.call none _ _ (by intro name same; cases same)) Bounded)
        (fun target _=>literal_bound target 33#64 (by decide))))

theorem short_branch_bound (source : PanSemStateFiniteExact 64 Guest.HostMemory) (length : BitVec 64)
    (cell : source.locals.lookup (ofString "rl")=some (.val (.word length))) (small : length.toNat<32) :
    ReturnFacts.Returns source shortBranch Bounded := by
  apply ReturnFacts.sequence source shortCopy (.return (localVar "rl")) Bounded
    (ReturnFacts.local_prefix source (ofString "rl") _ (.call none _ _ (by intro name same; cases same)) Bounded)
  intro current run
  have saved:=(CallNormal.ignored_lookup source current (ofString "rl") (ofString "memcpy") [localVar "dst",localVar "rp",localVar "rl"] run).trans cell
  exact ReturnFacts.returned current _ (.val (.word length)) Bounded
    (by simp [eval,evalHOLExact,toExact,localVar,saved]) ⟨length,rfl,by omega⟩

/-- The real short-reference condition supplies its own length bound.
Other successful paths return the literal33, regardless of hash callees. -/
theorem length_tail_bound (source : PanSemStateFiniteExact 64 Guest.HostMemory) : ReturnFacts.Returns source lengthTail Bounded := by
  cases lookup : source.locals.lookup (ofString "rl") with
  | none=>intro target value normal; simp [lengthTail,shortTest,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,evalHOLExact,toExact,localVar,lookup] at normal
  | some loaded=>
    cases loaded with
    | rStruct fields=>intro target value normal; simp [lengthTail,shortTest,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,evalHOLExact,toExact,localVar,lookup] at normal
    | nStruct name fields=>intro target value normal; simp [lengthTail,shortTest,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,evalHOLExact,toExact,localVar,lookup] at normal
    | val word=>
      cases word with
      | word word=>
        by_cases short : word.toNat<32
        · have selected : evaluateHOLFiniteState source lengthTail=evaluateHOLFiniteState source (.seq shortBranch digestScope):=by
            simp [lengthTail,shortTest,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,evalHOLExact,toExact,localVar,lookup,
              Flapjack.Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,short]
          intro target value normal
          rw [selected] at normal
          exact (ReturnFacts.sequence source shortBranch digestScope Bounded (short_branch_bound source word lookup short)
            (fun current _=>digest_scope_bound current)) target value normal
        · have selected : evaluateHOLFiniteState source lengthTail=evaluateHOLFiniteState source digestScope:=by
            simp [lengthTail,shortTest,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,evaluateHOLFiniteState_skip,evalHOLExact,toExact,localVar,lookup,
              Flapjack.Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,short]
          intro target value normal
          exact digest_scope_bound source target value (selected.symm.trans normal)

/-- Every actual normal reference-writer result is a scalar of at most33
bytes. Cache readability or a future successful hash is not assumed. -/
theorem normal_bound (source : PanSemStateFiniteExact 64 Guest.HostMemory) : ReturnFacts.Returns source body Bounded := by
  rw [body_shape]
  apply ReturnFacts.sequence
  · exact ReturnFacts.conditional source _ _ _ Bounded (null_branch_bound source) (ReturnFacts.skip source Bounded)
  · intro current _
    apply ReturnFacts.sequence
    · exact ReturnFacts.conditional current _ _ _ Bounded (hash_branch_bound current) (ReturnFacts.skip current Bounded)
    · intro afterNode _
      apply ReturnFacts.sequence
      · exact ReturnFacts.local_prefix afterNode (ofString "child") _ (.ite _ (.call none _ _ (by intro name same; cases same)) .skip) Bounded
      · intro afterGuard _
        exact ReturnFacts.declared afterGuard (ofString "rp") .one (readAt 8) afterPointer Bounded (fun _=>
          ReturnFacts.declared _ (ofString "rl") .one (readAt 16) lengthTail Bounded (fun _=>length_tail_bound _))

theorem hash_copy_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (installed : OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source hashCopy).2.clock≤42 := by
  exact BufferDynamicCost.copy_cost source nextByte (readAt 24) (.const 32#64) 32 installed (by decide) rfl

theorem digest_copy_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (installed : OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source digestCopy).2.clock≤42 := by
  exact BufferDynamicCost.copy_cost source nextByte (localVar "h") (.const 32#64) 32 installed (by decide) rfl

/-- A statement ending in an actual return cannot fall through, including
failed prefixes and failed evaluation of the return expression. -/
theorem sequence_return_stops (source : PanSemStateFiniteExact 64 Guest.HostMemory) (priorProgram : ProgHOL 64) (expression : ExpHOL 64) :
    (evaluateHOLFiniteState source (.seq priorProgram (.return expression))).1≠none := by
  intro normal
  have run : evaluateHOLFiniteState source (.seq priorProgram (.return expression))=(none,(evaluateHOLFiniteState source (.seq priorProgram (.return expression))).2):=Prod.ext normal rfl
  obtain ⟨middle,front,back⟩:=sequence_none source _ priorProgram (.return expression) run
  rw [evaluateHOLFiniteState_return] at back
  split at back
  · cases back
  · split at back <;> cases back

theorem null_branch_stops (source : PanSemStateFiniteExact 64 Guest.HostMemory) : (evaluateHOLFiniteState source nullBranch).1≠none:=
  sequence_return_stops source _ _

theorem hash_branch_stops (source : PanSemStateFiniteExact 64 Guest.HostMemory) : (evaluateHOLFiniteState source hashBranch).1≠none := by
  intro normal
  obtain ⟨middle,front,back⟩:=sequence_none source _ _ _ (Prod.ext normal rfl)
  exact sequence_return_stops middle hashCopy (.const 33#64) (congrArg Prod.fst back)

theorem short_branch_stops (source : PanSemStateFiniteExact 64 Guest.HostMemory) : (evaluateHOLFiniteState source shortBranch).1≠none:=
  sequence_return_stops source _ _

theorem null_branch_cost (code) : ClockCost.Bound code nullBranch 0:=
  ClockCost.sequence code _ _ 0 0 (ClockCost.store_byte code _ _) (ClockCost.returned code _)

theorem hash_branch_cost (code) (installed : OriginalCode.Installed code) : ClockCost.Bound code hashBranch 42 := by
  apply ClockCost.sequence code _ _ 0 42 (ClockCost.store_byte code _ _)
  exact ClockCost.sequence code _ _ 42 0 (by intro source codeEq; exact hash_copy_cost source (by rw [codeEq]; exact installed))
    (ClockCost.returned code _)

theorem digest_branch_cost (code) (installed : OriginalCode.Installed code) : ClockCost.Bound code digestBranch 42 := by
  apply ClockCost.sequence code _ _ 0 42 (ClockCost.store_byte code _ _)
  exact ClockCost.sequence code _ _ 42 0 (by intro source codeEq; exact digest_copy_cost source (by rw [codeEq]; exact installed))
    (ClockCost.returned code _)

theorem field_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (child word : BitVec 64) (offset : Nat)
    (childCell : source.locals.lookup (ofString "child")=some (.val (.word child)))
    (mapped : source.memaddrs (child+BitVec.ofNat 64 offset)) (stored : source.memory (child+BitVec.ofNat 64 offset)=.word word) :
    eval source (readAt offset)=some (.val (.word word)) := by
  simp [eval,readAt,evalHOLExact,evalListHOLExact,toExact,localVar,childCell,valueIsWord,valueWord,wordOpHOL,wordOp,
    memLoadHOLExact,isWfShapeExactHOL,mapped,stored]

set_option maxRecDepth 100000 in
theorem digest_scope_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (child heap pointer : BitVec 64) (length : Nat)
    (data : NodeHashCached.Data source child heap pointer length)
    (childCell : source.locals.lookup (ofString "child")=some (.val (.word child))) :
    source.clock-(evaluateHOLFiniteState source digestScope).2.clock≤CurrentKeccak.Hash.bodyPrice length+46 := by
  obtain ⟨callee,called,nodeCell⟩:=CallNormal.unary_environment source.code.lookup (ofString "node_hash_cached") "node"
    NodeHashCached.body child (NodeHashCached.original_code source.code data.installed)
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) [localVar "child"]=some [.val (.word child)]:=by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,childCell]
  have ready : NodeHashCached.Entry (callEntryStateHOLFinite source callee) child heap pointer length:=
    {toData:=data.of_frame rfl,nodeCell:=nodeCell}
  have price:=ClockCost.scoped_current source (ofString "h") .one (ofString "node_hash_cached") [localVar "child"] [.val (.word child)]
    NodeHashCached.body digestBranch callee .one (CurrentKeccak.Hash.bodyPrice length+3) 42 args called
    (NodeHashCached.body_cost (callEntryStateHOLFinite source callee) child heap pointer length ready) (digest_branch_cost source.code data.installed)
  change source.clock-(evaluateHOLFiniteState source digestScope).2.clock≤_ at price
  omega

theorem short_branch_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (length : BitVec 64)
    (installed : OriginalCode.Installed source.code)
    (cell : source.locals.lookup (ofString "rl")=some (.val (.word length))) (small : length.toNat<32) :
    source.clock-(evaluateHOLFiniteState source shortBranch).2.clock≤38 := by
  have read : eval source (localVar "rl")=some (.val (.word (BitVec.ofNat 64 length.toNat))):=by
    simp [eval,evalHOLExact,toExact,localVar,cell]
  have copyPrice:=BufferDynamicCost.copy_cost source (localVar "dst") (localVar "rp") (localVar "rl") length.toNat installed (by omega) read
  have price:=ClockCost.sequence_current source shortCopy (.return (localVar "rl")) (CopyAny.price length.toNat+1) 0 copyPrice (ClockCost.returned source.code _)
  have bounded : CopyAny.price length.toNat+1≤38:=by unfold CopyAny.price; omega
  exact Nat.le_trans price (by omega)

set_option maxRecDepth 100000 in
theorem length_tail_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (child heap pointer : BitVec 64) (length : Nat)
    (data : NodeHashCached.Data source child heap pointer length)
    (childCell : source.locals.lookup (ofString "child")=some (.val (.word child)))
    (lengthCell : source.locals.lookup (ofString "rl")=some (.val (.word (BitVec.ofNat 64 length)))) :
    source.clock-(evaluateHOLFiniteState source lengthTail).2.clock≤CurrentKeccak.Hash.bodyPrice length+46 := by
  have number : (BitVec.ofNat 64 length).toNat=length:=by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by have small:=data.small; omega)]
  have longPrice:=digest_scope_cost source child heap pointer length data childCell
  by_cases short : length<32
  · have cost:=ClockCost.stopping_guard_current source shortTest shortBranch digestScope 38 (CurrentKeccak.Hash.bodyPrice length+46)
      (short_branch_stops source) (short_branch_cost source (BitVec.ofNat 64 length) data.installed lengthCell (by rw [number]; exact short)) longPrice
    have positive : 38≤CurrentKeccak.Hash.bodyPrice length+46:=by omega
    simpa only [lengthTail,Nat.max_eq_right positive] using cost
  · have skipped : evaluateHOLFiniteState source (.ite shortTest shortBranch .skip)=(none,source):=by
      simp [shortTest,evaluateHOLFiniteState_ite,evaluateHOLFiniteState_skip,evalHOLExact,toExact,localVar,lengthCell,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,number,short]
    rw [lengthTail,evaluateHOLFiniteState_seq_line780,skipped]
    exact longPrice

set_option maxRecDepth 100000 in
theorem after_cache_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (child heap pointer : BitVec 64) (length : Nat)
    (data : NodeHashCached.Data source child heap pointer length)
    (childCell : source.locals.lookup (ofString "child")=some (.val (.word child))) :
    source.clock-(evaluateHOLFiniteState source afterCache).2.clock≤CurrentKeccak.Hash.bodyPrice length+46 := by
  have pointerRead:=field_read source child pointer 8 childCell data.pointerMapped data.pointerStored
  apply ClockCost.declared_current source "rp" (readAt 8) pointer afterPointer (CurrentKeccak.Hash.bodyPrice length+46) pointerRead
  let first:=bind source "rp" pointer
  have firstChild : first.locals.lookup (ofString "child")=some (.val (.word child)):=
    (bind_lookup_other source "rp" "child" pointer (by decide)).trans childCell
  have lengthRead:=field_read first child (BitVec.ofNat 64 length) 16 firstChild data.lengthMapped data.lengthStored
  apply ClockCost.declared_current first "rl" (readAt 16) (BitVec.ofNat 64 length) lengthTail (CurrentKeccak.Hash.bodyPrice length+46) lengthRead
  exact length_tail_cost _ child heap pointer length (data.of_frame rfl)
    ((bind_lookup_other first "rl" "child" _ (by decide)).trans firstChild) (bind_lookup_same _ _ _)

set_option maxRecDepth 100000 in
/-- Missing RLP caches stop at the actual failure guard; reached normal
guards are the only paths that require bounded populated-cache data. -/
theorem after_hash_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (child heap pointer : BitVec 64) (length : Nat)
    (installed : OriginalCode.Installed source.code)
    (childCell : source.locals.lookup (ofString "child")=some (.val (.word child)))
    (cacheMapped : source.memaddrs (child+8#64)) (cacheStored : source.memory (child+8#64)=.word pointer)
    (data : pointer≠0#64→NodeHashCached.Data source child heap pointer length) :
    source.clock-(evaluateHOLFiniteState source afterHash).2.clock≤CurrentKeccak.Hash.bodyPrice length+46 := by
  have price:=Fail.guard_reached_cost source missingTest 13#64 afterCache (CurrentKeccak.Hash.bodyPrice length+46) installed (by
    intro passed
    have active : pointer≠0#64:=by
      intro zero
      have read:=field_read source child pointer 8 childCell cacheMapped cacheStored
      have expected : eval source missingTest=some (.val (.word 1#64)):=by
        simp only [eval] at read
        simp [eval,missingTest,evalHOLExact,read,zero,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
      have actual:=(Fail.guard_normal source source missingTest [.const 13#64] installed passed).1
      have impossible : (1#64 : BitVec 64)=0#64:=by simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using expected.symm.trans actual
      exact (by decide : (1#64 : BitVec 64)≠0#64) impossible
    exact after_cache_cost source child heap pointer length (data active) childCell)
  have positive : 1≤CurrentKeccak.Hash.bodyPrice length+46:=by omega
  simpa only [afterHash,Nat.max_eq_right positive] using price

set_option maxRecDepth 100000 in
theorem after_null_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (child tag heap pointer : BitVec 64) (length : Nat)
    (installed : OriginalCode.Installed source.code)
    (childCell : source.locals.lookup (ofString "child")=some (.val (.word child)))
    (headerMapped : source.memaddrs child) (headerStored : source.memory child=.word tag)
    (cache : tag≠0#64→source.memaddrs (child+8#64) ∧ source.memory (child+8#64)=.word pointer)
    (data : tag≠0#64→pointer≠0#64→NodeHashCached.Data source child heap pointer length) :
    source.clock-(evaluateHOLFiniteState source afterNull).2.clock≤CurrentKeccak.Hash.bodyPrice length+46 := by
  have price:=ClockCost.stopping_guard_reached source hashTest hashBranch afterHash 42 (CurrentKeccak.Hash.bodyPrice length+46)
    (hash_branch_stops source) (hash_branch_cost source.code installed source rfl) (by
      intro passed
      have nonHash : tag≠0#64:=by
        intro zero
        have read:=field_read source child tag 0 childCell (by simpa using headerMapped) (by simpa using headerStored)
        have taken : evaluateHOLFiniteState source (.ite hashTest hashBranch .skip)=evaluateHOLFiniteState source hashBranch:=by
          simp only [eval] at read
          simp [hashTest,evaluateHOLFiniteState_ite,evalHOLExact,read,zero,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
        exact hash_branch_stops source (congrArg Prod.fst (taken.symm.trans passed))
      obtain ⟨mapped,stored⟩:=cache nonHash
      exact after_hash_cost source child heap pointer length installed childCell mapped stored (data nonHash))
  have positive : 42≤CurrentKeccak.Hash.bodyPrice length+46:=by omega
  simpa only [afterNull,Nat.max_eq_right positive] using price

set_option maxRecDepth 100000 in
/-- Every real reference-writer outcome is bounded. Null/hash children
need no RLP cache; absent caches stop before length/hash entry conditions
are required. Only populated non-hash caches supply their incoming data. -/
theorem body_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (child tag heap pointer : BitVec 64) (length : Nat)
    (installed : OriginalCode.Installed source.code)
    (childCell : source.locals.lookup (ofString "child")=some (.val (.word child)))
    (header : child≠0#64→source.memaddrs child ∧ source.memory child=.word tag)
    (cache : child≠0#64→tag≠0#64→source.memaddrs (child+8#64) ∧ source.memory (child+8#64)=.word pointer)
    (data : child≠0#64→tag≠0#64→pointer≠0#64→NodeHashCached.Data source child heap pointer length) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤CurrentKeccak.Hash.bodyPrice length+46 := by
  rw [body_shape]
  have price:=ClockCost.stopping_guard_reached source nullTest nullBranch afterNull 0 (CurrentKeccak.Hash.bodyPrice length+46)
    (null_branch_stops source) (null_branch_cost source.code source rfl) (by
      intro passed
      have active : child≠0#64:=by
        intro zero
        have taken : evaluateHOLFiniteState source (.ite nullTest nullBranch .skip)=evaluateHOLFiniteState source nullBranch:=by
          simp [nullTest,evaluateHOLFiniteState_ite,evalHOLExact,toExact,localVar,childCell,zero,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
        exact null_branch_stops source (congrArg Prod.fst (taken.symm.trans passed))
      obtain ⟨mapped,stored⟩:=header active
      exact after_null_cost source child tag heap pointer length installed childCell mapped stored (cache active) (data active))
  simpa only [Nat.zero_max] using price

theorem environment (codeFn : MlS→Option (List (MlS×ShapeHOL)×ProgHOL 64×ShapeHOL)) (child dst : BitVec 64)
    (known : codeFn (ofString "node_write_ref")=some (formals,body,.one)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),lookupCodeHOLFinite codeFn (ofString "node_write_ref") [.val (.word child),.val (.word dst)]=some (body,callee,.one) ∧
      callee.lookup (ofString "child")=some (.val (.word child)) ∧ callee.lookup (ofString "dst")=some (.val (.word dst)) :=
  word_pair_environment codeFn (ofString "node_write_ref") (ofString "child") (ofString "dst") body .one child dst (by decide) known

theorem call_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (arguments : List (ExpHOL 64)) (destination : Option (Option MlS))
    (child dst tag heap pointer : BitVec 64) (length : Nat) (installed : OriginalCode.Installed source.code)
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=some [.val (.word child),.val (.word dst)])
    (header : child≠0#64→source.memaddrs child ∧ source.memory child=.word tag)
    (cache : child≠0#64→tag≠0#64→source.memaddrs (child+8#64) ∧ source.memory (child+8#64)=.word pointer)
    (data : child≠0#64→tag≠0#64→pointer≠0#64→NodeHashCached.Data source child heap pointer length) :
    source.clock-(evaluateHOLFiniteState source (.call (LocalEffects.callInfo destination) (ofString "node_write_ref") arguments)).2.clock≤
      CurrentKeccak.Hash.bodyPrice length+47 := by
  obtain ⟨callee,called,childCell,dstCell⟩:=environment source.code.lookup child dst (original_code source.code installed)
  have price:=ClockCost.call_current source destination (ofString "node_write_ref") arguments _ body callee .one (CurrentKeccak.Hash.bodyPrice length+46)
    args called (body_cost (callEntryStateHOLFinite source callee) child tag heap pointer length installed childCell header cache
      (fun active nonHash populated=>(data active nonHash populated).of_frame rfl))
  have sum : CurrentKeccak.Hash.bodyPrice length+46+1=CurrentKeccak.Hash.bodyPrice length+47:=by omega
  rw [sum] at price
  exact price

end InitECandidate.Solver.Mpt.NodeWriteRef

#print axioms InitECandidate.Solver.Mpt.NodeWriteRef.body_shape
#print axioms InitECandidate.Solver.Mpt.NodeWriteRef.original_code
#print axioms InitECandidate.Solver.Mpt.NodeWriteRef.short_branch_bound
#print axioms InitECandidate.Solver.Mpt.NodeWriteRef.length_tail_bound
#print axioms InitECandidate.Solver.Mpt.NodeWriteRef.normal_bound
#print axioms InitECandidate.Solver.Mpt.NodeWriteRef.hash_copy_cost
#print axioms InitECandidate.Solver.Mpt.NodeWriteRef.digest_copy_cost
#print axioms InitECandidate.Solver.Mpt.NodeHashCached.Data.of_frame
#print axioms InitECandidate.Solver.Mpt.NodeWriteRef.sequence_return_stops
#print axioms InitECandidate.Solver.Mpt.NodeWriteRef.hash_branch_cost
#print axioms InitECandidate.Solver.Mpt.NodeWriteRef.digest_branch_cost
#print axioms InitECandidate.Solver.Mpt.NodeWriteRef.digest_scope_cost
#print axioms InitECandidate.Solver.Mpt.NodeWriteRef.short_branch_cost
#print axioms InitECandidate.Solver.Mpt.NodeWriteRef.length_tail_cost
#print axioms InitECandidate.Solver.Mpt.NodeWriteRef.after_cache_cost
#print axioms InitECandidate.Solver.Mpt.NodeWriteRef.after_hash_cost
#print axioms InitECandidate.Solver.Mpt.NodeWriteRef.after_null_cost
#print axioms InitECandidate.Solver.Mpt.NodeWriteRef.body_cost
#print axioms InitECandidate.Solver.Mpt.NodeWriteRef.call_cost
