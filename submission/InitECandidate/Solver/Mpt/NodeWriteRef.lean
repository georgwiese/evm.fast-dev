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
import InitECandidate.Solver.Input.WordStoreNormal
import InitECandidate.Solver.PanHeapGlobals
import InitECandidate.Solver.Input.CurrentRlp.WriteFrame
import InitECandidate.Solver.Input.ScopedCallNormal
import InitECandidate.Solver.Input.CallPrefixScopedActual
import InitECandidate.Solver.Mpt.NodeRefLenNormal

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

namespace InitECandidate.Solver.Mpt.NodeHashCached
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix Input
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The actual footer derives its mapped cache destination, installs the
real digest pointer and returns that same pointer. -/
theorem footer_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (node out : BitVec 64)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node)))
    (outCell : source.locals.lookup (ofString "h")=some (.val (.word out)))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source footer=(some (.returned value),target)) :
    value=.val (.word out) ∧ target=emptyLocalsHOLFinite {source with memory:=StoreWord.put source.memory (node+24#64) out} ∧
      source.memaddrs (node+24#64) := by
  obtain ⟨middle,storeRun,returnRun⟩:=sequence_returned source target _ _ value
    ((LocalPrefix.store (key:=ofString "node") _ _).summary_full source).2.1 normal
  have address : eval source (.op .add [localVar "node",.const 24#64])=some (.val (.word (node+24#64))):=by
    simp [eval,evalHOLExact,evalListHOLExact,toExact,localVar,nodeCell,valueIsWord,valueWord,wordOpHOL,wordOp]
  have outRead : eval source (localVar "h")=some (.val (.word out)):=by simp [eval,evalHOLExact,toExact,localVar,outCell]
  obtain ⟨mapped,changed⟩:=word_store_normal source middle _ _ (node+24#64) out address outRead storeRun
  obtain ⟨returned,endpoint⟩:=return_normal middle target (localVar "h") value returnRun
  have read : eval middle (localVar "h")=some (.val (.word out)):=by rw [changed]; exact outRead
  exact ⟨Option.some.inj (returned.symm.trans read),by rw [endpoint,changed],mapped⟩

structure TailOutput (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (node out stp pad : BitVec 64) (value : ValueHOL 64) : Prop where
  answer : value=.val (.word out)
  fields : MemoryMetadata.erase post=MemoryMetadata.erase source
  stored : post.memory (node+24#64)=.word out
  memory : ∀ query : BitVec 64,query≠node+24#64→CopyGeneral.Away stp query 200→CopyGeneral.Away pad query 136→
    CopyGeneral.Away out query 32→post.memory query=source.memory query

set_option maxRecDepth 100000 in
/-- Every phase of the actual hash-and-cache suffix comes from this same
normal return. Its memory frame requires no readable-input-span premise. -/
theorem after_allocation_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (node pointer out stp pad : BitVec 64) (length : Nat)
    (environment : CurrentKeccak.Hash.Environment source stp pad)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node)))
    (outCell : source.locals.lookup (ofString "h")=some (.val (.word out)))
    (pointerRead : eval source (readAt 8)=some (.val (.word pointer)))
    (lengthRead : eval source (readAt 16)=some (.val (.word (BitVec.ofNat 64 length))))
    (small : length+136<2^64) (outArena : AllocatedBytes.Arena out 32)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source afterAllocation=(some (.returned value),post)) :
    TailOutput source post node out stp pad value := by
  rw [shapes.2.2.2.2.2] at normal
  obtain ⟨middle,hashRun,footerRun⟩:=sequence_returned source post hashCall footer value
    ((LocalPrefix.call (key:=ofString "node") none _ _ (by intro name same; cases same)).summary_full source).2.1 normal
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) hashArguments=
      some (CurrentKeccak.Hash.values pointer out length):=by
    simp only [eval] at pointerRead lengthRead
    simp [hashArguments,CurrentKeccak.Hash.values,evalListHOLFinite,evalListHOLExact,pointerRead,lengthRead,evalHOLExact,toExact,localVar,outCell]
  have metadata:=CurrentKeccak.Hash.call_metadata source.code environment.installed hashArguments (some none) source rfl
  change MemoryMetadata.erase (evaluateHOLFiniteState source hashCall).2=MemoryMetadata.erase source at metadata
  rw [hashRun] at metadata
  have nextNode : middle.locals.lookup (ofString "node")=some (.val (.word node)):=
    (CallNormal.ignored_lookup source middle (ofString "node") (ofString "keccak256") hashArguments hashRun).trans nodeCell
  have nextOut : middle.locals.lookup (ofString "h")=some (.val (.word out)):=
    (CallNormal.ignored_lookup source middle (ofString "h") (ofString "keccak256") hashArguments hashRun).trans outCell
  obtain ⟨answer,endpoint,mapped⟩:=footer_normal middle post node out nextNode nextOut value footerRun
  refine ⟨answer,?_,?_,?_⟩
  · rw [endpoint]
    exact metadata
  · rw [endpoint]
    exact if_pos rfl
  · intro query notCache stateAway padAway outAway
    have frame:=CurrentKeccak.Hash.call_span_frame source middle stp pad pointer out query length environment hashArguments args
      small outArena stateAway padAway outAway hashRun
    rw [endpoint]
    exact (if_neg notCache).trans frame.memory

end InitECandidate.Solver.Mpt.NodeHashCached

#print axioms InitECandidate.Solver.Mpt.NodeHashCached.footer_normal
#print axioms InitECandidate.Solver.Mpt.NodeHashCached.after_allocation_normal

namespace InitECandidate.Solver.Mpt.NodeHashCached
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix Input
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

structure AllocatedOutput (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (node heap stp pad : BitVec 64) (value : ValueHOL 64) : Prop where
  room : heap.toNat+32≤2952790016
  answer : value=.val (.word heap)
  fields : MemoryMetadata.erase post=MemoryMetadata.erase (PersistentAlloc.post source heap 32#64)
  stored : post.memory (node+24#64)=.word heap
  memory : ∀ query : BitVec 64,query≠node+24#64→CopyGeneral.Away stp query 200→CopyGeneral.Away pad query 136→
    CopyGeneral.Away heap query 32→post.memory query=source.memory query

set_option maxRecDepth 100000 in
/-- The real scoped allocation derives room, hash output ownership and
the complete hash/cache frame, then restores the caller's h binding. -/
theorem allocation_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (node heap pointer stp pad : BitVec 64) (length : Nat)
    (data : Entry source node heap pointer length) (environment : CurrentKeccak.Hash.Environment source stp pad)
    (heapLower : 2701131776≤heap.toNat) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source allocation=(some (.returned value),post)) :
    AllocatedOutput source post node heap stp pad value := by
  rw [shapes.2.2.2.2.1] at normal
  obtain ⟨room,funded,inner,continued,endpoint⟩:=PersistentAlloc.call_normal source post "h" [.const 32#64] afterAllocation heap 32#64 rfl
    (PersistentAlloc.original_code source.code data.installed) (Trap.original_code source.code data.installed) data.heapCell data.heapUpper value normal
  change heap.toNat+32≤2952790016 at room
  let ready:=bind (PersistentAlloc.post {source with clock:=source.clock-1} heap 32#64) "h" heap
  have nextNode : ready.locals.lookup (ofString "node")=some (.val (.word node)):=
    (bind_lookup_other _ "h" "node" heap (by decide)).trans data.nodeCell
  have pointerRead:=field_read ready node pointer 8 nextNode data.pointerMapped data.pointerStored
  have lengthRead:=field_read ready node (BitVec.ofNat 64 length) 16 nextNode data.lengthMapped data.lengthStored
  have stateGlobal : ready.globals.lookup (ofString "keccak_st")=source.globals.lookup (ofString "keccak_st"):=
    HeapGlobals.update source (PersistentAlloc.rounded heap 32#64) _ (by decide)
  have padGlobal : ready.globals.lookup (ofString "keccak_pad")=source.globals.lookup (ofString "keccak_pad"):=
    HeapGlobals.update source (PersistentAlloc.rounded heap 32#64) _ (by decide)
  have readyEnvironment : CurrentKeccak.Hash.Environment ready stp pad:={
    environment with stateGlobal:=stateGlobal.trans environment.stateGlobal,padGlobal:=padGlobal.trans environment.padGlobal }
  have outArena : AllocatedBytes.Arena heap 32:=⟨heapLower,by omega⟩
  have completed:=after_allocation_normal ready inner node pointer heap stp pad length readyEnvironment nextNode (bind_lookup_same _ _ _)
    pointerRead lengthRead data.small outArena value continued
  rw [endpoint]
  exact ⟨room,completed.answer,completed.fields,completed.stored,completed.memory⟩

def result (heap cached : BitVec 64) : BitVec 64:=if cached=0#64 then heap else cached
def resultBase (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap cached : BitVec 64) :=
  if cached=0#64 then PersistentAlloc.post source heap 32#64 else source
def nextHeap (heap cached : BitVec 64) : BitVec 64:=if cached=0#64 then PersistentAlloc.rounded heap 32#64 else heap

structure Output (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (node heap cached stp pad : BitVec 64) (value : ValueHOL 64) : Prop where
  answer : value=.val (.word (result heap cached))
  fields : MemoryMetadata.erase post=MemoryMetadata.erase (resultBase source heap cached)
  stored : post.memory (node+24#64)=.word (result heap cached)
  room : cached=0#64→heap.toNat+32≤2952790016
  memory : ∀ query : BitVec 64,query≠node+24#64→CopyGeneral.Away stp query 200→CopyGeneral.Away pad query 136→
    (cached=0#64→CopyGeneral.Away heap query 32)→post.memory query=source.memory query

set_option maxRecDepth 100000 in
/-- The complete actual helper either returns its old cache unchanged or
derives its fresh32-byte allocation and real hash/cache writes. -/
theorem body_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (node heap pointer cached stp pad : BitVec 64) (length : Nat)
    (data : Entry source node heap pointer length) (environment : CurrentKeccak.Hash.Environment source stp pad)
    (heapLower : 2701131776≤heap.toNat)
    (cacheMapped : source.memaddrs (node+24#64)) (cacheStored : source.memory (node+24#64)=.word cached)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body=(some (.returned value),post)) :
    Output source post node heap cached stp pad value := by
  rw [shapes.1] at normal
  obtain ⟨inner,continued,endpoint⟩:=declaration_return_word source post "cached" (readAt 24) cached afterCached value
    (field_read source node cached 24 data.nodeCell cacheMapped cacheStored) normal
  let entered:=bind source "cached" cached
  have cachedCell : entered.locals.lookup (ofString "cached")=some (.val (.word cached)):=bind_lookup_same _ _ _
  by_cases zero : cached=0#64
  · have skipped : evaluateHOLFiniteState entered cachedGuard=(none,entered):=by
      simp [shapes.2.2.1,evaluateHOLFiniteState_ite,evaluateHOLFiniteState_skip,evalHOLExact,toExact,localVar,cachedCell,zero,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    rw [shapes.2.1,evaluateHOLFiniteState_seq_line780,skipped] at continued
    rw [shapes.2.2.2.1] at continued
    obtain ⟨guardRun,allocationRun⟩:=Fail.guard_return entered inner missingTest [.const 13#64] allocation value data.installed continued
    have completed:=allocation_normal entered inner node heap pointer stp pad length (data.bind_cached cached) (environment.of_frame rfl) heapLower value allocationRun
    refine ⟨?_,?_,?_,?_,?_⟩
    · simpa only [result,if_pos zero] using completed.answer
    · rw [resultBase,if_pos zero,endpoint]
      exact completed.fields
    · rw [result,if_pos zero,endpoint]
      exact completed.stored
    · exact fun _=>completed.room
    · intro query away stateAway padAway outAway
      rw [endpoint]
      exact completed.memory query away stateAway padAway (outAway zero)
  · have actual : evaluateHOLFiniteState entered afterCached=(some (.returned (.val (.word cached))),emptyLocalsHOLFinite entered):=by
      simp [shapes.2.1,shapes.2.2.1,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,evaluateHOLFiniteState_return,
        evalHOLExact,toExact,localVar,cachedCell,zero,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,shapeOfHOLExact,sizeOfShapeWithContextHOL]
    have answer : value=.val (.word cached):=PanSemResultExact.returned.inj (Option.some.inj (congrArg Prod.fst (continued.symm.trans actual)))
    have innerEq : inner=emptyLocalsHOLFinite entered:=congrArg Prod.snd (continued.symm.trans actual)
    refine ⟨by simpa only [result,if_neg zero] using answer,?_,?_,by intro impossible; exact (zero impossible).elim,?_⟩
    · rw [resultBase,if_neg zero,endpoint,innerEq]
      rfl
    · rw [result,if_neg zero,endpoint,innerEq]
      exact cacheStored
    · intro query _ _ _ _
      rw [endpoint,innerEq]
      rfl

theorem Output.heap {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {node heap cached stp pad : BitVec 64} {value : ValueHOL 64}
    (output : Output source post node heap cached stp pad value)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (bounded : heap.toNat≤2952790016) (aligned : heap.toNat%8=0) :
    post.globals.lookup (ofString "heap_ptr")=some (.val (.word (nextHeap heap cached))) ∧
      heap.toNat≤(nextHeap heap cached).toNat ∧ (nextHeap heap cached).toNat≤2952790016 ∧ (nextHeap heap cached).toNat%8=0 := by
  have same:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>state.globals.lookup (ofString "heap_ptr")) output.fields
  change post.globals.lookup (ofString "heap_ptr")=(resultBase source heap cached).globals.lookup (ofString "heap_ptr") at same
  by_cases zero : cached=0#64
  · have guards:=PersistentAlloc.guards heap 32#64 (output.room zero)
    refine ⟨?_,?_,?_,?_⟩
    · simpa [resultBase,nextHeap,zero,PersistentAlloc.post,HolFiniteMapExact.update,FUPDATE] using same
    · simp only [nextHeap,if_pos zero]
      have grows:=guards.2.2.1
      change heap.toNat+32≤(PersistentAlloc.rounded heap 32#64).toNat at grows
      omega
    · simpa only [nextHeap,if_pos zero] using guards.2.2.2.1
    · simpa only [nextHeap,if_pos zero] using guards.2.2.2.2
  · simp only [resultBase,if_neg zero] at same
    simpa only [nextHeap,if_neg zero] using And.intro (same.trans heapCell) (And.intro (Nat.le_refl _) (And.intro bounded aligned))

theorem Output.heap_globals {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {node heap cached stp pad : BitVec 64} {value : ValueHOL 64}
    (output : Output source post node heap cached stp pad value) : HeapGlobals source post := by
  intro key other
  have same:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>state.globals.lookup key) output.fields
  change post.globals.lookup key=(resultBase source heap cached).globals.lookup key at same
  unfold resultBase at same
  split at same
  · exact same.trans (HeapGlobals.update source _ key other)
  · exact same

theorem Output.runtime {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {node heap cached stp pad : BitVec 64} {value : ValueHOL 64}
    (output : Output source post node heap cached stp pad value) :
    post.memaddrs=source.memaddrs ∧ post.be=source.be ∧ post.code=source.code := by
  have domain:=congrArg PanSemStateFiniteExact.memaddrs output.fields
  have endian:=congrArg PanSemStateFiniteExact.be output.fields
  have code:=congrArg PanSemStateFiniteExact.code output.fields
  change post.memaddrs=(resultBase source heap cached).memaddrs at domain
  change post.be=(resultBase source heap cached).be at endian
  change post.code=(resultBase source heap cached).code at code
  unfold resultBase at domain endian code
  split at domain <;> split at endian <;> split at code <;> exact ⟨domain,endian,code⟩

theorem Output.environment {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {node heap cached stp pad : BitVec 64} {value : ValueHOL 64}
    (output : Output source post node heap cached stp pad value) (environment : CurrentKeccak.Hash.Environment source stp pad) :
    CurrentKeccak.Hash.Environment post stp pad :=
  ⟨by rw [output.runtime.2.2]; exact environment.installed,output.runtime.1.trans environment.domain,
    (output.heap_globals _ (by decide)).trans environment.stateGlobal,(output.heap_globals _ (by decide)).trans environment.padGlobal,
    environment.stateArena,environment.padArena,environment.stateAligned,environment.padAligned⟩

/-- With the actual node/workspace extents below the persistent cap, every
normal cached-hash path preserves the entire live high scratch stack. -/
theorem Output.above_cap {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {node heap cached stp pad : BitVec 64} {value : ValueHOL 64}
    (output : Output source post node heap cached stp pad value)
    (cacheBefore : (node+24#64).toNat<2952790016) (stateBefore : stp.toNat+200≤2952790016) (padBefore : pad.toNat+136≤2952790016)
    (query : BitVec 64) (above : 2952790016≤query.toNat) : post.memory query=source.memory query := by
  exact output.memory query (by intro same; have number:=congrArg BitVec.toNat same; omega)
    (CopyGeneral.Away.before stp query 200 2952790016 stateBefore (by decide) above)
    (CopyGeneral.Away.before pad query 136 2952790016 padBefore (by decide) above)
    (fun zero=>CopyGeneral.Away.before heap query 32 2952790016 (output.room zero) (by decide) above)

end InitECandidate.Solver.Mpt.NodeHashCached

#print axioms InitECandidate.Solver.Mpt.NodeHashCached.allocation_normal
#print axioms InitECandidate.Solver.Mpt.NodeHashCached.body_normal
#print axioms InitECandidate.Solver.Mpt.NodeHashCached.Output.heap
#print axioms InitECandidate.Solver.Mpt.NodeHashCached.Output.heap_globals
#print axioms InitECandidate.Solver.Mpt.NodeHashCached.Output.runtime
#print axioms InitECandidate.Solver.Mpt.NodeHashCached.Output.environment
#print axioms InitECandidate.Solver.Mpt.NodeHashCached.Output.above_cap

namespace InitECandidate.Solver.Mpt.NodeWriteRef
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix Input
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch CurrentRlp

/-- An actual successful copy supplies its real source word through the
checked ABI. Only destination/length reads are needed to frame its writes. -/
theorem copy_dynamic_frame (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (destination sourceExpression size : ExpHOL 64)
    (dst : BitVec 64) (length : Nat) (installed : OriginalCode.Installed source.code) (small : length+32<2^64)
    (dstRead : eval source destination=some (.val (.word dst)))
    (sizeRead : eval source size=some (.val (.word (BitVec.ofNat 64 length))))
    (normal : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "memcpy") [destination,sourceExpression,size])=(none,post)) :
    WriteFrame source post dst length := by
  cases srcRead : eval source sourceExpression with
  | none=>
    have absent : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) [destination,sourceExpression,size]=none:=by
      simp only [eval] at dstRead srcRead
      simp [evalListHOLFinite,evalListHOLExact,dstRead,srcRead]
    rw [evaluateHOLFiniteState_call,absent] at normal
    cases normal
  | some loaded=>
    have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) [destination,sourceExpression,size]=
        some [.val (.word dst),loaded,.val (.word (BitVec.ofNat 64 length))]:=by
      simp only [eval] at dstRead srcRead sizeRead
      simp [evalListHOLFinite,evalListHOLExact,dstRead,srcRead,sizeRead]
    obtain ⟨funded,values,actual,callee,shape,target,value,actualArgs,called,bodyRun,checked,endpoint,fields⟩:=
      CallNormal.ignored_data source post (ofString "memcpy") [destination,sourceExpression,size] normal
    have sameValues : values=[.val (.word dst),loaded,.val (.word (BitVec.ofNat 64 length))]:=Option.some.inj (actualArgs.symm.trans args)
    subst values
    obtain ⟨actualDst,src,actualLength,dstEq,srcEq,lengthEq⟩:=CallNormal.three_scalar_words source.code.lookup (ofString "memcpy")
      (ofString "dst") (ofString "src") (ofString "n") Copy32.body actual .one shape (CopyGeneral.original_code source.code installed)
      (.val (.word dst)) loaded (.val (.word (BitVec.ofNat 64 length))) callee called
    rw [srcEq] at args
    have frame:=CopyAny.call_span_normal source post dst src length small [destination,sourceExpression,size] args installed normal
    exact ⟨frame.1.fields,frame.1.memory⟩

def taggedCopy (sourceExpression : ExpHOL 64) : ProgHOL 64:=
  .seq (.storeByte (localVar "dst") (.const 160#64))
    (.seq (.call (some (none,none)) (ofString "memcpy") [nextByte,sourceExpression,.const 32#64]) (.return (.const 33#64)))

/-- The real hash-reference writer stores exactly its one-byte tag and
32-byte payload. No readable source or owned destination is assumed. -/
theorem tagged_copy_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (dst : BitVec 64) (sourceExpression : ExpHOL 64)
    (installed : OriginalCode.Installed source.code)
    (dstCell : source.locals.lookup (ofString "dst")=some (.val (.word dst)))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source (taggedCopy sourceExpression)=(some (.returned value),post)) :
    value=.val (.word 33#64) ∧ WriteFrame source post dst 33 := by
  obtain ⟨tagged,storeRun,afterStore⟩:=sequence_returned source post _ _ value
    ((LocalPrefix.storeByte (key:=ofString "child") _ _).summary_full source).2.1 normal
  have dstRead : eval source (localVar "dst")=some (.val (.word dst)):=by simp [eval,evalHOLExact,toExact,localVar,dstCell]
  have first:=byte_store_normal_frame source tagged (localVar "dst") (.const 160#64) dst dstRead storeRun
  have firstFrame:=WriteFrame.byte source tagged dst 0#64 33 (by decide) (localVar "dst") (.const 160#64) (by simpa using dstRead) storeRun
  have taggedDst : tagged.locals.lookup (ofString "dst")=some (.val (.word dst)):=by rw [first.1]; exact dstCell
  have taggedInstalled : OriginalCode.Installed tagged.code:=by rw [first.1]; exact installed
  have nextRead : eval tagged nextByte=some (.val (.word (dst+1#64))):=by
    simp [eval,nextByte,evalHOLExact,evalListHOLExact,toExact,localVar,taggedDst,valueIsWord,valueWord,wordOpHOL,wordOp]
  obtain ⟨copied,copyRun,returnRun⟩:=sequence_returned tagged post _ _ value
    ((LocalPrefix.call (key:=ofString "child") none _ _ (by intro name same; cases same)).summary_full tagged).2.1 afterStore
  have copiedFrame:=copy_dynamic_frame tagged copied nextByte sourceExpression (.const 32#64) (dst+1#64) 32 taggedInstalled (by decide) nextRead rfl copyRun
  have secondFrame:=WriteFrame.shift dst 1 32 33 copiedFrame (by decide)
  obtain ⟨returned,endpoint⟩:=return_normal copied post (.const 33#64) value returnRun
  have answer : value=.val (.word 33#64):=Option.some.inj returned.symm
  have lastFrame : WriteFrame copied post dst 33:=by rw [endpoint]; exact ⟨rfl,by intros; rfl⟩
  exact ⟨answer,(firstFrame.trans secondFrame).trans lastFrame⟩

theorem hash_branch_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (dst : BitVec 64)
    (installed : OriginalCode.Installed source.code) (dstCell : source.locals.lookup (ofString "dst")=some (.val (.word dst)))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source hashBranch=(some (.returned value),post)) :
    value=.val (.word 33#64) ∧ WriteFrame source post dst 33:=
  tagged_copy_normal source post dst (readAt 24) installed dstCell value normal

theorem digest_branch_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (dst : BitVec 64)
    (installed : OriginalCode.Installed source.code) (dstCell : source.locals.lookup (ofString "dst")=some (.val (.word dst)))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source digestBranch=(some (.returned value),post)) :
    value=.val (.word 33#64) ∧ WriteFrame source post dst 33:=
  tagged_copy_normal source post dst (localVar "h") installed dstCell value normal

theorem null_branch_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (dst : BitVec 64)
    (dstCell : source.locals.lookup (ofString "dst")=some (.val (.word dst)))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source nullBranch=(some (.returned value),post)) :
    value=.val (.word 1#64) ∧ WriteFrame source post dst 1 := by
  obtain ⟨tagged,storeRun,returnRun⟩:=sequence_returned source post _ _ value
    ((LocalPrefix.storeByte (key:=ofString "child") _ _).summary_full source).2.1 normal
  have read : eval source (localVar "dst")=some (.val (.word dst)):=by simp [eval,evalHOLExact,toExact,localVar,dstCell]
  have first:=WriteFrame.byte source tagged dst 0#64 1 (by decide) (localVar "dst") (.const 128#64) (by simpa using read) storeRun
  obtain ⟨returned,endpoint⟩:=return_normal tagged post (.const 1#64) value returnRun
  have answer : value=.val (.word 1#64):=Option.some.inj returned.symm
  have last : WriteFrame tagged post dst 1:=by rw [endpoint]; exact ⟨rfl,by intros; rfl⟩
  exact ⟨answer,first.trans last⟩

theorem short_branch_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (dst pointer : BitVec 64) (length : Nat)
    (installed : OriginalCode.Installed source.code) (small : length<32)
    (dstCell : source.locals.lookup (ofString "dst")=some (.val (.word dst)))
    (pointerCell : source.locals.lookup (ofString "rp")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "rl")=some (.val (.word (BitVec.ofNat 64 length))))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source shortBranch=(some (.returned value),post)) :
    value=.val (.word (BitVec.ofNat 64 length)) ∧ WriteFrame source post dst length := by
  obtain ⟨copied,copyRun,returnRun⟩:=sequence_returned source post shortCopy _ value
    ((LocalPrefix.call (key:=ofString "rl") none _ _ (by intro name same; cases same)).summary_full source).2.1 normal
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) [localVar "dst",localVar "rp",localVar "rl"]=
      some (CopyGeneral.values dst pointer length):=by
    simp [CopyGeneral.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,dstCell,pointerCell,lengthCell]
  obtain ⟨frame,localsEq⟩:=CopyAny.call_span_normal source copied dst pointer length (by omega) _ args installed copyRun
  obtain ⟨returned,endpoint⟩:=return_normal copied post (localVar "rl") value returnRun
  have read : eval copied (localVar "rl")=some (.val (.word (BitVec.ofNat 64 length))):=by
    simp [eval,evalHOLExact,toExact,localVar,localsEq,lengthCell]
  have answer : value=.val (.word (BitVec.ofNat 64 length)):=Option.some.inj (returned.symm.trans read)
  rw [endpoint]
  exact ⟨answer,frame.fields,frame.memory⟩

end InitECandidate.Solver.Mpt.NodeWriteRef

#print axioms InitECandidate.Solver.Mpt.NodeWriteRef.copy_dynamic_frame
#print axioms InitECandidate.Solver.Mpt.NodeWriteRef.tagged_copy_normal
#print axioms InitECandidate.Solver.Mpt.NodeWriteRef.hash_branch_normal
#print axioms InitECandidate.Solver.Mpt.NodeWriteRef.digest_branch_normal
#print axioms InitECandidate.Solver.Mpt.NodeWriteRef.null_branch_normal
#print axioms InitECandidate.Solver.Mpt.NodeWriteRef.short_branch_normal

namespace InitECandidate.Solver.Mpt.NodeWriteRef
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix Input
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch CurrentRlp

structure DigestOutput (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (child dst heap cached stp pad : BitVec 64) (value : ValueHOL 64) : Prop where
  answer : value=.val (.word 33#64)
  room : cached=0#64→heap.toNat+32≤2952790016
  fields : MemoryMetadata.erase post=MemoryMetadata.erase (NodeHashCached.resultBase source heap cached)
  memory : ∀ query : BitVec 64,CopyGeneral.Away dst query 33→query≠child+24#64→CopyGeneral.Away stp query 200→CopyGeneral.Away pad query 136→
    (cached=0#64→CopyGeneral.Away heap query 32)→post.memory query=source.memory query

set_option maxRecDepth 100000 in
/-- The actual scoped cached-hash call supplies its real allocation/cache
frame. The following tag and copy add precisely the33-byte reference span. -/
theorem digest_scope_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (child dst heap pointer cached stp pad : BitVec 64) (length : Nat)
    (data : NodeHashCached.Data source child heap pointer length) (environment : CurrentKeccak.Hash.Environment source stp pad)
    (heapLower : 2701131776≤heap.toNat)
    (childCell : source.locals.lookup (ofString "child")=some (.val (.word child)))
    (dstCell : source.locals.lookup (ofString "dst")=some (.val (.word dst)))
    (cacheMapped : source.memaddrs (child+24#64)) (cacheStored : source.memory (child+24#64)=.word cached)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source digestScope=(some (.returned value),post)) :
    DigestOutput source post child dst heap cached stp pad value := by
  obtain ⟨callee,called,nodeCell⟩:=CallNormal.unary_environment source.code.lookup (ofString "node_hash_cached") "node"
    NodeHashCached.body child (NodeHashCached.original_code source.code data.installed)
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) [localVar "child"]=some [.val (.word child)]:=by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,childCell]
  obtain ⟨funded,hashed,returned,inner,hashRun,checked,continued,endpoint⟩:=CallNormal.scoped_normal source post "h" .one (ofString "node_hash_cached")
    [localVar "child"] [.val (.word child)] NodeHashCached.body digestBranch callee .one args called value normal
  have readyData : NodeHashCached.Entry (callEntryStateHOLFinite source callee) child heap pointer length:={toData:=data.of_frame rfl,nodeCell:=nodeCell}
  have hashedOutput:=NodeHashCached.body_normal (callEntryStateHOLFinite source callee) hashed child heap pointer cached stp pad length readyData
    (environment.of_frame rfl) heapLower cacheMapped cacheStored returned hashRun
  let ready:=CallNormal.continuationEntry source hashed "h" returned
  have readyDst : ready.locals.lookup (ofString "dst")=some (.val (.word dst)):=
    (CallNormal.continuation_lookup_other source hashed "h" "dst" returned (by decide)).trans dstCell
  have readyInstalled : OriginalCode.Installed ready.code:=by change OriginalCode.Installed hashed.code; rw [hashedOutput.runtime.2.2]; exact data.installed
  obtain ⟨answer,written⟩:=digest_branch_normal ready inner dst readyInstalled readyDst value continued
  refine ⟨answer,hashedOutput.room,?_,?_⟩
  · rw [endpoint]
    have readyFrame : MemoryMetadata.erase ready=MemoryMetadata.erase hashed:=rfl
    have baseFrame : MemoryMetadata.erase (NodeHashCached.resultBase (callEntryStateHOLFinite source callee) heap cached)=
        MemoryMetadata.erase (NodeHashCached.resultBase source heap cached):=by
      unfold NodeHashCached.resultBase
      split <;> rfl
    exact written.metadata.trans (readyFrame.trans (hashedOutput.fields.trans baseFrame))
  · intro query dstAway notCache stateAway padAway outAway
    rw [endpoint]
    exact (written.memory query dstAway).trans (hashedOutput.memory query notCache stateAway padAway outAway)

end InitECandidate.Solver.Mpt.NodeWriteRef

#print axioms InitECandidate.Solver.Mpt.NodeWriteRef.digest_scope_normal

namespace InitECandidate.Solver.Mpt.NodeWriteRef
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix Input
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch CurrentRlp

def outputBase (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap cached : BitVec 64) (hashed : Bool) :=
  if hashed then NodeHashCached.resultBase source heap cached else source

structure Output (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (child dst heap cached stp pad : BitVec 64) (value : ValueHOL 64) where
  bytes : Nat
  bounded : bytes≤33
  hashed : Bool
  answer : value=.val (.word (BitVec.ofNat 64 bytes))
  fields : MemoryMetadata.erase post=MemoryMetadata.erase (outputBase source heap cached hashed)
  room : hashed=true→cached=0#64→heap.toNat+32≤2952790016
  memory : ∀ query : BitVec 64,CopyGeneral.Away dst query bytes→query≠child+24#64→CopyGeneral.Away stp query 200→CopyGeneral.Away pad query 136→
    (hashed=true→cached=0#64→CopyGeneral.Away heap query 32)→post.memory query=source.memory query

def Output.of_write {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {child dst heap cached stp pad : BitVec 64} {value : ValueHOL 64}
    (bytes : Nat) (bounded : bytes≤33) (answer : value=.val (.word (BitVec.ofNat 64 bytes))) (frame : WriteFrame source post dst bytes) :
    Output source post child dst heap cached stp pad value:={
  bytes:=bytes,bounded:=bounded,hashed:=false,answer:=answer,fields:=frame.metadata,room:=by intro impossible; cases impossible
  memory:=by intro query away _ _ _ _; exact frame.memory query away }

def Output.of_digest {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {child dst heap cached stp pad : BitVec 64} {value : ValueHOL 64}
    (output : DigestOutput source post child dst heap cached stp pad value) : Output source post child dst heap cached stp pad value:={
  bytes:=33,bounded:=by decide,hashed:=true,answer:=output.answer,fields:=output.fields,room:=fun _=>output.room
  memory:=fun query away notCache stateAway padAway outAway=>output.memory query away notCache stateAway padAway (outAway rfl) }

theorem output_base_frame {source outer : PanSemStateFiniteExact 64 Guest.HostMemory} (heap cached : BitVec 64) (hashed : Bool)
    (frame : LocalEffects.erase source=LocalEffects.erase outer) :
    MemoryMetadata.erase (outputBase source heap cached hashed)=MemoryMetadata.erase (outputBase outer heap cached hashed) := by
  unfold outputBase
  split
  · unfold NodeHashCached.resultBase
    split
    · have same:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>MemoryMetadata.erase (PersistentAlloc.post state heap 32#64)) frame
      exact same
    · exact MemoryMetadata.of_frame frame
  · exact MemoryMetadata.of_frame frame

def Output.reframe {source post outer final : PanSemStateFiniteExact 64 Guest.HostMemory} {child dst heap cached stp pad : BitVec 64} {value : ValueHOL 64}
    (output : Output source post child dst heap cached stp pad value)
    (first : LocalEffects.erase source=LocalEffects.erase outer) (last : LocalEffects.erase final=LocalEffects.erase post) :
    Output outer final child dst heap cached stp pad value:={
  bytes:=output.bytes,bounded:=output.bounded,hashed:=output.hashed,answer:=output.answer,room:=output.room
  fields:=(MemoryMetadata.of_frame last).trans (output.fields.trans (output_base_frame heap cached output.hashed first))
  memory:=fun query away notCache stateAway padAway outAway=>
    (congrFun (LocalEffects.memory_of_erase post final last) query).trans
      ((output.memory query away notCache stateAway padAway outAway).trans (congrFun (LocalEffects.memory_of_erase outer source first) query)) }

theorem sequence_of_stops (source : PanSemStateFiniteExact 64 Guest.HostMemory) (first second : ProgHOL 64)
    (stops : (evaluateHOLFiniteState source first).1≠none) : evaluateHOLFiniteState source (.seq first second)=evaluateHOLFiniteState source first := by
  rw [evaluateHOLFiniteState_seq_line780]
  generalize computed : evaluateHOLFiniteState source first=output at stops ⊢
  obtain ⟨result,post⟩:=output
  cases result with
  | none=>exact (stops rfl).elim
  | some result=>rfl

def referenceBytes (child tag : BitVec 64) (length : Nat) : Nat:=
  if child=0#64 then 1 else if tag=0#64 then 33 else if length<32 then length else 33

theorem reference_bytes_bound (child tag : BitVec 64) (length : Nat) : referenceBytes child tag length≤33 := by
  unfold referenceBytes
  split
  · omega
  · split
    · omega
    · split <;> omega

/-- The writer's exact byte count agrees with the earlier reference-length
helper, using the same physical child tag and representable cache length. -/
theorem reference_word_eq (child tag : BitVec 64) (length : Nat) (small : length<2^64) :
    NodeRefLen.referenceWord child tag (BitVec.ofNat 64 length)=BitVec.ofNat 64 (referenceBytes child tag length) := by
  have number : (BitVec.ofNat 64 length).toNat=length:=by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt small]
  unfold NodeRefLen.referenceWord referenceBytes
  split
  · rfl
  · split
    · rfl
    · rw [number]
      split <;> rfl

set_option maxRecDepth 100000 in
theorem length_tail_normal_exact (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (child dst heap pointer cached stp pad : BitVec 64) (length : Nat)
    (data : NodeHashCached.Data source child heap pointer length) (environment : CurrentKeccak.Hash.Environment source stp pad)
    (heapLower : 2701131776≤heap.toNat)
    (childCell : source.locals.lookup (ofString "child")=some (.val (.word child)))
    (dstCell : source.locals.lookup (ofString "dst")=some (.val (.word dst)))
    (pointerCell : source.locals.lookup (ofString "rp")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "rl")=some (.val (.word (BitVec.ofNat 64 length))))
    (cacheMapped : source.memaddrs (child+24#64)) (cacheStored : source.memory (child+24#64)=.word cached)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source lengthTail=(some (.returned value),post)) :
    ∃ output : Output source post child dst heap cached stp pad value,output.bytes=(if length<32 then length else 33) := by
  have number : (BitVec.ofNat 64 length).toNat=length:=by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by have small:=data.small; omega)]
  by_cases short : length<32
  · have chosen : evaluateHOLFiniteState source lengthTail=evaluateHOLFiniteState source (.seq shortBranch digestScope):=by
      simp [lengthTail,shortTest,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,evalHOLExact,toExact,localVar,lengthCell,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,number,short]
    have selected:=chosen.trans (sequence_of_stops source shortBranch digestScope (short_branch_stops source))
    obtain ⟨answer,frame⟩:=short_branch_normal source post dst pointer length data.installed short dstCell pointerCell lengthCell value (selected.symm.trans normal)
    exact ⟨Output.of_write length (by omega) answer frame,by simp only [Output.of_write,if_pos short]⟩
  · have selected : evaluateHOLFiniteState source lengthTail=evaluateHOLFiniteState source digestScope:=by
      simp [lengthTail,shortTest,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,evaluateHOLFiniteState_skip,evalHOLExact,toExact,localVar,lengthCell,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,number,short]
    exact ⟨Output.of_digest (digest_scope_normal source post child dst heap pointer cached stp pad length data environment heapLower
      childCell dstCell cacheMapped cacheStored value (selected.symm.trans normal)),by simp only [Output.of_digest,if_neg short]⟩

theorem length_tail_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (child dst heap pointer cached stp pad : BitVec 64) (length : Nat)
    (data : NodeHashCached.Data source child heap pointer length) (environment : CurrentKeccak.Hash.Environment source stp pad)
    (heapLower : 2701131776≤heap.toNat)
    (childCell : source.locals.lookup (ofString "child")=some (.val (.word child)))
    (dstCell : source.locals.lookup (ofString "dst")=some (.val (.word dst)))
    (pointerCell : source.locals.lookup (ofString "rp")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "rl")=some (.val (.word (BitVec.ofNat 64 length))))
    (cacheMapped : source.memaddrs (child+24#64)) (cacheStored : source.memory (child+24#64)=.word cached)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source lengthTail=(some (.returned value),post)) :
    Nonempty (Output source post child dst heap cached stp pad value) := by
  obtain ⟨output,_size⟩:=length_tail_normal_exact source post child dst heap pointer cached stp pad length data environment heapLower
    childCell dstCell pointerCell lengthCell cacheMapped cacheStored value normal
  exact ⟨output⟩

set_option maxRecDepth 100000 in
theorem after_cache_normal_exact (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (child dst heap pointer cached stp pad : BitVec 64) (length : Nat)
    (data : NodeHashCached.Data source child heap pointer length) (environment : CurrentKeccak.Hash.Environment source stp pad)
    (heapLower : 2701131776≤heap.toNat)
    (childCell : source.locals.lookup (ofString "child")=some (.val (.word child)))
    (dstCell : source.locals.lookup (ofString "dst")=some (.val (.word dst)))
    (cacheMapped : source.memaddrs (child+24#64)) (cacheStored : source.memory (child+24#64)=.word cached)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source afterCache=(some (.returned value),post)) :
    ∃ output : Output source post child dst heap cached stp pad value,output.bytes=(if length<32 then length else 33) := by
  obtain ⟨inner,continued,endpoint⟩:=declaration_return_word source post "rp" (readAt 8) pointer afterPointer value
    (field_read source child pointer 8 childCell data.pointerMapped data.pointerStored) normal
  let first:=bind source "rp" pointer
  have firstChild : first.locals.lookup (ofString "child")=some (.val (.word child)):=
    (bind_lookup_other source "rp" "child" pointer (by decide)).trans childCell
  have firstDst : first.locals.lookup (ofString "dst")=some (.val (.word dst)):=
    (bind_lookup_other source "rp" "dst" pointer (by decide)).trans dstCell
  obtain ⟨last,lengthRun,lengthEndpoint⟩:=declaration_return_word first inner "rl" (readAt 16) (BitVec.ofNat 64 length) lengthTail value
    (field_read first child (BitVec.ofNat 64 length) 16 firstChild data.lengthMapped data.lengthStored) continued
  let entered:=bind first "rl" (BitVec.ofNat 64 length)
  obtain ⟨output,size⟩:=length_tail_normal_exact entered last child dst heap pointer cached stp pad length (data.of_frame rfl) (environment.of_frame rfl) heapLower
    ((bind_lookup_other first "rl" "child" _ (by decide)).trans firstChild) ((bind_lookup_other first "rl" "dst" _ (by decide)).trans firstDst)
    ((bind_lookup_other first "rl" "rp" _ (by decide)).trans (bind_lookup_same _ _ _)) (bind_lookup_same _ _ _)
    cacheMapped cacheStored value lengthRun
  exact ⟨output.reframe rfl (by rw [endpoint,lengthEndpoint]; rfl),size⟩

theorem after_cache_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (child dst heap pointer cached stp pad : BitVec 64) (length : Nat)
    (data : NodeHashCached.Data source child heap pointer length) (environment : CurrentKeccak.Hash.Environment source stp pad)
    (heapLower : 2701131776≤heap.toNat)
    (childCell : source.locals.lookup (ofString "child")=some (.val (.word child)))
    (dstCell : source.locals.lookup (ofString "dst")=some (.val (.word dst)))
    (cacheMapped : source.memaddrs (child+24#64)) (cacheStored : source.memory (child+24#64)=.word cached)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source afterCache=(some (.returned value),post)) :
    Nonempty (Output source post child dst heap cached stp pad value) := by
  obtain ⟨output,_size⟩:=after_cache_normal_exact source post child dst heap pointer cached stp pad length data environment heapLower
    childCell dstCell cacheMapped cacheStored value normal
  exact ⟨output⟩

end InitECandidate.Solver.Mpt.NodeWriteRef

#print axioms InitECandidate.Solver.Mpt.NodeWriteRef.output_base_frame
#print axioms InitECandidate.Solver.Mpt.NodeWriteRef.sequence_of_stops
#print axioms InitECandidate.Solver.Mpt.NodeWriteRef.length_tail_normal
#print axioms InitECandidate.Solver.Mpt.NodeWriteRef.after_cache_normal

namespace InitECandidate.Solver.Mpt.NodeWriteRef
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix Input
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch CurrentRlp

theorem stopping_guard_selected (source : PanSemStateFiniteExact 64 Guest.HostMemory) (test : ExpHOL 64) (first second : ProgHOL 64)
    (read : eval source test=some (.val (.word 1#64))) (stops : (evaluateHOLFiniteState source first).1≠none) :
    evaluateHOLFiniteState source (.seq (.ite test first .skip) second)=evaluateHOLFiniteState source first := by
  have selected : evaluateHOLFiniteState source (.ite test first .skip)=evaluateHOLFiniteState source first:=by
    simp only [eval] at read
    simp [evaluateHOLFiniteState_ite,read]
  calc
    _=evaluateHOLFiniteState source (.seq first second):=by simp only [evaluateHOLFiniteState_seq_line780,selected]
    _=evaluateHOLFiniteState source first:=sequence_of_stops source first second stops

theorem stopping_guard_skipped (source : PanSemStateFiniteExact 64 Guest.HostMemory) (test : ExpHOL 64) (first second : ProgHOL 64)
    (read : eval source test=some (.val (.word 0#64))) :
    evaluateHOLFiniteState source (.seq (.ite test first .skip) second)=evaluateHOLFiniteState source second := by
  simp only [eval] at read
  simp [evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,evaluateHOLFiniteState_skip,read]

set_option maxRecDepth 100000 in
/-- The complete actual writer normal frame. Earlier guards derive the
nonnull/populated-cache conditions before those data are required. Every
successful branch reports and protects exactly its own written byte count. -/
theorem body_normal_exact (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (child dst tag heap pointer cached stp pad : BitVec 64) (length : Nat)
    (environment : CurrentKeccak.Hash.Environment source stp pad) (heapLower : 2701131776≤heap.toNat)
    (childCell : source.locals.lookup (ofString "child")=some (.val (.word child)))
    (dstCell : source.locals.lookup (ofString "dst")=some (.val (.word dst)))
    (header : child≠0#64→source.memaddrs child ∧ source.memory child=.word tag)
    (cache : child≠0#64→tag≠0#64→source.memaddrs (child+8#64) ∧ source.memory (child+8#64)=.word pointer)
    (data : child≠0#64→tag≠0#64→pointer≠0#64→NodeHashCached.Data source child heap pointer length)
    (digest : child≠0#64→tag≠0#64→pointer≠0#64→source.memaddrs (child+24#64) ∧ source.memory (child+24#64)=.word cached)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body=(some (.returned value),post)) :
    ∃ output : Output source post child dst heap cached stp pad value,output.bytes=referenceBytes child tag length := by
  by_cases null : child=0#64
  · have read : eval source nullTest=some (.val (.word 1#64)):=by
      simp [eval,nullTest,evalHOLExact,toExact,localVar,childCell,null,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    have selected:=stopping_guard_selected source nullTest nullBranch afterNull read (null_branch_stops source)
    rw [←body_shape] at selected
    obtain ⟨answer,frame⟩:=null_branch_normal source post dst dstCell value (selected.symm.trans normal)
    exact ⟨Output.of_write 1 (by decide) answer frame,by simp only [Output.of_write,referenceBytes,if_pos null]⟩
  · have read : eval source nullTest=some (.val (.word 0#64)):=by
      simp [eval,nullTest,evalHOLExact,toExact,localVar,childCell,null,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    have selected:=stopping_guard_skipped source nullTest nullBranch afterNull read
    rw [←body_shape] at selected
    have afterNullRun:=selected.symm.trans normal
    obtain ⟨headerMapped,headerStored⟩:=header null
    have headerRead:=field_read source child tag 0 childCell (by simpa using headerMapped) (by simpa using headerStored)
    by_cases isHash : tag=0#64
    · have tagRead : eval source hashTest=some (.val (.word 1#64)):=by
        simp only [eval] at headerRead
        simp [eval,hashTest,evalHOLExact,headerRead,isHash,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
      have chosen:=stopping_guard_selected source hashTest hashBranch afterHash tagRead (hash_branch_stops source)
      obtain ⟨answer,frame⟩:=hash_branch_normal source post dst environment.installed dstCell value (chosen.symm.trans afterNullRun)
      exact ⟨Output.of_write 33 (by decide) answer frame,by simp only [Output.of_write,referenceBytes,if_neg null,if_pos isHash]⟩
    · have tagRead : eval source hashTest=some (.val (.word 0#64)):=by
        simp only [eval] at headerRead
        simp [eval,hashTest,evalHOLExact,headerRead,isHash,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
      have chosen:=stopping_guard_skipped source hashTest hashBranch afterHash tagRead
      have afterHashRun:=chosen.symm.trans afterNullRun
      obtain ⟨passed,cacheRun⟩:=Fail.guard_return source post missingTest [.const 13#64] afterCache value environment.installed afterHashRun
      obtain ⟨mapped,stored⟩:=cache null isHash
      have populated : pointer≠0#64:=by
        intro zero
        have pointerRead:=field_read source child pointer 8 childCell mapped stored
        have expected : eval source missingTest=some (.val (.word 1#64)):=by
          simp only [eval] at pointerRead
          simp [eval,missingTest,evalHOLExact,pointerRead,zero,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
        have actual:=(Fail.guard_normal source source missingTest [.const 13#64] environment.installed passed).1
        have impossible : (1#64 : BitVec 64)=0#64:=by simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using expected.symm.trans actual
        exact (by decide : (1#64 : BitVec 64)≠0#64) impossible
      obtain ⟨digestMapped,digestStored⟩:=digest null isHash populated
      obtain ⟨output,size⟩:=after_cache_normal_exact source post child dst heap pointer cached stp pad length (data null isHash populated) environment heapLower
        childCell dstCell digestMapped digestStored value cacheRun
      exact ⟨output,by simpa only [referenceBytes,if_neg null,if_neg isHash] using size⟩

theorem body_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (child dst tag heap pointer cached stp pad : BitVec 64) (length : Nat)
    (environment : CurrentKeccak.Hash.Environment source stp pad) (heapLower : 2701131776≤heap.toNat)
    (childCell : source.locals.lookup (ofString "child")=some (.val (.word child)))
    (dstCell : source.locals.lookup (ofString "dst")=some (.val (.word dst)))
    (header : child≠0#64→source.memaddrs child ∧ source.memory child=.word tag)
    (cache : child≠0#64→tag≠0#64→source.memaddrs (child+8#64) ∧ source.memory (child+8#64)=.word pointer)
    (data : child≠0#64→tag≠0#64→pointer≠0#64→NodeHashCached.Data source child heap pointer length)
    (digest : child≠0#64→tag≠0#64→pointer≠0#64→source.memaddrs (child+24#64) ∧ source.memory (child+24#64)=.word cached)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body=(some (.returned value),post)) :
    Nonempty (Output source post child dst heap cached stp pad value) := by
  obtain ⟨output,_size⟩:=body_normal_exact source post child dst tag heap pointer cached stp pad length environment heapLower
    childCell dstCell header cache data digest value normal
  exact ⟨output⟩

theorem Output.heap_globals {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {child dst heap cached stp pad : BitVec 64} {value : ValueHOL 64}
    (output : Output source post child dst heap cached stp pad value) : HeapGlobals source post := by
  intro key other
  have same:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>state.globals.lookup key) output.fields
  change post.globals.lookup key=(outputBase source heap cached output.hashed).globals.lookup key at same
  unfold outputBase at same
  split at same
  · unfold NodeHashCached.resultBase at same
    split at same
    · exact same.trans (HeapGlobals.update source _ key other)
    · exact same
  · exact same

theorem Output.runtime {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {child dst heap cached stp pad : BitVec 64} {value : ValueHOL 64}
    (output : Output source post child dst heap cached stp pad value) :
    post.memaddrs=source.memaddrs ∧ post.be=source.be ∧ post.code=source.code := by
  have domain:=congrArg PanSemStateFiniteExact.memaddrs output.fields
  have endian:=congrArg PanSemStateFiniteExact.be output.fields
  have code:=congrArg PanSemStateFiniteExact.code output.fields
  change post.memaddrs=(outputBase source heap cached output.hashed).memaddrs at domain
  change post.be=(outputBase source heap cached output.hashed).be at endian
  change post.code=(outputBase source heap cached output.hashed).code at code
  have baseDomain : (outputBase source heap cached output.hashed).memaddrs=source.memaddrs:=by
    unfold outputBase; split; unfold NodeHashCached.resultBase; split <;> rfl; rfl
  have baseEndian : (outputBase source heap cached output.hashed).be=source.be:=by
    unfold outputBase; split; unfold NodeHashCached.resultBase; split <;> rfl; rfl
  have baseCode : (outputBase source heap cached output.hashed).code=source.code:=by
    unfold outputBase; split; unfold NodeHashCached.resultBase; split <;> rfl; rfl
  exact ⟨domain.trans baseDomain,endian.trans baseEndian,code.trans baseCode⟩

theorem Output.above_cap {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {child dst heap cached stp pad : BitVec 64} {value : ValueHOL 64}
    (output : Output source post child dst heap cached stp pad value)
    (dstBefore : dst.toNat+output.bytes≤2952790016) (cacheBefore : (child+24#64).toNat<2952790016)
    (stateBefore : stp.toNat+200≤2952790016) (padBefore : pad.toNat+136≤2952790016)
    (query : BitVec 64) (above : 2952790016≤query.toNat) : post.memory query=source.memory query := by
  exact output.memory query (CopyGeneral.Away.before dst query output.bytes 2952790016 dstBefore (by decide) above)
    (by intro same; have number:=congrArg BitVec.toNat same; omega)
    (CopyGeneral.Away.before stp query 200 2952790016 stateBefore (by decide) above)
    (CopyGeneral.Away.before pad query 136 2952790016 padBefore (by decide) above)
    (fun hashed zero=>CopyGeneral.Away.before heap query 32 2952790016 (output.room hashed zero) (by decide) above)

end InitECandidate.Solver.Mpt.NodeWriteRef

#print axioms InitECandidate.Solver.Mpt.NodeWriteRef.body_normal
#print axioms InitECandidate.Solver.Mpt.NodeWriteRef.Output.heap_globals
#print axioms InitECandidate.Solver.Mpt.NodeWriteRef.Output.runtime
#print axioms InitECandidate.Solver.Mpt.NodeWriteRef.Output.above_cap

namespace InitECandidate.Solver.Mpt.NodeWriteRef
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix Input
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch CurrentRlp

def outputHeap (heap cached : BitVec 64) (hashed : Bool) := if hashed then NodeHashCached.nextHeap heap cached else heap

theorem Output.heap {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {child dst heap cached stp pad : BitVec 64} {value : ValueHOL 64}
    (output : Output source post child dst heap cached stp pad value)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (bounded : heap.toNat≤2952790016) (aligned : heap.toNat%8=0) :
    post.globals.lookup (ofString "heap_ptr")=some (.val (.word (outputHeap heap cached output.hashed))) ∧
      heap.toNat≤(outputHeap heap cached output.hashed).toNat ∧ (outputHeap heap cached output.hashed).toNat≤2952790016 ∧
      (outputHeap heap cached output.hashed).toNat%8=0 := by
  have same:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>state.globals.lookup (ofString "heap_ptr")) output.fields
  change post.globals.lookup (ofString "heap_ptr")=(outputBase source heap cached output.hashed).globals.lookup (ofString "heap_ptr") at same
  cases hashed : output.hashed with
  | false=>
    simp only [outputBase,hashed,Bool.false_eq_true,if_false] at same
    simpa only [outputHeap,hashed,Bool.false_eq_true,if_false] using And.intro (same.trans heapCell) (And.intro (Nat.le_refl _) (And.intro bounded aligned))
  | true=>
    by_cases zero : cached=0#64
    · have guards:=PersistentAlloc.guards heap 32#64 (output.room hashed zero)
      refine ⟨?_,?_,?_,?_⟩
      · simpa [outputBase,outputHeap,hashed,NodeHashCached.resultBase,NodeHashCached.nextHeap,zero,PersistentAlloc.post,HolFiniteMapExact.update,FUPDATE] using same
      · simp only [outputHeap,hashed,↓reduceIte,NodeHashCached.nextHeap,if_pos zero]
        have grows:=guards.2.2.1
        change heap.toNat+32≤(PersistentAlloc.rounded heap 32#64).toNat at grows
        omega
      · simpa only [outputHeap,hashed,↓reduceIte,NodeHashCached.nextHeap,if_pos zero] using guards.2.2.2.1
      · simpa only [outputHeap,hashed,↓reduceIte,NodeHashCached.nextHeap,if_pos zero] using guards.2.2.2.2
    · simp only [outputBase,hashed,↓reduceIte,NodeHashCached.resultBase,if_neg zero] at same
      simpa only [outputHeap,hashed,↓reduceIte,NodeHashCached.nextHeap,if_neg zero] using
        And.intro (same.trans heapCell) (And.intro (Nat.le_refl _) (And.intro bounded aligned))

theorem Output.environment {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {child dst heap cached stp pad : BitVec 64} {value : ValueHOL 64}
    (output : Output source post child dst heap cached stp pad value) (environment : CurrentKeccak.Hash.Environment source stp pad) :
    CurrentKeccak.Hash.Environment post stp pad :=
  ⟨by rw [output.runtime.2.2]; exact environment.installed,output.runtime.1.trans environment.domain,
    (output.heap_globals _ (by decide)).trans environment.stateGlobal,(output.heap_globals _ (by decide)).trans environment.padGlobal,
    environment.stateArena,environment.padArena,environment.stateAligned,environment.padAligned⟩

set_option maxRecDepth 100000 in
/-- A genuine checked scoped call supplies its real written length,
caller result binding and whole writer frame for the finish-loop step. -/
theorem reached_normal_exact (source current : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String) (arguments : List (ExpHOL 64))
    (child dst tag heap pointer cached stp pad : BitVec 64) (length : Nat)
    (environment : CurrentKeccak.Hash.Environment source stp pad) (heapLower : 2701131776≤heap.toNat)
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=some [.val (.word child),.val (.word dst)])
    (header : child≠0#64→source.memaddrs child ∧ source.memory child=.word tag)
    (cache : child≠0#64→tag≠0#64→source.memaddrs (child+8#64) ∧ source.memory (child+8#64)=.word pointer)
    (data : child≠0#64→tag≠0#64→pointer≠0#64→NodeHashCached.Data source child heap pointer length)
    (digest : child≠0#64→tag≠0#64→pointer≠0#64→source.memaddrs (child+24#64) ∧ source.memory (child+24#64)=.word cached)
    (reached : CallPrefix.Reaches source (.scoped (ofString name) .one (ofString "node_write_ref") arguments) current) :
    current.locals.lookup (ofString name)=some (.val (.word (BitVec.ofNat 64 (referenceBytes child tag length)))) ∧
      ∃ output : Output source current child dst heap cached stp pad (.val (.word (BitVec.ofNat 64 (referenceBytes child tag length)))),
        output.bytes=referenceBytes child tag length := by
  obtain ⟨callee,called,childCell,dstCell⟩:=NodeWriteRef.environment source.code.lookup child dst (original_code source.code environment.installed)
  obtain ⟨target,returned,run,endpoint⟩:=reached.scoped_known (ofString name) .one (ofString "node_write_ref") arguments
    [.val (.word child),.val (.word dst)] body callee .one args called
  obtain ⟨output,size⟩:=body_normal_exact (callEntryStateHOLFinite source callee) target child dst tag heap pointer cached stp pad length
    (environment.of_frame rfl) heapLower childCell dstCell header cache (fun active nonHash populated=>(data active nonHash populated).of_frame rfl) digest returned run
  let lifted : Output source current child dst heap cached stp pad returned:=output.reframe rfl (by rw [endpoint]; rfl)
  have answer : returned=.val (.word (BitVec.ofNat 64 (referenceBytes child tag length))):=by rw [output.answer,size]
  have exactSize : lifted.bytes=referenceBytes child tag length:=size
  refine ⟨?_,?_⟩
  · rw [endpoint]
    have assigned : (setVarHOLFinite (ofString name) returned {target with locals:=source.locals}).locals.lookup (ofString name)=some returned:=by
      simp [setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
    exact assigned.trans (congrArg some answer)
  · subst returned
    exact ⟨lifted,exactSize⟩

theorem reached_normal (source current : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String) (arguments : List (ExpHOL 64))
    (child dst tag heap pointer cached stp pad : BitVec 64) (length : Nat)
    (environment : CurrentKeccak.Hash.Environment source stp pad) (heapLower : 2701131776≤heap.toNat)
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=some [.val (.word child),.val (.word dst)])
    (header : child≠0#64→source.memaddrs child ∧ source.memory child=.word tag)
    (cache : child≠0#64→tag≠0#64→source.memaddrs (child+8#64) ∧ source.memory (child+8#64)=.word pointer)
    (data : child≠0#64→tag≠0#64→pointer≠0#64→NodeHashCached.Data source child heap pointer length)
    (digest : child≠0#64→tag≠0#64→pointer≠0#64→source.memaddrs (child+24#64) ∧ source.memory (child+24#64)=.word cached)
    (reached : CallPrefix.Reaches source (.scoped (ofString name) .one (ofString "node_write_ref") arguments) current) :
    ∃ bytes : Nat,bytes≤33 ∧ current.locals.lookup (ofString name)=some (.val (.word (BitVec.ofNat 64 bytes))) ∧
      Nonempty (Output source current child dst heap cached stp pad (.val (.word (BitVec.ofNat 64 bytes)))) := by
  obtain ⟨answer,output,_size⟩:=reached_normal_exact source current name arguments child dst tag heap pointer cached stp pad length
    environment heapLower args header cache data digest reached
  exact ⟨referenceBytes child tag length,reference_bytes_bound child tag length,answer,⟨output⟩⟩

end InitECandidate.Solver.Mpt.NodeWriteRef

#print axioms InitECandidate.Solver.Mpt.NodeWriteRef.Output.heap
#print axioms InitECandidate.Solver.Mpt.NodeWriteRef.Output.environment
#print axioms InitECandidate.Solver.Mpt.NodeWriteRef.reached_normal
#print axioms InitECandidate.Solver.Mpt.NodeWriteRef.length_tail_normal_exact
#print axioms InitECandidate.Solver.Mpt.NodeWriteRef.after_cache_normal_exact
#print axioms InitECandidate.Solver.Mpt.NodeWriteRef.body_normal_exact
#print axioms InitECandidate.Solver.Mpt.NodeWriteRef.reference_bytes_bound
#print axioms InitECandidate.Solver.Mpt.NodeWriteRef.reference_word_eq
#print axioms InitECandidate.Solver.Mpt.NodeWriteRef.reached_normal_exact
