import InitECandidate.Solver.Mpt.CompactToNibblesNormal
import InitECandidate.Solver.Mpt.CurrentConstructorArena
import InitECandidate.Solver.Mpt.CompactToNibblesCost
import InitECandidate.Solver.Input.WordPairEnvironment
import InitECandidate.Solver.Input.ClockCostScopedReached
import InitECandidate.Solver.Input.ScopedCallNormal

namespace InitECandidate.Solver.Mpt.CompactToNibbles
open Input Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- Physical compact output at main's actual arena, with the allocator's
real persistent ceiling kept distinct from the ordinary memory domain. -/
structure CurrentSnapshot (origin target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (length : Nat) (heap : BitVec 64) (nibbles : Nat) (leaf : BitVec 64) : Prop where
  positive : 1≤length
  outputArena : AllocatedBytes.Arena heap (2*length)
  nibbleBound : nibbles≤2*length
  leafBinary : leaf=0#64 ∨ leaf=1#64
  arena : CurrentStartup.ArenaState target
  heapCell : target.globals.lookup (ofString "heap_ptr")=some (.val (.word (PersistentAlloc.rounded heap (BitVec.ofNat 64 (2*length)))))
  nextArena : AllocatedBytes.Arena (PersistentAlloc.rounded heap (BitVec.ofNat 64 (2*length))) 0
  nextBound : (PersistentAlloc.rounded heap (BitVec.ofNat 64 (2*length))).toNat≤2952790016
  nextAligned : (PersistentAlloc.rounded heap (BitVec.ofNat 64 (2*length))).toNat%8=0
  grows : heap.toNat+2*length≤(PersistentAlloc.rounded heap (BitVec.ofNat 64 (2*length))).toNat
  metadata : KeyToNibbles.writeMetadata target=KeyToNibbles.writeMetadata (PersistentAlloc.post origin heap (BitVec.ofNat 64 (2*length)))
  memory : ∀ query : BitVec 64,query.toNat<heap.toNat ∨ heap.toNat+2*length≤query.toNat→target.memory query=origin.memory query

theorem body_current_snapshot (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer heap : BitVec 64) (length : Nat) (bounded : length≤1024)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 length))))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (heapBound : heap.toNat≤2952790016) (aligned : heap.toNat%8=0)
    (arena : CurrentStartup.ArenaState source)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body=(some (.returned value),target)) :
    ∃ nibbles leaf,value=output heap nibbles leaf ∧ CurrentSnapshot source target length heap nibbles leaf := by
  obtain ⟨positive,room,outputArena,nibbles,leaf,nibbleBound,binary,valueEq,metadata,memory⟩:=
    body_normal source target pointer heap length bounded pointerCell lengthCell heapCell heapArena heapBound aligned arena.code value normal
  have amountNumber : (BitVec.ofNat 64 (2*length)).toNat=2*length := by
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have checked:=PersistentAlloc.guards heap (BitVec.ofNat 64 (2*length)) (by rw [amountNumber]; exact room)
  have grows:=checked.2.2.1
  rw [amountNumber] at grows
  have nextArena : AllocatedBytes.Arena (PersistentAlloc.rounded heap (BitVec.ofNat 64 (2*length))) 0 :=
    ⟨by have lower:=heapArena.lower; omega,by have upper:=checked.2.2.2.1; omega⟩
  have globals:=congrArg PanSemStateFiniteExact.globals metadata
  change target.globals=(PersistentAlloc.post source heap (BitVec.ofNat 64 (2*length))).globals at globals
  have nextHeap : target.globals.lookup (ofString "heap_ptr")=some (.val (.word (PersistentAlloc.rounded heap (BitVec.ofNat 64 (2*length))))) := by
    rw [globals]
    simp [PersistentAlloc.post,HolFiniteMapExact.update,FUPDATE]
  exact ⟨nibbles,leaf,valueEq,positive,outputArena,nibbleBound,binary,current_arena source target arena _ normal,nextHeap,nextArena,
    checked.2.2.2.1,checked.2.2.2.2,grows,metadata,memory⟩

/-- Price the suffix only with the genuine allocated compact output and
its physical/heap frame. All failed or malformed earlier outcomes are covered. -/
theorem scoped_current_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer heap : BitVec 64) (length : Nat) (bounded : length≤1024)
    (name : String) (expressions : List (ExpHOL 64)) (continuation : ProgHOL 64) (tailPrice : Nat)
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) expressions=
      some [.val (.word pointer),.val (.word (BitVec.ofNat 64 length))])
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (heapBound : heap.toNat≤2952790016) (aligned : heap.toNat%8=0)
    (arena : CurrentStartup.ArenaState source)
    (tail : ∀ target nibbles leaf,CurrentSnapshot source target length heap nibbles leaf→
      let ready:=CallNormal.continuationEntry source target name (output heap nibbles leaf)
      ready.clock-(evaluateHOLFiniteState ready continuation).2.clock≤tailPrice) :
    source.clock-(evaluateHOLFiniteState source (.decCall (ofString name) resultShape (ofString "compact_to_nibbles") expressions continuation)).2.clock≤length/4+tailPrice+7 := by
  obtain ⟨callee,called,pointerLocal,lengthLocal⟩:=word_pair_environment source.code.lookup (ofString "compact_to_nibbles")
    (ofString "p") (ofString "n") body resultShape pointer (BitVec.ofNat 64 length) (by decide) (original_code source.code arena.code)
  have actual:=ClockCost.scoped_reached_current source name resultShape (ofString "compact_to_nibbles") expressions _ body continuation callee resultShape
    (length/4+6) tailPrice args called (body_cost (callEntryStateHOLFinite source callee) pointer length (by omega) pointerLocal lengthLocal arena.code) ?_
  · omega
  · intro target value normal checked
    obtain ⟨nibbles,leaf,valueEq,snapshot⟩:=body_current_snapshot (callEntryStateHOLFinite source callee) target pointer heap length bounded
      pointerLocal lengthLocal heapCell heapArena heapBound aligned (arena.of_frame rfl) value normal
    have current : CurrentSnapshot source target length heap nibbles leaf :=
      ⟨snapshot.positive,snapshot.outputArena,snapshot.nibbleBound,snapshot.leafBinary,snapshot.arena,snapshot.heapCell,snapshot.nextArena,
        snapshot.nextBound,snapshot.nextAligned,snapshot.grows,snapshot.metadata,snapshot.memory⟩
    rw [valueEq]
    exact tail target nibbles leaf current

/-- A genuine normal whole caller supplies the same physical snapshot and
its actual continued caller, independently of any stopping-cost alternative. -/
theorem scoped_current_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer heap : BitVec 64) (length : Nat) (bounded : length≤1024)
    (name : String) (expressions : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) expressions=
      some [.val (.word pointer),.val (.word (BitVec.ofNat 64 length))])
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (heapBound : heap.toNat≤2952790016) (aligned : heap.toNat%8=0)
    (arena : CurrentStartup.ArenaState source) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (.decCall (ofString name) resultShape (ofString "compact_to_nibbles") expressions continuation)=(some (.returned value),post)) :
    ∃ target nibbles leaf inner,CurrentSnapshot source target length heap nibbles leaf ∧
      evaluateHOLFiniteState (CallNormal.continuationEntry source target name (output heap nibbles leaf)) continuation=(some (.returned value),inner) ∧
      post=QueryBranch.restore source name inner := by
  obtain ⟨callee,called,pointerLocal,lengthLocal⟩:=word_pair_environment source.code.lookup (ofString "compact_to_nibbles")
    (ofString "p") (ofString "n") body resultShape pointer (BitVec.ofNat 64 length) (by decide) (original_code source.code arena.code)
  obtain ⟨funded,target,answer,inner,bodyRun,checked,continued,endpoint⟩:=CallNormal.scoped_normal source post name resultShape
    (ofString "compact_to_nibbles") expressions _ body continuation callee resultShape args called value normal
  obtain ⟨nibbles,leaf,valueEq,snapshot⟩:=body_current_snapshot (callEntryStateHOLFinite source callee) target pointer heap length bounded
    pointerLocal lengthLocal heapCell heapArena heapBound aligned (arena.of_frame rfl) answer bodyRun
  have current : CurrentSnapshot source target length heap nibbles leaf :=
    ⟨snapshot.positive,snapshot.outputArena,snapshot.nibbleBound,snapshot.leafBinary,snapshot.arena,snapshot.heapCell,snapshot.nextArena,
      snapshot.nextBound,snapshot.nextAligned,snapshot.grows,snapshot.metadata,snapshot.memory⟩
  rw [valueEq] at continued
  exact ⟨target,nibbles,leaf,inner,current,continued,endpoint⟩

end InitECandidate.Solver.Mpt.CompactToNibbles

#print axioms InitECandidate.Solver.Mpt.CompactToNibbles.body_current_snapshot
#print axioms InitECandidate.Solver.Mpt.CompactToNibbles.scoped_current_cost

#print axioms InitECandidate.Solver.Mpt.CompactToNibbles.scoped_current_normal
