import InitECandidate.Solver.Mpt.WitnessResolveLookupNormal
import InitECandidate.Solver.MutableTable.WitnessDatabaseAnyNormal
import InitECandidate.Solver.Input.CallResumeFields

namespace InitECandidate.Solver.Mpt.WitnessResolve
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem hash_allocated_erase (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (heap hash : BitVec 64)
    (pure : Input.LocalEffects.erase target=Input.LocalEffects.erase source) :
    Input.LocalEffects.erase (hashAllocated target heap hash)=Input.LocalEffects.erase (hashAllocated source heap hash) := by
  have framed:=congrArg (fun state=>Input.LocalEffects.erase (hashAllocated state heap hash)) pure
  exact framed

/-- The actual original lookup call supplies a real bounded witness hit
or allocates its own hashed node on absence. The nonlocal frame is derived
from the same genuine complete returning call, for arbitrary query bytes. -/
theorem lookup_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (array table scratch pointer header payload flag heap : BitVec 64) (count maximum : Nat) (slices : Nat→Graph.Slice)
    (actual : MutableTable.WitnessBuild.Database source array table count maximum slices scratch)
    (dbCell : source.locals.lookup (ofString "db")=some (.val (.word table)))
    (itemCell : source.locals.lookup (ofString "it")=some (Rlp.Item.result pointer header payload flag))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (arena : AllocatedBytes.Arena heap 0) (aligned : heap.toNat%8=0)
    (installed : Input.OriginalCode.Installed source.code)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source lookupCall=(some (.returned value),post)) :
    (value=.rStruct [.val (.word 0#64),.val (.word heap),.val (.word 0#64),.val (.word 0#64)] ∧
      AllocatedBytes.Arena heap 32 ∧ Input.LocalEffects.erase post=Input.LocalEffects.erase (hashAllocated source heap (pointer+header))) ∨
    ∃ slice : Graph.Slice,value=.rStruct [.val (.word 1#64),.val (.word slice.1),.val (.word slice.2),.val (.word (pointer+header))] ∧
      slice.2.toNat≤maximum ∧ AllocatedBytes.Arena slice.1 slice.2.toNat ∧
      2713731432≤slice.1.toNat ∧ slice.1.toNat+slice.2.toNat≤table.toNat ∧
      Input.LocalEffects.erase post=Input.LocalEffects.erase source := by
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) queryArguments=
      some (MutableTable.NodeDb.arguments table (pointer+header)):=by
    simp [queryArguments,field,localVar,Rlp.Item.result,MutableTable.NodeDb.arguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,dbCell,itemCell]
  obtain ⟨target,answer,inner,pure,hit,continued,endpoint⟩:=actual.any_scoped_normal source post array table count maximum slices scratch (pointer+header)
    installed "r" queryArguments afterLookup args value normal
  let ready:=Input.CallNormal.continuationEntry source target "r" (MutableTable.NodeDb.output answer)
  have readyPure : Input.LocalEffects.erase ready=Input.LocalEffects.erase source:=
    (Input.CallNormal.continuation_erase source target "r" _).trans pure
  have readyItem : ready.locals.lookup (ofString "it")=some (Rlp.Item.result pointer header payload flag):=
    (Input.CallNormal.continuation_lookup_other source target "r" "it" _ (by decide)).trans itemCell
  have readyR : ready.locals.lookup (ofString "r")=some (MutableTable.NodeDb.output answer):=Input.CallNormal.continuation_lookup_same _ _ _ _
  have readyGlobals:=congrArg PanSemStateFiniteExact.globals readyPure
  change ready.globals=source.globals at readyGlobals
  have readyHeap : ready.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)):=by rw [readyGlobals]; exact heapCell
  have readyDomain : ready.memaddrs=InitE.ordinaryDomain:=
    (congrArg PanSemStateFiniteExact.memaddrs readyPure).trans actual.domain
  have readyInstalled : Input.OriginalCode.Installed ready.code:=by rw [Input.LocalEffects.code_of_erase source ready readyPure]; exact installed
  have classified:=after_lookup_normal ready inner pointer header payload flag heap answer readyItem readyR readyHeap readyDomain arena aligned readyInstalled value continued
  cases answer with
  | none=>
    obtain ⟨valueEq,nodeArena,funding,exactFrame⟩:=classified
    have erased : Input.LocalEffects.erase inner=Input.LocalEffects.erase (hashAllocated ready heap (pointer+header)):=
      congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>{state with clock:=0}) exactFrame
    left
    refine ⟨valueEq,nodeArena,?_⟩
    rw [endpoint]
    exact erased.trans (hash_allocated_erase source ready heap (pointer+header) readyPure)
  | some slice=>
    obtain ⟨valueEq,innerEq⟩:=classified
    obtain ⟨index,inside,same,small,sliceArena,lower,before⟩:=hit slice rfl
    right
    refine ⟨slice,valueEq,small,sliceArena,lower,before,?_⟩
    rw [endpoint,innerEq]
    exact readyPure

end InitECandidate.Solver.Mpt.WitnessResolve

#print axioms InitECandidate.Solver.Mpt.WitnessResolve.hash_allocated_erase
#print axioms InitECandidate.Solver.Mpt.WitnessResolve.lookup_normal
