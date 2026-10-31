import InitECandidate.Solver.Mpt.WitnessResolveLookupNormal
import InitECandidate.Solver.Input.CurrentTable.NodeLookup.Call
import InitECandidate.Solver.Input.CallResumeFields

namespace InitECandidate.Solver.Mpt.WitnessResolve
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem hash_allocated_erase (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (heap hash : BitVec 64)
    (pure : Input.LocalEffects.erase target=Input.LocalEffects.erase source) :
    Input.LocalEffects.erase (hashAllocated target heap hash)=Input.LocalEffects.erase (hashAllocated source heap hash) := by
  have framed:=congrArg (fun state=>Input.LocalEffects.erase (hashAllocated state heap hash)) pure
  exact framed

/-- The real current Patricia lookup supplies a bounded decoded row or
allocates its own hashed node on absence. The normal lookup and its real
continuation derive all result/frame/room facts, even for arbitrary queries. -/
theorem lookup_normal (data : Input.CurrentTable.NodeBuild.Data) (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer header payload flag heap : BitVec 64)
    (actual : Input.CurrentTable.NodeLookup.Database source data)
    (dbCell : source.locals.lookup (ofString "db")=some (.val (.word data.table)))
    (itemCell : source.locals.lookup (ofString "it")=some (Rlp.Item.result pointer header payload flag))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (arena : AllocatedBytes.Arena heap 0) (aligned : heap.toNat%8=0)
    (installed : Input.OriginalCode.Installed source.code)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source lookupCall=(some (.returned value),post)) :
    (value=.rStruct [.val (.word 0#64),.val (.word heap),.val (.word 0#64),.val (.word 0#64)] ∧
      heap.toNat+32≤2952790016 ∧ AllocatedBytes.Arena heap 32 ∧
      Input.LocalEffects.erase post=Input.LocalEffects.erase (hashAllocated source heap (pointer+header))) ∨
    ∃ nextPointer nextLength,value=.rStruct [.val (.word 1#64),.val (.word nextPointer),.val (.word nextLength),.val (.word (pointer+header))] ∧
      nextLength.toNat≤1024 ∧ AllocatedBytes.Arena nextPointer nextLength.toNat ∧
      2701131776≤nextPointer.toNat ∧ nextPointer.toNat+nextLength.toNat≤data.table.toNat ∧
      Input.LocalEffects.erase post=Input.LocalEffects.erase source := by
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) queryArguments=
      some [.val (.word data.table),.val (.word (pointer+header))]:=by
    simp [queryArguments,field,localVar,Rlp.Item.result,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,dbCell,itemCell]
  obtain ⟨root,next,count,valid,bits,left,right,keys,image,bounded⟩:=actual.image
  obtain ⟨target,answer,inner,result,pure,forward,price,continued,endpoint⟩:=Input.CurrentTable.NodeLookup.scoped_returned data source post
    data.table data.cap root (pointer+header) next count valid bits left right keys image actual.rows installed "r" queryArguments afterLookup args value normal
  have classified : ∃ hit : Option (BitVec 64×BitVec 64),answer=lookupValue hit ∧
      (match hit with | none=>True | some (p,n)=>n.toNat≤1024 ∧ AllocatedBytes.Arena p n.toNat ∧
        2701131776≤p.toNat ∧ p.toNat+n.toNat≤data.table.toNat) := by
    rcases actual.result result with absent|⟨p,n,same,allocation,small,lower,before⟩
    · exact ⟨none,absent,True.intro⟩
    · exact ⟨some (p,n),same,small,allocation,lower,before⟩
  obtain ⟨hit,answerEq,hitData⟩:=classified
  rw [answerEq] at continued
  let ready:=Input.CallNormal.continuationEntry source target "r" (lookupValue hit)
  have readyPure : Input.LocalEffects.erase ready=Input.LocalEffects.erase source:=pure
  have readyItem : ready.locals.lookup (ofString "it")=some (Rlp.Item.result pointer header payload flag):=
    (Input.CallNormal.continuation_lookup_other source target "r" "it" _ (by decide)).trans itemCell
  have readyR : ready.locals.lookup (ofString "r")=some (lookupValue hit):=Input.CallNormal.continuation_lookup_same _ _ _ _
  have readyGlobals:=congrArg PanSemStateFiniteExact.globals readyPure
  change ready.globals=source.globals at readyGlobals
  have readyHeap : ready.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)):=by rw [readyGlobals]; exact heapCell
  have readyDomain : ready.memaddrs=InitE.ordinaryDomain:=
    (congrArg PanSemStateFiniteExact.memaddrs readyPure).trans image.domain
  have readyInstalled : Input.OriginalCode.Installed ready.code:=by rw [Input.LocalEffects.code_of_erase source ready readyPure]; exact installed
  have tail:=after_lookup_normal ready inner pointer header payload flag heap hit readyItem readyR readyHeap readyDomain arena aligned readyInstalled value continued
  cases hit with
  | none=>
    obtain ⟨valueEq,room,nodeArena,funding,exactFrame⟩:=tail
    have erased : Input.LocalEffects.erase inner=Input.LocalEffects.erase (hashAllocated ready heap (pointer+header)):=
      congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>{state with clock:=0}) exactFrame
    left
    refine ⟨valueEq,room,nodeArena,?_⟩
    rw [endpoint]
    exact erased.trans (hash_allocated_erase source ready heap (pointer+header) readyPure)
  | some slice=>
    rcases slice with ⟨p,n⟩
    obtain ⟨valueEq,innerEq⟩:=tail
    obtain ⟨small,allocation,lower,before⟩:=hitData
    right
    refine ⟨p,n,valueEq,small,allocation,lower,before,?_⟩
    rw [endpoint,innerEq]
    exact readyPure

end InitECandidate.Solver.Mpt.WitnessResolve

#print axioms InitECandidate.Solver.Mpt.WitnessResolve.hash_allocated_erase
#print axioms InitECandidate.Solver.Mpt.WitnessResolve.lookup_normal
