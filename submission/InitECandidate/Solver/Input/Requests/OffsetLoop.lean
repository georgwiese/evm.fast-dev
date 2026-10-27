import InitECandidate.Solver.Input.Requests.OffsetStep
import InitECandidate.Solver.Input.WhileActive
import InitECandidate.Solver.PanControl

namespace InitECandidate.Solver.Input.Requests
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix WitnessRadix.AllocatedBytes
open Flapjack.Basis.Pure.MlString QueryBranch
set_option maxRecDepth 10000
set_option maxHeartbeats 400000

/-- The literal offset loop writes exactly its five scratch words from copied
input, preserves all other words/control/locals, and pays one clock per row. -/
theorem offset_loop_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer array : BitVec 64) (start index rounds : Nat) (finish : index+rounds=5)
    (heap : Blob.HeapInput source input pointer) (extent : start+20≤input.length%2^64)
    (wp : source.locals.lookup (ofString "p")=some (.val (.word (pointer+BitVec.ofNat 64 start))))
    (i : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index))))
    (offsets : source.globals.lookup (ofString "ssz_offs")=some (.val (.word array)))
    (domain : source.memaddrs=InitE.ordinaryDomain) (pointerAligned : pointer.toNat%8=0)
    (arrayAligned : array.toNat%8=0) (arrayLower : 2701131776≤array.toNat)
    (before : array.toNat+40≤pointer.toNat) (upper : pointer.toNat+input.length%2^64+8≤33806089496)
    (cells : ∀ position<index,source.memory (byteAddress array (8*position))=.word (offsetWord input start position))
    (enough : rounds+1≤source.clock) :
    ∃ target,evaluateHOLFiniteState source offsetLoop=(none,target) ∧ target.clock=source.clock-rounds ∧
      BackingLayout.control target=BackingLayout.control source ∧ Blob.HeapInput target input pointer ∧
      target.locals.lookup (ofString "i")=some (.val (.word 5#64)) ∧
      (∀ name,name≠ofString "i" → target.locals.lookup name=source.locals.lookup name) ∧
      (∀ position<5,target.memory (byteAddress array (8*position))=.word (offsetWord input start position)) ∧
      (∀ query,query.toNat<array.toNat ∨ array.toNat+40≤query.toNat → target.memory query=source.memory query) := by
  classical
  induction rounds generalizing source index with
  | zero=>
    have indexEq : index=5:=by omega
    subst index
    have test:=offset_test source 5 (by omega) i
    simp only [if_neg (by omega : ¬5<5)] at test
    have bridge : evalHOLFinite source offsetTest=eval source offsetTest :=
      congrArg (fun h : DecidablePred source.memaddrs=>@evalHOLExact 64 Guest.HostMemory _ source.toExact h offsetTest) (Subsingleton.elim _ _)
    refine ⟨source,?_,by simp,rfl,heap,i,by intros;rfl,cells,by intros;rfl⟩
    rw [offsetLoop,evaluateHOLFiniteState_while_total,bridge.trans test]
    simp
  | succ rounds ih=>
    have active : index<5:=by omega
    have test:=offset_test source index (by omega) i
    simp only [if_pos active] at test
    let entry:=decClockHOLFinite source
    let next:=offsetNext entry input array start index
    obtain ⟨stepRun,nextHeap,newCell,stepFrame⟩:=offset_step entry input pointer array start index active heap extent wp i offsets domain
      pointerAligned arrayAligned arrayLower before upper
    have nextClock : next.clock=source.clock-1:=rfl
    have nextI : next.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 (index+1)))):=bind_lookup_same _ _ _
    have nextWp : next.locals.lookup (ofString "p")=some (.val (.word (pointer+BitVec.ofNat 64 start))):=
      (bind_lookup_other _ "i" "p" _ (by decide)).trans wp
    have nextCells : ∀ position<index+1,next.memory (byteAddress array (8*position))=.word (offsetWord input start position) := by
      intro position inside
      by_cases current : position=index
      · subst position;exact newCell
      · have away : byteAddress array (8*position)≠byteAddress array (8*index):=
          byteAddress_ne array (8*position) (8*index) (by omega) (by omega) (by omega)
        exact (stepFrame _ away).trans (cells position (by omega))
    obtain ⟨target,tailRun,clock,control,targetHeap,targetI,otherLocals,targetCells,targetFrame⟩:=ih next (index+1) (by omega)
      nextHeap nextWp nextI offsets domain nextCells
      (by rw [nextClock];omega)
    have unfoldLoop:=while_active source next offsetTest offsetStep none test (by omega) stepRun (by rw [nextClock]; exact Nat.le_refl _)
    have actual : evaluateHOLFiniteState source offsetLoop=(none,target):=unfoldLoop.trans tailRun
    refine ⟨target,actual,?_,control,targetHeap,targetI,?_,targetCells,?_⟩
    · rw [nextClock] at clock
      omega
    · intro name different
      have stepLocal : next.locals.lookup name=source.locals.lookup name := by
        change (source.locals.update (ofString "i",.val (.word (BitVec.ofNat 64 (index+1))))).lookup name=_
        simp [HolFiniteMapExact.lookup_update,FUPDATE,show (ofString "i"==name)=false from beq_eq_false_iff_ne.mpr (Ne.symm different)]
      exact (otherLocals name different).trans stepLocal
    · intro query outside
      have number:=byteAddress_toNat array (8*index) (by omega)
      have away : query≠byteAddress array (8*index) := by
        intro equal
        have same:=congrArg BitVec.toNat equal
        rcases outside with low|high <;>omega
      exact (targetFrame query outside).trans (stepFrame query away)

end InitECandidate.Solver.Input.Requests

#print axioms InitECandidate.Solver.Input.Requests.offset_loop_execute
