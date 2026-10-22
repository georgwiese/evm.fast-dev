import InitECandidate.Solver.Mpt.NewFields

namespace InitECandidate.Solver.Mpt.NewTrie
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def post (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap root secured : BitVec 64):=
  {source with
    clock:=source.clock-2,
    globals:=source.globals.update (ofString "heap_ptr",.val (.word (PersistentAlloc.rounded heap 16#64))),
    memory:=StoreWord.put (StoreWord.put source.memory heap root) (heap+8#64) secured}

/-- The real checked scoped mpt_new call supplies fresh room and the exact
caller update, including both call ticks and both initialized words. -/
theorem scoped_target {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    (name : MlS) (arguments : List (ExpHOL 64)) (heap root secured : BitVec 64)
    (installed : Input.OriginalCode.Installed source.code)
    (argsRead : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (values root secured))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (domain : source.memaddrs=InitE.ordinaryDomain) (frontier : AllocatedBytes.Arena heap 0) (aligned : heap.toNat%8=0)
    (reached : Input.CallPrefix.Reaches source (.scoped name .one (ofString "mpt_new") arguments) target) :
    AllocatedBytes.Arena heap 16 ∧ target=setVarHOLFinite name (.val (.word heap)) (post source heap root secured) := by
  cases reached with
  | «scoped» _ _ _ _ actualValues actualBody callee returnShape returned childTarget args called funded run checked=>
    have sameValues : actualValues=values root secured:=Option.some.inj (args.symm.trans argsRead)
    subst actualValues
    obtain ⟨expected,expectedCall,rootLocal,securedLocal⟩:=environment source.code.lookup root secured (original_code source.code installed)
    have same:=Option.some.inj (called.symm.trans expectedCall)
    have bodyEq:=congrArg Prod.fst same
    have mapEq:=congrArg (fun triple : ProgHOL 64×HolFiniteMapExact MlS (ValueHOL 64)×ShapeHOL=>triple.2.1) same
    have shapeEq:=congrArg (fun triple : ProgHOL 64×HolFiniteMapExact MlS (ValueHOL 64)×ShapeHOL=>triple.2.2) same
    change actualBody=body at bodyEq
    change callee=expected at mapEq
    change returnShape=.one at shapeEq
    subst actualBody
    subst callee
    subst returnShape
    obtain ⟨arena,valueEq,frame⟩:=normal (callEntryStateHOLFinite source expected) childTarget heap root secured installed rootLocal securedLocal heapCell domain frontier aligned returned run
    have restored:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>{state with locals:=source.locals}) frame
    have callerEq : {childTarget with locals:=source.locals}=post source heap root secured:=by
      change {childTarget with locals:=source.locals}={source with
        globals:=source.globals.update (ofString "heap_ptr",.val (.word (PersistentAlloc.rounded heap 16#64))),
        memory:=StoreWord.put (StoreWord.put source.memory heap root) (heap+8#64) secured,
        clock:=source.clock-1-1} at restored
      simpa only [Nat.sub_sub,post] using restored
    refine ⟨arena,?_⟩
    rw [valueEq]
    exact congrArg (setVarHOLFinite name (.val (.word heap))) callerEq

theorem scoped_next {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    (name : MlS) (arguments : List (ExpHOL 64)) (heap root secured : BitVec 64) (rest : List Input.CallPrefix.Action)
    (installed : Input.OriginalCode.Installed source.code)
    (argsRead : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (values root secured))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (domain : source.memaddrs=InitE.ordinaryDomain) (frontier : AllocatedBytes.Arena heap 0) (aligned : heap.toNat%8=0)
    (execution : Input.CallPrefix.Execution source (.scoped name .one (ofString "mpt_new") arguments::rest) target) :
    AllocatedBytes.Arena heap 16 ∧ Input.CallPrefix.Execution (setVarHOLFinite name (.val (.word heap)) (post source heap root secured)) rest target := by
  obtain ⟨middle,first,next⟩:=execution.head
  obtain ⟨arena,same⟩:=scoped_target name arguments heap root secured installed argsRead heapCell domain frontier aligned first
  rw [same] at next
  exact ⟨arena,next⟩

theorem post_cells (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap root secured : BitVec 64) (arena : AllocatedBytes.Arena heap 16) :
    (post source heap root secured).memory heap=.word root ∧ (post source heap root secured).memory (heap+8#64)=.word secured :=
  ready_cells source heap root secured arena

theorem post_older (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap root secured query : BitVec 64)
    (arena : AllocatedBytes.Arena heap 16) (before : query.toNat<heap.toNat) :
    (post source heap root secured).memory query=source.memory query := ready_older source heap root secured query arena before

end InitECandidate.Solver.Mpt.NewTrie

#print axioms InitECandidate.Solver.Mpt.NewTrie.scoped_target
#print axioms InitECandidate.Solver.Mpt.NewTrie.scoped_next
#print axioms InitECandidate.Solver.Mpt.NewTrie.post_cells
#print axioms InitECandidate.Solver.Mpt.NewTrie.post_older
