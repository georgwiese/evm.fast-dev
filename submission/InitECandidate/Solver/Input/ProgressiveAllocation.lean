import InitECandidate.Solver.Input.ProgressiveFoldProgram
import InitECandidate.Solver.Input.TerminatingProgramPrefix

namespace InitECandidate.Solver.Input.Progressive
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch ProgramPrefix

def allocationActions : List Action := [.allocate "roots" (.panop .mul [.const 24#64,.const 32#64]),.allocate "acc" (.const 32#64),
  .declare "k" (.const 0#64),.declare "off" (.const 0#64),.declare "size" (.const 1#64)]
def accPointer (roots : BitVec 64) := roots+768#64
def temporary (roots : BitVec 64) := accPointer roots+32#64
def allocatedRoots (source : PanSemStateFiniteExact 64 Guest.HostMemory) (roots : BitVec 64) :=
  bind (PersistentAlloc.post {source with clock:=source.clock-1} roots 768#64) "roots" roots
def allocatedAcc (source : PanSemStateFiniteExact 64 Guest.HostMemory) (roots : BitVec 64) :=
  let first := allocatedRoots source roots
  bind (PersistentAlloc.post {first with clock:=first.clock-1} (accPointer roots) 32#64) "acc" (accPointer roots)
def initialized (source : PanSemStateFiniteExact 64 Guest.HostMemory) (roots : BitVec 64) :=
  bind (bind (bind (allocatedAcc source roots) "k" 0#64) "off" 0#64) "size" 1#64
def restoreInitial (source : PanSemStateFiniteExact 64 Guest.HostMemory) (roots : BitVec 64) (target : PanSemStateFiniteExact 64 Guest.HostMemory) :=
  restore source "roots" (restore (allocatedRoots source roots) "acc" (restore (allocatedAcc source roots) "k"
    (restore (bind (allocatedAcc source roots) "k" 0#64) "off" (restore (bind (bind (allocatedAcc source roots) "k" 0#64) "off" 0#64) "size" target))))

set_option maxRecDepth 100000 in
theorem allocation_shape : body=.decCall (ofString "mark") .one (ofString "heap_mark") [] afterMark ∧
    afterMark=ProgramPrefix.program allocationActions loopAndSuffix := by
  simp only [afterMark,loopAndSuffix,afterOff,afterK,afterAcc,afterRoots,body,Guest.guestFn_merkleize_progressive,progToHOL,expToHOL,shapeToHOL,
    List.map_cons,List.map_nil,allocationActions,ProgramPrefix.program]
  exact ⟨True.intro,True.intro⟩

theorem allocation_geometry (roots : BitVec 64) (arena : AllocatedBytes.Arena roots 800) (aligned : roots.toNat%8=0) :
    (accPointer roots).toNat=roots.toNat+768 ∧ (temporary roots).toNat=roots.toNat+800 ∧
    (accPointer roots).toNat%8=0 ∧ (temporary roots).toNat%8=0 ∧
    PersistentAlloc.rounded roots 768#64=accPointer roots ∧ PersistentAlloc.rounded (accPointer roots) 32#64=temporary roots := by
  have upper := arena.upper
  have firstNumber : (accPointer roots).toNat=roots.toNat+768 := BitVec.toNat_add_of_lt (by change roots.toNat+768<2^64; omega)
  have lastNumber : (temporary roots).toNat=roots.toNat+800 := by
    rw [temporary,BitVec.toNat_add_of_lt (by change (accPointer roots).toNat+32<2^64; omega),firstNumber]
    rfl
  have firstAligned : (accPointer roots).toNat%8=0 := by rw [firstNumber]; omega
  have lastAligned : (temporary roots).toNat%8=0 := by rw [lastNumber]; omega
  have firstRound : PersistentAlloc.rounded roots 768#64=accPointer roots := by
    apply BitVec.eq_of_toNat_eq
    rw [PersistentAlloc.rounded_nat roots 768#64 (by change roots.toNat+768+7<2^64; omega),firstNumber]
    change (roots.toNat+768+7)/8*8=roots.toNat+768
    omega
  have lastRound : PersistentAlloc.rounded (accPointer roots) 32#64=temporary roots := by
    apply BitVec.eq_of_toNat_eq
    rw [PersistentAlloc.rounded_nat (accPointer roots) 32#64 (by change (accPointer roots).toNat+32+7<2^64; omega),firstNumber,lastNumber]
    change (roots.toNat+768+32+7)/8*8=roots.toNat+800
    omega
  exact ⟨firstNumber,lastNumber,firstAligned,lastAligned,firstRound,lastRound⟩

private theorem setup (source : PanSemStateFiniteExact 64 Guest.HostMemory) (roots : BitVec 64)
    (installed : OriginalCode.Installed source.code) (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word roots)))
    (arena : AllocatedBytes.Arena roots 800) (aligned : roots.toNat%8=0) (enough : 2≤source.clock) :
    Executes source allocationActions (initialized source roots) (restoreInitial source roots) := by
  have geometry := allocation_geometry roots arena aligned
  have upper := arena.upper
  have firstHeap : (allocatedRoots source roots).globals.lookup (ofString "heap_ptr")=some (.val (.word (accPointer roots))) := by
    change (source.globals.update (ofString "heap_ptr",.val (.word (PersistentAlloc.rounded roots 768#64)))).lookup _=_
    rw [geometry.2.2.2.2.1]
    simp [HolFiniteMapExact.lookup_update,FUPDATE]
  unfold allocationActions initialized restoreInitial
  apply Executes.allocate (restoreRest:=fun target=>restore (allocatedRoots source roots) "acc" (restore (allocatedAcc source roots) "k"
    (restore (bind (allocatedAcc source roots) "k" 0#64) "off" (restore (bind (bind (allocatedAcc source roots) "k" 0#64) "off" 0#64) "size" target)))) roots 768#64
    (by simp [eval,evalHOLExact,evalListHOLExact,toExact,valueIsWord,valueWord,panOpHOL]) (PersistentAlloc.original_code source.code installed) heap (by change roots.toNat+768≤33806089496; omega) (by omega)
  apply Executes.allocate (source:=allocatedRoots source roots) (restoreRest:=fun target=>restore (allocatedAcc source roots) "k"
    (restore (bind (allocatedAcc source roots) "k" 0#64) "off" (restore (bind (bind (allocatedAcc source roots) "k" 0#64) "off" 0#64) "size" target))) (accPointer roots) 32#64 rfl
    (PersistentAlloc.original_code source.code installed) firstHeap (by change (accPointer roots).toNat+32≤33806089496; rw [geometry.1]; omega) (by change 1≤source.clock-1; omega)
  apply Executes.declare (restoreRest:=fun target=>restore (bind (allocatedAcc source roots) "k" 0#64) "off" (restore (bind (bind (allocatedAcc source roots) "k" 0#64) "off" 0#64) "size" target)) 0#64 rfl
  apply Executes.declare (restoreRest:=restore (bind (bind (allocatedAcc source roots) "k" 0#64) "off" 0#64) "size") 0#64 rfl
  exact Executes.declare (restoreRest:=id) 1#64 rfl (Executes.done _)

/-- Original two allocations/three declarations derive their two funded
caller ticks from the same non-timeout continuation, retaining all scopes. -/
theorem allocation_prefix (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (roots : BitVec 64)
    (installed : OriginalCode.Installed source.code) (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word roots)))
    (arena : AllocatedBytes.Arena roots 800) (aligned : roots.toNat%8=0)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source afterMark=(result,post)) (notTimeout : result≠some .timeOut) :
    2≤source.clock ∧ ∃ final,evaluateHOLFiniteState (initialized source roots) loopAndSuffix=(result,final) ∧ post=restoreInitial source roots final := by
  have padded := setup {source with clock:=source.clock+2} roots installed heap arena aligned (by change 2≤source.clock+2; omega)
  rw [allocation_shape.2] at run
  have paid := terminating_program_prefix source post (initialized {source with clock:=source.clock+2} roots) allocationActions loopAndSuffix
    (restoreInitial {source with clock:=source.clock+2} roots) 2 padded result run notTimeout
  have funded : 2≤source.clock := by change 2≤source.clock+2-1-1 at paid; omega
  have actual := setup source roots installed heap arena aligned funded
  rw [ProgramPrefix.execute actual loopAndSuffix] at run
  let final := (evaluateHOLFiniteState (initialized source roots) loopAndSuffix).2
  have observed := congrArg Prod.fst run
  have endpoint := congrArg Prod.snd run
  exact ⟨funded,final,Prod.ext observed rfl,endpoint.symm⟩

theorem initialized_frame (source : PanSemStateFiniteExact 64 Guest.HostMemory) (roots : BitVec 64) :
    (initialized source roots).clock=source.clock-2 ∧ (∀ target,emptyLocalsHOLFinite (restoreInitial source roots target)=emptyLocalsHOLFinite target) := by
  refine ⟨?_,by intro target; rfl⟩
  change source.clock-1-1=source.clock-2
  omega

end InitECandidate.Solver.Input.Progressive

#print axioms InitECandidate.Solver.Input.Progressive.allocation_shape
#print axioms InitECandidate.Solver.Input.Progressive.allocation_geometry
#print axioms InitECandidate.Solver.Input.Progressive.allocation_prefix
#print axioms InitECandidate.Solver.Input.Progressive.initialized_frame
