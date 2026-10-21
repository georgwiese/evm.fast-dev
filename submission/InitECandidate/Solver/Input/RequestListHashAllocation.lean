import InitECandidate.Solver.Input.RequestListHashSuffix
import InitECandidate.Solver.Input.AllocationTrace

namespace InitECandidate.Solver.Input.RequestListHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def amount (n : Nat) := 32*n+32
def cursor (roots : BitVec 64) (n : Nat) := roots+BitVec.ofNat 64 (amount n)
def allocated (source : PanSemStateFiniteExact 64 Guest.HostMemory) (roots : BitVec 64) (n : Nat) :=
  bind (PersistentAlloc.post {source with clock:=source.clock-1} roots (BitVec.ofNat 64 (amount n))) "roots" roots

theorem amount_word (n : Nat) (bounded : n≤134217728) : (BitVec.ofNat 64 (amount n)).toNat=amount n := by
  rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by unfold amount; omega)]

theorem allocation_arguments (source : PanSemStateFiniteExact 64 Guest.HostMemory) (n : Nat)
    (count : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 n)))) :
    evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) allocationArguments=some (PersistentAlloc.values (BitVec.ofNat 64 (amount n))) := by
  simp [allocationArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,count,PersistentAlloc.values,valueIsWord,valueWord,panOpHOL,wordOpHOL,wordOp,BitVec.ofNat_mul,BitVec.ofNat_add,amount,BitVec.mul_comm]

theorem allocation_geometry (roots : BitVec 64) (n : Nat) (bounded : n≤134217728)
    (arena : AllocatedBytes.Arena roots (96*n+1312)) (aligned : roots.toNat%8=0) :
    PersistentAlloc.rounded roots (BitVec.ofNat 64 (amount n))=cursor roots n ∧
    AllocatedBytes.Arena roots (32*n) ∧ AllocatedBytes.Arena (cursor roots n) (1280+64*n) ∧ (cursor roots n).toNat%8=0 := by
  have upper := arena.upper
  have number : (cursor roots n).toNat=roots.toNat+amount n := byteAddress_toNat roots (amount n) (by unfold amount; omega)
  have round : PersistentAlloc.rounded roots (BitVec.ofNat 64 (amount n))=cursor roots n := by
    apply BitVec.eq_of_toNat_eq
    rw [PersistentAlloc.rounded_nat roots (BitVec.ofNat 64 (amount n)) (by rw [amount_word n bounded]; unfold amount; omega),amount_word n bounded,number]
    unfold amount
    omega
  refine ⟨round,AllocatedBytes.Arena.weaken roots _ (32*n) arena (by omega),?_,?_⟩
  · exact AllocatedBytes.Arena.subrange roots (96*n+1312) (amount n) (1280+64*n) arena (by unfold amount; omega)
  · rw [number]; unfold amount; omega

theorem allocated_workspace (source : PanSemStateFiniteExact 64 Guest.HostMemory) (roots stp accel chunk zeros : BitVec 64) (n : Nat)
    (workspace : SszHash.Workspace source stp accel chunk zeros) : SszHash.Workspace (allocated source roots n) stp accel chunk zeros :=
  SszHash.Workspace.of_fields source _ stp accel chunk zeros workspace rfl rfl (by
    intro key different
    change (source.globals.update (ofString "heap_ptr",.val (.word (PersistentAlloc.rounded roots (BitVec.ofNat 64 (amount n)))))).lookup key=_
    simp [HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different])

theorem allocated_other (source : PanSemStateFiniteExact 64 Guest.HostMemory) (roots : BitVec 64) (n : Nat) (name : String) (different : ofString "roots"≠ofString name) :
    (allocated source roots n).locals.lookup (ofString name)=source.locals.lookup (ofString name) := bind_lookup_other _ "roots" name roots different

theorem allocated_heap (source : PanSemStateFiniteExact 64 Guest.HostMemory) (roots : BitVec 64) (n : Nat)
    (round : PersistentAlloc.rounded roots (BitVec.ofNat 64 (amount n))=cursor roots n) :
    (allocated source roots n).globals.lookup (ofString "heap_ptr")=some (.val (.word (cursor roots n))) := by
  change (source.globals.update (ofString "heap_ptr",.val (.word (PersistentAlloc.rounded roots (BitVec.ofNat 64 (amount n)))))).lookup _=_
  rw [round]
  simp [HolFiniteMapExact.lookup_update,FUPDATE]

theorem allocation_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (roots : BitVec 64) (n : Nat)
    (bounded : n≤134217728) (installed : OriginalCode.Installed source.code)
    (count : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 n))))
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word roots)))
    (arena : AllocatedBytes.Arena roots (96*n+1312))
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source afterMark=(result,post)) (notTimeout : result≠some .timeOut) :
    1≤source.clock ∧ ∃ final,evaluateHOLFiniteState (allocated source roots n) afterRoots=(result,final) ∧ post=restore source "roots" final :=
  PersistentAlloc.call_trace source post "roots" allocationArguments afterRoots roots (BitVec.ofNat 64 (amount n)) (allocation_arguments source n count)
    (PersistentAlloc.original_code source.code installed) heap (by rw [amount_word n bounded]; have upper:=arena.upper; unfold amount; omega) result run notTimeout

/-- Exact known declaration scope at its actual result, including failures. -/
theorem after_roots_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source afterRoots=(result,post)) :
    ∃ final,evaluateHOLFiniteState (bind source "i" 0#64) loopAndSuffix=(result,final) ∧ post=restore source "i" final := by
  let output := evaluateHOLFiniteState (bind source "i" 0#64) loopAndSuffix
  have actual := ScalarScope.declare_execute source output.2 "i" (.const 0#64) 0#64 loopAndSuffix output.1 rfl rfl
  change evaluateHOLFiniteState source afterRoots=_ at actual
  rw [actual] at run
  have observed := congrArg Prod.fst run
  have endpoint := congrArg Prod.snd run
  exact ⟨output.2,Prod.ext observed rfl,endpoint.symm⟩

end InitECandidate.Solver.Input.RequestListHash

#print axioms InitECandidate.Solver.Input.RequestListHash.amount_word
#print axioms InitECandidate.Solver.Input.RequestListHash.allocation_arguments
#print axioms InitECandidate.Solver.Input.RequestListHash.allocation_geometry
#print axioms InitECandidate.Solver.Input.RequestListHash.allocated_workspace
#print axioms InitECandidate.Solver.Input.RequestListHash.allocated_other
#print axioms InitECandidate.Solver.Input.RequestListHash.allocated_heap
#print axioms InitECandidate.Solver.Input.RequestListHash.allocation_trace
#print axioms InitECandidate.Solver.Input.RequestListHash.after_roots_trace
