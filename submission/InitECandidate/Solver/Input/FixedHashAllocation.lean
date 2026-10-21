import InitECandidate.Solver.Input.FixedHashTail
import InitECandidate.Solver.Input.AllocationTrace

namespace InitECandidate.Solver.Input.FixedHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def Kind.cursor (kind : Kind) (ch : BitVec 64) := ch+BitVec.ofNat 64 (32*kind.count)
def Kind.allocated (kind : Kind) (source : PanSemStateFiniteExact 64 Guest.HostMemory) (ch : BitVec 64) :=
  bind (PersistentAlloc.post {source with clock:=source.clock-1} ch (BitVec.ofNat 64 (32*kind.count))) "ch" ch

theorem allocation_arguments (kind : Kind) (source : PanSemStateFiniteExact 64 Guest.HostMemory) :
    evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) kind.allocationArguments=some (PersistentAlloc.values (BitVec.ofNat 64 (32*kind.count))) := by
  simp [Kind.allocationArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,PersistentAlloc.values,valueIsWord,valueWord,panOpHOL,BitVec.ofNat_mul,BitVec.mul_comm]

theorem amount_word (kind : Kind) : (BitVec.ofNat 64 (32*kind.count)).toNat=32*kind.count := by cases kind <;> rfl

set_option maxRecDepth 4000 in
theorem allocation_geometry (kind : Kind) (ch p : BitVec 64)
    (inputArena : AllocatedBytes.Arena p kind.length) (arena : AllocatedBytes.Arena ch (32*kind.count+1120)) (aligned : ch.toNat%8=0) :
    PersistentAlloc.rounded ch (BitVec.ofNat 64 (32*kind.count))=kind.cursor ch ∧ Geometry p ch (kind.cursor ch) kind.length kind.count := by
  have upper := arena.upper
  have number : (kind.cursor ch).toNat=ch.toNat+32*kind.count := byteAddress_toNat ch (32*kind.count) (by omega)
  have round : PersistentAlloc.rounded ch (BitVec.ofNat 64 (32*kind.count))=kind.cursor ch := by
    apply BitVec.eq_of_toNat_eq
    rw [PersistentAlloc.rounded_nat ch (BitVec.ofNat 64 (32*kind.count)) (by rw [amount_word]; omega),amount_word,number]
    omega
  exact ⟨round,⟨inputArena,AllocatedBytes.Arena.weaken ch _ (32*kind.count) arena (by omega),aligned,
    AllocatedBytes.Arena.subrange ch (32*kind.count+1120) (32*kind.count) 1120 arena (by omega),by rw [number]; omega⟩⟩

theorem allocated_ready (kind : Kind) (source : PanSemStateFiniteExact 64 Guest.HostMemory) (p ch out mark stp accel chunk zeros : BitVec 64)
    (workspace : SszHash.Workspace source stp accel chunk zeros)
    (pointer : source.locals.lookup (ofString kind.inputName)=some (.val (.word p)))
    (output : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (saved : source.locals.lookup (ofString "mark")=some (.val (.word mark)))
    (round : PersistentAlloc.rounded ch (BitVec.ofNat 64 (32*kind.count))=kind.cursor ch) :
    Ready (kind.allocated source ch) kind.inputName p ch out (kind.cursor ch) mark stp accel chunk zeros := by
  have nextWorkspace := SszHash.Workspace.of_fields source (kind.allocated source ch) stp accel chunk zeros workspace rfl rfl (by
    intro key different
    change (source.globals.update (ofString "heap_ptr",.val (.word (PersistentAlloc.rounded ch (BitVec.ofNat 64 (32*kind.count)))))).lookup key=_
    simp [HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different])
  have other (name : String) (different : ofString "ch"≠ofString name) : (kind.allocated source ch).locals.lookup (ofString name)=source.locals.lookup (ofString name) := bind_lookup_other _ "ch" name ch different
  refine ⟨nextWorkspace,(other kind.inputName (by cases kind <;> decide)).trans pointer,bind_lookup_same _ _ _,(other "out" (by decide)).trans output,(other "mark" (by decide)).trans saved,?_⟩
  change (source.globals.update (ofString "heap_ptr",.val (.word (PersistentAlloc.rounded ch (BitVec.ofNat 64 (32*kind.count)))))).lookup _=_
  rw [round]
  simp [HolFiniteMapExact.lookup_update,FUPDATE]

/-- Actual fixed record temporary allocation derives its caller funding
and exact current chunk/heap state from the enclosing execution. -/
theorem allocation_trace (kind : Kind) (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (ch : BitVec 64)
    (installed : OriginalCode.Installed source.code)
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word ch)))
    (arena : AllocatedBytes.Arena ch (32*kind.count+1120))
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source kind.afterMark=(result,post)) (notTimeout : result≠some .timeOut) :
    1≤source.clock ∧ ∃ final,evaluateHOLFiniteState (kind.allocated source ch) kind.afterAllocation=(result,final) ∧ post=restore source "ch" final :=
  PersistentAlloc.call_trace source post "ch" kind.allocationArguments kind.afterAllocation ch (BitVec.ofNat 64 (32*kind.count)) (allocation_arguments kind source)
    (PersistentAlloc.original_code source.code installed) heap (by rw [amount_word]; have h:=arena.upper; omega) result run notTimeout

end InitECandidate.Solver.Input.FixedHash

#print axioms InitECandidate.Solver.Input.FixedHash.allocation_arguments
#print axioms InitECandidate.Solver.Input.FixedHash.amount_word
#print axioms InitECandidate.Solver.Input.FixedHash.allocation_geometry
#print axioms InitECandidate.Solver.Input.FixedHash.allocated_ready
#print axioms InitECandidate.Solver.Input.FixedHash.allocation_trace
