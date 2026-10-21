import InitECandidate.Solver.MutableTable.WitnessBuildCallTrace
import InitECandidate.Solver.PanHeapGlobals
import InitECandidate.Solver.Input.HashInputRegion
import InitECandidate.Solver.WitnessRadix.CopyAwayIntervals

namespace InitECandidate.Solver.MutableTable.WitnessBuild
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- The actual constructor's hash control retains immutable metadata and
all globals except its real persistent heap advance. -/
theorem Normal.fields (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (array heap : BitVec 64) (count : Nat)
    (stp pad scratch : BitVec 64) (actual : Normal source target array heap count stp pad scratch) :
    target.code=source.code ∧ target.memaddrs=source.memaddrs ∧ target.be=source.be ∧ target.eshapes=source.eshapes ∧
      target.ffi.oracle=source.ffi.oracle ∧ HeapGlobals source target := by
  obtain ⟨next,lower,upper,aligned,control⟩ := actual.control
  have code:=congrArg PanSemStateFiniteExact.code control
  have domain:=congrArg PanSemStateFiniteExact.memaddrs control
  have endian:=congrArg PanSemStateFiniteExact.be control
  have exceptions:=congrArg PanSemStateFiniteExact.eshapes control
  have oracle:=congrArg (fun state=>state.ffi.oracle) control
  refine ⟨code,domain,endian,exceptions,oracle,?_⟩
  intro key other
  have cell:=congrArg (fun state=>state.globals.lookup key) control
  change target.globals.lookup key=(source.globals.update (ofString "heap_ptr",.val (.word (BitVec.ofNat 64 next)))).lookup key at cell
  rw [cell]
  simp [HolFiniteMapExact.lookup_update,FUPDATE,other,Ne.symm other]

theorem Normal.heap (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (array heap : BitVec 64) (count : Nat)
    (stp pad scratch : BitVec 64) (actual : Normal source target array heap count stp pad scratch)
    (room : heap.toNat+72+57*(4*count+4)+7≤33806089496) :
    ∃ current,target.globals.lookup (ofString "heap_ptr")=some (.val (.word current)) ∧ heap.toNat≤current.toNat ∧
      current.toNat≤heap.toNat+72+57*(4*count+4)+7 ∧ current.toNat%8=0 ∧ current.toNat≤33806089496 := by
  obtain ⟨next,lower,upper,aligned,control⟩ := actual.control
  have globals:=congrArg PanSemStateFiniteExact.globals control
  change target.globals=source.globals.update (ofString "heap_ptr",.val (.word (BitVec.ofNat 64 next))) at globals
  have number : (BitVec.ofNat 64 next).toNat=next := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  refine ⟨BitVec.ofNat 64 next,?_,by rwa [number],by rwa [number],by rwa [number],by rw [number]; omega⟩
  rw [globals]
  simp [HolFiniteMapExact.lookup_update,FUPDATE]

theorem Normal.environment (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (array heap : BitVec 64) (count : Nat)
    (stp pad scratch : BitVec 64) (actual : Normal source target array heap count stp pad scratch)
    (environment : Keccak256.Environment source stp pad) : Keccak256.Environment target stp pad := by
  obtain ⟨code,domain,endian,exceptions,oracle,globals⟩ := actual.fields source target array heap count stp pad scratch
  exact Keccak256.Environment.of_fields source target stp pad environment domain code oracle globals

/-- The physical decoded input and all record arrays before the incoming
heap survive hashing/table writes when the three real hash buffers end
below that region. -/
theorem Normal.input_frame (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (array heap : BitVec 64) (count : Nat)
    (stp pad scratch : BitVec 64) (actual : Normal source target array heap count stp pad scratch) (lower upper : Nat)
    (stateBefore : stp.toNat+200≤lower) (padBefore : pad.toNat+136≤lower) (scratchBefore : scratch.toNat+32≤lower)
    (before : upper≤heap.toNat) : Input.HashInput.Frame source target lower upper := by
  constructor
  intro query low high
  have small : lower<2^64 := by have bound:=heap.isLt; omega
  exact actual.memory query ⟨CopyGeneral.Away.before stp query 200 lower stateBefore small low,
    CopyGeneral.Away.before pad query 136 lower padBefore small low,
    CopyGeneral.Away.before scratch query 32 lower scratchBefore small low⟩ (high.trans_le before)

end InitECandidate.Solver.MutableTable.WitnessBuild

#print axioms InitECandidate.Solver.MutableTable.WitnessBuild.Normal.fields
#print axioms InitECandidate.Solver.MutableTable.WitnessBuild.Normal.heap
#print axioms InitECandidate.Solver.MutableTable.WitnessBuild.Normal.environment
#print axioms InitECandidate.Solver.MutableTable.WitnessBuild.Normal.input_frame
