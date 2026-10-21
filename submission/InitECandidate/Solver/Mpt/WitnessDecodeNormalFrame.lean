import InitECandidate.Solver.Rlp.ValidationWriteFrame
import InitECandidate.Solver.Input.LocalEffects

namespace InitECandidate.Solver.Mpt.WitnessDecode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- Physical frame for a genuine original decoder stage. Its real heap
can advance and its real scratch cursor can decrease. All older storage
above the incoming cursor and below the incoming heap remains untouched. -/
structure NormalFrame (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (heap cursor limit : BitVec 64) : Prop where
  nextHeap : ∃ next,target.globals.lookup (ofString "heap_ptr")=some (.val (.word next)) ∧
    AllocatedBytes.Arena next 0 ∧ next.toNat%8=0 ∧ heap.toNat≤next.toNat
  nextScratch : ∃ next,Rlp.Validation.Arena target next limit ∧ next.toNat≤cursor.toNat
  domain : target.memaddrs=source.memaddrs
  endian : target.be=source.be
  code : target.code=source.code
  globals : ∀ key,key≠ofString "heap_ptr"→key≠ofString "scratch_ptr"→target.globals.lookup key=source.globals.lookup key
  memory : ∀ query : BitVec 64,cursor.toNat≤query.toNat→query.toNat<heap.toNat→target.memory query=source.memory query

theorem NormalFrame.of_erase (source target current : PanSemStateFiniteExact 64 Guest.HostMemory) (heap cursor limit : BitVec 64)
    (frame : NormalFrame source current heap cursor limit) (pure : Input.LocalEffects.erase target=Input.LocalEffects.erase current) :
    NormalFrame source target heap cursor limit := by
  have memory:=Input.LocalEffects.memory_of_erase current target pure
  have domain:=congrArg PanSemStateFiniteExact.memaddrs pure
  have endian:=congrArg PanSemStateFiniteExact.be pure
  have codeEq:=congrArg PanSemStateFiniteExact.code pure
  have globals:=congrArg PanSemStateFiniteExact.globals pure
  change target.globals=current.globals at globals
  obtain ⟨next,cell,arena,aligned,grows⟩:=frame.nextHeap
  obtain ⟨cursor2,scratch,below⟩:=frame.nextScratch
  exact ⟨⟨next,by rw [globals]; exact cell,arena,aligned,grows⟩,
    ⟨cursor2,scratch.of_fields current target cursor2 limit domain globals,below⟩,
    domain.trans frame.domain,endian.trans frame.endian,codeEq.trans frame.code,
    by intro key notHeap notScratch; rw [globals]; exact frame.globals key notHeap notScratch,
    by intro query above below; rw [memory]; exact frame.memory query above below⟩

theorem NormalFrame.prefix (source middle target : PanSemStateFiniteExact 64 Guest.HostMemory) (heap cursor limit : BitVec 64)
    (frame : NormalFrame middle target heap cursor limit)
    (domain : middle.memaddrs=source.memaddrs) (endian : middle.be=source.be) (codeEq : middle.code=source.code)
    (globals : ∀ key,middle.globals.lookup key=source.globals.lookup key)
    (above : Rlp.Validation.Above source middle cursor.toNat) : NormalFrame source target heap cursor limit :=
  ⟨frame.nextHeap,frame.nextScratch,frame.domain.trans domain,frame.endian.trans endian,frame.code.trans codeEq,
    fun key notHeap notScratch=>(frame.globals key notHeap notScratch).trans (globals key),
    fun query lower upper=>(frame.memory query lower upper).trans (above query lower)⟩

/-- Compose actual decoder stages at their real evolving heap and scratch
frontiers. The agreement band is the original incoming one, not the larger
band below a later heap that may contain newly mutated nodes. -/
theorem NormalFrame.compose (source middle target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap cursor nextHeap nextCursor limit : BitVec 64)
    (first : NormalFrame source middle heap cursor limit) (second : NormalFrame middle target nextHeap nextCursor limit)
    (grows : heap.toNat≤nextHeap.toNat) (drops : nextCursor.toNat≤cursor.toNat) : NormalFrame source target heap cursor limit := by
  obtain ⟨heap3,cell,arena,aligned,nextGrows⟩:=second.nextHeap
  obtain ⟨cursor3,scratch,nextDrops⟩:=second.nextScratch
  exact ⟨⟨heap3,cell,arena,aligned,grows.trans nextGrows⟩,⟨cursor3,scratch,nextDrops.trans drops⟩,
    second.domain.trans first.domain,second.endian.trans first.endian,second.code.trans first.code,
    fun key notHeap notScratch=>(second.globals key notHeap notScratch).trans (first.globals key notHeap notScratch),
    fun query above below=>(second.memory query (drops.trans above) (below.trans_le grows)).trans (first.memory query above below)⟩

end InitECandidate.Solver.Mpt.WitnessDecode

#print axioms InitECandidate.Solver.Mpt.WitnessDecode.NormalFrame.of_erase
#print axioms InitECandidate.Solver.Mpt.WitnessDecode.NormalFrame.prefix
#print axioms InitECandidate.Solver.Mpt.WitnessDecode.NormalFrame.compose
