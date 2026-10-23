import InitECandidate.Solver.Mpt.NodeBranchPhysical
import InitECandidate.Solver.Input.LocalEffects

namespace InitECandidate.Solver.Mpt.NodeConstructor
open Flapjack PanSemStateFiniteExact WitnessRadix

/-- Callee entry, restored caller locals and lexical scope restoration
retain every physical constructor fact. Clocks and locals may differ. -/
theorem Physical.of_erase (kind : Kind) (source target source' target' : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap : BitVec 64) (words : String → BitVec 64) (physical : Physical kind source target heap words)
    (entry : Input.LocalEffects.erase source'=Input.LocalEffects.erase source)
    (exit : Input.LocalEffects.erase target'=Input.LocalEffects.erase target) : Physical kind source' target' heap words := by
  have sourceMemory:=congrArg PanSemStateFiniteExact.memory entry
  have sourceDomain:=congrArg PanSemStateFiniteExact.memaddrs entry
  have sourceEndian:=congrArg PanSemStateFiniteExact.be entry
  have targetMemory:=congrArg PanSemStateFiniteExact.memory exit
  have targetDomain:=congrArg PanSemStateFiniteExact.memaddrs exit
  have targetEndian:=congrArg PanSemStateFiniteExact.be exit
  have targetGlobals:=congrArg PanSemStateFiniteExact.globals exit
  change source'.memory=source.memory at sourceMemory
  change source'.memaddrs=source.memaddrs at sourceDomain
  change source'.be=source.be at sourceEndian
  change target'.memory=target.memory at targetMemory
  change target'.memaddrs=target.memaddrs at targetDomain
  change target'.be=target.be at targetEndian
  change target'.globals=target.globals at targetGlobals
  refine ⟨physical.arena,?_,?_,?_,physical.nextArena,physical.nextAligned,physical.before,?_,?_⟩
  · exact targetDomain.trans (physical.domain.trans sourceDomain.symm)
  · exact targetEndian.trans (physical.endian.trans sourceEndian.symm)
  · rw [targetGlobals]
    exact physical.heapCell
  · intro field member
    rw [targetMemory]
    exact physical.cells field member
  · intro query outside
    rw [targetMemory,sourceMemory]
    exact physical.memory query outside

theorem BranchPhysical.of_erase (source target source' target' : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap : BitVec 64) (physical : BranchPhysical source target heap)
    (entry : Input.LocalEffects.erase source'=Input.LocalEffects.erase source)
    (exit : Input.LocalEffects.erase target'=Input.LocalEffects.erase target) : BranchPhysical source' target' heap := by
  have memory:=congrArg PanSemStateFiniteExact.memory exit
  change target'.memory=target.memory at memory
  refine ⟨physical.allocation.of_erase .branch source target source' target' heap _ entry exit,?_,?_⟩
  · rw [memory]
    exact physical.tag
  · intro offset positive inside aligned
    rw [memory]
    exact physical.zeros offset positive inside aligned

end InitECandidate.Solver.Mpt.NodeConstructor

#print axioms InitECandidate.Solver.Mpt.NodeConstructor.Physical.of_erase
#print axioms InitECandidate.Solver.Mpt.NodeConstructor.BranchPhysical.of_erase
