import InitECandidate.Solver.Mpt.WitnessCoreRegistryTerminal
import InitECandidate.Solver.Input.Copy32SpanCall
import InitECandidate.Solver.WitnessRadix.CopyGeneralCode
import InitECandidate.Solver.WitnessRadix.CopyAwayIntervals

namespace InitECandidate.Solver.Mpt.WitnessCore
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact GasBudget WitnessRadix
open Flapjack.Basis.Pure.MlString

theorem NodeRegistry.of_fields (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frontier : Nat) (heap db : BitVec 64) (registry : NodeRegistry source frontier heap db)
    (memory : target.memory=source.memory) (domain : target.memaddrs=source.memaddrs) :
    ∃ next : NodeRegistry target frontier heap db,next.graph.valid=registry.graph.valid := by
  obtain ⟨graph,validEq,regions,disjoint,⟨values⟩⟩:=registry.graph.after_agreement source target 1024 frontier heap.toNat (WitnessValue db)
    registry.values registry.regions registry.disjoint domain (fun _ _=>congrFun memory _) (fun _ _=>congrFun memory _)
  exact ⟨⟨graph,values,regions,disjoint⟩,validEq⟩

/-- The real original copy writes only its fresh aligned32-byte buffer.
Every previously completed node and every word below its old heap bound
survives, regardless of source/destination byte overlap. -/
theorem NodeRegistry.copy32_after (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frontier : Nat) (heap db src dst : BitVec 64) (arguments : List (ExpHOL 64))
    (registry : NodeRegistry source frontier heap db) (before : heap.toNat≤dst.toNat)
    (targetArena : AllocatedBytes.Arena dst 32) (aligned : dst.toNat%8=0)
    (installed : Input.OriginalCode.Installed source.code)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (CopyGeneral.values dst src 32))
    (normal : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "memcpy") arguments)=(none,target)) :
    (∃ next : NodeRegistry target frontier heap db,next.graph.valid=registry.graph.valid) ∧
      (∀ query : BitVec 64,query.toNat<heap.toNat → target.memory query=source.memory query) := by
  obtain ⟨frame,locals⟩:=Input.Copy32Span.call_normal source target dst src arguments args installed normal
  have domainEq : target.memaddrs=source.memaddrs:=frame.domain
  have memory : ∀ query : BitVec 64,query.toNat<heap.toNat → target.memory query=source.memory query:=by
    intro query below
    exact frame.memory query (CopyGeneral.Away.after dst query 32 aligned
      (by have upper:=targetArena.upper; omega) (below.trans_le before))
  obtain ⟨graph,validEq,regions,disjoint,⟨values⟩⟩:=registry.graph.after_agreement source target 1024 frontier heap.toNat (WitnessValue db)
    registry.values registry.regions registry.disjoint domainEq
    (fun query required=>memory query (registry.graph.footprint_bounds frontier heap.toNat registry.regions query required).2)
    (fun query required=>memory query (registry.graph.value_bounds frontier heap.toNat registry.regions query required).2)
  exact ⟨⟨⟨graph,values,regions,disjoint⟩,validEq⟩,memory⟩

end InitECandidate.Solver.Mpt.WitnessCore

#print axioms InitECandidate.Solver.Mpt.WitnessCore.NodeRegistry.of_fields
#print axioms InitECandidate.Solver.Mpt.WitnessCore.NodeRegistry.copy32_after
