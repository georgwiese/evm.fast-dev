import InitECandidate.Solver.Mpt.StateInitBlockFrame
import InitECandidate.Solver.Mpt.StateInitBlockAllocation
import InitECandidate.Solver.Mpt.StateInitTailNormal

namespace InitECandidate.Solver.Mpt.StateInit.Block
open Flapjack PanSemStateFiniteExact

theorem walk_code (specs : List Action) (source : PanSemStateFiniteExact 64 Guest.HostMemory) (block start : Nat) :
    (walk source block start specs).code=source.code:=
  congrArg Prod.fst (walk_runtime specs source block start)

theorem walk_domain (specs : List Action) (source : PanSemStateFiniteExact 64 Guest.HostMemory) (block start : Nat) :
    (walk source block start specs).memaddrs=source.memaddrs:=
  congrArg (fun fields=>fields.2.1) (walk_runtime specs source block start)

theorem walk_endian (specs : List Action) (source : PanSemStateFiniteExact 64 Guest.HostMemory) (block start : Nat) :
    (walk source block start specs).be=source.be:=
  congrArg (fun fields=>fields.2.2.1) (walk_runtime specs source block start)

theorem completed_runtime (source : PanSemStateFiniteExact 64 Guest.HostMemory) (start : Nat) :
    runtimeFields (completed source start)=runtimeFields source:=rfl

theorem completed_domain (source : PanSemStateFiniteExact 64 Guest.HostMemory) (start : Nat) :
    (completed source start).memaddrs=source.memaddrs:=rfl

theorem completed_endian (source : PanSemStateFiniteExact 64 Guest.HostMemory) (start : Nat) :
    (completed source start).be=source.be:=rfl

theorem ready_runtime (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap workspace : BitVec 64) :
    runtimeFields (ready source heap workspace)=runtimeFields source:=rfl

end InitECandidate.Solver.Mpt.StateInit.Block

#print axioms InitECandidate.Solver.Mpt.StateInit.Block.walk_code
#print axioms InitECandidate.Solver.Mpt.StateInit.Block.walk_domain
#print axioms InitECandidate.Solver.Mpt.StateInit.Block.walk_endian
#print axioms InitECandidate.Solver.Mpt.StateInit.Block.completed_runtime
#print axioms InitECandidate.Solver.Mpt.StateInit.Block.completed_domain
#print axioms InitECandidate.Solver.Mpt.StateInit.Block.completed_endian
#print axioms InitECandidate.Solver.Mpt.StateInit.Block.ready_runtime
