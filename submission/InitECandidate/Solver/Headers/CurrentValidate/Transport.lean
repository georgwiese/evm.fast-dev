import InitECandidate.Solver.Headers.CurrentValidate.Round

namespace InitECandidate.Solver.Headers.CurrentValidate
open Flapjack PanSemStateFiniteExact WitnessRadix

/-- Current input/row/loop facts pass through real code/domain equality,
unchanged globals/locals and a proved physical input-memory frame. -/
theorem RoundState.transport (data : Data) (origin source target : PanSemStateFiniteExact 64 Guest.HostMemory) (index : Nat)
    (state : RoundState data origin source index)
    (code : target.code=source.code) (domain : target.memaddrs=source.memaddrs)
    (globals : ∀ key,target.globals.lookup key=source.globals.lookup key)
    (locals : ∀ key,target.locals.lookup key=source.locals.lookup key)
    (frame : Input.HashInput.Frame source target data.lower data.upper) : RoundState data origin target index := by
  have installed : Input.OriginalCode.Installed target.code := by rw [code]; exact state.arena.code
  have actualDomain:=domain.trans state.arena.domain
  refine ⟨⟨(globals _).trans state.arena.scratch,(globals _).trans state.arena.frame,actualDomain,installed⟩,
    ⟨installed,actualDomain,(globals _).trans state.environment.stateGlobal,(globals _).trans state.environment.padGlobal,
      state.environment.stateArena,state.environment.padArena,state.environment.stateAligned,state.environment.padAligned⟩,
    state.input.trans origin source target data.lower data.upper frame,
    state.rows.of_frame source target data.array data.pointers data.lengths data.count data.lower data.upper frame,?_,
    (locals _).trans state.arrayCell,(locals _).trans state.countCell,(locals _).trans state.hsCell,(locals _).trans state.hashesCell,(locals _).trans state.indexCell,?_⟩
  · obtain ⟨pointer,cell,bounded,aligned,before⟩:=state.heap
    exact ⟨pointer,(globals _).trans cell,bounded,aligned,before⟩
  · intro key different
    exact (globals key).trans (state.globals key different)

end InitECandidate.Solver.Headers.CurrentValidate

#print axioms InitECandidate.Solver.Headers.CurrentValidate.RoundState.transport
