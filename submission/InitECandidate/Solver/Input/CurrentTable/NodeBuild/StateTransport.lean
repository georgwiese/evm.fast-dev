import InitECandidate.Solver.Input.CurrentTable.NodeBuild.LoopState

namespace InitECandidate.Solver.Input.CurrentTable.NodeBuild
open Flapjack PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix

def ImageUpTo (data : Data) (current : PanSemStateFiniteExact 64 Guest.HostMemory) (processed : Nat) : Prop :=
  ∃ root next count valid bits left right keys,
    Image current data.table data.cap root next count valid bits left right keys (ValueOf data) ∧ count≤processed

/-- Reassemble the real loop state from preserved physical input, globals,
noncounter locals and the newly established table image/counter. -/
theorem State.transport (data : Data) (origin source target : PanSemStateFiniteExact 64 Guest.HostMemory) (index nextIndex : Nat)
    (state : State data origin source index)
    (code : target.code=source.code) (domain : target.memaddrs=source.memaddrs) (endian : target.be=source.be)
    (globals : ∀ key,target.globals.lookup key=source.globals.lookup key)
    (locals : ∀ key,ofString "i"≠key → target.locals.lookup key=source.locals.lookup key)
    (frame : HashInput.Frame source target data.lower data.upper)
    (counter : target.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 nextIndex))))
    (image : ImageUpTo data target nextIndex) : State data origin target nextIndex := by
  have installed : OriginalCode.Installed target.code := by rw [code]; exact state.arena.code
  have targetDomain := domain.trans state.arena.domain
  have arena : CurrentStartup.ArenaState target :=
    ⟨(globals _).trans state.arena.scratch,(globals _).trans state.arena.frame,targetDomain,installed⟩
  have environment : CurrentKeccak.Hash.Environment target data.stp data.pad :=
    ⟨installed,targetDomain,(globals _).trans state.environment.stateGlobal,(globals _).trans state.environment.padGlobal,
      state.environment.stateArena,state.environment.padArena,state.environment.stateAligned,state.environment.padAligned⟩
  obtain ⟨heap,cell,lower,upper,aligned⟩ := state.heap
  exact ⟨arena,endian.trans state.little,environment,(globals _).trans state.outCell,
    state.rows.of_frame source target data.array data.pointers data.lengths data.total data.lower data.upper frame,
    state.input.trans origin source target data.lower data.upper frame,
    ⟨heap,(globals _).trans cell,lower,upper,aligned⟩,
    (fun key=>(globals key).trans (state.globals key)),
    (locals _ (by decide)).trans state.arrayCell,(locals _ (by decide)).trans state.countCell,
    (locals _ (by decide)).trans state.tableCell,counter,image⟩

end InitECandidate.Solver.Input.CurrentTable.NodeBuild

#print axioms InitECandidate.Solver.Input.CurrentTable.NodeBuild.State.transport
