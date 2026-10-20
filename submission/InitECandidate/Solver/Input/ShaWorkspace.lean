import InitECandidate.Solver.Input.ShaPairCallCost

namespace InitECandidate.Solver.Input.ShaPair
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix

/-- Runtime facts about the current real SHA environment. This stores no
cryptographic data, future trace or assumed successful execution. -/
structure Workspace (source : PanSemStateFiniteExact 64 Guest.HostMemory) (stp accel : BitVec 64) : Prop where
  installed : OriginalCode.Installed source.code
  domain : source.memaddrs=InitE.ordinaryDomain
  state : source.globals.lookup (ofString "sha_st")=some (.val (.word stp))
  accelerator : source.globals.lookup (ofString "sha_accel")=some (.val (.word accel))
  arena : AllocatedBytes.Arena accel 96
  aligned : accel.toNat%8=0

theorem Workspace.of_fields (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (stp accel : BitVec 64)
    (actual : Workspace source stp accel) (code : target.code=source.code) (domain : target.memaddrs=source.memaddrs)
    (state : target.globals.lookup (ofString "sha_st")=source.globals.lookup (ofString "sha_st"))
    (accelerator : target.globals.lookup (ofString "sha_accel")=source.globals.lookup (ofString "sha_accel")) : Workspace target stp accel :=
  ⟨code.symm ▸ actual.installed,domain.trans actual.domain,state.trans actual.state,accelerator.trans actual.accelerator,actual.arena,actual.aligned⟩

theorem Workspace.after (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (stp accel : BitVec 64)
    (actual : Workspace source stp accel) (program : ProgHOL 64) (result : Option (PanSemResultExact 64))
    (run : evaluateHOLFiniteState source program=(result,target))
    (statePure : GlobalEffects.Preserves (ofString "sha_st") source.code program)
    (acceleratorPure : GlobalEffects.Preserves (ofString "sha_accel") source.code program) : Workspace target stp accel := by
  have fields := evaluation_fields source target program result run
  have state := statePure source rfl
  have accelerator := acceleratorPure source rfl
  rw [run] at state accelerator
  exact Workspace.of_fields source target stp accel actual fields.2.2.2 fields.1 (congrArg Prod.snd state) (congrArg Prod.snd accelerator)

theorem Workspace.at_callee (source : PanSemStateFiniteExact 64 Guest.HostMemory) (callee : HolFiniteMapExact MlS (ValueHOL 64))
    (stp accel : BitVec 64) (actual : Workspace source stp accel) : Workspace (callEntryStateHOLFinite source callee) stp accel :=
  Workspace.of_fields source _ stp accel actual rfl rfl rfl rfl

end InitECandidate.Solver.Input.ShaPair

#print axioms InitECandidate.Solver.Input.ShaPair.Workspace.of_fields
#print axioms InitECandidate.Solver.Input.ShaPair.Workspace.after
#print axioms InitECandidate.Solver.Input.ShaPair.Workspace.at_callee
