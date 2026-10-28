import InitECandidate.Solver.CurrentKeccak.Globals
import InitECandidate.Solver.CurrentKeccak.AbsorbCall
import InitECandidate.Solver.WitnessRadix.AllocatedBytes

namespace InitECandidate.Solver.CurrentKeccak.Hash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString Input WitnessRadix

/-- Current allocated software-hash workspace, without a cryptographic
oracle or any future successful call or read. -/
structure Environment (source : PanSemStateFiniteExact 64 Guest.HostMemory) (stp pad : BitVec 64) : Prop where
  installed : OriginalCode.Installed source.code
  domain : source.memaddrs=InitE.ordinaryDomain
  stateGlobal : source.globals.lookup (ofString "keccak_st")=some (.val (.word stp))
  padGlobal : source.globals.lookup (ofString "keccak_pad")=some (.val (.word pad))
  stateArena : AllocatedBytes.Arena stp 200
  padArena : AllocatedBytes.Arena pad 136
  stateAligned : stp.toNat%8=0
  padAligned : pad.toNat%8=0

theorem Environment.of_frame {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {stp pad : BitVec 64}
    (ready : Environment source stp pad) (same : LocalEffects.erase target=LocalEffects.erase source) : Environment target stp pad := by
  have code:=congrArg PanSemStateFiniteExact.code same
  have domain:=congrArg PanSemStateFiniteExact.memaddrs same
  have globals:=congrArg PanSemStateFiniteExact.globals same
  change target.code=source.code at code
  change target.memaddrs=source.memaddrs at domain
  change target.globals=source.globals at globals
  exact ⟨by rw [code]; exact ready.installed,domain.trans ready.domain,by rw [globals]; exact ready.stateGlobal,
    by rw [globals]; exact ready.padGlobal,ready.stateArena,ready.padArena,ready.stateAligned,ready.padAligned⟩

theorem Environment.after {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {stp pad : BitVec 64}
    (ready : Environment source stp pad) (program : ProgHOL 64) (result : Option (PanSemResultExact 64))
    (globals : ∀ key,GlobalEffects.Preserves key source.code program)
    (run : evaluateHOLFiniteState source program=(result,target)) : Environment target stp pad := by
  have fields:=evaluation_fields source target program result run
  have state:=globals (ofString "keccak_st") source rfl
  have padding:=globals (ofString "keccak_pad") source rfl
  rw [run] at state padding
  exact ⟨by rw [fields.2.2.2]; exact ready.installed,fields.1.trans ready.domain,
    (congrArg Prod.snd state).trans ready.stateGlobal,(congrArg Prod.snd padding).trans ready.padGlobal,
    ready.stateArena,ready.padArena,ready.stateAligned,ready.padAligned⟩

theorem zero_call_globals (key : MlS) (code) (installed : OriginalCode.Installed code) (arguments : List (ExpHOL 64)) :
    GlobalEffects.Preserves key code (.call (some (none,none)) (ofString "memzero") arguments) :=
  GlobalEffects.call_body key code (some none) _ arguments Zero.formals Zero.body .one (Zero.original_code code installed) (zero_globals key code)

theorem copy_call_globals (key : MlS) (code) (installed : OriginalCode.Installed code) (arguments : List (ExpHOL 64)) :
    GlobalEffects.Preserves key code (.call (some (none,none)) (ofString "memcpy") arguments) :=
  GlobalEffects.call_body key code (some none) _ arguments CopyGeneral.formals Copy32.body .one (CopyGeneral.original_code code installed) (copy_globals key code)

theorem absorb_call_globals (key : MlS) (code) (installed : OriginalCode.Installed code) (arguments : List (ExpHOL 64)) :
    GlobalEffects.Preserves key code (.call (some (none,none)) (ofString "keccak_absorb_block") arguments) :=
  GlobalEffects.call_body key code (some none) _ arguments Absorb.formals Absorb.body .one (Absorb.original_code code installed) (absorb_globals key code installed)

theorem blocks_globals (key : MlS) (code) (installed : OriginalCode.Installed code) :
    GlobalEffects.Preserves key code blocks :=
  GlobalEffects.loop key code condition blockBody (GlobalEffects.sequence key code _ _ (absorb_call_globals key code installed blockArguments) (GlobalEffects.assign key code _ _))

end InitECandidate.Solver.CurrentKeccak.Hash

#print axioms InitECandidate.Solver.CurrentKeccak.Hash.Environment.after
#print axioms InitECandidate.Solver.CurrentKeccak.Hash.blocks_globals
