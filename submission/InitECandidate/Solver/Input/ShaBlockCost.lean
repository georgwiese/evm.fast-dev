import InitECandidate.Solver.Input.ShaBlockCounterCost
import InitECandidate.Solver.Input.ClockCostCurrentConditional
import InitECandidate.Solver.WitnessRadix.CopyGeneralCost

namespace InitECandidate.Solver.Input.ShaFixedCost
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def blockGuard : ProgHOL 64 := match blockBody with | .seq first _=>first | _=>.skip
def blockTest : ExpHOL 64 := .cmp .notEqual (localVar "blk") (.op .add [.var .global (ofString "sha_accel"),.const 32#64])
def blockCopyArguments : List (ExpHOL 64) := [.op .add [.var .global (ofString "sha_accel"),.const 32#64],localVar "blk",.const 64#64]

theorem block_shape : blockBody=.seq blockGuard blockSuffix := by
  simp only [blockBody,blockGuard,blockSuffix,Guest.guestFn_sha256_block,progToHOL]

theorem block_guard_shape : blockGuard=.ite blockTest (.call (some (none,none)) (ofString "memcpy") blockCopyArguments) .skip := by
  simp only [blockGuard,blockBody,Guest.guestFn_sha256_block,progToHOL,expToHOL,Option.map_none,List.map_cons,List.map_nil,
    blockTest,blockCopyArguments,localVar]

/-- Complete original SHA block including its optional64-byte copy and both
actual accelerator loops. Only current operand mapping and actual installed
code are required; all failure and timeout outcomes retain this cost bound. -/
theorem block_price_current (source : PanSemStateFiniteExact 64 Guest.HostMemory) (block accel : BitVec 64)
    (installed : OriginalCode.Installed source.code)
    (blockLocal : source.locals.lookup (ofString "blk")=some (.val (.word block)))
    (workspace : source.globals.lookup (ofString "sha_accel")=some (.val (.word accel)))
    (domain : source.memaddrs=InitE.ordinaryDomain)
    (blockArena : AllocatedBytes.Arena block 64) (workspaceArena : AllocatedBytes.Arena (accel+32#64) 64) :
    source.clock-(evaluateHOLFiniteState source blockBody).2.clock≤17 := by
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) blockCopyArguments=
      some (CopyGeneral.values (accel+32#64) block 64) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,blockCopyArguments,CopyGeneral.values,localVar,
      blockLocal,workspace,valueIsWord,valueWord,wordOpHOL,wordOp]
  have copyCost := CopyGeneral.call_cost_arena source blockCopyArguments block (accel+32#64) 64 args
    (CopyGeneral.original_code source.code installed) domain blockArena workspaceArena
  have blocks := CopyGeneral.cost_word_multiple block (accel+32#64) 64 (by decide)
  have guardCost : source.clock-(evaluateHOLFiniteState source blockGuard).2.clock≤9 := by
    rw [block_guard_shape]
    have cost := ClockCost.conditional_current source blockTest (.call (some (none,none)) (ofString "memcpy") blockCopyArguments) .skip 9 0 (by omega) (ClockCost.skip source.code source rfl)
    exact cost
  rw [block_shape]
  exact ClockCost.sequence_current source blockGuard blockSuffix 9 8 guardCost (block_suffix_price source.code)

end InitECandidate.Solver.Input.ShaFixedCost

#print axioms InitECandidate.Solver.Input.ShaFixedCost.block_shape
#print axioms InitECandidate.Solver.Input.ShaFixedCost.block_guard_shape
#print axioms InitECandidate.Solver.Input.ShaFixedCost.block_price_current
