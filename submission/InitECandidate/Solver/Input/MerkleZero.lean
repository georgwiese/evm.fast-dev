import InitECandidate.Solver.Input.MerkleDepthPrefix
import InitECandidate.Solver.Input.NoFallthrough

namespace InitECandidate.Solver.Input.Merkle
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def zeroTest : ExpHOL 64 := .cmp .equal (localVar "n") (.const 0#64)
def zeroArguments : List (ExpHOL 64) := [localVar "out",.op .add [.var .global (ofString "zero_hashes"),.panop .mul [localVar "target",.const 32#64]],.const 32#64]
def zeroBody : ProgHOL 64 := .seq (.call (some (none,none)) (ofString "memcpy") zeroArguments) (.return (.const 0#64))
def zeroGuard : ProgHOL 64 := .ite zeroTest zeroBody .skip
def afterZero : ProgHOL 64 := match afterDepth with | .seq _ rest=>rest | _=>.skip

set_option maxRecDepth 100000 in
theorem zero_shape : afterDepth=.seq zeroGuard afterZero := by
  simp only [afterDepth,afterCount,afterLimit,body,afterZero,Guest.guestFn_merkleize,progToHOL,expToHOL,shapeToHOL,
    List.map_cons,List.map_nil,Option.map_none,zeroGuard,zeroTest,zeroBody,zeroArguments,localVar]

theorem zero_body_stops : NoFallthrough zeroBody := NoFallthrough.sequence _ _ (NoFallthrough.returned _)

/-- The actual empty-tree branch copies one initialized zero-hash chunk.
Every depth<64 is in the real2048-byte table; no zero-hash contents need be
assumed for this execution-clock bound. -/
theorem zero_body_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (out zeros : BitVec 64) (target : Nat)
    (small : target<64) (installed : OriginalCode.Installed source.code) (domain : source.memaddrs=InitE.ordinaryDomain)
    (output : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (depth : source.locals.lookup (ofString "target")=some (.val (.word (BitVec.ofNat 64 target))))
    (table : source.globals.lookup (ofString "zero_hashes")=some (.val (.word zeros)))
    (outputArena : AllocatedBytes.Arena out 32) (tableArena : AllocatedBytes.Arena zeros 2048) :
    source.clock-(evaluateHOLFiniteState source zeroBody).2.clock≤5 := by
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) zeroArguments=
      some (CopyGeneral.values out (zeros+BitVec.ofNat 64 (32*target)) 32) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,zeroArguments,localVar,output,depth,table,CopyGeneral.values,
      valueIsWord,valueWord,wordOpHOL,wordOp,panOpHOL,BitVec.ofNat_mul,Nat.mul_comm]
  have srcArena : AllocatedBytes.Arena (zeros+BitVec.ofNat 64 (32*target)) 32 := AllocatedBytes.Arena.subrange zeros 2048 (32*target) 32 tableArena (by omega)
  have cost := CopyGeneral.call_cost_arena source zeroArguments (zeros+BitVec.ofNat 64 (32*target)) out 32 args
    (CopyGeneral.original_code source.code installed) domain srcArena outputArena
  have blocks := CopyGeneral.cost_word_multiple (zeros+BitVec.ofNat 64 (32*target)) out 32 (by decide)
  exact ClockCost.sequence_current source _ _ 5 0 (by omega) (ClockCost.returned source.code _)

theorem zero_guard_selected (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (count : source.locals.lookup (ofString "n")=some (.val (.word 0#64))) :
    evaluateHOLFiniteState source zeroGuard=evaluateHOLFiniteState source zeroBody := by
  have read : eval source zeroTest=some (.val (.word 1#64)) := by
    simp [eval,zeroTest,localVar,evalHOLExact,toExact,count,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  simp only [eval] at read
  rw [zeroGuard,evaluateHOLFiniteState_ite,read]
  rfl

theorem after_depth_zero_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (out zeros : BitVec 64) (target : Nat)
    (small : target<64) (installed : OriginalCode.Installed source.code) (domain : source.memaddrs=InitE.ordinaryDomain)
    (count : source.locals.lookup (ofString "n")=some (.val (.word 0#64)))
    (output : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (depth : source.locals.lookup (ofString "target")=some (.val (.word (BitVec.ofNat 64 target))))
    (table : source.globals.lookup (ofString "zero_hashes")=some (.val (.word zeros)))
    (outputArena : AllocatedBytes.Arena out 32) (tableArena : AllocatedBytes.Arena zeros 2048) :
    source.clock-(evaluateHOLFiniteState source afterDepth).2.clock≤5 := by
  have cost := zero_body_cost source out zeros target small installed domain output depth table outputArena tableArena
  have stops := zero_body_stops source
  rw [zero_shape,evaluateHOLFiniteState_seq_line780,zero_guard_selected source count]
  generalize observed : evaluateHOLFiniteState source zeroBody=response at cost stops ⊢
  obtain ⟨result,post⟩ := response
  cases result with
  | none=>exact (stops rfl).elim
  | some result=>exact cost

theorem zero_guard_passes (source : PanSemStateFiniteExact 64 Guest.HostMemory) (n : BitVec 64)
    (count : source.locals.lookup (ofString "n")=some (.val (.word n))) (nonzero : n≠0#64) :
    evaluateHOLFiniteState source zeroGuard=(none,source) := by
  have read : eval source zeroTest=some (.val (.word 0#64)) := by
    simp [eval,zeroTest,localVar,evalHOLExact,toExact,count,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,nonzero]
  simp only [eval] at read
  rw [zeroGuard,evaluateHOLFiniteState_ite,read]
  simp [evaluateHOLFiniteState_skip]

theorem after_depth_nonzero (source : PanSemStateFiniteExact 64 Guest.HostMemory) (n : BitVec 64)
    (count : source.locals.lookup (ofString "n")=some (.val (.word n))) (nonzero : n≠0#64) :
    evaluateHOLFiniteState source afterDepth=evaluateHOLFiniteState source afterZero := by
  rw [zero_shape,StateSteps.next_sequence source source _ _ (zero_guard_passes source n count nonzero) (Nat.le_refl _)]

end InitECandidate.Solver.Input.Merkle

#print axioms InitECandidate.Solver.Input.Merkle.zero_shape
#print axioms InitECandidate.Solver.Input.Merkle.zero_body_cost
#print axioms InitECandidate.Solver.Input.Merkle.after_depth_zero_cost
#print axioms InitECandidate.Solver.Input.Merkle.after_depth_nonzero
