import InitECandidate.Solver.Input.MerkleOuterProgram

namespace InitECandidate.Solver.Input.Merkle
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def extensionLoop : ProgHOL 64 := (BuildProgram.loops body)[2]?.getD .skip
def extensionStep : ProgHOL 64 := match extensionLoop with | .while _ step=>step | _=>.skip
def extensionTest : ExpHOL 64 := .cmp .less (localVar "d") (localVar "target")
def extensionArguments : List (ExpHOL 64) := [localVar "buf",.op .add [.var .global (ofString "zero_hashes"),.panop .mul [localVar "d",.const 32#64]],localVar "buf"]
def extensionCall : ProgHOL 64 := .call (some (none,none)) (ofString "sha256_pair") extensionArguments
def extensionIncrement : ProgHOL 64 := .assign .local (ofString "d") (.op .add [localVar "d",.const 1#64])
def afterExtension : ProgHOL 64 := match afterDense with
  | .dec _ _ _ rest=>(match rest with | .seq _ tail=>tail | _=>.skip)
  | _=>.skip
def outputArguments : List (ExpHOL 64) := [localVar "out",localVar "buf",.const 32#64]

set_option maxRecDepth 100000 in
theorem extension_shape : afterDense=.dec (ofString "d") .one (localVar "dn") (.seq extensionLoop afterExtension) ∧
    extensionLoop=.while extensionTest extensionStep ∧ extensionStep=.seq extensionCall extensionIncrement ∧
    afterExtension=.seq (.call (some (none,none)) (ofString "memcpy") outputArguments)
      (.seq (.call (some (none,none)) (ofString "heap_release") [localVar "mark"]) (.return (.const 0#64))) := by
  simp only [afterDense,denseContinuation,afterClear,afterCopy,afterBuffer,afterMark,afterZero,afterDepth,afterCount,afterLimit,body,
    extensionLoop,extensionStep,extensionTest,extensionArguments,extensionCall,extensionIncrement,afterExtension,outputArguments,
    BuildProgram.loops,Guest.guestFn_merkleize,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,List.append_nil,List.nil_append,List.cons_append,
    List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Option.map_none,localVar]
  exact ⟨True.intro,True.intro,True.intro,True.intro⟩

theorem extension_advances : CounterFlow.Advances (ofString "d") 1 extensionStep := by
  rw [extension_shape.2.2.1]
  exact CounterFlow.sequence _ _ _ 0 1 (CounterFlow.preserved _ _ (.call none _ _ (by intro name impossible; cases impossible))) (CounterFlow.increment _)

theorem extension_other (key : MlS) (different : key≠ofString "d") : LocalPrefix key extensionStep := by
  rw [extension_shape.2.2.1]
  exact .seq (.call none _ _ (by intro name impossible; cases impossible)) (.assign _ _ different)

theorem extension_globals (key : MlS) (code) (installed : OriginalCode.Installed code) : GlobalEffects.Preserves key code extensionStep := by
  rw [extension_shape.2.2.1]
  exact GlobalEffects.sequence key code _ _
    (GlobalEffects.call_body key code (some none) (ofString "sha256_pair") extensionArguments _ _ _
      (ShaFixedCost.pair_code code installed) (ShaFixedCost.pair_globals key code installed)) (GlobalEffects.assign key code _ _)

theorem extension_arguments (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor zeros : BitVec 64) (index : Nat)
    (buffer : source.locals.lookup (ofString "buf")=some (.val (.word cursor)))
    (d : source.locals.lookup (ofString "d")=some (.val (.word (BitVec.ofNat 64 index))))
    (table : source.globals.lookup (ofString "zero_hashes")=some (.val (.word zeros))) :
    evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) extensionArguments=
      some (ShaPair.values cursor (zeros+BitVec.ofNat 64 (32*index)) cursor) := by
  simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,extensionArguments,localVar,buffer,d,table,
    ShaPair.values,valueIsWord,valueWord,wordOpHOL,wordOp,panOpHOL,BitVec.ofNat_mul,Nat.mul_comm]

/-- Actual extension pairs read one mapped zero-hash chunk per current
small depth, and reuse the real mapped32-byte root buffer. -/
theorem extension_step_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor zeros stp accel : BitVec 64) (index : Nat)
    (small : index<64) (workspace : ShaPair.Workspace source stp accel)
    (bufferArena : AllocatedBytes.Arena cursor 32) (tableArena : AllocatedBytes.Arena zeros 2048)
    (buffer : source.locals.lookup (ofString "buf")=some (.val (.word cursor)))
    (d : source.locals.lookup (ofString "d")=some (.val (.word (BitVec.ofNat 64 index))))
    (table : source.globals.lookup (ofString "zero_hashes")=some (.val (.word zeros))) :
    source.clock-(evaluateHOLFiniteState source extensionStep).2.clock≤53 := by
  have zeroArena := AllocatedBytes.Arena.subrange zeros 2048 (32*index) 32 tableArena (by omega)
  have cost := ShaPair.call_cost source cursor (zeros+BitVec.ofNat 64 (32*index)) cursor stp accel workspace.installed (some none) extensionArguments
    (extension_arguments source cursor zeros index buffer d table) workspace.state workspace.accelerator workspace.domain bufferArena zeroArena workspace.arena workspace.aligned
  rw [extension_shape.2.2.1]
  exact ClockCost.sequence_current source extensionCall extensionIncrement 53 0 cost (ClockCost.assign source.code _ _)

end InitECandidate.Solver.Input.Merkle

#print axioms InitECandidate.Solver.Input.Merkle.extension_shape
#print axioms InitECandidate.Solver.Input.Merkle.extension_advances
#print axioms InitECandidate.Solver.Input.Merkle.extension_other
#print axioms InitECandidate.Solver.Input.Merkle.extension_globals
#print axioms InitECandidate.Solver.Input.Merkle.extension_arguments
#print axioms InitECandidate.Solver.Input.Merkle.extension_step_cost
