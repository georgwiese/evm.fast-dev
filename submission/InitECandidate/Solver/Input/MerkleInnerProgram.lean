import InitECandidate.Solver.Input.MerkleBufferedProgram
import InitECandidate.Solver.Input.ShaWorkspace
import InitECandidate.Solver.Input.CounterFlow

namespace InitECandidate.Solver.Input.Merkle
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def innerLoop : ProgHOL 64 := (BuildProgram.loops body)[1]?.getD .skip
def innerStep : ProgHOL 64 := match innerLoop with | .while _ step=>step | _=>.skip
def innerArguments : List (ExpHOL 64) := [.op .add [localVar "buf",.panop .mul [localVar "j",.const 64#64]],
  .op .add [localVar "buf",.panop .mul [localVar "j",.const 64#64],.const 32#64],
  .op .add [localVar "buf",.panop .mul [localVar "j",.const 32#64]]]
def innerCall : ProgHOL 64 := .call (some (none,none)) (ofString "sha256_pair") innerArguments
def innerIncrement : ProgHOL 64 := .assign .local (ofString "j") (.op .add [localVar "j",.const 1#64])

set_option maxRecDepth 100000 in
theorem inner_shape : innerLoop=.while (.cmp .less (localVar "j") (localVar "half")) innerStep ∧
    innerStep=.seq innerCall innerIncrement := by
  simp only [innerLoop,innerStep,BuildProgram.loops,body,Guest.guestFn_merkleize,progToHOL,expToHOL,shapeToHOL,
    List.map_cons,List.map_nil,List.append_nil,List.nil_append,List.cons_append,List.getElem?_cons_zero,List.getElem?_cons_succ,
    Option.getD_some,Option.map_none,innerCall,innerArguments,innerIncrement,localVar]
  exact ⟨True.intro,True.intro⟩

theorem inner_advances : CounterFlow.Advances (ofString "j") 1 innerStep := by
  rw [inner_shape.2]
  exact CounterFlow.sequence _ _ _ 0 1 (CounterFlow.preserved _ _ (.call none _ _ (by intro name impossible; cases impossible))) (CounterFlow.increment _)

theorem inner_other (key : MlS) (different : key≠ofString "j") : LocalPrefix key innerStep := by
  rw [inner_shape.2]
  exact .seq (.call none _ _ (by intro name impossible; cases impossible)) (.assign _ _ different)

theorem inner_globals (key : MlS) (code) (installed : OriginalCode.Installed code) : GlobalEffects.Preserves key code innerStep := by
  rw [inner_shape.2]
  exact GlobalEffects.sequence key code _ _
    (GlobalEffects.call_body key code (some none) (ofString "sha256_pair") innerArguments _ _ _
      (ShaFixedCost.pair_code code installed) (ShaFixedCost.pair_globals key code installed)) (GlobalEffects.assign key code _ _)

theorem inner_arguments (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : BitVec 64) (index : Nat)
    (buffer : source.locals.lookup (ofString "buf")=some (.val (.word cursor)))
    (j : source.locals.lookup (ofString "j")=some (.val (.word (BitVec.ofNat 64 index)))) :
    evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) innerArguments=
      some (ShaPair.values (cursor+BitVec.ofNat 64 (64*index)) (cursor+BitVec.ofNat 64 (64*index+32)) (cursor+BitVec.ofNat 64 (32*index))) := by
  simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,innerArguments,localVar,buffer,j,
    ShaPair.values,valueIsWord,valueWord,wordOpHOL,wordOp,panOpHOL,BitVec.ofNat_mul,BitVec.ofNat_add,BitVec.add_assoc,Nat.mul_comm]

/-- Real original SHA pair at one reached dense-loop index, with mapped
input chunks derived from this actual buffer and index. -/
theorem inner_call_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor stp accel : BitVec 64) (index half : Nat)
    (workspace : ShaPair.Workspace source stp accel) (inside : index<half) (arena : AllocatedBytes.Arena cursor (64*half))
    (buffer : source.locals.lookup (ofString "buf")=some (.val (.word cursor)))
    (j : source.locals.lookup (ofString "j")=some (.val (.word (BitVec.ofNat 64 index)))) :
    source.clock-(evaluateHOLFiniteState source innerCall).2.clock≤53 := by
  have aArena := AllocatedBytes.Arena.subrange cursor (64*half) (64*index) 32 arena (by omega)
  have bArena := AllocatedBytes.Arena.subrange cursor (64*half) (64*index+32) 32 arena (by omega)
  exact ShaPair.call_cost source _ _ _ stp accel workspace.installed (some none) innerArguments (inner_arguments source cursor index buffer j)
    workspace.state workspace.accelerator workspace.domain aArena bArena workspace.arena workspace.aligned

theorem inner_step_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor stp accel : BitVec 64) (index half : Nat)
    (workspace : ShaPair.Workspace source stp accel) (inside : index<half) (arena : AllocatedBytes.Arena cursor (64*half))
    (buffer : source.locals.lookup (ofString "buf")=some (.val (.word cursor)))
    (j : source.locals.lookup (ofString "j")=some (.val (.word (BitVec.ofNat 64 index)))) :
    source.clock-(evaluateHOLFiniteState source innerStep).2.clock≤53 := by
  rw [inner_shape.2]
  exact ClockCost.sequence_current source innerCall innerIncrement 53 0 (inner_call_cost source cursor stp accel index half workspace inside arena buffer j)
    (ClockCost.assign source.code _ _)

end InitECandidate.Solver.Input.Merkle

#print axioms InitECandidate.Solver.Input.Merkle.inner_shape
#print axioms InitECandidate.Solver.Input.Merkle.inner_advances
#print axioms InitECandidate.Solver.Input.Merkle.inner_other
#print axioms InitECandidate.Solver.Input.Merkle.inner_globals
#print axioms InitECandidate.Solver.Input.Merkle.inner_arguments
#print axioms InitECandidate.Solver.Input.Merkle.inner_call_cost
#print axioms InitECandidate.Solver.Input.Merkle.inner_step_cost
