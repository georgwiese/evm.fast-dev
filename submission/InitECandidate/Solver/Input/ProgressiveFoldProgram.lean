import InitECandidate.Solver.Input.ProgressiveProgram
import InitECandidate.Solver.Input.AssignNormal

namespace InitECandidate.Solver.Input.Progressive
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def afterMark : ProgHOL 64 := match body with | .decCall _ _ _ _ tail=>tail | _=>.skip
def afterRoots : ProgHOL 64 := match afterMark with | .decCall _ _ _ _ tail=>tail | _=>.skip
def afterAcc : ProgHOL 64 := match afterRoots with | .decCall _ _ _ _ tail=>tail | _=>.skip
def afterK : ProgHOL 64 := match afterAcc with | .dec _ _ _ tail=>tail | _=>.skip
def afterOff : ProgHOL 64 := match afterK with | .dec _ _ _ tail=>tail | _=>.skip
def loopAndSuffix : ProgHOL 64 := match afterOff with | .dec _ _ _ tail=>tail | _=>.skip
def afterLoop : ProgHOL 64 := match loopAndSuffix with | .seq _ tail=>tail | _=>.skip
def afterZeroAcc : ProgHOL 64 := match afterLoop with | .seq _ tail=>tail | _=>.skip
def afterFold : ProgHOL 64 := match afterZeroAcc with | .seq _ tail=>tail | _=>.skip

def foldLoop : ProgHOL 64 := (BuildProgram.loops body)[1]?.getD .skip
def foldStep : ProgHOL 64 := match foldLoop with | .while _ step=>step | _=>.skip
def foldTest : ExpHOL 64 := .cmp .notEqual (localVar "k") (.const 0#64)
def decrementExpression : ExpHOL 64 := .op .sub [localVar "k",.const 1#64]
def decrement : ProgHOL 64 := .assign .local (ofString "k") decrementExpression

def foldArguments : List (ExpHOL 64) := [.op .add [localVar "roots",.panop .mul [localVar "k",.const 32#64]],localVar "acc",localVar "acc"]
def zeroArguments : List (ExpHOL 64) := [localVar "acc",.const 32#64]
def outputArguments : List (ExpHOL 64) := [localVar "out",localVar "acc",.const 32#64]

set_option maxRecDepth 100000 in
theorem fold_shape : foldLoop=.while foldTest foldStep ∧
    foldStep=.seq decrement (.call (some (none,none)) (ofString "sha256_pair") foldArguments) ∧
    loopAndSuffix=.seq loop afterLoop ∧
    afterLoop=.seq (.call (some (none,none)) (ofString "memzero") zeroArguments) afterZeroAcc ∧
    afterZeroAcc=.seq foldLoop afterFold ∧
    afterFold=.seq (.call (some (none,none)) (ofString "memcpy") outputArguments)
      (.seq (.call (some (none,none)) (ofString "heap_release") [localVar "mark"]) (.return (.const 0#64))) := by
  simp only [foldLoop,foldStep,afterMark,afterRoots,afterAcc,afterK,afterOff,loopAndSuffix,afterLoop,afterZeroAcc,afterFold,
    loop,BuildProgram.loops,body,Guest.guestFn_merkleize_progressive,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,
    List.append_nil,List.nil_append,List.cons_append,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Option.map_none,
    foldTest,decrement,decrementExpression,foldArguments,zeroArguments,outputArguments,localVar]
  exact ⟨True.intro,True.intro,True.intro,True.intro,True.intro,True.intro⟩

theorem fold_other (key : MlS) (different : key≠ofString "k") : LocalPrefix key foldStep := by
  rw [fold_shape.2.1]
  exact .seq (.assign _ _ different) (.call none _ _ (by intro name impossible; cases impossible))

theorem fold_globals (key : MlS) (code) (installed : OriginalCode.Installed code) : GlobalEffects.Preserves key code foldStep := by
  rw [fold_shape.2.1]
  exact GlobalEffects.sequence key code _ _ (GlobalEffects.assign key code _ _)
    (GlobalEffects.call_body key code (some none) (ofString "sha256_pair") foldArguments ShaFixedCost.pairFormals ShaFixedCost.pairBody .one
      (ShaFixedCost.pair_code code installed) (ShaFixedCost.pair_globals key code installed))

theorem decrement_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (k : Nat) (positive : 0<k) (small : k<2^64)
    (round : source.locals.lookup (ofString "k")=some (.val (.word (BitVec.ofNat 64 k)))) :
    eval source decrementExpression=some (.val (.word (BitVec.ofNat 64 (k-1)))) := by
  have difference := BitVec.ofNat_sub_ofNat_of_le (w:=64) k 1 (by decide) (by omega)
  simp [eval,decrementExpression,localVar,evalHOLExact,evalListHOLExact,toExact,round,valueIsWord,valueWord,wordOpHOL,wordOp,difference]

/-- The original decrement happens before the real SHA pair call. Every
actual continuing step retains that actual decremented caller binding. -/
theorem fold_advances (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (k : Nat) (positive : 0<k) (small : k<2^64)
    (round : source.locals.lookup (ofString "k")=some (.val (.word (BitVec.ofNat 64 k))))
    (run : evaluateHOLFiniteState source foldStep=(none,post)) :
    post.locals.lookup (ofString "k")=some (.val (.word (BitVec.ofNat 64 (k-1)))) := by
  rw [fold_shape.2.1] at run
  obtain ⟨middle,first,called⟩ := sequence_none source post decrement _ run
  have middleEq := assign_none source middle "k" decrementExpression (BitVec.ofNat 64 (k-1)) (decrement_read source k positive small round) first
  have safe : LocalPrefix (ofString "k") (.call (some (none,none)) (ofString "sha256_pair") foldArguments) := .call none _ _ (by intro name impossible; cases impossible)
  have summary := safe.summary_full middle
  unfold LocalSummary at summary
  rw [called] at summary
  have preserved := summary.1 rfl
  rw [preserved,middleEq]
  exact bind_lookup_same _ _ _

end InitECandidate.Solver.Input.Progressive

#print axioms InitECandidate.Solver.Input.Progressive.fold_shape
#print axioms InitECandidate.Solver.Input.Progressive.fold_other
#print axioms InitECandidate.Solver.Input.Progressive.fold_globals
#print axioms InitECandidate.Solver.Input.Progressive.decrement_read
#print axioms InitECandidate.Solver.Input.Progressive.fold_advances
