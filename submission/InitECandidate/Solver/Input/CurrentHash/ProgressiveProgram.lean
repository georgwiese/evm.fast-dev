import InitECandidate.Solver.Input.ProgressiveBudget
import InitECandidate.Solver.Input.MerkleEnvironment
import InitECandidate.Solver.Input.LocalPrefix
import InitECandidate.Solver.PanTraversal

namespace InitECandidate.Solver.Input.Progressive
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def body : ProgHOL 64 := match Guest.Software.guestFn_merkleize_progressive with | .function fn=>progToHOL fn.body | _=>.skip
def formals : List (MlS×ShapeHOL) := [(ofString "p",.one),(ofString "n",.one),(ofString "out",.one)]
def loop : ProgHOL 64 := (BuildProgram.loops body)[0]?.getD .skip
def step : ProgHOL 64 := match loop with | .while _ step=>step | _=>.skip
def test : ExpHOL 64 := .cmp .lower (localVar "off") (localVar "n")
def countExpression : ExpHOL 64 := .op .sub [localVar "n",localVar "off"]
def capTest : ExpHOL 64 := .cmp .lower (localVar "size") (localVar "cnt")
def capGuard : ProgHOL 64 := .ite capTest (.assign .local (ofString "cnt") (localVar "size")) .skip

def arguments : List (ExpHOL 64) := [
  .op .add [localVar "p",.panop .mul [localVar "off",.const 32#64]],localVar "cnt",localVar "size",
  .op .add [localVar "roots",.panop .mul [localVar "k",.const 32#64]]]
def updates : ProgHOL 64 := .seq (.assign .local (ofString "off") (.op .add [localVar "off",localVar "size"]))
  (.seq (.assign .local (ofString "size") (.shift .lsl (localVar "size") (.const 2#64)))
    (.assign .local (ofString "k") (.op .add [localVar "k",.const 1#64])))
def afterCap : ProgHOL 64 := .seq (.call (some (none,none)) (ofString "merkleize") arguments) updates

def afterCount : ProgHOL 64 := .seq capGuard afterCap

set_option maxRecDepth 100000 in
theorem loop_shape : loop=.while test step ∧ step=.dec (ofString "cnt") .one countExpression afterCount := by
  simp only [loop,step,BuildProgram.loops,body,Guest.Software.guestFn_merkleize_progressive,progToHOL,expToHOL,shapeToHOL,
    List.map_cons,List.map_nil,List.append_nil,List.nil_append,List.cons_append,List.getElem?_cons_zero,Option.getD_some,
    test,countExpression,afterCount,capGuard,capTest,afterCap,arguments,updates,localVar,Option.map_none]
  exact ⟨True.intro,True.intro⟩

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : OriginalCode.Installed code) : code.lookup (ofString "merkleize_progressive")=some (formals,body,.one) := by
  have checked := CurrentHash.Code.installed code installed .merkleize_progressive
  simpa only [CurrentHash.Code.name, CurrentHash.Code.formals, CurrentHash.Code.body, CurrentHash.Code.shape,
    CurrentHash.Code.entry, CurrentHash.Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,formals,body,Guest.Software.guestFn_merkleize_progressive,
    shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

/-- Only the real count, off, size and round bindings can change during
one original progressive step. The declaration restores its cnt binding. -/
theorem step_other (key : MlS) (notCnt : key≠ofString "cnt") (notOff : key≠ofString "off") (notSize : key≠ofString "size") (notK : key≠ofString "k") :
    LocalPrefix key step := by
  rw [loop_shape.2]
  unfold afterCount capGuard afterCap updates
  exact .dec _ _ _ notCnt (.seq (.ite _ (.assign _ _ notCnt) .skip)
    (.seq (.call none _ _ (by intro name impossible; cases impossible))
      (.seq (.assign _ _ notOff) (.seq (.assign _ _ notSize) (.assign _ _ notK)))))

/-- Actual mapped pair/chunk pointers follow the original four-argument
expression list, rather than a synthetic Merkle invocation. -/
theorem merkle_arguments (source : PanSemStateFiniteExact 64 Guest.HostMemory) (p roots : BitVec 64) (off count size k : Nat)
    (pointer : source.locals.lookup (ofString "p")=some (.val (.word p)))
    (root : source.locals.lookup (ofString "roots")=some (.val (.word roots)))
    (position : source.locals.lookup (ofString "off")=some (.val (.word (BitVec.ofNat 64 off))))
    (countLocal : source.locals.lookup (ofString "cnt")=some (.val (.word (BitVec.ofNat 64 count))))
    (sizeLocal : source.locals.lookup (ofString "size")=some (.val (.word (BitVec.ofNat 64 size))))
    (round : source.locals.lookup (ofString "k")=some (.val (.word (BitVec.ofNat 64 k)))) :
    evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=
      some (Merkle.values (p+BitVec.ofNat 64 (32*off)) (BitVec.ofNat 64 count) (BitVec.ofNat 64 size) (roots+BitVec.ofNat 64 (32*k))) := by
  simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,arguments,localVar,pointer,root,position,countLocal,sizeLocal,round,
    Merkle.values,valueIsWord,valueWord,wordOpHOL,wordOp,panOpHOL,BitVec.ofNat_mul,Nat.mul_comm]

end InitECandidate.Solver.Input.Progressive

#print axioms InitECandidate.Solver.Input.Progressive.loop_shape
#print axioms InitECandidate.Solver.Input.Progressive.original_code
#print axioms InitECandidate.Solver.Input.Progressive.step_other
#print axioms InitECandidate.Solver.Input.Progressive.merkle_arguments
