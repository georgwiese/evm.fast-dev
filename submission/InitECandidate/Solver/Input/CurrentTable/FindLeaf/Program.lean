import InitECandidate.Solver.Input.OriginalEntry
import InitECandidate.Solver.Input.OriginalCode
import InitECandidate.Solver.PanState
import InitECandidate.Solver.Input.QuietClock
import InitECandidate.Solver.Input.LocalEffectsLoop

namespace InitECandidate.Solver.Input.CurrentTable.FindLeaf
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def body : ProgHOL 64 := match Guest.Software.guestFn_htab_find_leaf with | .function fn=>progToHOL fn.body | _=>.skip
def formals : List (MlS×ShapeHOL) := [(ofString "t",.one),(ofString "key",.one)]
def afterBits : ProgHOL 64 := match body with | .dec _ _ _ rest=>rest | _=>.skip
def afterNodes : ProgHOL 64 := match afterBits with | .dec _ _ _ rest=>rest | _=>.skip
def afterRoot : ProgHOL 64 := match afterNodes with | .dec _ _ _ rest=>rest | _=>.skip
def loop : ProgHOL 64 := match afterRoot with | .seq first _=>first | _=>.skip
def step : ProgHOL 64 := match loop with | .while _ rest=>rest | _=>.skip
def afterBit : ProgHOL 64 := match step with | .dec _ _ _ rest=>rest | _=>.skip
def branch : ProgHOL 64 := match afterBit with | .seq _ rest=>rest | _=>.skip
def keyTest : ExpHOL 64 := match branch with | .ite test _ _=>test | _=>.const 0#64

def test : ExpHOL 64 := .cmp .notEqual (localVar "n") (.const 0#64)
def address (offset : Nat) : ExpHOL 64 := .op .add [localVar "nodes",.panop .mul [localVar "n",.const 32#64],.const (BitVec.ofNat 64 offset)]
def cell (base node : BitVec 64) (offset : Nat) : BitVec 64 := base+node*32#64+BitVec.ofNat 64 offset
def leafGuard : ProgHOL 64 := .ite (.cmp .equal (localVar "b") (localVar "keybits")) .break .skip

set_option maxRecDepth 100000 in
theorem shapes :
    loop=.while test step ∧ step=.dec (ofString "b") .one (.load .one (address 24)) afterBit ∧
    afterBit=.seq leafGuard branch ∧
    branch=.ite keyTest (.assign .local (ofString "n") (.load .one (address 8))) (.assign .local (ofString "n") (.load .one (address 16))) := by
  simp only [body,afterBits,afterNodes,afterRoot,loop,step,afterBit,branch,keyTest,test,address,leafGuard,
    Guest.Software.guestFn_htab_find_leaf,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,localVar]
  trivial

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "htab_find_leaf")=some (formals,body,.one) := by
  have checked:=OriginalCode.indexed code installed 119 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.Software.guestFn_htab_find_leaf) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,formals,body,
    Guest.Software.guestFn_htab_find_leaf,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

theorem step_quiet (code) : QuietClock.Preserves code step := by
  rw [shapes.2.1,shapes.2.2.1,shapes.2.2.2]
  exact QuietClock.declared code _ _ _ _ (QuietClock.sequence code _ _
    (QuietClock.conditional code _ _ _ (QuietClock.stopped code).1 (QuietClock.skip code))
    (QuietClock.conditional code _ _ _ (QuietClock.assign code _ _) (QuietClock.assign code _ _)))

theorem step_readonly (code) : LocalEffects.Preserves code step := by
  rw [shapes.2.1,shapes.2.2.1,shapes.2.2.2]
  exact LocalEffects.declared code _ _ _ _ (LocalEffects.sequence code _ _
    (LocalEffects.conditional code _ _ _ (LocalEffects.stopped code).1 (LocalEffects.skip code))
    (LocalEffects.conditional code _ _ _ (LocalEffects.assign code _ _) (LocalEffects.assign code _ _)))

end InitECandidate.Solver.Input.CurrentTable.FindLeaf

#print axioms InitECandidate.Solver.Input.CurrentTable.FindLeaf.original_code
#print axioms InitECandidate.Solver.Input.CurrentTable.FindLeaf.step_quiet
#print axioms InitECandidate.Solver.Input.CurrentTable.FindLeaf.step_readonly
