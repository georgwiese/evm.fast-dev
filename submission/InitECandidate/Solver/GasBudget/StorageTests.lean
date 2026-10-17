import InitECandidate.Solver.GasBudget.StorageDebt

namespace InitECandidate.Solver.GasBudget.StorageTests
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def boolWord (flag : Bool) : BitVec 64:=if flag then 1#64 else 0#64
def truth (expression : ExpHOL 64) : ExpHOL 64:=.cmp .notEqual (.const 0#64) expression
def nonzero (name : String) : ExpHOL 64:=.cmp .notEqual (localVar name) (.const 0#64)
def zero (name : String) : ExpHOL 64:=.cmp .equal (localVar name) (.const 0#64)
def triple (a b c : ExpHOL 64) : ExpHOL 64:=.op .and [truth a,truth b,truth c]
def chargeTest : ExpHOL 64:=triple (nonzero "oc") (zero "cn") (nonzero "oz")
def refundTest : ExpHOL 64:=triple (zero "cn") (nonzero "on") (nonzero "oz")
def program (continuation : ProgHOL 64) : ProgHOL 64:=
  .dec (ofString "state_gas") .one (.const 0#64)
    (.seq (.ite chargeTest (.assign .local (ofString "state_gas") (.const 97920#64)) .skip)
      (.seq (.ite refundTest (.call (some (none,none)) (ofString "credit_state_gas_refund") [.const 97920#64]) .skip) continuation))

def findSite : ProgHOL 64→Option (ProgHOL 64)
  | p@(.dec name _ _ rest)=>if name=ofString "state_gas" then some p else findSite rest
  | .seq a b | .ite _ a b=>(findSite a).orElse (fun _=>findSite b)
  | .decCall _ _ _ _ rest | .while _ rest=>findSite rest
  | _=>none
def erase : ProgHOL 64→ProgHOL 64
  | .dec name shape value (.seq a (.seq b _))=>.dec name shape value (.seq a (.seq b .skip))
  | _=>.skip
def selectedSite : ProgHOL 64:=match Guest.guestFn_op_sstore with
  | .function fn=>erase ((findSite (progToHOL fn.body)).getD .skip)
  | _=>.skip

set_option maxRecDepth 10000 in
theorem actual_site : selectedSite=program .skip := by
  simp only [selectedSite,Guest.guestFn_op_sstore,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,
    Option.map_none,findSite,↓reduceIte,Option.orElse_none,Option.orElse_some,Option.getD_some,
    erase,program,chargeTest,refundTest,triple,truth,nonzero,zero,localVar]
  rfl

theorem nonzero_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String) (flag : Bool)
    (stored : source.locals.lookup (ofString name)=some (.val (.word (boolWord flag)))) :
    eval source (nonzero name)=some (.val (.word (boolWord flag))) := by
  cases flag <;> simp [eval,nonzero,evalHOLExact,toExact,localVar,stored,boolWord,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]

theorem zero_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String) (flag : Bool)
    (stored : source.locals.lookup (ofString name)=some (.val (.word (boolWord flag)))) :
    eval source (zero name)=some (.val (.word (boolWord (!flag)))) := by
  cases flag <;> simp [eval,zero,evalHOLExact,toExact,localVar,stored,boolWord,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]

theorem triple_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (a b c : ExpHOL 64) (x y z : Bool)
    (ea : eval source a=some (.val (.word (boolWord x))))
    (eb : eval source b=some (.val (.word (boolWord y))))
    (ec : eval source c=some (.val (.word (boolWord z)))) :
    eval source (triple a b c)=some (.val (.word (boolWord (x && y && z)))) := by
  simp only [eval] at ea eb ec ⊢
  simp only [triple,truth,evalHOLExact,evalListHOLExact,ea,eb,ec]
  cases x <;> cases y <;> cases z <;>
    simp [boolWord,valueIsWord,valueWord,wordOpHOL,wordOp,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  all_goals rfl

theorem charge_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (oc cn oz : Bool)
    (ocLocal : source.locals.lookup (ofString "oc")=some (.val (.word (boolWord oc))))
    (cnLocal : source.locals.lookup (ofString "cn")=some (.val (.word (boolWord cn))))
    (ozLocal : source.locals.lookup (ofString "oz")=some (.val (.word (boolWord oz)))) :
    eval source chargeTest=some (.val (.word (boolWord (oc && !cn && oz)))) :=
  triple_read source _ _ _ _ _ _ (nonzero_read source "oc" oc ocLocal) (zero_read source "cn" cn cnLocal) (nonzero_read source "oz" oz ozLocal)

theorem refund_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cn on oz : Bool)
    (cnLocal : source.locals.lookup (ofString "cn")=some (.val (.word (boolWord cn))))
    (onLocal : source.locals.lookup (ofString "on")=some (.val (.word (boolWord on))))
    (ozLocal : source.locals.lookup (ofString "oz")=some (.val (.word (boolWord oz)))) :
    eval source refundTest=some (.val (.word (boolWord (!cn && on && oz)))) :=
  triple_read source _ _ _ _ _ _ (zero_read source "cn" cn cnLocal) (nonzero_read source "on" on onLocal) (nonzero_read source "oz" oz ozLocal)

end InitECandidate.Solver.GasBudget.StorageTests

#print axioms InitECandidate.Solver.GasBudget.StorageTests.actual_site
#print axioms InitECandidate.Solver.GasBudget.StorageTests.nonzero_read
#print axioms InitECandidate.Solver.GasBudget.StorageTests.zero_read
#print axioms InitECandidate.Solver.GasBudget.StorageTests.triple_read
#print axioms InitECandidate.Solver.GasBudget.StorageTests.charge_read
#print axioms InitECandidate.Solver.GasBudget.StorageTests.refund_read
