import InitECandidate.Solver.Input.PBytesProgram
import InitECandidate.Solver.Input.NoFallthrough

namespace InitECandidate.Solver.Input.BytesVector
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def body : ProgHOL 64 := match Guest.guestFn_htr_bytes_vector with | .function fn=>progToHOL fn.body | _=>.skip
def formals : List (MlS×ShapeHOL) := [(ofString "p",.one),(ofString "n",.one),(ofString "out",.one)]
def afterGuard : ProgHOL 64 := match body with | .seq _ tail=>tail | _=>.skip
def afterMark : ProgHOL 64 := match afterGuard with | .decCall _ _ _ _ tail=>tail | _=>.skip
def afterPack : ProgHOL 64 := match afterMark with | .decCall _ _ _ _ tail=>tail | _=>.skip

def test : ExpHOL 64 := .cmp .notLower (.const 32#64) (localVar "n")
def zeroArguments : List (ExpHOL 64) := [localVar "out",.const 32#64]
def copyArguments : List (ExpHOL 64) := [localVar "out",localVar "p",localVar "n"]
def shortBody : ProgHOL 64 := .seq (.call (some (none,none)) (ofString "memzero") zeroArguments)
  (.seq (.call (some (none,none)) (ofString "memcpy") copyArguments) (.return (.const 0#64)))
def guard : ProgHOL 64 := .ite test shortBody .skip
def packArguments : List (ExpHOL 64) := [localVar "p",localVar "n"]
def merkleArguments : List (ExpHOL 64) := [.rfield 0 (localVar "pk"),.rfield 1 (localVar "pk"),.rfield 1 (localVar "pk"),localVar "out"]
def afterMerkle : ProgHOL 64 := .seq (.call (some (none,none)) (ofString "heap_release") [localVar "mark"]) (.return (.const 0#64))

set_option maxRecDepth 100000 in
theorem body_shape : body=.seq guard afterGuard ∧
    afterGuard=.decCall (ofString "mark") .one (ofString "heap_mark") [] afterMark ∧
    afterMark=.decCall (ofString "pk") PackBytes.returnShape (ofString "pack_bytes") packArguments afterPack ∧
    afterPack=.seq (.call (some (none,none)) (ofString "merkleize") merkleArguments) afterMerkle := by
  simp only [body,afterGuard,afterMark,afterPack,Guest.guestFn_htr_bytes_vector,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,
    guard,test,shortBody,zeroArguments,copyArguments,packArguments,merkleArguments,afterMerkle,localVar,PackBytes.returnShape]
  exact ⟨True.intro,True.intro,True.intro,True.intro⟩

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : OriginalCode.Installed code) : code.lookup (ofString "htr_bytes_vector")=some (formals,body,.one) := by
  have checked := OriginalCode.indexed code installed 182 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_htr_bytes_vector) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,formals,body,Guest.guestFn_htr_bytes_vector,
    shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

theorem short_stops : NoFallthrough shortBody := NoFallthrough.sequence _ _ (NoFallthrough.sequence _ _ (NoFallthrough.returned _))

theorem test_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (n : Nat) (small : n≤134217728)
    (count : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 n)))) :
    eval source test=some (.val (.word (if n≤32 then 1#64 else 0#64))) := by
  have number : (BitVec.ofNat 64 n).toNat=n := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  simp [eval,evalHOLExact,toExact,test,localVar,count,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,number]

theorem long_entry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (n : Nat) (small : n≤134217728) (long : 32<n)
    (count : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 n)))) :
    evaluateHOLFiniteState source body=evaluateHOLFiniteState source afterGuard := by
  have read := test_read source n small count
  simp only [if_neg (by omega : ¬n≤32),eval] at read
  have passes : evaluateHOLFiniteState source guard=(none,source) := by
    rw [guard,evaluateHOLFiniteState_ite,read]
    exact evaluateHOLFiniteState_skip source
  rw [body_shape.1,StateSteps.next_sequence source source _ _ passes (Nat.le_refl _)]

end InitECandidate.Solver.Input.BytesVector

#print axioms InitECandidate.Solver.Input.BytesVector.body_shape
#print axioms InitECandidate.Solver.Input.BytesVector.original_code
#print axioms InitECandidate.Solver.Input.BytesVector.short_stops
#print axioms InitECandidate.Solver.Input.BytesVector.test_read
#print axioms InitECandidate.Solver.Input.BytesVector.long_entry
