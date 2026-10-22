import InitECandidate.Solver.Mpt.NibbleKeyCall

namespace InitECandidate.Solver.Mpt.SetTrie
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def body : ProgHOL 64:=match Guest.guestFn_mpt_set with | .function fn=>progToHOL fn.body | _=>.skip
def formals : List (MlS×ShapeHOL):=[(ofString "m",.one),(ofString "key",.one),(ofString "klen",.one),(ofString "vptr",.one),(ofString "vlen",.one)]
def keyArguments : List (ExpHOL 64):=[localVar "m",localVar "key",localVar "klen"]
def afterKey : ProgHOL 64:=match body with | .decCall _ _ _ _ rest=>rest | _=>.skip
def actions : List Input.CallPrefix.Action:=[.scoped (ofString "nk") NibbleKey.returnShape (ofString "mpt_nibble_key") keyArguments]

theorem body_shape : body=.decCall (ofString "nk") NibbleKey.returnShape (ofString "mpt_nibble_key") keyArguments afterKey := by
  simp only [body,afterKey,Guest.guestFn_mpt_set,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,
    Option.map_some,Option.map_none,NibbleKey.returnShape,keyArguments,localVar]

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "mpt_set")=some (formals,body,.one) := by
  have checked:=Input.OriginalCode.indexed code installed 256 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_mpt_set) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,formals,body,Guest.guestFn_mpt_set,
    shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

theorem key_arguments (source : PanSemStateFiniteExact 64 Guest.HostMemory) (m key : BitVec 64) (length : Nat)
    (mCell : source.locals.lookup (ofString "m")=some (.val (.word m)))
    (keyCell : source.locals.lookup (ofString "key")=some (.val (.word key)))
    (lengthCell : source.locals.lookup (ofString "klen")=some (.val (.word (BitVec.ofNat 64 length)))) :
    evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) keyArguments=
      some [.val (.word m),.val (.word key),.val (.word (BitVec.ofNat 64 length))]:=by
  simp [keyArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,mCell,keyCell,lengthCell]

theorem key_trace (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source body=(some (.returned value),target)) :
    ∃ current inner,Input.CallPrefix.Execution source actions current ∧ target.clock=inner.clock ∧
      evaluateHOLFiniteState current afterKey=(some (.returned value),inner) := by
  rw [body_shape] at normal
  exact Input.CallPrefix.normal_trace source target actions afterKey value (Input.NoReturn.scoped_call _ _ _ _ _ Input.NoReturn.skip) normal

end InitECandidate.Solver.Mpt.SetTrie

#print axioms InitECandidate.Solver.Mpt.SetTrie.body_shape
#print axioms InitECandidate.Solver.Mpt.SetTrie.original_code
#print axioms InitECandidate.Solver.Mpt.SetTrie.key_arguments
#print axioms InitECandidate.Solver.Mpt.SetTrie.key_trace
