import InitECandidate.Solver.Mpt.WitnessDecodeRootEnvironment
import InitECandidate.Solver.Mpt.NewProgram
import InitECandidate.Solver.Input.WordTripleEnvironment

namespace InitECandidate.Solver.Mpt.FromWitness
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def body : ProgHOL 64:=match Guest.guestFn_mpt_from_witness with | .function fn=>progToHOL fn.body | _=>.skip
def formals : List (MlS×ShapeHOL):=[(ofString "db",.one),(ofString "root_hash",.one),(ofString "secured",.one)]
def values (db root flag : BitVec 64) : List (ValueHOL 64):=[.val (.word db),.val (.word root),.val (.word flag)]
def decodeArguments : List (ExpHOL 64):=[localVar "db",localVar "root_hash"]
def newArguments : List (ExpHOL 64):=[localVar "root",localVar "secured"]
def tail : ProgHOL 64:=.call none (ofString "mpt_new") newArguments

theorem body_shape : body=.decCall (ofString "root") .one (ofString "decode_witness_to_mpt") decodeArguments tail := by
  simp only [body,tail,Guest.guestFn_mpt_from_witness,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,
    decodeArguments,newArguments,localVar]

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "mpt_from_witness")=some (formals,body,.one) := by
  have checked:=Input.OriginalCode.indexed code installed 245 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_mpt_from_witness) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,formals,body,Guest.guestFn_mpt_from_witness,
    shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

theorem environment (codeFn : MlS→Option (List (MlS×ShapeHOL)×ProgHOL 64×ShapeHOL)) (db root flag : BitVec 64)
    (known : codeFn (ofString "mpt_from_witness")=some (formals,body,.one)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),
      lookupCodeHOLFinite codeFn (ofString "mpt_from_witness") (values db root flag)=some (body,callee,.one) ∧
      callee.lookup (ofString "db")=some (.val (.word db)) ∧ callee.lookup (ofString "root_hash")=some (.val (.word root)) ∧
      callee.lookup (ofString "secured")=some (.val (.word flag)) :=
  Input.word_triple_environment codeFn (ofString "mpt_from_witness") (ofString "db") (ofString "root_hash") (ofString "secured") body .one
    db root flag (by decide) (by decide) (by decide) known

theorem decode_arguments (source : PanSemStateFiniteExact 64 Guest.HostMemory) (db root : BitVec 64)
    (dbCell : source.locals.lookup (ofString "db")=some (.val (.word db)))
    (rootCell : source.locals.lookup (ofString "root_hash")=some (.val (.word root))) :
    evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) decodeArguments=some (WitnessDecodeRoot.values db root) := by
  simp [decodeArguments,WitnessDecodeRoot.values,localVar,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,dbCell,rootCell]

end InitECandidate.Solver.Mpt.FromWitness

#print axioms InitECandidate.Solver.Mpt.FromWitness.body_shape
#print axioms InitECandidate.Solver.Mpt.FromWitness.original_code
#print axioms InitECandidate.Solver.Mpt.FromWitness.environment
#print axioms InitECandidate.Solver.Mpt.FromWitness.decode_arguments
