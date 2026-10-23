import InitECandidate.Solver.Mpt.NibbleKeyProgram
import InitECandidate.Solver.Input.NoFallthrough

namespace InitECandidate.Solver.Mpt.NibbleKey
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def hashArguments : List (ExpHOL 64):=[localVar "key",localVar "klen",.var .global (ofString "mpt_hash_scratch")]
def hashCall : ProgHOL 64:=.call (some (none,none)) (ofString "keccak256") hashArguments
def secureAllocation : ProgHOL 64:=match securedBranch with | .seq _ rest=>rest | _=>.skip
def secureTail : ProgHOL 64:=match secureAllocation with | .decCall _ _ _ _ rest=>rest | _=>.skip
def secureConvertArguments : List (ExpHOL 64):=[.var .global (ofString "mpt_hash_scratch"),.const 32#64,localVar "nb"]
def secureConvert : ProgHOL 64:=.call (some (none,none)) (ofString "key_to_nibbles") secureConvertArguments
def secureResult : ExpHOL 64:=.rstruct [localVar "nb",.const 64#64]

theorem secure_shapes : securedBranch=.seq hashCall secureAllocation ∧
    secureAllocation=.decCall (ofString "nb") .one (ofString "alloc") [.const 64#64] secureTail ∧
    secureTail=.seq secureConvert (.return secureResult) := by
  simp only [securedBranch,securedGuard,body,secureAllocation,secureTail,hashCall,hashArguments,secureConvert,secureConvertArguments,secureResult,
    Guest.guestFn_mpt_nibble_key,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none,localVar] <;> simp

theorem secure_no_fallthrough : Input.NoFallthrough securedBranch := by
  rw [secure_shapes.1]
  apply Input.NoFallthrough.sequence
  rw [secure_shapes.2.1]
  apply Input.NoFallthrough.scoped
  rw [secure_shapes.2.2]
  exact Input.NoFallthrough.sequence _ _ (Input.NoFallthrough.returned secureResult)

/-- The real nonzero secure flag selects the hashing branch. Its actual
return exits the helper, so the unsecured suffix cannot run afterward. -/
theorem secured_run (source : PanSemStateFiniteExact 64 Guest.HostMemory) (m flag : BitVec 64)
    (mCell : source.locals.lookup (ofString "m")=some (.val (.word m)))
    (mapped : source.memaddrs (m+8#64)) (cell : source.memory (m+8#64)=.word flag) (nonzero : flag≠0#64) :
    evaluateHOLFiniteState source body=evaluateHOLFiniteState source securedBranch := by
  have addressRead : eval source securedAddress=some (.val (.word (m+8#64))):=by
    simp [eval,securedAddress,localVar,evalHOLExact,evalListHOLExact,toExact,mCell,valueIsWord,valueWord,wordOpHOL,wordOp]
  have loadRead : eval source (.load .one securedAddress)=some (.val (.word flag)):=by
    rw [Input.load_one_case source securedAddress (m+8#64) flag addressRead cell,if_pos mapped]
  have testRead : eval source securedTest=some (.val (.word 1#64)):=by
    simp only [eval] at loadRead ⊢
    rw [securedTest,evalHOLExact,loadRead]
    simp [evalHOLExact,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,nonzero]
  have guardRun : evaluateHOLFiniteState source (.ite securedTest securedBranch .skip)=evaluateHOLFiniteState source securedBranch:=by
    rw [evaluateHOLFiniteState_ite]
    simp only [eval] at testRead
    rw [testRead]
    simp
  have exits:=secure_no_fallthrough source
  rw [body_shape,evaluateHOLFiniteState_seq_line780,guardRun]
  generalize computed : evaluateHOLFiniteState source securedBranch=output at exits ⊢
  obtain ⟨result,target⟩:=output
  cases result with
  | none=>exact (exits rfl).elim
  | some stopped=>rfl

end InitECandidate.Solver.Mpt.NibbleKey

#print axioms InitECandidate.Solver.Mpt.NibbleKey.secure_shapes
#print axioms InitECandidate.Solver.Mpt.NibbleKey.secure_no_fallthrough
#print axioms InitECandidate.Solver.Mpt.NibbleKey.secured_run
