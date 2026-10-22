import InitECandidate.Solver.Input.HeaderEncoding.Program
import InitECandidate.Solver.Input.CallPrefixNormalTrace

namespace InitECandidate.Solver.Input.HeaderEncoding
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def firstByteFields : List Field:=[.bytes 16 32,.bytes 24 20,.bytes 32 32,.bytes 40 32,.bytes 48 32,.bytes 56 256]
def fieldActions : List Field→List CallPrefix.Action
  | []=>[]
  | field::rest=>.command (call field)::.command advance::fieldActions rest
def beforeWideActions : List CallPrefix.Action:=[
  .scoped (ofString "buf") .one (ofString "alloc") [.const 1024#64],
  .declare (ofString "p") .one (.op .add [localVar "buf",.const 9#64]),
  .scoped (ofString "w") .one (ofString "rlp_encode_bytes") (arguments firstField),
  .command advance]++fieldActions firstByteFields
def fromWide : ProgHOL 64:=fields (baseRest.drop 6) afterBase

theorem body_before_wide : body=CallPrefix.program beforeWideActions fromWide := by
  rw [body_shape]
  simp only [beforeWideActions,firstByteFields,fieldActions,CallPrefix.program,List.cons_append,List.nil_append,
    afterBuffer,afterPointer,afterFirst,fromWide,baseRest,fields]
  rfl

theorem field_never (field : Field) : NoReturn.Never (call field) := by
  intro F source value
  have safe : LocalPrefix (ofString "_") (call field):=
    .call (some (ofString "w")) _ _ (by intro name same; cases same; decide)
  exact (safe.summary source).2 value

private theorem advance_never : NoReturn.Never advance := by
  intro F source value
  have safe : LocalPrefix (ofString "_") advance:=.assign _ _ (by decide)
  exact (safe.summary source).2 value

theorem before_wide_never : NoReturn.Never (CallPrefix.program beforeWideActions .skip) := by
  simp only [beforeWideActions,firstByteFields,fieldActions,CallPrefix.program,List.cons_append,List.nil_append]
  repeat' first
    | apply NoReturn.scoped_call
    | apply NoReturn.declared
    | apply NoReturn.sequence
    | exact field_never _
    | exact advance_never
    | exact NoReturn.skip

theorem before_wide_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source body=(some (.returned value),post)) :
    ∃ current inner,CallPrefix.Execution source beforeWideActions current ∧ post.clock=inner.clock ∧
      evaluateHOLFiniteState current fromWide=(some (.returned value),inner) := by
  rw [body_before_wide] at normal
  exact CallPrefix.normal_trace source post beforeWideActions fromWide value before_wide_never normal

end InitECandidate.Solver.Input.HeaderEncoding

#print axioms InitECandidate.Solver.Input.HeaderEncoding.body_before_wide
#print axioms InitECandidate.Solver.Input.HeaderEncoding.field_never
#print axioms InitECandidate.Solver.Input.HeaderEncoding.before_wide_never
#print axioms InitECandidate.Solver.Input.HeaderEncoding.before_wide_trace
