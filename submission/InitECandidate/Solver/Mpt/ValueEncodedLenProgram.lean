import InitECandidate.Solver.Input.RlpLength.BytesSizeGeneral
import InitECandidate.Solver.Input.OriginalRlpCodes
import InitECandidate.Solver.Input.WordPairEnvironment
import InitECandidate.Solver.Input.ScalarAssignNormal

namespace InitECandidate.Solver.Mpt.ValueEncodedLen
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def body : ProgHOL 64:=match Guest.Software.guestFn_rlp_value_encoded_len with | .function fn=>progToHOL fn.body | _=>.skip
def formals : List (MlS×ShapeHOL):=[(ofString "p",.one),(ofString "n",.one)]
def arguments : List (ExpHOL 64):=[localVar "fb",localVar "n"]
def guard : ProgHOL 64:=.ite (.cmp .lower (.const 0#64) (localVar "n")) (.assign .local (ofString "fb") (.loadByte (localVar "p"))) .skip
def tail : ProgHOL 64:=.call none (ofString "rlp_bytes_encoded_len") arguments
def afterFirst : ProgHOL 64:=.seq guard tail

theorem body_shape : body=.dec (ofString "fb") .one (.const 0#64) afterFirst := by
  simp only [body,Guest.Software.guestFn_rlp_value_encoded_len,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,
    afterFirst,guard,tail,arguments,localVar]

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "rlp_value_encoded_len")=some (formals,body,.one) := by
  have checked:=Input.OriginalCode.indexed code installed 260 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.Software.guestFn_rlp_value_encoded_len) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,formals,body,Guest.Software.guestFn_rlp_value_encoded_len,
    shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

theorem environment (codeFn : MlS→Option (List (MlS×ShapeHOL)×ProgHOL 64×ShapeHOL)) (pointer length : BitVec 64)
    (known : codeFn (ofString "rlp_value_encoded_len")=some (formals,body,.one)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),lookupCodeHOLFinite codeFn (ofString "rlp_value_encoded_len") [.val (.word pointer),.val (.word length)]=some (body,callee,.one) ∧
      callee.lookup (ofString "p")=some (.val (.word pointer)) ∧ callee.lookup (ofString "n")=some (.val (.word length)) :=
  Input.word_pair_environment codeFn (ofString "rlp_value_encoded_len") (ofString "p") (ofString "n") body .one pointer length (by decide) known

theorem guard_safe : Input.LocalPrefix (ofString "n") guard:=.ite _ (.assign _ _ (by decide)) .skip

theorem guard_readonly (code) : Input.LocalEffects.Preserves code guard:=
  Input.LocalEffects.conditional code _ _ _ (Input.LocalEffects.assign code _ _) (Input.LocalEffects.skip code)

theorem guard_cost (code) : Input.ClockCost.Bound code guard 0:=
  Input.ClockCost.conditional code _ _ _ 0 0 (Input.ClockCost.assign code _ _) (Input.ClockCost.skip code)

/-- Normal continuation derives its actual first-byte word from the real
assignment. Empty values skip the byte read and retain literal zero. No
readable pointer or successful byte load is supplied in advance. -/
theorem guard_normal_exact (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (length : BitVec 64)
    (nCell : source.locals.lookup (ofString "n")=some (.val (.word length)))
    (fbCell : source.locals.lookup (ofString "fb")=some (.val (.word 0#64)))
    (normal : evaluateHOLFiniteState source guard=(none,target)) :
    ∃ first : BitVec 64,target.locals.lookup (ofString "fb")=some (.val (.word first)) ∧
      target.locals.lookup (ofString "n")=some (.val (.word length)) ∧ Input.LocalEffects.erase target=Input.LocalEffects.erase source ∧
      (0<length.toNat→eval source (.loadByte (localVar "p"))=some (.val (.word first))) := by
  have kept:=guard_safe.summary_full source
  unfold Input.LocalSummary at kept
  rw [normal] at kept
  have frame:=guard_readonly source.code source rfl
  rw [normal] at frame
  have selected : evaluateHOLFiniteState source guard=
      if 0<length.toNat then evaluateHOLFiniteState source (.assign .local (ofString "fb") (.loadByte (localVar "p"))) else (none,source):=by
    by_cases positive : 0<length.toNat <;>
      simp [guard,evaluateHOLFiniteState_ite,evaluateHOLFiniteState_skip,evalHOLExact,toExact,localVar,nCell,positive,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def]
  by_cases positive : 0<length.toNat
  · rw [if_pos positive] at selected
    obtain ⟨first,read,postEq⟩:=Input.scalar_assign_none source target "fb" (.loadByte (localVar "p")) 0#64 fbCell (selected.symm.trans normal)
    exact ⟨first,(by rw [postEq]; exact bind_lookup_same _ _ _),(kept.1 rfl).trans nCell,frame,fun _=>read⟩
  · rw [if_neg positive] at selected
    have same : target=source:=congrArg Prod.snd (normal.symm.trans selected)
    exact ⟨0#64,(by rw [same]; exact fbCell),(kept.1 rfl).trans nCell,frame,fun active=>(positive active).elim⟩

theorem guard_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (length : BitVec 64)
    (nCell : source.locals.lookup (ofString "n")=some (.val (.word length)))
    (fbCell : source.locals.lookup (ofString "fb")=some (.val (.word 0#64)))
    (normal : evaluateHOLFiniteState source guard=(none,target)) :
    ∃ first : BitVec 64,target.locals.lookup (ofString "fb")=some (.val (.word first)) ∧
      target.locals.lookup (ofString "n")=some (.val (.word length)) ∧ Input.LocalEffects.erase target=Input.LocalEffects.erase source := by
  obtain ⟨first,fb,nextLen,frame,_read⟩:=guard_normal_exact source target length nCell fbCell normal
  exact ⟨first,fb,nextLen,frame⟩

end InitECandidate.Solver.Mpt.ValueEncodedLen

#print axioms InitECandidate.Solver.Mpt.ValueEncodedLen.body_shape
#print axioms InitECandidate.Solver.Mpt.ValueEncodedLen.original_code
#print axioms InitECandidate.Solver.Mpt.ValueEncodedLen.environment
#print axioms InitECandidate.Solver.Mpt.ValueEncodedLen.guard_safe
#print axioms InitECandidate.Solver.Mpt.ValueEncodedLen.guard_readonly
#print axioms InitECandidate.Solver.Mpt.ValueEncodedLen.guard_cost
#print axioms InitECandidate.Solver.Mpt.ValueEncodedLen.guard_normal

#print axioms InitECandidate.Solver.Mpt.ValueEncodedLen.guard_normal_exact
