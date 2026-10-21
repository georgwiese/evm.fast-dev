import InitECandidate.Solver.Mpt.WitnessDecodeRecordNormal
import InitECandidate.Solver.Rlp.SlicesNormal
import InitECandidate.Solver.Input.NoFallthrough
import InitECandidate.Solver.Input.SequenceChoice

namespace InitECandidate.Solver.Mpt.WitnessDecode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

private theorem fields_never (baseName : String) (fields : List LocalFields.Field) (rest : ProgHOL 64)
    (tail : Input.NoFallthrough rest) : Input.NoFallthrough (LocalFields.program baseName fields rest) := by
  induction fields with
  | nil=>exact tail
  | cons field fields ih=>exact Input.NoFallthrough.sequence _ _ ih

theorem RecordKind.never (kind : RecordKind) : Input.NoFallthrough kind.call := by
  rw [kind.call_shape,kind.tail_shape (fun _=>0#64)]
  exact Input.NoFallthrough.scoped _ _ _ _ _ (fields_never _ _ _ (Input.NoFallthrough.returned _))

theorem extension_never : Input.NoFallthrough extensionBody := by
  have callShape:=RecordKind.call_shape .extension
  change extensionAllocate=.decCall (ofString "rec") .one (ofString "scratch_alloc") [.const 88#64] afterExtension at callShape
  rw [extension_shape,←callShape]
  exact Input.NoFallthrough.sequence _ _ (RecordKind.never .extension)

theorem pair_never : Input.NoFallthrough pairBody := by
  rw [path_shape]
  apply Input.NoFallthrough.scoped
  rw [after_path_shape]
  apply Input.NoFallthrough.sequence
  rw [compact_shape]
  apply Input.NoFallthrough.scoped
  rw [after_compact_shape]
  exact Input.NoFallthrough.sequence _ _ extension_never

theorem branch_never : Input.NoFallthrough branchBody := by
  have callShape:=RecordKind.call_shape .branch
  change branchRecord=.decCall (ofString "rec2") .one (ofString "scratch_alloc") [.const 88#64] afterBranchRecord at callShape
  rw [branch_shape,←callShape]
  exact Input.NoFallthrough.sequence _ _ (Input.NoFallthrough.scoped _ _ _ _ _ (RecordKind.never .branch))

theorem after_array_shape : afterArray=.seq (.ite (.cmp .equal (field "sl" 1) (.const 2#64)) pairBody .skip) branchBody := by
  simp only [afterArray,after_slices_shape,decRest]

/-- The actual two-item branch cannot fall through to the branch-node
case, even on failed reads or invalid exception shapes. -/
theorem array_choice (source : PanSemStateFiniteExact 64 Guest.HostMemory) (array count : BitVec 64)
    (sliceCell : source.locals.lookup (ofString "sl")=some (Rlp.Slices.result array count)) :
    evaluateHOLFiniteState source afterArray=
      if count=2#64 then evaluateHOLFiniteState source pairBody else evaluateHOLFiniteState source branchBody := by
  have selected : evaluateHOLFiniteState source (.ite (.cmp .equal (field "sl" 1) (.const 2#64)) pairBody .skip)=
      if count=2#64 then evaluateHOLFiniteState source pairBody else (none,source):=by
    by_cases two : count=2#64
    · simp [evaluateHOLFiniteState_ite,evalHOLExact,field,localVar,toExact,sliceCell,Rlp.Slices.result,two,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    · simp [evaluateHOLFiniteState_ite,evalHOLExact,field,localVar,toExact,sliceCell,Rlp.Slices.result,two,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,evaluateHOLFiniteState_skip]
  rw [after_array_shape]
  exact Input.sequence_choice source _ pairBody branchBody (count=2#64) selected pair_never

end InitECandidate.Solver.Mpt.WitnessDecode

#print axioms InitECandidate.Solver.Mpt.WitnessDecode.RecordKind.never
#print axioms InitECandidate.Solver.Mpt.WitnessDecode.extension_never
#print axioms InitECandidate.Solver.Mpt.WitnessDecode.pair_never
#print axioms InitECandidate.Solver.Mpt.WitnessDecode.branch_never
#print axioms InitECandidate.Solver.Mpt.WitnessDecode.after_array_shape
#print axioms InitECandidate.Solver.Mpt.WitnessDecode.array_choice
