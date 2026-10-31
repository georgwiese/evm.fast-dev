import InitECandidate.Solver.Mpt.CurrentWitnessDecodeLeaf
import InitECandidate.Solver.Mpt.WitnessDecodeRecursiveCuts
import InitECandidate.Solver.Input.ReturnFactsScopedAny

namespace InitECandidate.Solver.Mpt.WitnessDecode
open Input Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

/-- A decode step either finishes a node (flag zero) or supplies a pending
frame (flag one). The latter is a real normal result with mapped scratch. -/
def BinaryResult (value : ValueHOL 64) : Prop :=
  ∃ flag : BitVec 64,∃ second : ValueHOL 64,
    (flag=0#64 ∨ flag=1#64) ∧ value=.rStruct [.val (.word flag),second]

theorem binary_pair_return (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (flag : BitVec 64) (expression : ExpHOL 64) (binary : flag=0#64 ∨ flag=1#64) :
    ReturnFacts.Returns source (.return (.rstruct [.const flag,expression])) BinaryResult := by
  cases read : eval source expression with
  | none=>
    have failed : eval source (.rstruct [.const flag,expression])=none := by
      simp only [eval] at read
      simp [eval,evalHOLExact,evalListHOLExact,read]
    intro post value normal
    have observed:=(Input.return_normal source post _ value normal).1
    rw [failed] at observed
    cases observed
  | some second=>
    apply ReturnFacts.returned source _ (.rStruct [.val (.word flag),second]) BinaryResult _ ⟨flag,second,binary,rfl⟩
    simp only [eval] at read
    simp [eval,evalHOLExact,evalListHOLExact,read]

private theorem ignored_binary (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (function : MlS) (arguments : List (ExpHOL 64)) :
    ReturnFacts.Returns source (.call (some (none,none)) function arguments) BinaryResult := by
  intro post value normal
  exact (NoReturn.ignored_call function arguments source value (congrArg Prod.fst normal)).elim

private theorem store_then_binary (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (address value : ExpHOL 64) (rest : ProgHOL 64)
    (tail : ∀ middle,ReturnFacts.Returns middle rest BinaryResult) :
    ReturnFacts.Returns source (.seq (.store address value) rest) BinaryResult := by
  apply ReturnFacts.sequence
  · intro post answer normal
    exact (NoReturn.store address value source answer (congrArg Prod.fst normal)).elim
  · intro middle normal
    exact tail middle

private theorem guard_binary (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (test : ExpHOL 64) (error : BitVec 64) (rest : ProgHOL 64)
    (tail : ∀ middle,ReturnFacts.Returns middle rest BinaryResult) :
    ReturnFacts.Returns source (.seq (.ite test (fail error) .skip) rest) BinaryResult := by
  apply ReturnFacts.sequence
  · exact ReturnFacts.conditional source _ _ _ BinaryResult (ignored_binary source _ _) (ReturnFacts.skip source BinaryResult)
  · intro middle normal
    exact tail middle

set_option maxRecDepth 100000 in
/-- All six extension-frame stores precede the real flag-one return. -/
theorem extension_body_binary (source : PanSemStateFiniteExact 64 Guest.HostMemory) :
    ReturnFacts.Returns source extensionBody BinaryResult := by
  rw [extension_shape]
  apply guard_binary
  intro middle
  apply ReturnFacts.scoped_any
  intro ready
  simp only [afterExtension,extensionAllocate,extensionBody,afterCompact,compactCall,afterPath,pairBody,afterArray,afterSlices,slicesCall,
    WitnessStep.afterRlp,WitnessStep.body,WitnessStep.original,callRest,seqRest,seqFirst,decRest,yesBranch,
    Guest.Software.guestFn__decode_step,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none]
  repeat first
    | apply store_then_binary
    | exact binary_pair_return _ 1#64 _ (Or.inr rfl)
    | intro current

/-- Either compact branch has the actual terminal/suspended tag. -/
theorem after_compact_binary (source : PanSemStateFiniteExact 64 Guest.HostMemory) :
    ReturnFacts.Returns source afterCompact BinaryResult := by
  rw [after_compact_shape]
  apply ReturnFacts.sequence
  · apply ReturnFacts.conditional
    · intro post value normal
      obtain ⟨second,same⟩:=leaf_body_zero source post value normal
      exact ⟨0#64,second,Or.inl rfl,same⟩
    · exact ReturnFacts.skip source BinaryResult
  · intro middle normal
    exact extension_body_binary middle

theorem compact_call_binary (source : PanSemStateFiniteExact 64 Guest.HostMemory) :
    ReturnFacts.Returns source compactCall BinaryResult := by
  rw [compact_shape]
  exact ReturnFacts.scoped_any source _ _ _ _ _ BinaryResult after_compact_binary

theorem after_path_binary (source : PanSemStateFiniteExact 64 Guest.HostMemory) :
    ReturnFacts.Returns source afterPath BinaryResult := by
  rw [after_path_shape]
  exact guard_binary source _ 5#64 _ compact_call_binary

theorem current_pair_binary (source : PanSemStateFiniteExact 64 Guest.HostMemory) :
    ReturnFacts.Returns source pairBody BinaryResult := by
  rw [path_shape]
  exact ReturnFacts.scoped_any source _ _ _ _ _ BinaryResult after_path_binary

set_option maxRecDepth 100000 in
/-- All seven actual branch-record stores precede the flag-one return. -/
theorem branch_record_binary (source : PanSemStateFiniteExact 64 Guest.HostMemory) :
    ReturnFacts.Returns source branchRecord BinaryResult := by
  rw [branch_record_call_shape]
  apply ReturnFacts.scoped_any
  intro ready
  simp only [afterBranchRecord,branchRecord,branchAllocate,branchBody,afterArray,afterSlices,slicesCall,
    WitnessStep.afterRlp,WitnessStep.body,WitnessStep.original,callRest,seqRest,seqFirst,decRest,yesBranch,
    Guest.Software.guestFn__decode_step,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none]
  repeat first
    | apply store_then_binary
    | exact binary_pair_return _ 1#64 _ (Or.inr rfl)
    | intro current

theorem branch_allocate_binary (source : PanSemStateFiniteExact 64 Guest.HostMemory) :
    ReturnFacts.Returns source branchAllocate BinaryResult := by
  rw [branch_allocate_shape]
  exact ReturnFacts.scoped_any source _ _ _ _ _ BinaryResult branch_record_binary

theorem branch_body_binary (source : PanSemStateFiniteExact 64 Guest.HostMemory) :
    ReturnFacts.Returns source branchBody BinaryResult := by
  rw [branch_body_shape]
  exact guard_binary source _ 4#64 _ branch_allocate_binary

end InitECandidate.Solver.Mpt.WitnessDecode

#print axioms InitECandidate.Solver.Mpt.WitnessDecode.binary_pair_return
#print axioms InitECandidate.Solver.Mpt.WitnessDecode.extension_body_binary
#print axioms InitECandidate.Solver.Mpt.WitnessDecode.after_compact_binary
#print axioms InitECandidate.Solver.Mpt.WitnessDecode.current_pair_binary
#print axioms InitECandidate.Solver.Mpt.WitnessDecode.branch_record_binary
#print axioms InitECandidate.Solver.Mpt.WitnessDecode.branch_body_binary
