import InitECandidate.Solver.Input.CurrentHash.MerklePairLoops
import InitECandidate.Solver.Input.CurrentHash.Sha256Memory
import InitECandidate.Solver.Input.MemoryBoundedLoop
import InitECandidate.Solver.Input.MemoryContinue
import InitECandidate.Solver.Input.CopyAwaySubrange

set_option maxRecDepth 100000

namespace InitECandidate.Solver.Input.CurrentHash.MerklePairMemory
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch
open MerklePairLoops

def argument (phase : Phase) (i : Nat) : ExpHOL 64 := (arguments phase)[i]?.getD (.const 0#64)
def outputPointer (phase : Phase) (buffer : BitVec 64) (i : Nat) : BitVec 64 :=
  match phase with | .dense => buffer+BitVec.ofNat 64 (32*i) | .extension => buffer

theorem arguments_three (phase : Phase) : arguments phase = [argument phase 0,argument phase 1,argument phase 2] := by
  cases phase <;>
    simp only [argument,arguments,step,loop,index,BuildProgram.loops,Code.body,Code.entry,Code.declaration,
      GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,Guest.Software.guestFn_merkleize,
      progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,List.append_nil,List.nil_append,List.cons_append,
      List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Option.map_none,localVar]

theorem output_shape (phase : Phase) : argument phase 2 = match phase with
    | .dense => .op .add [localVar "buf",.panop .mul [localVar "j",.const 32#64]]
    | .extension => localVar "buf" := by
  cases phase <;>
    simp only [argument,arguments,step,loop,index,BuildProgram.loops,Code.body,Code.entry,Code.declaration,
      GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,Guest.Software.guestFn_merkleize,
      progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,List.append_nil,List.nil_append,List.cons_append,
      List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Option.map_none,localVar]

theorem output_read (phase : Phase) (source : PanSemStateFiniteExact 64 Guest.HostMemory) (buffer : BitVec 64) (i : Nat)
    (pointer : source.locals.lookup (ofString "buf") = some (.val (.word buffer)))
    (position : source.locals.lookup (counter phase) = some (.val (.word (BitVec.ofNat 64 i)))) :
    evalHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) (argument phase 2) =
      some (.val (.word (outputPointer phase buffer i))) := by
  rw [output_shape]
  cases phase <;> simp [counter] at position
  all_goals simp [outputPointer,evalHOLFinite,evalHOLExact,evalListHOLExact,toExact,localVar,pointer,position,
    valueIsWord,valueWord,wordOpHOL,wordOp,panOpHOL,BitVec.ofNat_mul,Nat.mul_comm]

/-- Actual pair-step writes are confined to its actual32-byte output. Both
input expressions and their contents remain unrestricted. -/
theorem step_memory (phase : Phase) (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (buffer query : BitVec 64) (i : Nat)
    (installed : OriginalCode.Installed source.code)
    (pointer : source.locals.lookup (ofString "buf") = some (.val (.word buffer)))
    (position : source.locals.lookup (counter phase) = some (.val (.word (BitVec.ofNat 64 i))))
    (away : CopyGeneral.Away (outputPointer phase buffer i) query 32)
    (actual : evaluateHOLFiniteState source (step phase) = (none,post)) : post.memory query = source.memory query := by
  rw [(source_shape phase).2] at actual
  obtain ⟨middle,normal,remaining⟩ := Input.sequence_none source post _ _ actual
  rw [pairCall,arguments_three phase] at normal
  have hashed := Sha256Memory.call_output_memory source middle (argument phase 0) (argument phase 1) (argument phase 2)
    (outputPointer phase buffer i) query installed (output_read phase source buffer i pointer position)
    (by intro offset inside; exact (away offset inside).2) normal
  have assigned := MemoryAt.assign_current middle .local (counter phase) (.op .add [.var .local (counter phase),.const 1#64]) query
  change evaluateHOLFiniteState middle (.assign .local (counter phase) (.op .add [.var .local (counter phase),.const 1#64])) = (none,post) at remaining
  rw [remaining] at assigned
  exact assigned.trans hashed

/-- The signed tests use the same real bounded nonnegative counter as their
source-cost proofs. Their arithmetic can be read without any memory premise. -/
theorem test_read (phase : Phase) (source : PanSemStateFiniteExact 64 Guest.HostMemory) (i maximum : Nat)
    (small : maximum<2^63) (inside : i≤maximum)
    (position : source.locals.lookup (counter phase) = some (.val (.word (BitVec.ofNat 64 i))))
    (bound : source.locals.lookup (limit phase) = some (.val (.word (BitVec.ofNat 64 maximum)))) :
    evalHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address))
      (.cmp .less (.var .local (counter phase)) (.var .local (limit phase))) =
      some (.val (.word (if i+1≤maximum then 1#64 else 0#64))) := by
  have iNumber : (BitVec.ofNat 64 i).toNat = i := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have maxNumber : (BitVec.ofNat 64 maximum).toNat = maximum := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have equivalent : (i<maximum) = (i+1≤maximum) := propext (by omega)
  simp [evalHOLFinite,evalHOLExact,toExact,position,bound,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,
    Flapjack.Compiler.Encoders.Asm.holAsmSignedLess,iNumber,maxNumber,
    show i<9223372036854775808 from by omega,show maximum<9223372036854775808 from small,equivalent]

/-- Normal dense/extension loops preserve protected metadata. The actual
counter determines each output slot; no SHA workspace or input mapping is
assumed, and failed paths are not supplied as successful future calls. -/
theorem loop_memory (phase : Phase) (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (buffer query : BitVec 64) (i maximum : Nat)
    (small : maximum<2^63) (inside : i≤maximum) (installed : OriginalCode.Installed source.code)
    (pointer : source.locals.lookup (ofString "buf") = some (.val (.word buffer)))
    (position : source.locals.lookup (counter phase) = some (.val (.word (BitVec.ofNat 64 i))))
    (bound : source.locals.lookup (limit phase) = some (.val (.word (BitVec.ofNat 64 maximum))))
    (away : ∀ j, j<maximum → CopyGeneral.Away (outputPointer phase buffer j) query 32)
    (actual : evaluateHOLFiniteState source (loop phase) = (none,post)) : post.memory query = source.memory query := by
  have notCounter : limit phase ≠ counter phase := by cases phase <;> decide
  have bufOther : ofString "buf" ≠ counter phase := by cases phase <;> decide
  let invariant := fun current : PanSemStateFiniteExact 64 Guest.HostMemory =>
    current.locals.lookup (ofString "buf") = some (.val (.word buffer)) ∧
    current.locals.lookup (limit phase) = some (.val (.word (BitVec.ofNat 64 maximum)))
  rw [(source_shape phase).1] at actual
  have framed := MemoryAt.bounded_counter_loop_normal source.code (counter phase) (limit phase)
    (.cmp .less (.var .local (counter phase)) (.var .local (limit phase))) (step phase) 1 maximum query
    ((other phase (limit phase) notCounter).summary_full) (advances phase) invariant
    (by intro current ready; exact ready)
    (by intro current ready index inside cell; exact test_read phase current index maximum small inside cell ready.2)
    (by intro current codeEq ready index active cell target normal
        have currentCode : OriginalCode.Installed current.code := by rw [codeEq]; exact installed
        have kept (key : MlS) (different : key ≠ counter phase) : target.locals.lookup key = current.locals.lookup key := by
          have summary := (other phase key different).summary_full current
          unfold LocalSummary at summary
          rw [normal] at summary
          exact summary.1 rfl
        exact ⟨⟨(kept _ bufOther).trans ready.1,(kept _ notCounter).trans ready.2⟩,
          step_memory phase current target buffer query index currentCode ready.1 cell (away index (by omega)) normal⟩)
    source post i rfl ⟨pointer,bound⟩ inside position actual
  exact framed.2.2

end InitECandidate.Solver.Input.CurrentHash.MerklePairMemory

#print axioms InitECandidate.Solver.Input.CurrentHash.MerklePairMemory.arguments_three
#print axioms InitECandidate.Solver.Input.CurrentHash.MerklePairMemory.output_shape
#print axioms InitECandidate.Solver.Input.CurrentHash.MerklePairMemory.output_read
#print axioms InitECandidate.Solver.Input.CurrentHash.MerklePairMemory.step_memory
#print axioms InitECandidate.Solver.Input.CurrentHash.MerklePairMemory.test_read
#print axioms InitECandidate.Solver.Input.CurrentHash.MerklePairMemory.loop_memory
