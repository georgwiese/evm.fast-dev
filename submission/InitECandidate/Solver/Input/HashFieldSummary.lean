import InitECandidate.Solver.Input.FixedHashSteps
import InitECandidate.Solver.Input.BytesVectorMemory
import InitECandidate.Solver.Input.U64HashMemory

namespace InitECandidate.Solver.Input.FixedHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Present physical limits for an original field operation, allowing the
actual temporary extent needed by larger payload fields. -/
def Step.Fits (step : Step) (inputLength fields temporaryLength : Nat) : Prop :=
  step.inputOffset+step.length≤inputLength ∧ step.field<fields ∧
  match step with
  | .vector _ length _ depth=>length≤134217728 ∧ depth<64 ∧ PackBytes.chunks length≤2^depth ∧ 832+96*PackBytes.chunks length≤temporaryLength
  | _=>True

/-- One actual original field hash/copy: cost uses its real static vector
length, and normal calls restore the current temporary heap. -/
theorem Step.current_summary (step : Step) (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (inputName : String) (p ch cursor stp accel chunk zeros : BitVec 64)
    (inputLength fields temporaryLength : Nat) (valid : step.Fits inputLength fields temporaryLength) (workspace : SszHash.Workspace source stp accel chunk zeros)
    (pointer : source.locals.lookup (ofString inputName)=some (.val (.word p)))
    (chunks : source.locals.lookup (ofString "ch")=some (.val (.word ch)))
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor)))
    (inputArena : AllocatedBytes.Arena p inputLength) (fieldArena : AllocatedBytes.Arena ch (32*fields)) (fieldAligned : ch.toNat%8=0)
    (arena : AllocatedBytes.Arena cursor temporaryLength) (aligned : cursor.toNat%8=0)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source (step.program inputName)=(result,post)) (notTimeout : result≠some .timeOut) :
    source.clock-post.clock≤step.price ∧ (result=none → post.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor))) := by
  have inputSlice := AllocatedBytes.Arena.subrange p inputLength step.inputOffset step.length inputArena valid.1
  have outputSlice := AllocatedBytes.Arena.subrange ch (32*fields) (32*step.field) 32 fieldArena (by have h:=valid.2.1; omega)
  have outputNumber : (ch+BitVec.ofNat 64 (32*step.field)).toNat=ch.toNat+32*step.field := byteAddress_toNat ch (32*step.field) (by have h:=fieldArena.upper; have f:=valid.2.1; omega)
  have outputAligned : (ch+BitVec.ofNat 64 (32*step.field)).toNat%8=0 := by rw [outputNumber]; omega
  have args := step.arguments_read source inputName p ch pointer chunks
  cases step with
  | scalar offset field=>
    have price := U64Hash.call_cost source (p+BitVec.ofNat 64 offset) (ch+BitVec.ofNat 64 (32*field)) workspace.sha.installed workspace.sha.domain inputSlice outputSlice outputAligned (some none) _ args
    change source.clock-(evaluateHOLFiniteState source (.call (some (none,none)) (ofString "htr_u64_at") _)).2.clock≤5 at price
    change evaluateHOLFiniteState source (.call (some (none,none)) (ofString "htr_u64_at") _)=(result,post) at run
    rw [run] at price
    change source.clock-post.clock≤_ at price
    refine ⟨price,?_⟩
    intro normal
    have frame := GlobalEffects.call_body (ofString "heap_ptr") source.code (some none) (ofString "htr_u64_at") ((Step.scalar offset field).arguments inputName) U64Hash.formals U64Hash.body .one
      (U64Hash.original_code source.code workspace.sha.installed) (U64Hash.globals (ofString "heap_ptr") source.code workspace.sha.installed) source rfl
    change GlobalEffects.erase (ofString "heap_ptr") (evaluateHOLFiniteState source (.call (some (none,none)) (ofString "htr_u64_at") _)).2=_ at frame
    rw [run] at frame
    exact (congrArg Prod.snd frame).trans heap
  | copy offset field=>
    have price := CopyGeneral.call_cost_arena source _ (p+BitVec.ofNat 64 offset) (ch+BitVec.ofNat 64 (32*field)) 32 args
      (CopyGeneral.original_code source.code workspace.sha.installed) workspace.sha.domain inputSlice outputSlice
    have blocks := CopyGeneral.cost_word_multiple (p+BitVec.ofNat 64 offset) (ch+BitVec.ofNat 64 (32*field)) 32 (by decide)
    change evaluateHOLFiniteState source (.call (some (none,none)) (ofString "memcpy") _)=(result,post) at run
    rw [run] at price
    change source.clock-post.clock≤_ at price
    refine ⟨by change source.clock-post.clock≤5; omega,?_⟩
    intro normal
    have frame := GlobalEffects.call_body (ofString "heap_ptr") source.code (some none) (ofString "memcpy") ((Step.copy offset field).arguments inputName) CopyGeneral.formals Copy32.body .one
      (CopyGeneral.original_code source.code workspace.sha.installed) (Copy32.globals (ofString "heap_ptr") source.code) source rfl
    change GlobalEffects.erase (ofString "heap_ptr") (evaluateHOLFiniteState source (.call (some (none,none)) (ofString "memcpy") _)).2=_ at frame
    rw [run] at frame
    exact (congrArg Prod.snd frame).trans heap
  | vector offset length field depth=>
    have constraints := valid.2.2
    have temporary := AllocatedBytes.Arena.weaken cursor temporaryLength (832+96*PackBytes.chunks length) arena constraints.2.2.2
    have price := BytesVector.call_cost source post (p+BitVec.ofNat 64 offset) cursor (ch+BitVec.ofNat 64 (32*field)) stp accel chunk zeros length depth constraints.1 constraints.2.1 constraints.2.2.1 workspace heap inputSlice temporary aligned outputSlice outputAligned (some none) _ args result run notTimeout
    refine ⟨price,?_⟩
    intro normal
    subst result
    exact BytesVector.ignored_return_heap source post (p+BitVec.ofNat 64 offset) cursor (ch+BitVec.ofNat 64 (32*field)) stp accel chunk zeros length depth constraints.1 constraints.2.1 constraints.2.2.1 workspace heap temporary aligned outputSlice _ args run


end InitECandidate.Solver.Input.FixedHash

#print axioms InitECandidate.Solver.Input.FixedHash.Step.current_summary
