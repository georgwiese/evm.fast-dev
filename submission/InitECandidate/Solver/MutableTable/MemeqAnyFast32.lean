import InitECandidate.Solver.MutableTable.MemeqAnyBlockLoop

namespace InitECandidate.Solver.WitnessRadix.CompareChain
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- Every literal comparison chain returns or fails, including unreadable
operands; it cannot fall through into a later algorithmic branch. -/
theorem chain_ne_none (checks : List Comparison) (source : PanSemStateFiniteExact 64 Guest.HostMemory) :
    (evaluateHOLFiniteState source (chain checks)).1≠none := by
  induction checks generalizing source with
  | nil => rw [chain,return_word]; simp
  | cons check rest ih =>
    rw [chain,evaluateHOLFiniteState_seq_line780]
    generalize computed : evaluateHOLFiniteState source (.ite (.cmp .notEqual check.left check.right) (returned 0#64) .skip)=output
    obtain ⟨answer,middle⟩ := output
    cases answer with
    | none => exact ih middle
    | some answer => simp

end InitECandidate.Solver.WitnessRadix.CompareChain

namespace InitECandidate.Solver.MutableTable.MemeqAny
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def alignedFront : ProgHOL 64 := .seq (.ite (Memeq32.sizeTest 20#64) Memeq32.parts.twenty .skip)
  (.seq (.ite (Memeq32.sizeTest 32#64) Memeq32.parts.thirtyTwo .skip) Memeq32.parts.otherAligned)
def phase : ProgHOL 64 := .ite Memeq32.alignmentTest alignedFront .skip

theorem fast_ne_none (source : PanSemStateFiniteExact 64 Guest.HostMemory) :
    (evaluateHOLFiniteState source Memeq32.parts.thirtyTwo).1≠none := by
  rw [Memeq32.thirtyTwo_shape (fun _=>0#64) (fun _=>0#64)]
  exact CompareChain.chain_ne_none _ source

/-- At actual n=32 the aligned branch executes only the original unrolled
comparison, including all failed reads. The generic loops are unreachable. -/
theorem aligned_front (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (nCell : source.locals.lookup (ofString "n")=some (.val (.word 32#64))) :
    evaluateHOLFiniteState source alignedFront=evaluateHOLFiniteState source Memeq32.parts.thirtyTwo := by
  have test20 : eval source (Memeq32.sizeTest 20#64)=some (.val (.word 0#64)) := by
    simp [eval,Memeq32.sizeTest,localVar,evalHOLExact,toExact,nCell,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  have test32 : eval source (Memeq32.sizeTest 32#64)=some (.val (.word 1#64)) := by
    simp [eval,Memeq32.sizeTest,localVar,evalHOLExact,toExact,nCell,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  simp only [eval] at test20 test32
  have skip20 : evaluateHOLFiniteState source (.ite (Memeq32.sizeTest 20#64) Memeq32.parts.twenty .skip)=(none,source) := by
    rw [evaluateHOLFiniteState_ite,test20]
    simp [evaluateHOLFiniteState_skip]
  have take32 : evaluateHOLFiniteState source (.ite (Memeq32.sizeTest 32#64) Memeq32.parts.thirtyTwo .skip)=
      evaluateHOLFiniteState source Memeq32.parts.thirtyTwo := by
    rw [evaluateHOLFiniteState_ite,test32]
    rfl
  rw [alignedFront,evaluateHOLFiniteState_seq_line780,skip20]
  change evaluateHOLFiniteState source (.seq (.ite (Memeq32.sizeTest 32#64) Memeq32.parts.thirtyTwo .skip) Memeq32.parts.otherAligned)=_
  rw [evaluateHOLFiniteState_seq_line780,take32]
  have terminal:=fast_ne_none source
  generalize computed : evaluateHOLFiniteState source Memeq32.parts.thirtyTwo=output at terminal ⊢
  obtain ⟨answer,target⟩ := output
  cases answer with
  | none => exact (terminal rfl).elim
  | some answer => rfl

/-- The alignment phase spends no source ticks. Its only genuine normal
fallthrough is the original skip at the unchanged state. -/
theorem phase_summary (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (nCell : source.locals.lookup (ofString "n")=some (.val (.word 32#64))) :
    source.clock-(evaluateHOLFiniteState source phase).2.clock≤0 ∧
    (∀ post,evaluateHOLFiniteState source phase=(none,post) → post=source) := by
  have fastPrice:=decisions.2.1.quiet source.code source rfl
  have terminal:=fast_ne_none source
  rw [phase,evaluateHOLFiniteState_ite]
  generalize observed : @evalHOLExact 64 Guest.HostMemory _ source.toExact
    (fun address=>Classical.propDecidable (source.memaddrs address)) Memeq32.alignmentTest=value
  cases value with
  | none => exact ⟨by simp,by intro post impossible; cases impossible⟩
  | some value =>
    cases value with
    | rStruct fields => exact ⟨by simp,by intro post impossible; cases impossible⟩
    | nStruct name fields => exact ⟨by simp,by intro post impossible; cases impossible⟩
    | val payload =>
      cases payload with
      | word word =>
        simp only
        by_cases zero : word=0
        · rw [if_pos zero,evaluateHOLFiniteState_skip]
          exact ⟨by change source.clock-source.clock≤0; omega,by intro post normal; exact (congrArg Prod.snd normal).symm⟩
        · rw [if_neg zero,aligned_front source nCell]
          exact ⟨by rw [fastPrice]; omega,by intro post impossible; exact (terminal (congrArg Prod.fst impossible)).elim⟩

/-- Every actual original32-byte comparison costs at most four body ticks,
without mapping, alignment, byte values or successful-read premises. -/
theorem tight_body_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (nCell : source.locals.lookup (ofString "n")=some (.val (.word 32#64))) :
    source.clock-(evaluateHOLFiniteState source Memeq32.body).2.clock≤4 := by
  let entered:=QueryBranch.bind source "i" 0#64
  have enteredN : entered.locals.lookup (ofString "n")=some (.val (.word 32#64)) :=
    (bind_lookup_other source "i" "n" 0#64 (by decide)).trans nCell
  have front:=phase_summary entered enteredN
  have price:=Input.ClockCost.sequence_reached_current entered phase Memeq32.parts.tailCode 0 4 front.1 (by
    intro middle normal
    have same:=front.2 middle normal
    subst middle
    exact tail_cost entered (bind_lookup_same source "i" 0#64) enteredN)
  rw [Memeq32.body_shape]
  exact Input.ClockCost.declared_current source "i" (.const 0#64) 0#64 _ 4 rfl price

end InitECandidate.Solver.MutableTable.MemeqAny

#print axioms InitECandidate.Solver.WitnessRadix.CompareChain.chain_ne_none
#print axioms InitECandidate.Solver.MutableTable.MemeqAny.fast_ne_none
#print axioms InitECandidate.Solver.MutableTable.MemeqAny.aligned_front
#print axioms InitECandidate.Solver.MutableTable.MemeqAny.phase_summary
#print axioms InitECandidate.Solver.MutableTable.MemeqAny.tight_body_cost
