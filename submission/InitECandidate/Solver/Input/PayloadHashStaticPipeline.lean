import InitECandidate.Solver.Input.PayloadHashStaticStep
import InitECandidate.Solver.Input.ClockCostTerminatingSequence

namespace InitECandidate.Solver.Input.PayloadHash.StaticFields
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Literal original static fields compose with a reached continuation
using actual preserved input and caller bindings. Failed prefixes are kept. -/
theorem program_cost (fields : List Field) (tail : ProgHOL 64) (tailPrice : Nat)
    (origin : PanSemStateFiniteExact 64 Guest.HostMemory) (lower upper : Nat)
    (pl raw ch out cursor mark stp accel chunk zeros : BitVec 64)
    (fits : ∀ field∈fields,field.Fits 540 19 1600) (geometry : Geometry raw ch cursor)
    (separation : HashInput.Separation stp accel chunk lower) (small : lower<2^64) (before : upper≤ch.toNat)
    (tailCost : ∀ source post : PanSemStateFiniteExact 64 Guest.HostMemory,State origin source lower upper pl raw ch out cursor mark stp accel chunk zeros → ∀ result,
      evaluateHOLFiniteState source tail=(result,post) → result≠some .timeOut → source.clock-post.clock≤tailPrice)
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (actual : State origin source lower upper pl raw ch out cursor mark stp accel chunk zeros)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source (program fields tail)=(result,post)) (notTimeout : result≠some .timeOut) :
    source.clock-post.clock≤(fields.map FixedHash.Step.price).sum+tailPrice := by
  induction fields generalizing source post result with
  | nil=>simpa using tailCost source post actual result run notTimeout
  | cons field rest ih=>
    change evaluateHOLFiniteState source (.seq (step field) (program rest tail))=(result,post) at run
    have currentFit := fits field (by simp)
    have price := ClockCost.sequence_terminating source post _ _ field.price ((rest.map FixedHash.Step.price).sum+tailPrice)
      (by intro observed target evaluated notTimeout
          exact (step_summary field source target raw ch out cursor mark stp accel chunk zeros currentFit actual.ready geometry observed evaluated notTimeout).1)
      (by intro middle normal observed target evaluated notTimeout
          have next := step_normal field origin source middle lower upper pl raw ch out cursor mark stp accel chunk zeros currentFit actual geometry separation small before normal
          exact ih (by intro field member; exact fits field (by simp [member])) middle target next observed evaluated notTimeout)
      result run notTimeout
    simpa only [List.map_cons,List.sum_cons,Nat.add_assoc] using price

/-- Actual static pipeline normal returns retain the protected input region;
each reached tail receives metadata from that same original execution. -/
theorem program_frame (fields : List Field) (tail : ProgHOL 64)
    (origin : PanSemStateFiniteExact 64 Guest.HostMemory) (lower upper : Nat)
    (pl raw ch out cursor mark stp accel chunk zeros : BitVec 64)
    (fits : ∀ field∈fields,field.Fits 540 19 1600) (geometry : Geometry raw ch cursor)
    (separation : HashInput.Separation stp accel chunk lower) (small : lower<2^64) (before : upper≤ch.toNat)
    (tailFrame : ∀ source post : PanSemStateFiniteExact 64 Guest.HostMemory,State origin source lower upper pl raw ch out cursor mark stp accel chunk zeros → ∀ value,
      evaluateHOLFiniteState source tail=(some (.returned value),post) → HashInput.Frame origin post lower upper)
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (actual : State origin source lower upper pl raw ch out cursor mark stp accel chunk zeros)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source (program fields tail)=(some (.returned value),post)) : HashInput.Frame origin post lower upper := by
  induction fields generalizing source post with
  | nil=>exact tailFrame source post actual value run
  | cons field rest ih=>
    change evaluateHOLFiniteState source (.seq (step field) (program rest tail))=(some (.returned value),post) at run
    obtain ⟨middle,normal,remaining⟩ := sequence_returned source post _ _ value ((step_local field (ofString "raw")).summary_full source).2.1 run
    have next := step_normal field origin source middle lower upper pl raw ch out cursor mark stp accel chunk zeros (fits field (by simp)) actual geometry separation small before normal
    exact ih (by intro field member; exact fits field (by simp [member])) middle post next remaining

theorem program_return_heap (fields : List Field) (tail : ProgHOL 64)
    (origin : PanSemStateFiniteExact 64 Guest.HostMemory) (lower upper : Nat)
    (pl raw ch out cursor mark stp accel chunk zeros : BitVec 64)
    (fits : ∀ field∈fields,field.Fits 540 19 1600) (geometry : Geometry raw ch cursor)
    (separation : HashInput.Separation stp accel chunk lower) (small : lower<2^64) (before : upper≤ch.toNat)
    (tailHeap : ∀ source post : PanSemStateFiniteExact 64 Guest.HostMemory,State origin source lower upper pl raw ch out cursor mark stp accel chunk zeros → ∀ value,
      evaluateHOLFiniteState source tail=(some (.returned value),post) → post.globals.lookup (ofString "heap_ptr")=some (.val (.word mark)))
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (actual : State origin source lower upper pl raw ch out cursor mark stp accel chunk zeros)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source (program fields tail)=(some (.returned value),post)) : post.globals.lookup (ofString "heap_ptr")=some (.val (.word mark)) := by
  induction fields generalizing source post with
  | nil=>exact tailHeap source post actual value run
  | cons field rest ih=>
    change evaluateHOLFiniteState source (.seq (step field) (program rest tail))=(some (.returned value),post) at run
    obtain ⟨middle,normal,remaining⟩ := sequence_returned source post _ _ value ((step_local field (ofString "raw")).summary_full source).2.1 run
    have next := step_normal field origin source middle lower upper pl raw ch out cursor mark stp accel chunk zeros (fits field (by simp)) actual geometry separation small before normal
    exact ih (by intro field member; exact fits field (by simp [member])) middle post next remaining

theorem program_globals (fields : List Field) (tail : ProgHOL 64) (key : MlS) (code) (installed : OriginalCode.Installed code)
    (different : key≠ofString "heap_ptr") (tailPure : GlobalEffects.Preserves key code tail) : GlobalEffects.Preserves key code (program fields tail) := by
  induction fields with
  | nil=>exact tailPure
  | cons field rest ih=>exact GlobalEffects.sequence key code _ _ (step_globals field key code installed different) ih

end InitECandidate.Solver.Input.PayloadHash.StaticFields

#print axioms InitECandidate.Solver.Input.PayloadHash.StaticFields.program_cost
#print axioms InitECandidate.Solver.Input.PayloadHash.StaticFields.program_frame
#print axioms InitECandidate.Solver.Input.PayloadHash.StaticFields.program_return_heap
#print axioms InitECandidate.Solver.Input.PayloadHash.StaticFields.program_globals
