import InitECandidate.Solver.Input.PayloadHashStaticPipeline

namespace InitECandidate.Solver.Input.PayloadHash.StaticFields
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- A reached normal original phase can retain the input/caller relation
while restoring a different actual heap scope. Counter i is allowed to advance. -/
theorem State.after_program (origin source post : PanSemStateFiniteExact 64 Guest.HostMemory) (lower upper : Nat)
    (pl raw ch out cursor nextCursor mark stp accel chunk zeros : BitVec 64)
    (actual : State origin source lower upper pl raw ch out cursor mark stp accel chunk zeros)
    (program : ProgHOL 64) (run : evaluateHOLFiniteState source program=(none,post))
    (heap : post.globals.lookup (ofString "heap_ptr")=some (.val (.word nextCursor)))
    (globals : ∀ key,key≠ofString "heap_ptr" → GlobalEffects.Preserves key source.code program)
    (locals : ∀ name : String,ofString name≠ofString "i" → post.locals.lookup (ofString name)=source.locals.lookup (ofString name))
    (memory : ∀ query : BitVec 64,lower≤query.toNat → query.toNat<upper → post.memory query=source.memory query) :
    State origin post lower upper pl raw ch out nextCursor mark stp accel chunk zeros := by
  have workspace := SszHash.Workspace.after source post stp accel chunk zeros actual.ready.workspace program none run globals
  exact ⟨⟨workspace,(locals "raw" (by decide)).trans actual.ready.pointer,(locals "ch" (by decide)).trans actual.ready.chunks,
    (locals "out" (by decide)).trans actual.ready.output,(locals "mark" (by decide)).trans actual.ready.saved,heap⟩,
    (locals "pl" (by decide)).trans actual.payload,⟨by intro query low high; exact (memory query low high).trans (actual.input.words query low high)⟩⟩

/-- Actual normal original ignored helper calls reinstall the caller's
bindings. The caller composes only heap/memory/global facts derived from
that same observed helper execution. -/
theorem State.after_call (origin source post : PanSemStateFiniteExact 64 Guest.HostMemory) (lower upper : Nat)
    (pl raw ch out cursor mark stp accel chunk zeros : BitVec 64)
    (actual : State origin source lower upper pl raw ch out cursor mark stp accel chunk zeros)
    (function : MlS) (arguments : List (ExpHOL 64))
    (run : evaluateHOLFiniteState source (.call (some (none,none)) function arguments)=(none,post))
    (heap : post.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor)))
    (globals : ∀ key,key≠ofString "heap_ptr" → GlobalEffects.Preserves key source.code (.call (some (none,none)) function arguments))
    (memory : ∀ query : BitVec 64,lower≤query.toNat → query.toNat<upper → post.memory query=source.memory query) :
    State origin post lower upper pl raw ch out cursor mark stp accel chunk zeros := by
  have workspace := SszHash.Workspace.after source post stp accel chunk zeros actual.ready.workspace _ none run globals
  have other (name : String) : post.locals.lookup (ofString name)=source.locals.lookup (ofString name) := CallNormal.ignored_lookup source post (ofString name) function arguments run
  exact ⟨⟨workspace,(other "raw").trans actual.ready.pointer,(other "ch").trans actual.ready.chunks,(other "out").trans actual.ready.output,(other "mark").trans actual.ready.saved,heap⟩,
    (other "pl").trans actual.payload,⟨by intro query low high; exact (memory query low high).trans (actual.input.words query low high)⟩⟩

end InitECandidate.Solver.Input.PayloadHash.StaticFields

#print axioms InitECandidate.Solver.Input.PayloadHash.StaticFields.State.after_call

#print axioms InitECandidate.Solver.Input.PayloadHash.StaticFields.State.after_program
