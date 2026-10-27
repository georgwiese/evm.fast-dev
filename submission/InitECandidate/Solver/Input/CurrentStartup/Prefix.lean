import InitECandidate.Solver.Input.CurrentStartup.Effects
import InitECandidate.Solver.Input.MainMemoryPrefix

namespace InitECandidate.Solver.Input.CurrentStartup
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def routines : List Code.Routine := [.sha256_init, .keccak_init, .ssz_init, .mpt_init,
  .u256_ws_init, .secp256k1_init, .bn254_init, .bls_precompiles_init,
  .ripemd160_init, .blake2_init, .header_init, .evm_init, .fork_init]

def withTail (functions : List Code.Routine) (tail : ProgHOL 64) : ProgHOL 64 :=
  functions.foldr (fun routine rest => .seq (.call (some (none, none)) (Code.name routine) []) rest) tail

def seqTail : Nat → ProgHOL 64 → ProgHOL 64
  | 0, program => program
  | count + 1, .seq _ rest => seqTail count rest
  | _ + 1, _ => .skip

def afterStartup : ProgHOL 64 := seqTail 13 Main.afterMemory

theorem source_shape : Main.afterMemory = withTail routines afterStartup := by
  simp only [afterStartup, Main.afterMemory, Main.body, Guest.Software.guestFn_main,
    withTail, routines, seqTail, Code.name, progToHOL, expToHOL, shapeToHOL,
    List.foldr_cons, List.foldr_nil, List.map_cons, List.map_nil, Option.map_some, Option.map_none]

/-- Cut the genuine sequence at the end of its actual initializer calls.
Stopped prefixes retain their result/state; only a real fallthrough resumes
the supplied suffix. This is an exact evaluation identity at every clock. -/
theorem append_execution {F : Type} (functions : List Code.Routine)
    (source : PanSemStateFiniteExact 64 F) (tail : ProgHOL 64) :
    evaluateHOLFiniteState source (withTail functions tail) =
      (let output := evaluateHOLFiniteState source (withTail functions .skip)
       match output.1 with
       | none => evaluateHOLFiniteState output.2 tail
       | some _ => output) := by
  induction functions generalizing source with
  | nil => simp [withTail, evaluateHOLFiniteState_skip]
  | cons routine rest ih =>
    simp only [withTail, List.foldr_cons, evaluateHOLFiniteState_seq_line780]
    generalize front : evaluateHOLFiniteState source (.call (some (none, none)) (Code.name routine) []) = output
    obtain ⟨result, middle⟩ := output
    cases result with
    | none => exact ih middle
    | some result => rfl

theorem prefix_preserves (cursor : Cursor) (code) (installed : OriginalCode.Installed code)
    (functions : List Code.Routine) : GlobalEffects.Preserves (key cursor) code (withTail functions .skip) := by
  induction functions with
  | nil => exact GlobalEffects.skip (key cursor) code
  | cons routine rest ih =>
    exact GlobalEffects.sequence (key cursor) code _ _
      (Effects.call_preserves cursor code installed routine (some none) []) ih

/-- The two real startup cursors, actual code and actual source memory domain.
This predicate is established by main's declaration and mem_init execution. -/
structure ArenaState (state : PanSemStateFiniteExact 64 Guest.HostMemory) : Prop where
  scratch : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word 2701127680#64))
  frame : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word 2688618496#64))
  domain : state.memaddrs = InitE.ordinaryDomain
  code : OriginalCode.Installed state.code

theorem prefix_state (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (result : Option (PanSemResultExact 64)) (initial : ArenaState source)
    (actual : evaluateHOLFiniteState source (withTail routines .skip) = (result, target)) : ArenaState target := by
  have scratch := prefix_preserves .scratch source.code initial.code routines source rfl
  have frame := prefix_preserves .frame source.code initial.code routines source rfl
  rw [actual] at scratch frame
  have fields := evaluation_fields source target _ result actual
  refine ⟨?_, ?_, fields.1.trans initial.domain, ?_⟩
  · exact (congrArg Prod.snd scratch).trans initial.scratch
  · exact (congrArg Prod.snd frame).trans initial.frame
  · rw [fields.2.2.2]
    exact initial.code

/-- Classify a real remaining main execution. Either all13initializers
actually fall through, or main stopped inside that exact prefix. Both cases
retain the declaration-derived arena values; no future completion is assumed. -/
theorem split_execution (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (result : Option (PanSemResultExact 64)) (initial : ArenaState source)
    (actual : evaluateHOLFiniteState source Main.afterMemory = (result, target)) :
    (∃ middle, evaluateHOLFiniteState source (withTail routines .skip) = (none, middle) ∧
      ArenaState middle ∧ evaluateHOLFiniteState middle afterStartup = (result, target)) ∨
    (∃ stopped, evaluateHOLFiniteState source (withTail routines .skip) = (some stopped, target) ∧
      result = some stopped ∧ ArenaState target) := by
  rw [source_shape, append_execution] at actual
  generalize computed : evaluateHOLFiniteState source (withTail routines .skip) = output at actual
  obtain ⟨tag, middle⟩ := output
  have invariant := prefix_state source middle tag initial computed
  cases tag with
  | none => exact Or.inl ⟨middle, rfl, invariant, actual⟩
  | some stopped =>
    have same : middle = target := congrArg Prod.snd actual
    have tagEq : result = some stopped := (congrArg Prod.fst actual).symm
    exact Or.inr ⟨stopped, by simpa only [same] using computed, tagEq, by simpa only [same] using invariant⟩

/-- Every actual terminating source input reaches this real startup cut or
stops in it, with the exact original observation retained. No list-size,
validity or successful-initializer premise is added. -/
theorem reached (input : Guest.InputBlob) (outcome : HolOutcome) (events : List HolIoEvent)
    (terminates : InitE.sourceBehaviour input = .terminate outcome events) :
    ∃ origin target result actualOutcome,
      Main.Entry input origin ∧
      ((∃ middle, evaluateHOLFiniteState (Main.memoryState origin) (withTail routines .skip) = (none, middle) ∧
          ArenaState middle ∧ evaluateHOLFiniteState middle afterStartup = (result, target)) ∨
        (∃ stopped, evaluateHOLFiniteState (Main.memoryState origin) (withTail routines .skip) = (some stopped, target) ∧
          result = some stopped ∧ ArenaState target)) ∧
      (match result with
       | some (.finalFfi event) => actualOutcome = HolOutcome.ffiOutcome event
       | some (.returned _) => actualOutcome = HolOutcome.success
       | _ => False) ∧
      HolBehaviour.terminate outcome events = .terminate actualOutcome target.ffi.ioEvents := by
  obtain ⟨origin, target, result, actualOutcome, entry, positive, heap, scratch, frame, actual, classified, observation⟩ :=
    Main.reached_memory input outcome events terminates
  have initial : ArenaState (Main.memoryState origin) := ⟨scratch, frame, entry.domain, entry.code⟩
  exact ⟨origin, target, result, actualOutcome, entry,
    split_execution _ _ result initial actual, classified, observation⟩

end InitECandidate.Solver.Input.CurrentStartup

#print axioms InitECandidate.Solver.Input.CurrentStartup.source_shape
#print axioms InitECandidate.Solver.Input.CurrentStartup.append_execution
#print axioms InitECandidate.Solver.Input.CurrentStartup.prefix_preserves
#print axioms InitECandidate.Solver.Input.CurrentStartup.prefix_state
#print axioms InitECandidate.Solver.Input.CurrentStartup.split_execution
#print axioms InitECandidate.Solver.Input.CurrentStartup.reached
