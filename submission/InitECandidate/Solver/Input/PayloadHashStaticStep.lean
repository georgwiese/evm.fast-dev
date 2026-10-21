import InitECandidate.Solver.Input.PayloadHashStaticProgram
import InitECandidate.Solver.Input.FixedHashPipeline

namespace InitECandidate.Solver.Input.PayloadHash.StaticFields
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

structure Geometry (raw ch cursor : BitVec 64) : Prop where
  inputArena : AllocatedBytes.Arena raw 540
  chunksArena : AllocatedBytes.Arena ch 608
  chunksAligned : ch.toNat%8=0
  chunksBefore : ch.toNat+608≤cursor.toNat
  temporaryArena : AllocatedBytes.Arena cursor 1600
  aligned : cursor.toNat%8=0

/-- Only actual original caller bindings and agreement with actual decoded
input memory are retained between static field calls. -/
structure State (origin current : PanSemStateFiniteExact 64 Guest.HostMemory) (lower upper : Nat)
    (pl raw ch out cursor mark stp accel chunk zeros : BitVec 64) : Prop where
  ready : FixedHash.Ready current "raw" raw ch out cursor mark stp accel chunk zeros
  payload : current.locals.lookup (ofString "pl")=some (.val (.word pl))
  input : HashInput.Frame origin current lower upper

private theorem offset_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String) (offset : Nat) (p : BitVec 64)
    (pointer : source.locals.lookup (ofString name)=some (.val (.word p))) :
    evalHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) (FixedHash.offsetExpression name offset)=some (.val (.word (p+BitVec.ofNat 64 offset))) := by
  by_cases zero : offset=0
  · subst offset; simp [FixedHash.offsetExpression,localVar,evalHOLFinite,evalHOLExact,toExact,pointer]
  · simp [FixedHash.offsetExpression,zero,localVar,evalHOLFinite,evalHOLExact,evalListHOLExact,toExact,pointer,valueIsWord,valueWord,wordOpHOL,wordOp]

theorem arguments_read (field : Field) (source : PanSemStateFiniteExact 64 Guest.HostMemory) (raw ch : BitVec 64)
    (pointer : source.locals.lookup (ofString "raw")=some (.val (.word raw)))
    (chunks : source.locals.lookup (ofString "ch")=some (.val (.word ch))) :
    evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) (arguments field)=some (field.values raw ch) := by
  have inputRead : evalHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) (inputExpression field)=some (.val (.word (raw+BitVec.ofNat 64 field.inputOffset))) := by
    simp [evalHOLFinite,evalHOLExact,evalListHOLExact,toExact,inputExpression,localVar,pointer,valueIsWord,valueWord,wordOpHOL,wordOp]
  have outputRead := offset_read source "ch" (32*field.field) ch chunks
  simp only [evalHOLFinite] at inputRead outputRead
  cases field <;> simp only [arguments,FixedHash.Step.values,FixedHash.Step.inputOffset,FixedHash.Step.field] at inputRead outputRead ⊢
  all_goals simp only [outputExpression,evalListHOLFinite,evalListHOLExact,inputRead,outputRead,U64Hash.values,CopyGeneral.values,BytesVector.values,evalHOLExact]

theorem argument_equivalence (field : Field) (source : PanSemStateFiniteExact 64 Guest.HostMemory) (raw ch : BitVec 64)
    (pointer : source.locals.lookup (ofString "raw")=some (.val (.word raw)))
    (chunks : source.locals.lookup (ofString "ch")=some (.val (.word ch))) :
    evaluateHOLFiniteState source (step field)=evaluateHOLFiniteState source (field.program "raw") :=
  CallArguments.equivalent source (some (none,none)) field.function (arguments field) (field.arguments "raw")
    ((arguments_read field source raw ch pointer chunks).trans (field.arguments_read source "raw" raw ch pointer chunks).symm)

/-- Current original field summary applies to the literal payload argument
expressions, including raw+0, with exact unchanged full call semantics. -/
theorem step_summary (field : Field) (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (raw ch out cursor mark stp accel chunk zeros : BitVec 64) (fits : field.Fits 540 19 1600)
    (ready : FixedHash.Ready source "raw" raw ch out cursor mark stp accel chunk zeros) (geometry : Geometry raw ch cursor)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source (step field)=(result,post)) (notTimeout : result≠some .timeOut) :
    source.clock-post.clock≤field.price ∧ (result=none → post.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor))) := by
  have canonical := (argument_equivalence field source raw ch ready.pointer ready.chunks).symm.trans run
  exact field.current_summary source post "raw" raw ch cursor stp accel chunk zeros 540 19 1600 fits ready.workspace ready.pointer ready.chunks ready.heap
    geometry.inputArena geometry.chunksArena geometry.chunksAligned geometry.temporaryArena geometry.aligned result canonical notTimeout

theorem step_memory (field : Field) (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (raw ch out cursor mark stp accel chunk zeros query : BitVec 64) (fits : field.Fits 540 19 1600)
    (ready : FixedHash.Ready source "raw" raw ch out cursor mark stp accel chunk zeros) (geometry : Geometry raw ch cursor)
    (protection : SszHash.Protected source stp accel chunk zeros query) (below : query.toNat<ch.toNat)
    (run : evaluateHOLFiniteState source (step field)=(none,post)) : post.memory query=source.memory query := by
  have canonical := (argument_equivalence field source raw ch ready.pointer ready.chunks).symm.trans run
  exact field.current_memory source post "raw" raw ch cursor stp accel chunk zeros query 540 19 1600 fits protection ready.pointer ready.chunks ready.heap
    geometry.inputArena geometry.chunksArena geometry.chunksAligned geometry.temporaryArena geometry.aligned
    (by have h:=geometry.chunksBefore; omega) (CopyGeneral.Away.after ch query 608 geometry.chunksAligned (by have h:=geometry.chunksArena.upper; omega) below) canonical

/-- Derive the next real caller bindings/heap/workspace and preserved input
agreement from this same observed normal original field call. -/
theorem step_normal (field : Field) (origin source post : PanSemStateFiniteExact 64 Guest.HostMemory) (lower upper : Nat)
    (pl raw ch out cursor mark stp accel chunk zeros : BitVec 64) (fits : field.Fits 540 19 1600)
    (actual : State origin source lower upper pl raw ch out cursor mark stp accel chunk zeros) (geometry : Geometry raw ch cursor)
    (separation : HashInput.Separation stp accel chunk lower) (small : lower<2^64) (before : upper≤ch.toNat)
    (run : evaluateHOLFiniteState source (step field)=(none,post)) : State origin post lower upper pl raw ch out cursor mark stp accel chunk zeros := by
  have heap := (step_summary field source post raw ch out cursor mark stp accel chunk zeros fits actual.ready geometry none run (by simp)).2 rfl
  have workspace := SszHash.Workspace.after source post stp accel chunk zeros actual.ready.workspace (step field) none run
    (fun key different=>step_globals field key source.code actual.ready.workspace.sha.installed different)
  have other (name : String) : post.locals.lookup (ofString name)=source.locals.lookup (ofString name) := CallNormal.ignored_lookup source post (ofString name) field.function (arguments field) run
  have ready : FixedHash.Ready post "raw" raw ch out cursor mark stp accel chunk zeros :=
    ⟨workspace,(other "raw").trans actual.ready.pointer,(other "ch").trans actual.ready.chunks,(other "out").trans actual.ready.output,(other "mark").trans actual.ready.saved,heap⟩
  have input : HashInput.Frame origin post lower upper := by
    constructor
    intro query low high
    have protection := separation.at_word source stp accel chunk zeros query lower actual.ready.workspace small low
    have memory := step_memory field source post raw ch out cursor mark stp accel chunk zeros query fits actual.ready geometry protection (by omega) run
    exact memory.trans (actual.input.words query low high)
  exact ⟨ready,(other "pl").trans actual.payload,input⟩

end InitECandidate.Solver.Input.PayloadHash.StaticFields

#print axioms InitECandidate.Solver.Input.PayloadHash.StaticFields.arguments_read
#print axioms InitECandidate.Solver.Input.PayloadHash.StaticFields.argument_equivalence
#print axioms InitECandidate.Solver.Input.PayloadHash.StaticFields.step_summary
#print axioms InitECandidate.Solver.Input.PayloadHash.StaticFields.step_memory
#print axioms InitECandidate.Solver.Input.PayloadHash.StaticFields.step_normal
