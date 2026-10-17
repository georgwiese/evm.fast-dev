import InitECandidate.Solver.MutableTable.FindChain32

namespace InitECandidate.Solver.MutableTable.Find
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
attribute [local instance] Classical.propDecidable

/-- The actual while loop and literal absent-cap return, including early
matches. Setup/hash/caller and the table representation remain separate. -/
theorem tail32_execute (snapshot : PanSemStateFiniteExact 64 Guest.HostMemory) (p : Parameters)
    (index : BitVec 64) (length : Nat) (chain : Chain32 snapshot p index length)
    (query : WitnessRadix.ByteKeys.Key) (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (locals : Locals source p index) (keyLength : p.keyLength=32#64)
    (memory : snapshot.memory=source.memory) (domain : snapshot.memaddrs=source.memaddrs) (endian : snapshot.be=source.be)
    (queryView : WitnessRadix.MemoryBytes.ByteView source p.key query) (queryFits : p.key.toNat+32<2^64)
    (little : source.be=false)
    (code : source.code.lookup (ofString "memeq")=some (WitnessRadix.Memeq32.formals,WitnessRadix.Memeq32.body,.one))
    (enough : 6*length≤source.clock) :
    ∃ paid,paid≤6*length ∧
      (evaluateHOLFiniteState source afterIndex).1=some (.returned (.val (.word ((answer chain query).getD p.capacity)))) ∧
      emptyLocalsHOLFinite (evaluateHOLFiniteState source afterIndex).2=
        emptyLocalsHOLFinite {source with clock:=source.clock-paid} := by
  obtain ⟨paid,post,bound,run,frame,cap⟩:=chain32_execute snapshot p index length chain query source locals keyLength memory domain endian
    queryView queryFits little code enough
  have clock:=congrArg (fun s : PanSemStateFiniteExact 64 Guest.HostMemory=>s.clock) frame
  change post.clock=source.clock-paid at clock
  have fixed : fixClockHOLFinite source (answerResult (answer chain query),post)=(answerResult (answer chain query),post):=
    WitnessRadix.StateSteps.fixed_clock source post _ (by omega)
  refine ⟨paid,bound,?_⟩
  rw [afterIndex,evaluateHOLFiniteState_seq,run]
  simp only [fixed]
  cases selected : answer chain query with
  | none=>
    have capValue:=cap selected
    have returnRun : evaluateHOLFiniteState post (.return (localVar "cap"))=
        (some (.returned (.val (.word p.capacity))),emptyLocalsHOLFinite post) := by
      simp [evaluateHOLFiniteState_return,evalHOLExact,toExact,localVar,capValue,shapeOfHOLExact,sizeOfShapeWithContextHOL]
    simp only [selected,answerResult,Option.map_none,Option.getD_none]
    rw [returnRun]
    exact ⟨rfl,by simpa only [emptyLocalsHOLFinite] using frame⟩
  | some found=>
    simp only [selected,answerResult,Option.map_some,Option.getD_some]
    exact ⟨True.intro,frame⟩

end InitECandidate.Solver.MutableTable.Find

#print axioms InitECandidate.Solver.MutableTable.Find.tail32_execute
