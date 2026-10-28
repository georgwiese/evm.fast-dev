import InitECandidate.Solver.CurrentKeccak.Environment
import InitECandidate.Solver.Input.CopyZeroMemoryNormal
import InitECandidate.Solver.Input.FixedLoadShape

namespace InitECandidate.Solver.CurrentKeccak.Hash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString Input WitnessRadix WitnessRadix.QueryBranch

private def outStores : List Nat→ProgHOL 64
  | []=>.skip
  | [offset]=>outStore offset
  | offset::next::rest=>.seq (outStore offset) (outStores (next::rest))

private theorem store_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (out query : BitVec 64) (offset : Nat)
    (cell : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (away : query≠out+BitVec.ofNat 64 offset)
    (run : evaluateHOLFiniteState source (outStore offset)=(none,post)) : post.memory query=source.memory query := by
  have addressRead : eval source (outAddress "out" offset)=some (.val (.word (out+BitVec.ofNat 64 offset))) := by
    by_cases zero : offset=0
    · subst offset
      simp [outAddress,eval,evalHOLExact,toExact,localVar,cell]
    · simp [outAddress,zero,addConst,eval,evalHOLExact,evalListHOLExact,toExact,localVar,cell,valueIsWord,valueWord,wordOpHOL,wordOp]
  obtain ⟨value,memory,read,stored,endpoint⟩:=Input.store_at_normal source post _ _ (out+BitVec.ofNat 64 offset) addressRead run
  have size:=Input.load1_length source (outAddress "stp" offset) value read
  rw [endpoint]
  apply Input.words_away (flattenHOL value) (out+BitVec.ofNat 64 offset) query source.memaddrs source.memory memory stored
  intro index inside equal
  have zero : index=0 := by rw [size] at inside; omega
  subst index
  apply away
  simpa using equal

private theorem stores_memory (offsets : List Nat) (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (out query : BitVec 64)
    (cell : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (away : ∀ offset∈offsets,query≠out+BitVec.ofNat 64 offset)
    (run : evaluateHOLFiniteState source (outStores offsets)=(none,post)) : post.memory query=source.memory query := by
  induction offsets generalizing source post with
  | nil=>
    have endpoint : source=post := by simpa [outStores,evaluateHOLFiniteState_skip] using run
    subst post
    rfl
  | cons offset rest ih=>
    cases rest with
    | nil=>exact store_memory source post out query offset cell (away offset (by simp)) run
    | cons next rest=>
      obtain ⟨middle,front,back⟩:=Input.sequence_none source post _ _ run
      have first:=store_memory source middle out query offset cell (away offset (by simp)) front
      have middleCell : middle.locals.lookup (ofString "out")=some (.val (.word out)) := by
        rw [Input.store_none_frame source middle _ _ front]
        exact cell
      have later:=ih middle post middleCell (by intro entry member; exact away entry (by simp [member])) back
      exact later.trans first

/-- Both actual digest-output branches preserve words outside the32-byte
output. Word-load store widths follow from their real successful reads. -/
theorem output_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (stp pad out query : BitVec 64)
    (environment : Environment source stp pad)
    (stateCell : source.locals.lookup (ofString "stp")=some (.val (.word stp)))
    (outCell : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (outArena : AllocatedBytes.Arena out 32) (away : CopyGeneral.Away out query 32)
    (run : evaluateHOLFiniteState source outProgram=(none,post)) : post.memory query=source.memory query := by
  have test : eval source outAlignment=some (.val (.word (if out &&& 7#64=0#64 then 1#64 else 0#64))) := by
    by_cases aligned : out &&& 7#64=0#64
    all_goals simp [eval,outAlignment,evalHOLExact,evalListHOLExact,toExact,localVar,outCell,valueIsWord,valueWord,wordOpHOL,wordOp,AndOp.and,
      Flapjack.Compiler.Encoders.Asm.wordCmpHOL,aligned]
  simp only [eval] at test
  rw [outProgram,evaluateHOLFiniteState_ite,test] at run
  by_cases aligned : out &&& 7#64=0#64
  · simp only [if_pos aligned,show (1#64 : BitVec 64)≠0#64 from by decide,↓reduceIte] at run
    change evaluateHOLFiniteState source (outStores [0,8,16,24])=(none,post) at run
    apply stores_memory [0,8,16,24] source post out query outCell ?_ run
    intro offset member
    simp at member
    rcases member with rfl|rfl|rfl|rfl <;> exact (away _ (by decide)).1
  · simp only [if_neg aligned,↓reduceIte] at run
    have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) [localVar "out",localVar "stp",.const 32#64]=some (CopyGeneral.values out stp 32) := by
      simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,outCell,stateCell,CopyGeneral.values]
    have stateArena : AllocatedBytes.Arena stp 32 := ⟨environment.stateArena.lower,by have h:=environment.stateArena.upper; omega⟩
    exact MemoryAt.copy_normal source post _ stp out query 32 args environment.installed environment.domain stateArena outArena away run

end InitECandidate.Solver.CurrentKeccak.Hash

#print axioms InitECandidate.Solver.CurrentKeccak.Hash.output_memory
