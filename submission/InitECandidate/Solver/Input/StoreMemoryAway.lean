import InitECandidate.Solver.Input.WordStoreNormal
import InitECandidate.Solver.WitnessRadix.ByteStore

namespace InitECandidate.Solver.Input.MemoryAt
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open WitnessRadix WitnessRadix.QueryBranch

theorem word_store_normal {F : Type} (source post : PanSemStateFiniteExact 64 F) (address value : ExpHOL 64) (pointer word query : BitVec 64)
    (addressRead : eval source address=some (.val (.word pointer)))
    (valueRead : eval source value=some (.val (.word word))) (away : query≠pointer)
    (run : evaluateHOLFiniteState source (.store address value)=(none,post)) : post.memory query=source.memory query := by
  have frame := Input.word_store_normal source post address value pointer word addressRead valueRead run
  rw [frame.2]
  exact if_neg away

/-- Ordinary byte stores only touch the byte's backing word, even if
expression evaluation/mapping fails. No stored byte value is assumed. -/
theorem byte_store_current {F : Type} (source : PanSemStateFiniteExact 64 F) (address value : ExpHOL 64) (pointer query : BitVec 64)
    (addressRead : eval source address=some (.val (.word pointer))) (away : query≠panByteAlignHOL (width:=64) pointer) :
    (evaluateHOLFiniteState source (.storeByte address value)).2.memory query=source.memory query := by
  classical
  simp only [eval] at addressRead
  rw [evaluateHOLFiniteState_storeByte,addressRead]
  generalize valueRead : evalHOLExact source.toExact value=observed
  cases observed with
  | none=>rfl
  | some observed=>
    cases observed with
    | rStruct values=>rfl
    | nStruct name values=>rfl
    | val word=>
      cases word with
      | word word=>
        dsimp only
        cases stored : source.memory (panByteAlignHOL (width:=64) pointer) with
        | word old=>
          by_cases mapped : source.memaddrs (panByteAlignHOL (width:=64) pointer)
          · simp [panMemStoreByteWord8HOL,stored,mapped,away]
          · simp [panMemStoreByteWord8HOL,stored,mapped]

end InitECandidate.Solver.Input.MemoryAt

#print axioms InitECandidate.Solver.Input.MemoryAt.word_store_normal
#print axioms InitECandidate.Solver.Input.MemoryAt.byte_store_current
