import InitECandidate.Solver.Input.ByteStoreLocal

namespace InitECandidate.Solver.Input
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open WitnessRadix.QueryBranch

/-- A genuine normal ordinary byte store changes only its real aligned
word. Its value read and destination mapping are derived from execution. -/
theorem byte_store_normal_frame {F : Type} (source target : PanSemStateFiniteExact 64 F)
    (destination expression : ExpHOL 64) (address : BitVec 64)
    (readAddress : eval source destination=some (.val (.word address)))
    (normal : evaluateHOLFiniteState source (.storeByte destination expression)=(none,target)) :
    target={source with memory:=target.memory} ∧
      ∀ query : BitVec 64,query≠panByteAlignHOL (width:=64) address→target.memory query=source.memory query := by
  classical
  simp only [eval] at readAddress
  rw [evaluateHOLFiniteState_storeByte,readAddress] at normal
  generalize readValue : @evalHOLExact 64 F _ source.toExact (fun query=>Classical.propDecidable (source.memaddrs query)) expression=value at normal
  cases value with
  | none=>cases normal
  | some value=>
    cases value with
    | rStruct fields=>cases normal
    | nStruct name fields=>cases normal
    | val payload=>
      cases payload with
      | word value=>
        cases cell : source.memory (panByteAlignHOL (width:=64) address) with
        | word old=>
          by_cases mapped : source.memaddrs (panByteAlignHOL (width:=64) address)
          · simp only [panMemStoreByteWord8HOL,cell,if_pos mapped] at normal
            have targetEq:=(congrArg Prod.snd normal).symm
            let updated : BitVec 64→HolWordLab 64:=fun query=>
              if query=panByteAlignHOL (width:=64) address then (HolWordLab.word (panSetByteHOL address (BitVec.ofNat 64 (BitVec.ofNat 8 value.toNat).toNat) old source.be)) else source.memory query
            change target={source with memory:=updated} at targetEq
            refine ⟨?_,?_⟩
            · rw [targetEq]
            · intro query away
              rw [targetEq]
              exact if_neg away
          · simp only [panMemStoreByteWord8HOL,cell,if_neg mapped] at normal
            cases normal

end InitECandidate.Solver.Input

#print axioms InitECandidate.Solver.Input.byte_store_normal_frame
