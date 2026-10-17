import InitECandidate.Solver.MutableTable.InsertStores
import InitECandidate.Solver.MutableTable.CopyMapped

namespace InitECandidate.Solver.MutableTable.Insert
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix

def generalResultMemory (memory : WordWrites.Memory) (be : Bool) (width : Nat) (p : Find.Parameters)
    (table vals order position index count value : BitVec 64) : WordWrites.Memory :=
  suffixMemory (CopyGeneral.resultMemory memory be p.key (p.keys + index * p.stride) width)
    table vals p.used order position index count value

/-- Complete actual insertion tail from the first empty slot: real general memcpy,
all metadata stores and the scoped return, with exact final memory/clock. -/
theorem general_tail_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (p : Find.Parameters)
    (table vals order position index count value : BitVec 64) (locals : Find.Locals source p index)
    (width : Nat) (smallWidth : width ≤ 64) (keyLength : p.keyLength = BitVec.ofNat 64 width)
    (tLocal : source.locals.lookup (ofString "t")=some (.val (.word table)))
    (valueLocal : source.locals.lookup (ofString "value")=some (.val (.word value)))
    (orderLocal : source.locals.lookup (ofString "order")=some (.val (.word order)))
    (positionLocal : source.locals.lookup (ofString "order_pos")=some (.val (.word position)))
    (valsMapped : source.memaddrs (table+40#64)) (valsCell : source.memory (table+40#64)=.word vals)
    (valueMapped : source.memaddrs (vals+index*8#64))
    (usedMapped : source.memaddrs (panByteAlignHOL (width:=64) (p.used+index)))
    (orderMapped : source.memaddrs (order+count*8#64)) (positionMapped : source.memaddrs (position+index*8#64))
    (countMapped : source.memaddrs (table+24#64)) (countCell : source.memory (table+24#64)=.word count)
    (awayValue : table+24#64≠vals+index*8#64)
    (awayUsed : table+24#64≠panByteAlignHOL (width:=64) (p.used+index))
    (awayValsHeader : CopyGeneral.Away (p.keys + index * p.stride) (table + 40#64) width)
    (awayCountHeader : CopyGeneral.Away (p.keys + index * p.stride) (table + 24#64) width)
    (little : source.be = false)
    (code : source.code.lookup (ofString "memcpy") = some (CopyGeneral.formals, Copy32.body, .one))
    (sourceFits : p.key.toNat + width < 2 ^ 64)
    (destinationFits : (p.keys + index * p.stride).toNat + width < 2 ^ 64)
    (sourceMapped : ∀ offset < width, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress p.key offset)))
    (destinationMapped : ∀ offset < width, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress (p.keys + index * p.stride) offset)))
    (enough : MemeqByteRuntime.price width + 1 ≤ source.clock) :
    ∃ paid target, paid ≤ MemeqByteRuntime.price width + 1 ∧
      evaluateHOLFiniteState source afterLoop = (some (.returned (.val (.word 0#64))), target) ∧
      emptyLocalsHOLFinite target = emptyLocalsHOLFinite
        {source with
          memory := (generalResultMemory source.memory source.be width p table vals order position index count value)
          clock := source.clock - paid} := by
  let dst := p.keys + index * p.stride
  let paid := CopyGeneral.cost p.key dst width + 1
  let copied := CopyGeneral.callState source p.key dst width
  have paidBound : paid ≤ MemeqByteRuntime.price width + 1 := by
    dsimp only [paid]
    exact Nat.add_le_add_right (CopyMapped.cost_le_price p.key dst width) 1
  have args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address))
      [Find.keyAddress, localVar "key", localVar "klen"] = some (CopyGeneral.values dst p.key width) := by
    simp [CopyGeneral.values, evalListHOLFinite, Find.keyAddress, evalListHOLExact, evalHOLExact, toExact,
      localVar, locals.keys, locals.index, locals.stride, locals.key, locals.klen, keyLength,
      valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL, dst]
  have copyRun := CopyGeneral.call_execute source _ p.key dst width args code
    (CopyMapped.of_regions source p.key dst width sourceFits destinationFits sourceMapped destinationMapped)
    (by omega) (Nat.le_trans paidBound enough)
  have valsKept : copied.memory (table + 40#64) = .word vals :=
    (CopyGeneral.call_memory_away source p.key dst (table + 40#64) width awayValsHeader).trans valsCell
  have countKept : copied.memory (table + 24#64) = .word count :=
    (CopyGeneral.call_memory_away source p.key dst (table + 24#64) width awayCountHeader).trans countCell
  obtain ⟨target, tailRun, frame⟩ := after_copy copied table vals p.used order position index count value
    tLocal locals.index valueLocal locals.used orderLocal positionLocal valsMapped valsKept valueMapped usedMapped
    orderMapped positionMapped countMapped countKept awayValue awayUsed little
  refine ⟨paid, target, paidBound, ?_, frame⟩
  change evaluateHOLFiniteState source copyCall = (none, copied) at copyRun
  rw [afterLoop, StateSteps.next_sequence source copied copyCall afterCopy copyRun (Nat.sub_le _ _)]
  exact tailRun

end InitECandidate.Solver.MutableTable.Insert

#print axioms InitECandidate.Solver.MutableTable.Insert.general_tail_execute
