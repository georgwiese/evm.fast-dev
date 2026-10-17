import InitECandidate.Solver.MutableTable.InsertCopy32

namespace InitECandidate.Solver.MutableTable.Insert
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix

def resultMemory (memory : WordWrites.Memory) (p : Find.Parameters) (table vals order position index count value : BitVec 64)
    (words : Fin 4→BitVec 64) : WordWrites.Memory:=
  suffixMemory (Copy32.memory memory (p.keys+index*p.stride) words) table vals p.used order position index count value

/-- Complete actual insertion tail from the first empty slot: real memcpy,
all metadata stores and the scoped return, with exact final memory/clock. -/
theorem tail32_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (p : Find.Parameters)
    (table vals order position index count value : BitVec 64) (locals : Find.Locals source p index)
    (keyLength : p.keyLength=32#64) (words : Fin 4→BitVec 64)
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
    (awayValsHeader : table+40#64∉(Copy32.writes (p.keys+index*p.stride) words).map Prod.fst)
    (awayCountHeader : table+24#64∉(Copy32.writes (p.keys+index*p.stride) words).map Prod.fst)
    (little : source.be=false)
    (code : source.code.lookup (ofString "memcpy")=some (Copy32.formals,Copy32.body,.one))
    (mask : ((p.keys+index*p.stride) ||| p.key) &&& 7#64=0#64)
    (view : MemoryBytes.WordView source p.key words)
    (mapped : ∀ limb : Fin 4,source.memaddrs (p.keys+index*p.stride+BitVec.ofNat 64 (8*limb.val)))
    (separate : ∀ read write : Fin 4,p.key+BitVec.ofNat 64 (8*read.val)≠p.keys+index*p.stride+BitVec.ofNat 64 (8*write.val))
    (enough : 2≤source.clock) :
    ∃ target,evaluateHOLFiniteState source afterLoop=(some (.returned (.val (.word 0#64))),target) ∧
      emptyLocalsHOLFinite target=emptyLocalsHOLFinite
        {source with memory:=resultMemory source.memory p table vals order position index count value words,clock:=source.clock-2} := by
  let copied:={source with memory:=Copy32.memory source.memory (p.keys+index*p.stride) words,clock:=source.clock-2}
  have valsKept : copied.memory (table+40#64)=.word vals:=
    (WordWrites.write_away source.memory _ _ awayValsHeader).trans valsCell
  have countKept : copied.memory (table+24#64)=.word count:=
    (WordWrites.write_away source.memory _ _ awayCountHeader).trans countCell
  obtain ⟨target,tailRun,frame⟩:=after_copy copied table vals p.used order position index count value
    tLocal locals.index valueLocal locals.used orderLocal positionLocal valsMapped valsKept valueMapped usedMapped
    orderMapped positionMapped countMapped countKept awayValue awayUsed little
  refine ⟨target,lift_copy32 source p index locals keyLength words code mask view mapped separate enough target tailRun,frame⟩

end InitECandidate.Solver.MutableTable.Insert

#print axioms InitECandidate.Solver.MutableTable.Insert.tail32_execute
