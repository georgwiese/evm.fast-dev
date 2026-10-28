import InitECandidate.Solver.Input.CurrentTable.FirstDiff.ByteReads
import InitECandidate.Solver.WitnessRadix.Copy32Call
import InitECandidate.Solver.WitnessRadix.Copy32Alignment
import InitECandidate.Solver.WitnessRadix.CopyGeneralCode
import InitECandidate.Solver.WitnessRadix.AllocatedArena
import InitECandidate.Solver.ClockPaddingFull

namespace InitECandidate.Solver.Input.CurrentTable.KeyCopy
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix

/-- Reached physical32-byte key-copy operands. Current database keys are
aligned and precede fresh table storage; actual callers must derive this. -/
structure Context (source : PanSemStateFiniteExact 64 Guest.HostMemory) (src dst : BitVec 64) (key : KeyBits.Key) : Prop where
  domain : source.memaddrs = InitE.ordinaryDomain
  little : source.be = false
  sourceAligned : src.toNat%8 = 0
  targetAligned : dst.toNat%8 = 0
  sourceFits : src.toNat+32 < 2^64
  targetArena : AllocatedBytes.Arena dst 32
  ordered : src.toNat+32 ≤ dst.toNat
  bytes : FirstDiff.ByteView source src key

def result (source : PanSemStateFiniteExact 64 Guest.HostMemory) (src dst : BitVec 64) :=
  {source with memory := Copy32.memory source.memory dst (MemoryBytes.wordsOf source src),clock := source.clock-2}

theorem Context.of_frame {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {src dst : BitVec 64} {key : KeyBits.Key}
    (ready : Context source src dst key) (frame : LocalEffects.erase target = LocalEffects.erase source) : Context target src dst key := by
  have domain := congrArg PanSemStateFiniteExact.memaddrs frame
  have endian := congrArg PanSemStateFiniteExact.be frame
  change target.memaddrs = source.memaddrs at domain
  change target.be = source.be at endian
  exact ⟨domain.trans ready.domain,endian.trans ready.little,ready.sourceAligned,ready.targetAligned,ready.sourceFits,ready.targetArena,ready.ordered,ready.bytes.of_frame frame⟩

theorem Context.words {source : PanSemStateFiniteExact 64 Guest.HostMemory} {src dst : BitVec 64} {key : KeyBits.Key}
    (ready : Context source src dst key) : MemoryBytes.WordView source src (MemoryBytes.wordsOf source src) :=
  MemoryBytes.byteView_words source src key ready.sourceAligned ready.sourceFits ready.bytes

theorem Context.mapped {source : PanSemStateFiniteExact 64 Guest.HostMemory} {src dst : BitVec 64} {key : KeyBits.Key}
    (ready : Context source src dst key) (limb : Fin 4) : source.memaddrs (dst+BitVec.ofNat 64 (8*limb.val)) := by
  have inside : 8*limb.val < 32 := by have := limb.isLt; omega
  exact AllocatedBytes.word_mapped source dst 32 (8*limb.val) ready.domain ready.targetArena inside ready.targetAligned (by simp)

theorem Context.separated {source : PanSemStateFiniteExact 64 Guest.HostMemory} {src dst : BitVec 64} {key : KeyBits.Key}
    (ready : Context source src dst key) (read write : Fin 4) :
    src+BitVec.ofNat 64 (8*read.val) ≠ dst+BitVec.ofNat 64 (8*write.val) := by
  have rBound : 8*read.val < 32 := by have := read.isLt; omega
  have wBound : 8*write.val < 32 := by have := write.isLt; omega
  have rNumber := byteAddress_toNat src (8*read.val) (by have := ready.sourceFits; omega)
  have wNumber := byteAddress_toNat dst (8*write.val) (by have := ready.targetArena.upper; omega)
  change (src+BitVec.ofNat 64 (8*read.val)).toNat = src.toNat+8*read.val at rNumber
  change (dst+BitVec.ofNat 64 (8*write.val)).toNat = dst.toNat+8*write.val at wNumber
  intro same
  have number := congrArg BitVec.toNat same
  rw [rNumber,wNumber] at number
  have order := ready.ordered
  omega

/-- Actual ignored-result current memcpy, with one call and one loop tick. -/
theorem Context.execute {source : PanSemStateFiniteExact 64 Guest.HostMemory} {src dst : BitVec 64} {key : KeyBits.Key}
    (ready : Context source src dst key) (installed : OriginalCode.Installed source.code) (expressions : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address => Classical.propDecidable (source.memaddrs address)) expressions =
      some [.val (.word dst),.val (.word src),.val (.word 32#64)]) (enough : 2 ≤ source.clock) :
    evaluateHOLFiniteState source (.call (some (none,none)) (ofString "memcpy") expressions) = (none,result source src dst) := by
  obtain ⟨callee,called,dstCell,srcCell,lengthCell⟩ := CopyGeneral.environment source.code.lookup dst src 32 (CopyGeneral.original_code source.code installed)
  exact Copy32.call_execute source callee expressions src dst (MemoryBytes.wordsOf source src) args called srcCell dstCell lengthCell
    (Copy32.alignment_mask src dst ready.sourceAligned ready.targetAligned) ready.words ready.mapped ready.separated enough

/-- No successful future copy or source-clock funding is assumed by this
all-outcome price. Short entries are bounded by their actual remaining clock. -/
theorem Context.price {source : PanSemStateFiniteExact 64 Guest.HostMemory} {src dst : BitVec 64} {key : KeyBits.Key}
    (ready : Context source src dst key) (installed : OriginalCode.Installed source.code) (expressions : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address => Classical.propDecidable (source.memaddrs address)) expressions =
      some [.val (.word dst),.val (.word src),.val (.word 32#64)]) :
    source.clock-(evaluateHOLFiniteState source (.call (some (none,none)) (ofString "memcpy") expressions)).2.clock ≤ 2 := by
  by_cases enough : 2 ≤ source.clock
  · rw [ready.execute installed expressions args enough]
    change source.clock-(source.clock-2) ≤ 2
    omega
  · omega

/-- A real normal copy derives its own two paid clocks and exact caller
state; padding only inverts that actual run. -/
theorem Context.normal {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {src dst : BitVec 64} {key : KeyBits.Key}
    (ready : Context source src dst key) (installed : OriginalCode.Installed source.code) (expressions : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address => Classical.propDecidable (source.memaddrs address)) expressions =
      some [.val (.word dst),.val (.word src),.val (.word 32#64)])
    (normal : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "memcpy") expressions) = (none,post)) :
    2 ≤ source.clock ∧ post = result source src dst := by
  classical
  let padded := {source with clock := source.clock+2}
  have context : Context padded src dst key := ready.of_frame rfl
  have paddedArgs : evalListHOLFinite padded (h:=fun address => Classical.propDecidable (padded.memaddrs address)) expressions =
      some [.val (.word dst),.val (.word src),.val (.word 32#64)] := by
    change evalListHOLExact (stateAddClock source.toExact 2) expressions = _
    rw [evalListHOLExact_stateAddClock]
    exact args
  have actual := context.execute installed expressions paddedArgs (by change 2 ≤ source.clock+2; omega)
  have lifted := panPropsEvaluateAddClockEq (.call (some (none,none)) (ofString "memcpy") expressions) source none post 2
    ⟨normal,by intro impossible; cases impossible⟩
  have frame := congrArg Prod.snd (lifted.symm.trans actual)
  change {post with clock := post.clock+2} =
    {{source with memory := Copy32.memory source.memory dst (MemoryBytes.wordsOf source src)} with clock := source.clock+2-2} at frame
  exact InitECandidate.Solver.strip_full_clock_padding source post
    {source with memory := Copy32.memory source.memory dst (MemoryBytes.wordsOf source src)} 2 2 (by omega) frame

/-- The copied bytes are those actually read from the reached query buffer. -/
theorem Context.copied {source : PanSemStateFiniteExact 64 Guest.HostMemory} {src dst : BitVec 64} {key : KeyBits.Key}
    (ready : Context source src dst key) : FirstDiff.ByteView (result source src dst) dst key :=
  Copy32.byte_view source src dst (MemoryBytes.wordsOf source src) key ready.sourceAligned ready.targetAligned ready.sourceFits
    (by have bound := ready.targetArena.upper; omega) ready.little ready.words ready.bytes ready.mapped

end InitECandidate.Solver.Input.CurrentTable.KeyCopy

#print axioms InitECandidate.Solver.Input.CurrentTable.KeyCopy.Context.execute
#print axioms InitECandidate.Solver.Input.CurrentTable.KeyCopy.Context.price
#print axioms InitECandidate.Solver.Input.CurrentTable.KeyCopy.Context.normal
#print axioms InitECandidate.Solver.Input.CurrentTable.KeyCopy.Context.copied
