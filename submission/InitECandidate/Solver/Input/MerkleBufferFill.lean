import InitECandidate.Solver.Input.MerkleBufferedProgram

namespace InitECandidate.Solver.Input.Merkle
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def copiedBuffer (source : PanSemStateFiniteExact 64 Guest.HostMemory) (p cursor : BitVec 64) (n : Nat) := CopyGeneral.callState source p cursor (32*n)
def clearedBuffer (source : PanSemStateFiniteExact 64 Guest.HostMemory) (p cursor : BitVec 64) (n size : Nat) :=
  let copied := copiedBuffer source p cursor n
  {copied with memory:=Zero.finalMemory copied.memory (cursor+BitVec.ofNat 64 (32*n)) (32*(size-n)),clock:=copied.clock-(Zero.price (32*(size-n))+1)}
def denseEntry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (p cursor : BitVec 64) (n size : Nat) :=
  bind (clearedBuffer source p cursor n size) "cur" (BitVec.ofNat 64 size)
def fillPrice (p cursor : BitVec 64) (n size : Nat) := CopyGeneral.cost p cursor (32*n)+1+(Zero.price (32*(size-n))+1)

theorem fill_clock (source : PanSemStateFiniteExact 64 Guest.HostMemory) (p cursor : BitVec 64) (n size : Nat) :
    (denseEntry source p cursor n size).clock=source.clock-fillPrice p cursor n size := by
  change source.clock-(CopyGeneral.cost p cursor (32*n)+1)-(Zero.price (32*(size-n))+1)=_
  rw [Nat.sub_sub]
  rfl

theorem fill_price_bound (p cursor : BitVec 64) (n size : Nat) (inside : n≤size) : fillPrice p cursor n size≤3*n+size+2 := by
  have copy := CopyGeneral.cost_word_multiple p cursor (32*n) (by omega)
  have zero : Zero.price (32*(size-n))=size-n := by simp [Zero.price,Nat.mul_comm]
  dsimp only [fillPrice]
  rw [zero]
  omega

/-- Actual original buffer copy, tail zeroing and cur declaration reach the
dense loop with exact physical memory and source ticks. Only current mapped
operands/counts are assumed; all funding follows from the observed run. -/
theorem fill_prefix (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p cursor : BitVec 64) (n size : Nat)
    (inside : n≤size) (installed : OriginalCode.Installed source.code) (domain : source.memaddrs=InitE.ordinaryDomain)
    (pointer : source.locals.lookup (ofString "p")=some (.val (.word p)))
    (buffer : source.locals.lookup (ofString "buf")=some (.val (.word cursor)))
    (count : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 n))))
    (sizeLocal : source.locals.lookup (ofString "size")=some (.val (.word (BitVec.ofNat 64 size))))
    (inputArena : AllocatedBytes.Arena p (32*n)) (bufferArena : AllocatedBytes.Arena cursor (32*size)) (aligned : cursor.toNat%8=0)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source afterBuffer=(result,post)) (notTimeout : result≠some .timeOut) :
    fillPrice p cursor n size≤source.clock ∧ source.clock-(denseEntry source p cursor n size).clock≤3*n+size+2 ∧
      ∃ final,evaluateHOLFiniteState (denseEntry source p cursor n size) denseContinuation=(result,final) ∧
        post=restore (clearedBuffer source p cursor n size) "cur" final := by
  have inputUpper := inputArena.upper
  have bufferUpper := bufferArena.upper
  have nSmall : n<2^64 := by omega
  have args := buffer_copy_arguments source p cursor n pointer buffer count
  have copyArena := AllocatedBytes.Arena.weaken cursor (32*size) (32*n) bufferArena (by omega)
  rw [buffer_shape.1] at run
  obtain ⟨copyFunded,copyRun⟩ := BufferTrace.copy_prefix source post bufferCopyArguments p cursor (32*n) afterCopy args
    (CopyGeneral.original_code source.code installed) (AllocatedBytes.copy_mapped source p cursor (32*n) domain inputArena copyArena) (by omega) result run notTimeout
  let copied := copiedBuffer source p cursor n
  have zeroArgs := buffer_zero_arguments copied cursor n size inside nSmall buffer count sizeLocal
  have zeroArena : AllocatedBytes.Arena (cursor+BitVec.ofNat 64 (32*n)) (32*(size-n)) :=
    AllocatedBytes.Arena.subrange cursor (32*size) (32*n) (32*(size-n)) bufferArena (by omega)
  have address : (cursor+BitVec.ofNat 64 (32*n)).toNat=cursor.toNat+32*n := byteAddress_toNat cursor (32*n) (by omega)
  have zeroAligned : (cursor+BitVec.ofNat 64 (32*n)).toNat%8=0 := by simp [address,Nat.add_mod,Nat.mul_mod,aligned]
  have zeroSmall : 32*(size-n)+32<2^64 := by have upper := zeroArena.upper; omega
  change evaluateHOLFiniteState copied afterCopy=(result,post) at copyRun
  rw [buffer_shape.2.1] at copyRun
  obtain ⟨zeroFunded,zeroRun⟩ := BufferTrace.zero_prefix copied post bufferZeroArguments (cursor+BitVec.ofNat 64 (32*n)) (32*(size-n)) afterClear zeroArgs
    (Zero.original_code copied.code installed) zeroSmall (by omega) zeroAligned
    (by intro index indexInside multiple; exact AllocatedBytes.word_mapped copied _ _ index domain zeroArena (by omega) zeroAligned multiple)
    result copyRun notTimeout
  let cleared := clearedBuffer source p cursor n size
  change evaluateHOLFiniteState cleared afterClear=(result,post) at zeroRun
  have clearedLocals : cleared.locals=source.locals := rfl
  have read : eval cleared (localVar "size")=some (.val (.word (BitVec.ofNat 64 size))) := by
    simpa [eval,localVar,evalHOLExact,toExact,clearedLocals] using sizeLocal
  let current := denseEntry source p cursor n size
  let final := (evaluateHOLFiniteState current denseContinuation).2
  have declared := ScalarScope.declare_execute cleared final "cur" (localVar "size") (BitVec.ofNat 64 size) denseContinuation
    (evaluateHOLFiniteState current denseContinuation).1 read rfl
  rw [buffer_shape.2.2] at zeroRun
  have remaining := declared.symm.trans zeroRun
  have observed := congrArg Prod.fst remaining
  have endpoint := congrArg Prod.snd remaining
  have copyClock : copied.clock=source.clock-(CopyGeneral.cost p cursor (32*n)+1) := rfl
  have funded : fillPrice p cursor n size≤source.clock := by dsimp only [fillPrice]; omega
  have spent : source.clock-current.clock≤3*n+size+2 := by
    have bound := fill_price_bound p cursor n size inside
    rw [fill_clock]
    omega
  exact ⟨funded,spent,final,Prod.ext observed rfl,endpoint.symm⟩

theorem fill_fields (source : PanSemStateFiniteExact 64 Guest.HostMemory) (p cursor : BitVec 64) (n size : Nat) :
    (denseEntry source p cursor n size).locals=source.locals.update (ofString "cur",.val (.word (BitVec.ofNat 64 size))) ∧
    (denseEntry source p cursor n size).globals=source.globals ∧
    InitializerAllocations.context (denseEntry source p cursor n size)=InitializerAllocations.context source := ⟨rfl,rfl,rfl⟩

end InitECandidate.Solver.Input.Merkle

#print axioms InitECandidate.Solver.Input.Merkle.fill_clock
#print axioms InitECandidate.Solver.Input.Merkle.fill_price_bound
#print axioms InitECandidate.Solver.Input.Merkle.fill_prefix
#print axioms InitECandidate.Solver.Input.Merkle.fill_fields
