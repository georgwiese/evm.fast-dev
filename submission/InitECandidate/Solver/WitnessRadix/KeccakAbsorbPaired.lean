import InitECandidate.Solver.WitnessRadix.KeccakAbsorbRead
import InitECandidate.Solver.WitnessRadix.KeccakAbsorbLanesAgreement

namespace InitECandidate.Solver.WitnessRadix.KeccakAbsorb
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString QueryBranch
set_option maxRecDepth 10000

theorem prepared_domain (source : PanSemStateFiniteExact 64 Guest.HostMemory) (stp blk : BitVec 64) :
    (prepared source stp blk).memaddrs = source.memaddrs :=
  stateLanes_domain (bind source "i" 0#64) stp (isUnaligned blk) 0 17

theorem prepared_endian (source : PanSemStateFiniteExact 64 Guest.HostMemory) (stp blk : BitVec 64) :
    (prepared source stp blk).be = source.be :=
  congrArg (fun state => state.be) (stateLanes_control (bind source "i" 0#64) stp (isUnaligned blk) 0 17)

theorem prepared_ffi (source : PanSemStateFiniteExact 64 Guest.HostMemory) (stp blk : BitVec 64) :
    (prepared source stp blk).ffi = source.ffi :=
  congrArg (fun state => state.ffi) (stateLanes_control (bind source "i" 0#64) stp (isUnaligned blk) 0 17)

set_option maxHeartbeats 1000000 in
theorem target_memory_eq (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (stp blk : BitVec 64) (bytes : List (BitVec 8)) :
    (target source stp blk bytes).memory = (Keccak.post (prepared source stp blk) stp bytes).memory := by
  simp only [target, after, restore, emptyLocalsHOLFinite]

/-- The complete actual block absorber is independent of private memory and
unrelated code entries. Both executions perform the same permutation event
and preserve agreement on the selected public memory region. -/
theorem paired_execute (source right : PanSemStateFiniteExact 64 Guest.HostMemory)
    (stp blk : BitVec 64)
    (sourceStp : source.locals.lookup (ofString "stp") = some (.val (.word stp)))
    (rightStp : right.locals.lookup (ofString "stp") = some (.val (.word stp)))
    (sourceBlk : source.locals.lookup (ofString "blk") = some (.val (.word blk)))
    (rightBlk : right.locals.lookup (ofString "blk") = some (.val (.word blk)))
    (domain : source.memaddrs = right.memaddrs) (endian : source.be = right.be)
    (ffi : source.ffi = right.ffi)
    (region : BitVec 64 → Prop) (reads : ReadRegion region stp blk (isUnaligned blk))
    (stateBytes : ∀ offset < 200,
      region (panByteAlignHOL (width := 64) (byteAddress stp offset)))
    (same : ∀ query, region query → source.memory query = right.memory query)
    (mapped : Mapped source stp blk (isUnaligned blk))
    (sourceCode : source.code.lookup (ofString "keccak_f1600") = some (Keccak.formals, Keccak.f1600Body, .one))
    (rightCode : right.code.lookup (ofString "keccak_f1600") = some (Keccak.formals, Keccak.f1600Body, .one))
    (oracleEq : source.ffi.oracle = InitE.sourceOracle)
    (aligned : stp.toNat % 8 = 0) (fits : stp.toNat + 200 < 2^64)
    (sourceClock : 18 ≤ source.clock) (rightClock : 18 ≤ right.clock) :
    ∃ bytes : List (BitVec 8), bytes.length = 200 ∧
      evaluateHOLFiniteState source body =
        (some (.returned (.val (.word 0#64))), target source stp blk bytes) ∧
      evaluateHOLFiniteState right body =
        (some (.returned (.val (.word 0#64))), target right stp blk bytes) ∧
      (target source stp blk bytes).ffi = (target right stp blk bytes).ffi ∧
      ∀ query, region query →
        (target source stp blk bytes).memory query = (target right stp blk bytes).memory query := by
  classical
  let leftPrepared := prepared source stp blk
  let rightPrepared := prepared right stp blk
  have preparedDomain : leftPrepared.memaddrs = rightPrepared.memaddrs :=
    (prepared_domain source stp blk).trans (domain.trans (prepared_domain right stp blk).symm)
  have preparedEndian : leftPrepared.be = rightPrepared.be :=
    (prepared_endian source stp blk).trans (endian.trans (prepared_endian right stp blk).symm)
  have preparedFfi : leftPrepared.ffi = rightPrepared.ffi :=
    (prepared_ffi source stp blk).trans (ffi.trans (prepared_ffi right stp blk).symm)
  have preparedSame := prepared_memory_agrees source right stp blk sourceBlk rightBlk domain endian region reads same
  obtain ⟨bytes, sourceRead, length⟩ := ByteArray.read200 leftPrepared stp aligned fits (by
    intro word
    rw [prepared_domain]
    exact mapped.stateWords word)
  have equalRead := ByteArray.read_of_cells leftPrepared rightPrepared preparedDomain preparedEndian stp 200
    (by intro offset inside; exact preparedSame _ (stateBytes offset inside))
  have rightRead := equalRead.symm.trans sourceRead
  have readForSource : readBytearrayWordHOL (byteWidth := 8) stp 200
      (@panMemLoadByteWord8HOL 64 _ leftPrepared.memory source.memaddrs
        (fun query => Classical.propDecidable (source.memaddrs query)) source.be) = some bytes := by
    have readerEq : @panMemLoadByteWord8HOL 64 _ leftPrepared.memory leftPrepared.memaddrs
        (fun query => Classical.propDecidable (leftPrepared.memaddrs query)) leftPrepared.be =
        @panMemLoadByteWord8HOL 64 _ leftPrepared.memory source.memaddrs
          (fun query => Classical.propDecidable (source.memaddrs query)) source.be := by
      funext address
      simp only [leftPrepared, rightPrepared, panMemLoadByteWord8HOL, prepared_domain, prepared_endian]
    rw [readerEq] at sourceRead
    exact sourceRead
  have readForRight : readBytearrayWordHOL (byteWidth := 8) stp 200
      (@panMemLoadByteWord8HOL 64 _ rightPrepared.memory right.memaddrs
        (fun query => Classical.propDecidable (right.memaddrs query)) right.be) = some bytes := by
    have readerEq : @panMemLoadByteWord8HOL 64 _ rightPrepared.memory rightPrepared.memaddrs
        (fun query => Classical.propDecidable (rightPrepared.memaddrs query)) rightPrepared.be =
        @panMemLoadByteWord8HOL 64 _ rightPrepared.memory right.memaddrs
          (fun query => Classical.propDecidable (right.memaddrs query)) right.be := by
      funext address
      simp only [leftPrepared, rightPrepared, panMemLoadByteWord8HOL, prepared_domain, prepared_endian]
    rw [readerEq] at rightRead
    exact rightRead
  have rightMapped : Mapped right stp blk (isUnaligned blk) := by
    constructor
    · intro word; rw [← domain]; exact mapped.stateWords word
    · intro choice word; rw [← domain]; exact mapped.blockWords choice word
    · intro offset; rw [← domain]; exact mapped.blockBytes offset
  have rightOracle : right.ffi.oracle = InitE.sourceOracle := by rw [← ffi]; exact oracleEq
  have sourceRun := execute_with_read source stp blk sourceStp sourceBlk mapped sourceCode oracleEq
    aligned fits bytes readForSource sourceClock
  have rightRun := execute_with_read right stp blk rightStp rightBlk rightMapped rightCode rightOracle
    aligned fits bytes readForRight rightClock
  have postFfi := Keccak.post_ffi_agrees leftPrepared rightPrepared preparedFfi stp bytes
  have postSame := Keccak.post_memory_agrees leftPrepared rightPrepared preparedDomain preparedEndian
    region preparedSame stp bytes
  refine ⟨bytes, length, sourceRun, rightRun, ?_, ?_⟩
  · change (Keccak.post leftPrepared stp bytes).ffi = (Keccak.post rightPrepared stp bytes).ffi
    exact postFfi
  · simpa only [target_memory_eq] using postSame

end InitECandidate.Solver.WitnessRadix.KeccakAbsorb

#print axioms InitECandidate.Solver.WitnessRadix.KeccakAbsorb.prepared_domain
#print axioms InitECandidate.Solver.WitnessRadix.KeccakAbsorb.prepared_endian
#print axioms InitECandidate.Solver.WitnessRadix.KeccakAbsorb.prepared_ffi
#print axioms InitECandidate.Solver.WitnessRadix.KeccakAbsorb.paired_execute
