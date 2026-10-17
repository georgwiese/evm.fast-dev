import InitECandidate.Solver.WitnessRadix.SortScatter

namespace InitECandidate.Solver.WitnessRadix.SortProgram
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open QueryBranch

theorem second_other {F : Type} (source : PanSemStateFiniteExact 64 F) (dst : BitVec 64)
    (keyFor : BitVec 64 → ByteKeys.Key) (position start : Nat) (input : List (BitVec 64)) (name : MlS)
    (notI : ofString "i" ≠ name) (notZero : ofString "zero_cursor" ≠ name) (notOne : ofString "one_cursor" ≠ name) :
    (second source dst keyFor position start input).locals.lookup name = source.locals.lookup name := by
  simpa [second, QueryBranch.bind, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, notI] using
    scattered_other source dst keyFor position start input name notI notZero notOne

theorem copied_run {F : Type} (source : PanSemStateFiniteExact 64 F) (src dst keys : BitVec 64)
    (keyFor : BitVec 64 → ByteKeys.Key) (input : List (BitVec 64)) (position start limit : Nat)
    (premises : Inputs source src dst keys keyFor input position start limit) :
    evaluateHOLFiniteState (second source dst keyFor position start input) BuildCopy.copyLoop =
      (none, sorted source src dst keyFor position start input) := by
  classical
  have fits := premises.fits
  have allocation := premises.allocation
  have smallStart : start < 2 ^ 64 := by omega
  have smallCount : input.length < 2 ^ 64 := by omega
  have memoryEq := scattered_memory source dst keyFor position start limit input fits allocation
  have frame := scattered_frame source dst keyFor position start input
  have domainEq : (scattered source dst keyFor position start input).memaddrs = source.memaddrs :=
    congrArg (fun state => state.memaddrs) frame
  have clockEq : (scattered source dst keyFor position start input).clock = source.clock - input.length :=
    congrArg (fun state => state.clock) frame
  have backup := ScatterProgram.backup_rows source.memory source.memaddrs dst start limit keyFor position input
    fits allocation premises.ready.mapped
  rw [ScatterProgram.partition_memory source.memory dst start keyFor position input smallStart] at backup
  have rows : BuildCopy.Rows (second source dst keyFor position start input).memory
      (second source dst keyFor position start input).memaddrs dst (BitVec.ofNat 64 start) 0
      (ScatterProgram.partition keyFor position input) := by
    change BuildCopy.Rows (scattered source dst keyFor position start input).memory
      (scattered source dst keyFor position start input).memaddrs _ _ _ _
    rw [memoryEq, domainEq]
    exact backup
  have primaryMapped : ∀ i, 0 ≤ i → i < input.length →
      (second source dst keyFor position start input).memaddrs
        (BuildCopy.row src (BitVec.ofNat 64 start) (BitVec.ofNat 64 i)) := by
    intro i lo hi
    change (scattered source dst keyFor position start input).memaddrs _
    rw [domainEq]
    simpa only [Nat.zero_add] using BuildCopy.rows_mapped source.memory source.memaddrs src
      (BitVec.ofNat 64 start) 0 input premises.ready.rows i hi
  have separate : ∀ i j, 0 ≤ i → i < input.length → 0 ≤ j → j < input.length →
      BuildCopy.row dst (BitVec.ofNat 64 start) (BitVec.ofNat 64 j) ≠
        BuildCopy.row src (BitVec.ofNat 64 start) (BitVec.ofNat 64 i) := by
    intro i j ilo ihi jlo jhi
    rw [ScatterProgram.row_start dst start j smallStart]
    have away := premises.ready.wordAway (start + j) (by omega) i ihi
    simpa only [Nat.zero_add] using Ne.symm away
  have index : (second source dst keyFor position start input).locals.lookup (ofString "i") =
      some (.val (.word 0#64)) := bind_lookup_same (scattered source dst keyFor position start input) "i" 0#64
  have run := BuildCopy.loop_execute (ScatterProgram.partition keyFor position input)
    (second source dst keyFor position start input) src dst (BitVec.ofNat 64 start) 0 input.length
    smallCount (by simpa only [Nat.zero_add] using ScatterProgram.partition_length keyFor position input)
    ((second_other source dst keyFor position start input _ (by decide) (by decide) (by decide)).trans premises.srcLocal)
    ((second_other source dst keyFor position start input _ (by decide) (by decide) (by decide)).trans premises.dstLocal)
    ((second_other source dst keyFor position start input _ (by decide) (by decide) (by decide)).trans premises.startLocal)
    index ((second_other source dst keyFor position start input _ (by decide) (by decide) (by decide)).trans premises.countLocal)
    rows primaryMapped separate (by
      rw [ScatterProgram.partition_length]
      change input.length ≤ (scattered source dst keyFor position start input).clock
      rw [clockEq]
      have := premises.enough
      omega)
  exact run

end InitECandidate.Solver.WitnessRadix.SortProgram

#print axioms InitECandidate.Solver.WitnessRadix.SortProgram.copied_run
