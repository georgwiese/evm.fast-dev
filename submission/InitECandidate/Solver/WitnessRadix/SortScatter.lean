import InitECandidate.Solver.WitnessRadix.SortProgram

namespace InitECandidate.Solver.WitnessRadix.SortProgram
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open QueryBranch

theorem scattered_run {F : Type} (source : PanSemStateFiniteExact 64 F) (src dst keys : BitVec 64)
    (keyFor : BitVec 64 → ByteKeys.Key) (input : List (BitVec 64)) (position start limit : Nat)
    (premises : Inputs source src dst keys keyFor input position start limit) :
    evaluateHOLFiniteState (first source) ScatterProgram.scatterLoop =
      (none, scattered source dst keyFor position start input) := by
  classical
  have other (name : String) (neq : ofString "i" ≠ ofString name) := bind_lookup_other source "i" name 0#64 neq
  have ready := ScatterProgram.ready_of_fields source (first source) rfl rfl rfl _ _ _ _ _ _ _ _ premises.ready
  have sum := ScatterProgram.zero_one_sum keyFor position input
  exact ScatterProgram.loop_execute input (first source) src dst (BitVec.ofNat 64 start) keys keyFor
    position 0 input.length start (start + ScatterProgram.zeros keyFor position input) limit
    premises.inside (by have := premises.allocation; have := premises.fits; omega) (Nat.zero_add _)
    ((other _ (by decide)).trans premises.srcLocal) ((other _ (by decide)).trans premises.dstLocal)
    ((other _ (by decide)).trans premises.startLocal) ((other _ (by decide)).trans premises.keysLocal)
    ((other _ (by decide)).trans premises.bitLocal) (bind_lookup_same source "i" 0#64)
    ((other _ (by decide)).trans premises.countLocal) ((other _ (by decide)).trans premises.zeroLocal)
    ((other _ (by decide)).trans premises.oneLocal) ready (by have := premises.fits; omega)
    (by have := premises.fits; omega) (by change input.length ≤ source.clock; have := premises.enough; omega)

theorem scattered_frame {F : Type} (source : PanSemStateFiniteExact 64 F) (dst : BitVec 64)
    (keyFor : BitVec 64 → ByteKeys.Key) (position start : Nat) (input : List (BitVec 64)) :
    emptyLocalsHOLFinite (scattered source dst keyFor position start input) =
      emptyLocalsHOLFinite { source with
        memory := WordScatter.scatterWords (ScatterProgram.wordAddress dst) (ScatterProgram.keep keyFor position)
          input source.memory start (start + ScatterProgram.zeros keyFor position input)
        clock := source.clock - input.length } :=
  ScatterProgram.state_frame (first source) dst keyFor position input 0 start (start + ScatterProgram.zeros keyFor position input)

theorem scattered_index {F : Type} (source : PanSemStateFiniteExact 64 F) (dst : BitVec 64)
    (keyFor : BitVec 64 → ByteKeys.Key) (position start : Nat) (input : List (BitVec 64)) :
    (scattered source dst keyFor position start input).locals.lookup (ofString "i") =
      some (.val (.word (BitVec.ofNat 64 input.length))) := by
  simpa only [scattered, Nat.zero_add] using ScatterProgram.state_index (first source) dst keyFor position input 0 start
    (start + ScatterProgram.zeros keyFor position input) (bind_lookup_same source "i" 0#64)

theorem scattered_other {F : Type} (source : PanSemStateFiniteExact 64 F) (dst : BitVec 64)
    (keyFor : BitVec 64 → ByteKeys.Key) (position start : Nat) (input : List (BitVec 64)) (name : MlS)
    (notI : ofString "i" ≠ name) (notZero : ofString "zero_cursor" ≠ name) (notOne : ofString "one_cursor" ≠ name) :
    (scattered source dst keyFor position start input).locals.lookup name = source.locals.lookup name := by
  unfold scattered
  rw [ScatterProgram.state_other (first source) dst keyFor position input 0 start
    (start + ScatterProgram.zeros keyFor position input) name notI notZero notOne]
  simp [first, QueryBranch.bind, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, notI]

theorem scattered_memory {F : Type} (source : PanSemStateFiniteExact 64 F) (dst : BitVec 64)
    (keyFor : BitVec 64 → ByteKeys.Key) (position start limit : Nat) (input : List (BitVec 64))
    (fits : start + input.length ≤ limit) (allocation : dst.toNat + 8 * limit < 2 ^ 64) :
    (scattered source dst keyFor position start input).memory =
      BuildCopy.copyMemory source.memory dst (BitVec.ofNat 64 start) 0 (ScatterProgram.partition keyFor position input) := by
  have frame := congrArg (fun state : PanSemStateFiniteExact 64 F => state.memory)
    (scattered_frame source dst keyFor position start input)
  change (scattered source dst keyFor position start input).memory = _ at frame
  rw [WordScatter.scatter_eq_blocks _ _ _ _ _ _ (ScatterProgram.partition_cross dst start limit keyFor position input fits allocation),
    ScatterProgram.writeWords_copy, ScatterProgram.writeWords_copy,
    ScatterProgram.partition_memory source.memory dst start keyFor position input (by omega)] at frame
  exact frame

end InitECandidate.Solver.WitnessRadix.SortProgram

#print axioms InitECandidate.Solver.WitnessRadix.SortProgram.scattered_run
#print axioms InitECandidate.Solver.WitnessRadix.SortProgram.scattered_memory
