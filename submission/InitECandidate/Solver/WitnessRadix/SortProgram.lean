import InitECandidate.Solver.WitnessRadix.SplitProgram
import InitECandidate.Solver.WitnessRadix.PartitionRows
import InitECandidate.Solver.WitnessRadix.StateSteps
import InitECandidate.Solver.WitnessRadix.BindingLookup

namespace InitECandidate.Solver.WitnessRadix.SortProgram
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open QueryBranch

def code (continuation : ProgHOL 64) : ProgHOL 64 :=
  .seq SplitProgram.resetIndex (.seq ScatterProgram.scatterLoop
    (.seq SplitProgram.resetIndex (.seq BuildCopy.copyLoop continuation)))
def first {F : Type} (source : PanSemStateFiniteExact 64 F) : PanSemStateFiniteExact 64 F := bind source "i" 0#64
def scattered {F : Type} (source : PanSemStateFiniteExact 64 F) (dst : BitVec 64)
    (keyFor : BitVec 64 → ByteKeys.Key) (position start : Nat) (input : List (BitVec 64)) : PanSemStateFiniteExact 64 F :=
  ScatterProgram.scatterState (first source) dst keyFor position input 0 start (start + ScatterProgram.zeros keyFor position input)
def second {F : Type} (source : PanSemStateFiniteExact 64 F) (dst : BitVec 64)
    (keyFor : BitVec 64 → ByteKeys.Key) (position start : Nat) (input : List (BitVec 64)) : PanSemStateFiniteExact 64 F :=
  bind (scattered source dst keyFor position start input) "i" 0#64
def sorted {F : Type} (source : PanSemStateFiniteExact 64 F) (src dst : BitVec 64)
    (keyFor : BitVec 64 → ByteKeys.Key) (position start : Nat) (input : List (BitVec 64)) : PanSemStateFiniteExact 64 F :=
  BuildCopy.copyState (second source dst keyFor position start input) src (BitVec.ofNat 64 start) 0
    (ScatterProgram.partition keyFor position input)

structure Inputs {F : Type} (source : PanSemStateFiniteExact 64 F) (src dst keys : BitVec 64)
    (keyFor : BitVec 64 → ByteKeys.Key) (input : List (BitVec 64)) (position start limit : Nat) : Prop where
  inside : position < 256
  fits : start + input.length ≤ limit
  allocation : dst.toNat + 8 * limit < 2 ^ 64
  srcLocal : source.locals.lookup (ofString "src") = some (.val (.word src))
  dstLocal : source.locals.lookup (ofString "dst") = some (.val (.word dst))
  startLocal : source.locals.lookup (ofString "start") = some (.val (.word (BitVec.ofNat 64 start)))
  keysLocal : source.locals.lookup (ofString "keys") = some (.val (.word keys))
  bitLocal : source.locals.lookup (ofString "bit") = some (.val (.word (BitVec.ofNat 64 position)))
  countLocal : source.locals.lookup (ofString "count") = some (.val (.word (BitVec.ofNat 64 input.length)))
  indexLocal : source.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 input.length)))
  zeroLocal : source.locals.lookup (ofString "zero_cursor") = some (.val (.word (BitVec.ofNat 64 start)))
  oneLocal : source.locals.lookup (ofString "one_cursor") =
    some (.val (.word (BitVec.ofNat 64 (start + ScatterProgram.zeros keyFor position input))))
  ready : ScatterProgram.Ready source src dst (BitVec.ofNat 64 start) keys keyFor input 0 limit
  enough : 2 * input.length ≤ source.clock

theorem reset_execute {F : Type} (source : PanSemStateFiniteExact 64 F) (old : BitVec 64)
    (index : source.locals.lookup (ofString "i") = some (.val (.word old))) :
    evaluateHOLFiniteState source SplitProgram.resetIndex = (none, bind source "i" 0#64) := by
  exact StateSteps.assign_execute source "i" (.const 0#64) old 0#64 index rfl

end InitECandidate.Solver.WitnessRadix.SortProgram
