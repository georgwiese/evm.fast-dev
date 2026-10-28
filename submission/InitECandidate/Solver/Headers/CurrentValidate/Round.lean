import InitECandidate.Solver.Headers.CurrentValidate.Entry
import InitECandidate.Solver.Headers.ValidateRows
import InitECandidate.Solver.Headers.CurrentDecode.Call
import InitECandidate.Solver.CurrentKeccak.Call
import InitECandidate.Solver.PanHeapGlobals

namespace InitECandidate.Solver.Headers.CurrentValidate
open Validate
open Flapjack PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString Input WitnessRadix

/-- Fixed real caller arguments and already allocated destinations. -/
structure Data where
  array : BitVec 64
  hs : BitVec 64
  hashes : BitVec 64
  stp : BitVec 64
  pad : BitVec 64
  pointers : Nat→BitVec 64
  lengths : Nat→BitVec 64
  count : Nat
  lower : Nat
  upper : Nat

structure RoundLayout (data : Data) : Prop where
  hs : AllocatedBytes.Arena data.hs (8*data.count+8)
  hsAligned : data.hs.toNat%8=0
  hashes : AllocatedBytes.Arena data.hashes (32*data.count+32)
  hashesAligned : data.hashes.toNat%8=0
  inputBefore : data.upper≤data.hs.toNat
  hsBeforeHashes : data.hs.toNat+8*data.count+8≤data.hashes.toNat
  stateBefore : data.stp.toNat+200≤data.lower
  padBefore : data.pad.toNat+136≤data.lower
  lowerAligned : data.lower%8=0
  lower : 2701131776≤data.lower
  count : data.count≤256
  lengths : ∀ index<data.count,(data.lengths index).toNat≤1024

/-- Current physical input/records, actual software hash workspace, real
bounded heap and live loop locals. No future header/hash result is assumed. -/
structure RoundState (data : Data) (origin current : PanSemStateFiniteExact 64 Guest.HostMemory) (index : Nat) : Prop where
  arena : CurrentStartup.ArenaState current
  environment : CurrentKeccak.Hash.Environment current data.stp data.pad
  input : HashInput.Frame origin current data.lower data.upper
  rows : Rows current data.array data.pointers data.lengths data.count data.lower data.upper
  heap : ∃ pointer,current.globals.lookup (ofString "heap_ptr")=some (.val (.word pointer)) ∧
    pointer.toNat≤2952790016 ∧ pointer.toNat%8=0 ∧ data.hashes.toNat+32*data.count+32≤pointer.toNat
  arrayCell : current.locals.lookup (ofString "arr")=some (.val (.word data.array))
  countCell : current.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 data.count)))
  hsCell : current.locals.lookup (ofString "hs")=some (.val (.word data.hs))
  hashesCell : current.locals.lookup (ofString "hashes")=some (.val (.word data.hashes))
  indexCell : current.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index)))
  globals : HeapGlobals origin current

theorem RoundState.dec_clock (data : Data) (origin current : PanSemStateFiniteExact 64 Guest.HostMemory) (index : Nat)
    (state : RoundState data origin current index) : RoundState data origin (decClockHOLFinite current) index :=
  ⟨state.arena.of_frame rfl,state.environment.of_frame rfl,⟨state.input.words⟩,
    state.rows.of_frame current _ data.array data.pointers data.lengths data.count data.lower data.upper ⟨by intro query low high; rfl⟩,
    state.heap,state.arrayCell,state.countCell,state.hsCell,state.hashesCell,state.indexCell,state.globals⟩

end InitECandidate.Solver.Headers.CurrentValidate

#print axioms InitECandidate.Solver.Headers.CurrentValidate.RoundState.dec_clock
