import InitECandidate.Solver.PanHeapGlobals
import InitECandidate.Solver.Headers.ValidateRows
import InitECandidate.Solver.Headers.DecodeCallNormal
import InitECandidate.Solver.WitnessRadix.Keccak256EnvironmentFields

namespace InitECandidate.Solver.Headers.Validate
open Flapjack PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix

/-- Fixed data of the original validator invocation. This is an analysis
description of its real caller arguments and earlier allocations. -/
structure Data where
  array : BitVec 64
  hs : BitVec 64
  hashes : BitVec 64
  cursor : BitVec 64
  limit : BitVec 64
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
  state : AllocatedBytes.Arena data.stp 200
  stateAligned : data.stp.toNat%8=0
  pad : AllocatedBytes.Arena data.pad 136
  padAligned : data.pad.toNat%8=0
  stateBefore : data.stp.toNat+200≤data.lower
  padBefore : data.pad.toNat+136≤data.lower
  lowerAligned : data.lower%8=0
  lower : 2701131776≤data.lower
  count : data.count≤256
  scratchBefore : data.cursor.toNat≤data.lower

/-- Only current execution data is retained: actual input/record memory,
initialized hash environment, scratch, bounded current heap and real loop
locals. Neither a future header nor a successful hash is included. -/
structure RoundState (data : Data) (origin current : PanSemStateFiniteExact 64 Guest.HostMemory) (index : Nat) : Prop where
  installed : Input.OriginalCode.Installed current.code
  shape : current.eshapes.lookup (ofString "HdrErr")=some .one
  arena : Rlp.Validation.Arena current data.cursor data.limit
  environment : Keccak256.Environment current data.stp data.pad
  input : Input.HashInput.Frame origin current data.lower data.upper
  rows : Rows current data.array data.pointers data.lengths data.count data.lower data.upper
  heap : ∃ pointer,current.globals.lookup (ofString "heap_ptr")=some (.val (.word pointer)) ∧
    pointer.toNat≤33806089496 ∧ pointer.toNat%8=0 ∧ data.hashes.toNat+32*data.count+32≤pointer.toNat
  arrayCell : current.locals.lookup (ofString "arr")=some (.val (.word data.array))
  countCell : current.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 data.count)))
  hsCell : current.locals.lookup (ofString "hs")=some (.val (.word data.hs))
  hashesCell : current.locals.lookup (ofString "hashes")=some (.val (.word data.hashes))
  indexCell : current.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index)))
  globals : HeapGlobals origin current

theorem RoundState.dec_clock (data : Data) (origin current : PanSemStateFiniteExact 64 Guest.HostMemory) (index : Nat)
    (state : RoundState data origin current index) : RoundState data origin (decClockHOLFinite current) index := by
  refine ⟨state.installed,state.shape,Rlp.Validation.Arena.of_fields current _ _ _ state.arena rfl rfl,
    Keccak256.Environment.of_fields current _ _ _ state.environment rfl rfl rfl (by intro key other; rfl),
    ⟨state.input.words⟩,?_,state.heap,state.arrayCell,state.countCell,state.hsCell,state.hashesCell,state.indexCell,state.globals⟩
  exact state.rows.of_frame current _ data.array data.pointers data.lengths data.count data.lower data.upper ⟨by intro query low high; rfl⟩

end InitECandidate.Solver.Headers.Validate

#print axioms InitECandidate.Solver.Headers.Validate.RoundState.dec_clock
