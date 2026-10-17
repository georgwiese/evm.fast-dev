import InitECandidate.Solver.WitnessRadix.KeccakCall
import InitECandidate.Solver.WitnessRadix.CopyGeneralCall

namespace InitECandidate.Solver.WitnessRadix.KeccakAbsorb
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString QueryBranch

def body : ProgHOL 64 := match Guest.guestFn_keccak_absorb_block with | .function fn => progToHOL fn.body | _ => .skip
def address (name : String) (extras : List Nat := []) : ExpHOL 64 :=
  .op .add ([localVar name, localVar "i"] ++ extras.map (fun offset => .const (BitVec.ofNat 64 offset)))
def byte (extras : List Nat) : ExpHOL 64 := .loadByte (address "blk" extras)
def shifted (value : ExpHOL 64) (bits : Nat) : ExpHOL 64 := .shift .lsl value (.const (BitVec.ofNat 64 bits))
def highWord : ExpHOL 64 := .op .or [byte [4], shifted (byte [4,1]) 8, shifted (byte [4,2]) 16, shifted (byte [4,3]) 24]
def inputWord (unaligned : Bool) : ExpHOL 64 :=
  if unaligned then .op .or [byte [], shifted (byte [1]) 8, shifted (byte [2]) 16, shifted (byte [3]) 24, shifted highWord 32]
  else .load .one (address "blk")
def laneBody (unaligned : Bool) : ProgHOL 64 := .seq
  (.store (address "stp") (.op .xor [.load .one (address "stp"), inputWord unaligned]))
  (CopyBytes.increment 8#64)
def condition : ExpHOL 64 := .cmp .less (localVar "i") (.const 136#64)
def alignment : ExpHOL 64 := .cmp .equal (.op .and [localVar "blk", .const 7#64]) (.const 0#64)
def loop (unaligned : Bool) : ProgHOL 64 := .while condition (laneBody unaligned)
def tail : ProgHOL 64 := .seq (.call (some (none, none)) (ofString "keccak_f1600") [localVar "stp"]) (.return (.const 0#64))

theorem body_shape : body = .dec (ofString "i") .one (.const 0#64)
    (.seq (.ite alignment (loop false) (loop true)) tail) := by
  simp only [body, Guest.guestFn_keccak_absorb_block, progToHOL, expToHOL, shapeToHOL,
    List.map_cons, List.map_nil, alignment, loop, condition, laneBody, address, inputWord, highWord, byte, shifted,
    tail, CopyBytes.increment, localVar, addConst, ↓reduceIte]
  rfl

/-- The input-lane expression is the actual aligned word load or expanded
little-endian byte-load expression from the fixed guest. -/
theorem input_read {F : Type} (source : PanSemStateFiniteExact 64 F) (blk index : BitVec 64) (unaligned : Bool)
    (blkLocal : source.locals.lookup (ofString "blk") = some (.val (.word blk)))
    (indexLocal : source.locals.lookup (ofString "i") = some (.val (.word index)))
    (wordMapped : unaligned = false → source.memaddrs (blk + index))
    (byteMapped : ∀ offset : Fin 8, source.memaddrs (panByteAlignHOL (width := 64) (blk + index + BitVec.ofNat 64 offset.val))) :
    ∃ value : BitVec 64, eval source (inputWord unaligned) = some (.val (.word value)) := by
  classical
  cases unaligned with
  | false =>
    have mapped := wordMapped rfl
    cases cell : source.memory (blk + index) with
    | word value =>
      simp [eval, inputWord, address, localVar, evalHOLExact, evalListHOLExact, toExact, blkLocal, indexLocal,
        valueIsWord, valueWord, wordOpHOL, wordOp, memLoadHOLExact, mapped, cell]
  | true =>
    have m0 := byteMapped (⟨0, by decide⟩ : Fin 8)
    have m1 := byteMapped (⟨1, by decide⟩ : Fin 8)
    have m2 := byteMapped (⟨2, by decide⟩ : Fin 8)
    have m3 := byteMapped (⟨3, by decide⟩ : Fin 8)
    have m4 := byteMapped (⟨4, by decide⟩ : Fin 8)
    have m5 := byteMapped (⟨5, by decide⟩ : Fin 8)
    have m6 := byteMapped (⟨6, by decide⟩ : Fin 8)
    have m7 := byteMapped (⟨7, by decide⟩ : Fin 8)
    simp [BitVec.add_assoc] at m0 m1 m2 m3 m4 m5 m6 m7
    simp [eval, inputWord, highWord, byte, shifted, address, localVar, evalHOLExact, evalListHOLExact, toExact,
      blkLocal, indexLocal, valueIsWord, valueWord, wordOpHOL, wordOp, wordShiftHOL,
      panMemLoadByteHOL, panMemLoadByteWord8HOL, BitVec.add_assoc, m0,m1,m2,m3,m4,m5,m6,m7]

end InitECandidate.Solver.WitnessRadix.KeccakAbsorb

#print axioms InitECandidate.Solver.WitnessRadix.KeccakAbsorb.body_shape
#print axioms InitECandidate.Solver.WitnessRadix.KeccakAbsorb.input_read
