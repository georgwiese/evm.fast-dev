#!/usr/bin/env python3
"""Generate proof syntax for the unchanged20/52-byte unrolled hash paths."""
from pathlib import Path
root = Path(__file__).resolve().parents[2]
header = '''import InitECandidate.Solver.MutableTable.HashUnaligned32

namespace InitECandidate.Solver.MutableTable.HashSized
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

inductive Kind where | address | storage
  deriving DecidableEq

def keySize : Kind → Nat | .address => 20 | .storage => 52
def wordCount : Kind → Nat | .address => 2 | .storage => 6
def tailWord (bytes : Fin 4 → UInt8) : BitVec 64 :=
  Input.WordCodec.word4 (BitVec.ofNat 64 (bytes 0).toNat) (BitVec.ofNat 64 (bytes 1).toNat)
    (BitVec.ofNat 64 (bytes 2).toNat) (BitVec.ofNat 64 (bytes 3).toNat)
def mixed (kind : Kind) (words : Fin 6 → BitVec 64) (bytes : Fin 4 → UInt8) : BitVec 64 :=
  match kind with
  | .address => ((14695981039346656037#64 ^^^ words 0) ^^^ words 1) ^^^ tailWord bytes
  | .storage => ((((((14695981039346656037#64 ^^^ words 0) ^^^ words 1) ^^^ words 2) ^^^ words 3) ^^^ words 4) ^^^ words 5) ^^^ tailWord bytes

def resultWord (kind : Kind) (words : Fin 6 → BitVec 64) (bytes : Fin 4 → UInt8) : BitVec 64 :=
  let h := (mixed kind words bytes ^^^ (mixed kind words bytes >>> (32 : Nat))) * 1099511628211#64
  h ^^^ (h >>> (29 : Nat))

def chunkByte (bytes : Fin 52 → UInt8) (block : Fin 6) (byte : Fin 8) : BitVec 64 :=
  BitVec.ofNat 64 (bytes ⟨8 * block.val + byte.val, by have := block.isLt; have := byte.isLt; omega⟩).toNat

def packedWords (bytes : Fin 52 → UInt8) (block : Fin 6) : BitVec 64 :=
  Input.WordCodec.word8 (chunkByte bytes block 0) (chunkByte bytes block 1) (chunkByte bytes block 2) (chunkByte bytes block 3)
    (chunkByte bytes block 4) (chunkByte bytes block 5) (chunkByte bytes block 6) (chunkByte bytes block 7)
def tailBytes (kind : Kind) (bytes : Fin 52 → UInt8) (byte : Fin 4) : UInt8 :=
  bytes ⟨8 * wordCount kind + byte.val, by cases kind <;> have := byte.isLt <;> dsimp [wordCount] <;> omega⟩

'''
common = '''    simp [Hash.afterLocals, Hash.body, Guest.guestFn_htab_hash, progToHOL, expToHOL, shapeToHOL,
      evaluateHOLFiniteState_seq, evaluateHOLFiniteState_ite, evaluateHOLFiniteState_assign,
      evaluateHOLFiniteState_return, evalHOLExact, evalListHOLExact, toExact, setVarHOLFinite, setKvarHOLFinite,
      lookupKvarHOLFinite, isValidValueHOLFinite, HolFiniteMapExact.update, FUPDATE,
      p, length, hLocal, wLocal, foldAnd, foldXor, ALIGNMENT, valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL, wordShiftHOL,
      Flapjack.Compiler.Encoders.Asm.wordCmpHOL, memLoadHOLExact, isWfShapeExactHOL,
      shapeOfHOLExact, shapeEqHOL, fixClockHOLFinite, emptyLocalsHOLFinite, restore, WitnessRadix.QueryBranch.bind,
      resultWord, mixed, tailWord, keySize, wordCount, packedWords, chunkByte, tailBytes,
      Input.WordCodec.word8, Input.WordCodec.word4, BitVec.add_assoc, OrOp.or, BitVec.or_zero, rawAssoc,
      READS,
      show ofString "h" ≠ ofString "w" from by decide,
      show ofString "h" ≠ ofString "p" from by decide,
      show ofString "h" ≠ ofString "key_len" from by decide,
      show ofString "w" ≠ ofString "h" from by decide,
      show ofString "w" ≠ ofString "p" from by decide,
      show ofString "w" ≠ ofString "key_len" from by decide]
    all_goals simp only [HOr.hOr, OrOp.or, rawAssoc]
    all_goals rfl
'''
folds = '''  have foldAnd (a b : BitVec 64) : AndOp.and a (AndOp.and b (18446744073709551615#64)) = a &&& b := by
    change a &&& (b &&& BitVec.allOnes 64) = a &&& b
    rw [BitVec.and_allOnes]
  have foldXor (a b : BitVec 64) : XorOp.xor a (XorOp.xor b 0#64) = a ^^^ b := by
    change a ^^^ (b ^^^ 0#64) = a ^^^ b
    simp
  have rawAssoc (a b c : BitVec 64) : BitVec.or (BitVec.or a b) c = BitVec.or a (BitVec.or b c) := BitVec.or_assoc a b c
  cases kind with
'''
s = header + '''set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
/-- Actual aligned20/52-byte unrolled hash paths, with all real word/byte
loads. Pure exact return and no body clocks; no hash distribution premise. -/
theorem aligned_core (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : Kind) (pointer : BitVec 64)
    (words : Fin 6 → BitVec 64) (bytes : Fin 4 → UInt8)
    (p : source.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (length : source.locals.lookup (ofString "key_len") = some (.val (.word (BitVec.ofNat 64 (keySize kind)))))
    (hLocal : source.locals.lookup (ofString "h") = some (.val (.word 14695981039346656037#64)))
    (wLocal : source.locals.lookup (ofString "w") = some (.val (.word 0#64)))
    (aligned : pointer &&& 7#64 = 0#64)
    (mapped : ∀ i : Fin 6, i.val < wordCount kind → source.memaddrs (pointer + BitVec.ofNat 64 (8 * i.val)))
    (stored : ∀ i : Fin 6, i.val < wordCount kind → source.memory (pointer + BitVec.ofNat 64 (8 * i.val)) = .word (words i))
    (loaded : ∀ i : Fin 4, @panMemLoadByteHOL 64 _ source.memory source.memaddrs
      (fun address => Classical.propDecidable (source.memaddrs address)) source.be
      (pointer + BitVec.ofNat 64 (8 * wordCount kind + i.val)) = some (bytes i)) :
    evaluateHOLFiniteState source Hash.afterLocals =
      (some (.returned (.val (.word (resultWord kind words bytes)))), emptyLocalsHOLFinite source) := by
  classical
''' + folds
for kind,n in [('address',2),('storage',6)]:
    s += f'  | {kind} =>\n'
    names=[]
    for i in range(n):
        addr='pointer' if i == 0 else f'(pointer + {8*i}#64)'
        for tag,typ,assumption in [('m',f'source.memaddrs {addr}','mapped'),('s',f'source.memory {addr} = .word (words {i})','stored')]:
            s += f'    have {tag}{i} : {typ} := by simpa only [(show ({i} : Fin 6).val = {i} from rfl), Nat.reduceMul, BitVec.add_zero] using {assumption} {i} (by decide)\n'
            names.append(f'{tag}{i}')
    for j in range(4):
        s += f'''    have r{j} : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
        (fun address => Classical.propDecidable (source.memaddrs address)) source.be (pointer + {8*n+j}#64) = some (bytes {j}) := loaded {j}
'''
        names.append(f'r{j}')
    s += common.replace('ALIGNMENT','aligned').replace('READS',', '.join(names))
s += '''
set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
/-- Actual unaligned20/52-byte macro expansions, from their real byte loads.
All word assembly, shifts and XOR folds execute; no body clocks are consumed. -/
theorem unaligned_core (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : Kind) (pointer : BitVec 64)
    (bytes : Fin 52 → UInt8)
    (p : source.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (length : source.locals.lookup (ofString "key_len") = some (.val (.word (BitVec.ofNat 64 (keySize kind)))))
    (hLocal : source.locals.lookup (ofString "h") = some (.val (.word 14695981039346656037#64)))
    (wLocal : source.locals.lookup (ofString "w") = some (.val (.word 0#64)))
    (unaligned : pointer &&& 7#64 ≠ 0#64)
    (loaded : ∀ i : Fin 52, i.val < keySize kind → @panMemLoadByteHOL 64 _ source.memory source.memaddrs
      (fun address => Classical.propDecidable (source.memaddrs address)) source.be
      (pointer + BitVec.ofNat 64 i.val) = some (bytes i)) :
    evaluateHOLFiniteState source Hash.afterLocals =
      (some (.returned (.val (.word (resultWord kind (packedWords bytes) (tailBytes kind bytes))))), emptyLocalsHOLFinite source) := by
  classical
''' + folds
for kind,n in [('address',20),('storage',52)]:
    s += f'  | {kind} =>\n'
    for i in range(n):
        addr='pointer' if i == 0 else f'(pointer + {i}#64)'
        s += f'''    have r{i} : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
        (fun address => Classical.propDecidable (source.memaddrs address)) source.be {addr} = some (bytes {i}) := by simpa only [(show ({i} : Fin 52).val = {i} from rfl), BitVec.add_zero] using loaded {i} (by decide)
'''
    s += common.replace('ALIGNMENT','unaligned').replace('READS',', '.join(f'r{i}' for i in range(n)))
s += '''
end InitECandidate.Solver.MutableTable.HashSized

#print axioms InitECandidate.Solver.MutableTable.HashSized.aligned_core
#print axioms InitECandidate.Solver.MutableTable.HashSized.unaligned_core
'''
(root/'submission/InitECandidate/Solver/MutableTable/HashSized.lean').write_text(s)
