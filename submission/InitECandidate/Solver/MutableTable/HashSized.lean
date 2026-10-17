import InitECandidate.Solver.MutableTable.HashUnaligned32

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

set_option maxRecDepth 10000 in
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
  have foldAnd (a b : BitVec 64) : AndOp.and a (AndOp.and b (18446744073709551615#64)) = a &&& b := by
    change a &&& (b &&& BitVec.allOnes 64) = a &&& b
    rw [BitVec.and_allOnes]
  have foldXor (a b : BitVec 64) : XorOp.xor a (XorOp.xor b 0#64) = a ^^^ b := by
    change a ^^^ (b ^^^ 0#64) = a ^^^ b
    simp
  have rawAssoc (a b c : BitVec 64) : BitVec.or (BitVec.or a b) c = BitVec.or a (BitVec.or b c) := BitVec.or_assoc a b c
  cases kind with
  | address =>
    have m0 : source.memaddrs pointer := by simpa only [(show (0 : Fin 6).val = 0 from rfl), Nat.reduceMul, BitVec.add_zero] using mapped 0 (by decide)
    have s0 : source.memory pointer = .word (words 0) := by simpa only [(show (0 : Fin 6).val = 0 from rfl), Nat.reduceMul, BitVec.add_zero] using stored 0 (by decide)
    have m1 : source.memaddrs (pointer + 8#64) := by simpa only [(show (1 : Fin 6).val = 1 from rfl), Nat.reduceMul, BitVec.add_zero] using mapped 1 (by decide)
    have s1 : source.memory (pointer + 8#64) = .word (words 1) := by simpa only [(show (1 : Fin 6).val = 1 from rfl), Nat.reduceMul, BitVec.add_zero] using stored 1 (by decide)
    have r0 : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
        (fun address => Classical.propDecidable (source.memaddrs address)) source.be (pointer + 16#64) = some (bytes 0) := loaded 0
    have r1 : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
        (fun address => Classical.propDecidable (source.memaddrs address)) source.be (pointer + 17#64) = some (bytes 1) := loaded 1
    have r2 : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
        (fun address => Classical.propDecidable (source.memaddrs address)) source.be (pointer + 18#64) = some (bytes 2) := loaded 2
    have r3 : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
        (fun address => Classical.propDecidable (source.memaddrs address)) source.be (pointer + 19#64) = some (bytes 3) := loaded 3
    simp [Hash.afterLocals, Hash.body, Guest.guestFn_htab_hash, progToHOL, expToHOL, shapeToHOL,
      evaluateHOLFiniteState_seq, evaluateHOLFiniteState_ite, evaluateHOLFiniteState_assign,
      evaluateHOLFiniteState_return, evalHOLExact, evalListHOLExact, toExact, setVarHOLFinite, setKvarHOLFinite,
      lookupKvarHOLFinite, isValidValueHOLFinite, HolFiniteMapExact.update, FUPDATE,
      p, length, hLocal, wLocal, foldAnd, foldXor, aligned, valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL, wordShiftHOL,
      Flapjack.Compiler.Encoders.Asm.wordCmpHOL, memLoadHOLExact, isWfShapeExactHOL,
      shapeOfHOLExact, shapeEqHOL, fixClockHOLFinite, emptyLocalsHOLFinite, restore, WitnessRadix.QueryBranch.bind,
      resultWord, mixed, tailWord, keySize, wordCount, packedWords, chunkByte, tailBytes,
      Input.WordCodec.word8, Input.WordCodec.word4, BitVec.add_assoc, OrOp.or, BitVec.or_zero, rawAssoc,
      m0, s0, m1, s1, r0, r1, r2, r3,
      show ofString "h" ≠ ofString "w" from by decide,
      show ofString "h" ≠ ofString "p" from by decide,
      show ofString "h" ≠ ofString "key_len" from by decide,
      show ofString "w" ≠ ofString "h" from by decide,
      show ofString "w" ≠ ofString "p" from by decide,
      show ofString "w" ≠ ofString "key_len" from by decide]
    all_goals simp only [HOr.hOr, OrOp.or, rawAssoc]
    all_goals rfl
  | storage =>
    have m0 : source.memaddrs pointer := by simpa only [(show (0 : Fin 6).val = 0 from rfl), Nat.reduceMul, BitVec.add_zero] using mapped 0 (by decide)
    have s0 : source.memory pointer = .word (words 0) := by simpa only [(show (0 : Fin 6).val = 0 from rfl), Nat.reduceMul, BitVec.add_zero] using stored 0 (by decide)
    have m1 : source.memaddrs (pointer + 8#64) := by simpa only [(show (1 : Fin 6).val = 1 from rfl), Nat.reduceMul, BitVec.add_zero] using mapped 1 (by decide)
    have s1 : source.memory (pointer + 8#64) = .word (words 1) := by simpa only [(show (1 : Fin 6).val = 1 from rfl), Nat.reduceMul, BitVec.add_zero] using stored 1 (by decide)
    have m2 : source.memaddrs (pointer + 16#64) := by simpa only [(show (2 : Fin 6).val = 2 from rfl), Nat.reduceMul, BitVec.add_zero] using mapped 2 (by decide)
    have s2 : source.memory (pointer + 16#64) = .word (words 2) := by simpa only [(show (2 : Fin 6).val = 2 from rfl), Nat.reduceMul, BitVec.add_zero] using stored 2 (by decide)
    have m3 : source.memaddrs (pointer + 24#64) := by simpa only [(show (3 : Fin 6).val = 3 from rfl), Nat.reduceMul, BitVec.add_zero] using mapped 3 (by decide)
    have s3 : source.memory (pointer + 24#64) = .word (words 3) := by simpa only [(show (3 : Fin 6).val = 3 from rfl), Nat.reduceMul, BitVec.add_zero] using stored 3 (by decide)
    have m4 : source.memaddrs (pointer + 32#64) := by simpa only [(show (4 : Fin 6).val = 4 from rfl), Nat.reduceMul, BitVec.add_zero] using mapped 4 (by decide)
    have s4 : source.memory (pointer + 32#64) = .word (words 4) := by simpa only [(show (4 : Fin 6).val = 4 from rfl), Nat.reduceMul, BitVec.add_zero] using stored 4 (by decide)
    have m5 : source.memaddrs (pointer + 40#64) := by simpa only [(show (5 : Fin 6).val = 5 from rfl), Nat.reduceMul, BitVec.add_zero] using mapped 5 (by decide)
    have s5 : source.memory (pointer + 40#64) = .word (words 5) := by simpa only [(show (5 : Fin 6).val = 5 from rfl), Nat.reduceMul, BitVec.add_zero] using stored 5 (by decide)
    have r0 : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
        (fun address => Classical.propDecidable (source.memaddrs address)) source.be (pointer + 48#64) = some (bytes 0) := loaded 0
    have r1 : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
        (fun address => Classical.propDecidable (source.memaddrs address)) source.be (pointer + 49#64) = some (bytes 1) := loaded 1
    have r2 : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
        (fun address => Classical.propDecidable (source.memaddrs address)) source.be (pointer + 50#64) = some (bytes 2) := loaded 2
    have r3 : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
        (fun address => Classical.propDecidable (source.memaddrs address)) source.be (pointer + 51#64) = some (bytes 3) := loaded 3
    simp [Hash.afterLocals, Hash.body, Guest.guestFn_htab_hash, progToHOL, expToHOL, shapeToHOL,
      evaluateHOLFiniteState_seq, evaluateHOLFiniteState_ite, evaluateHOLFiniteState_assign,
      evaluateHOLFiniteState_return, evalHOLExact, evalListHOLExact, toExact, setVarHOLFinite, setKvarHOLFinite,
      lookupKvarHOLFinite, isValidValueHOLFinite, HolFiniteMapExact.update, FUPDATE,
      p, length, hLocal, wLocal, foldAnd, foldXor, aligned, valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL, wordShiftHOL,
      Flapjack.Compiler.Encoders.Asm.wordCmpHOL, memLoadHOLExact, isWfShapeExactHOL,
      shapeOfHOLExact, shapeEqHOL, fixClockHOLFinite, emptyLocalsHOLFinite, restore, WitnessRadix.QueryBranch.bind,
      resultWord, mixed, tailWord, keySize, wordCount, packedWords, chunkByte, tailBytes,
      Input.WordCodec.word8, Input.WordCodec.word4, BitVec.add_assoc, OrOp.or, BitVec.or_zero, rawAssoc,
      m0, s0, m1, s1, m2, s2, m3, s3, m4, s4, m5, s5, r0, r1, r2, r3,
      show ofString "h" ≠ ofString "w" from by decide,
      show ofString "h" ≠ ofString "p" from by decide,
      show ofString "h" ≠ ofString "key_len" from by decide,
      show ofString "w" ≠ ofString "h" from by decide,
      show ofString "w" ≠ ofString "p" from by decide,
      show ofString "w" ≠ ofString "key_len" from by decide]
    all_goals simp only [HOr.hOr, OrOp.or, rawAssoc]
    all_goals rfl

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
  have foldAnd (a b : BitVec 64) : AndOp.and a (AndOp.and b (18446744073709551615#64)) = a &&& b := by
    change a &&& (b &&& BitVec.allOnes 64) = a &&& b
    rw [BitVec.and_allOnes]
  have foldXor (a b : BitVec 64) : XorOp.xor a (XorOp.xor b 0#64) = a ^^^ b := by
    change a ^^^ (b ^^^ 0#64) = a ^^^ b
    simp
  have rawAssoc (a b c : BitVec 64) : BitVec.or (BitVec.or a b) c = BitVec.or a (BitVec.or b c) := BitVec.or_assoc a b c
  cases kind with
  | address =>
    have r0 : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
        (fun address => Classical.propDecidable (source.memaddrs address)) source.be pointer = some (bytes 0) := by simpa only [(show (0 : Fin 52).val = 0 from rfl), BitVec.add_zero] using loaded 0 (by decide)
    have r1 : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
        (fun address => Classical.propDecidable (source.memaddrs address)) source.be (pointer + 1#64) = some (bytes 1) := by simpa only [(show (1 : Fin 52).val = 1 from rfl), BitVec.add_zero] using loaded 1 (by decide)
    have r2 : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
        (fun address => Classical.propDecidable (source.memaddrs address)) source.be (pointer + 2#64) = some (bytes 2) := by simpa only [(show (2 : Fin 52).val = 2 from rfl), BitVec.add_zero] using loaded 2 (by decide)
    have r3 : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
        (fun address => Classical.propDecidable (source.memaddrs address)) source.be (pointer + 3#64) = some (bytes 3) := by simpa only [(show (3 : Fin 52).val = 3 from rfl), BitVec.add_zero] using loaded 3 (by decide)
    have r4 : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
        (fun address => Classical.propDecidable (source.memaddrs address)) source.be (pointer + 4#64) = some (bytes 4) := by simpa only [(show (4 : Fin 52).val = 4 from rfl), BitVec.add_zero] using loaded 4 (by decide)
    have r5 : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
        (fun address => Classical.propDecidable (source.memaddrs address)) source.be (pointer + 5#64) = some (bytes 5) := by simpa only [(show (5 : Fin 52).val = 5 from rfl), BitVec.add_zero] using loaded 5 (by decide)
    have r6 : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
        (fun address => Classical.propDecidable (source.memaddrs address)) source.be (pointer + 6#64) = some (bytes 6) := by simpa only [(show (6 : Fin 52).val = 6 from rfl), BitVec.add_zero] using loaded 6 (by decide)
    have r7 : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
        (fun address => Classical.propDecidable (source.memaddrs address)) source.be (pointer + 7#64) = some (bytes 7) := by simpa only [(show (7 : Fin 52).val = 7 from rfl), BitVec.add_zero] using loaded 7 (by decide)
    have r8 : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
        (fun address => Classical.propDecidable (source.memaddrs address)) source.be (pointer + 8#64) = some (bytes 8) := by simpa only [(show (8 : Fin 52).val = 8 from rfl), BitVec.add_zero] using loaded 8 (by decide)
    have r9 : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
        (fun address => Classical.propDecidable (source.memaddrs address)) source.be (pointer + 9#64) = some (bytes 9) := by simpa only [(show (9 : Fin 52).val = 9 from rfl), BitVec.add_zero] using loaded 9 (by decide)
    have r10 : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
        (fun address => Classical.propDecidable (source.memaddrs address)) source.be (pointer + 10#64) = some (bytes 10) := by simpa only [(show (10 : Fin 52).val = 10 from rfl), BitVec.add_zero] using loaded 10 (by decide)
    have r11 : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
        (fun address => Classical.propDecidable (source.memaddrs address)) source.be (pointer + 11#64) = some (bytes 11) := by simpa only [(show (11 : Fin 52).val = 11 from rfl), BitVec.add_zero] using loaded 11 (by decide)
    have r12 : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
        (fun address => Classical.propDecidable (source.memaddrs address)) source.be (pointer + 12#64) = some (bytes 12) := by simpa only [(show (12 : Fin 52).val = 12 from rfl), BitVec.add_zero] using loaded 12 (by decide)
    have r13 : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
        (fun address => Classical.propDecidable (source.memaddrs address)) source.be (pointer + 13#64) = some (bytes 13) := by simpa only [(show (13 : Fin 52).val = 13 from rfl), BitVec.add_zero] using loaded 13 (by decide)
    have r14 : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
        (fun address => Classical.propDecidable (source.memaddrs address)) source.be (pointer + 14#64) = some (bytes 14) := by simpa only [(show (14 : Fin 52).val = 14 from rfl), BitVec.add_zero] using loaded 14 (by decide)
    have r15 : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
        (fun address => Classical.propDecidable (source.memaddrs address)) source.be (pointer + 15#64) = some (bytes 15) := by simpa only [(show (15 : Fin 52).val = 15 from rfl), BitVec.add_zero] using loaded 15 (by decide)
    have r16 : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
        (fun address => Classical.propDecidable (source.memaddrs address)) source.be (pointer + 16#64) = some (bytes 16) := by simpa only [(show (16 : Fin 52).val = 16 from rfl), BitVec.add_zero] using loaded 16 (by decide)
    have r17 : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
        (fun address => Classical.propDecidable (source.memaddrs address)) source.be (pointer + 17#64) = some (bytes 17) := by simpa only [(show (17 : Fin 52).val = 17 from rfl), BitVec.add_zero] using loaded 17 (by decide)
    have r18 : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
        (fun address => Classical.propDecidable (source.memaddrs address)) source.be (pointer + 18#64) = some (bytes 18) := by simpa only [(show (18 : Fin 52).val = 18 from rfl), BitVec.add_zero] using loaded 18 (by decide)
    have r19 : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
        (fun address => Classical.propDecidable (source.memaddrs address)) source.be (pointer + 19#64) = some (bytes 19) := by simpa only [(show (19 : Fin 52).val = 19 from rfl), BitVec.add_zero] using loaded 19 (by decide)
    simp [Hash.afterLocals, Hash.body, Guest.guestFn_htab_hash, progToHOL, expToHOL, shapeToHOL,
      evaluateHOLFiniteState_seq, evaluateHOLFiniteState_ite, evaluateHOLFiniteState_assign,
      evaluateHOLFiniteState_return, evalHOLExact, evalListHOLExact, toExact, setVarHOLFinite, setKvarHOLFinite,
      lookupKvarHOLFinite, isValidValueHOLFinite, HolFiniteMapExact.update, FUPDATE,
      p, length, hLocal, wLocal, foldAnd, foldXor, unaligned, valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL, wordShiftHOL,
      Flapjack.Compiler.Encoders.Asm.wordCmpHOL, memLoadHOLExact, isWfShapeExactHOL,
      shapeOfHOLExact, shapeEqHOL, fixClockHOLFinite, emptyLocalsHOLFinite, restore, WitnessRadix.QueryBranch.bind,
      resultWord, mixed, tailWord, keySize, wordCount, packedWords, chunkByte, tailBytes,
      Input.WordCodec.word8, Input.WordCodec.word4, BitVec.add_assoc, OrOp.or, BitVec.or_zero, rawAssoc,
      r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19,
      show ofString "h" ≠ ofString "w" from by decide,
      show ofString "h" ≠ ofString "p" from by decide,
      show ofString "h" ≠ ofString "key_len" from by decide,
      show ofString "w" ≠ ofString "h" from by decide,
      show ofString "w" ≠ ofString "p" from by decide,
      show ofString "w" ≠ ofString "key_len" from by decide]
    all_goals simp only [HOr.hOr, OrOp.or, rawAssoc]
    all_goals rfl
  | storage =>
    have r0 : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
        (fun address => Classical.propDecidable (source.memaddrs address)) source.be pointer = some (bytes 0) := by simpa only [(show (0 : Fin 52).val = 0 from rfl), BitVec.add_zero] using loaded 0 (by decide)
    have r1 : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
        (fun address => Classical.propDecidable (source.memaddrs address)) source.be (pointer + 1#64) = some (bytes 1) := by simpa only [(show (1 : Fin 52).val = 1 from rfl), BitVec.add_zero] using loaded 1 (by decide)
    have r2 : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
        (fun address => Classical.propDecidable (source.memaddrs address)) source.be (pointer + 2#64) = some (bytes 2) := by simpa only [(show (2 : Fin 52).val = 2 from rfl), BitVec.add_zero] using loaded 2 (by decide)
    have r3 : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
        (fun address => Classical.propDecidable (source.memaddrs address)) source.be (pointer + 3#64) = some (bytes 3) := by simpa only [(show (3 : Fin 52).val = 3 from rfl), BitVec.add_zero] using loaded 3 (by decide)
    have r4 : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
        (fun address => Classical.propDecidable (source.memaddrs address)) source.be (pointer + 4#64) = some (bytes 4) := by simpa only [(show (4 : Fin 52).val = 4 from rfl), BitVec.add_zero] using loaded 4 (by decide)
    have r5 : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
        (fun address => Classical.propDecidable (source.memaddrs address)) source.be (pointer + 5#64) = some (bytes 5) := by simpa only [(show (5 : Fin 52).val = 5 from rfl), BitVec.add_zero] using loaded 5 (by decide)
    have r6 : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
        (fun address => Classical.propDecidable (source.memaddrs address)) source.be (pointer + 6#64) = some (bytes 6) := by simpa only [(show (6 : Fin 52).val = 6 from rfl), BitVec.add_zero] using loaded 6 (by decide)
    have r7 : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
        (fun address => Classical.propDecidable (source.memaddrs address)) source.be (pointer + 7#64) = some (bytes 7) := by simpa only [(show (7 : Fin 52).val = 7 from rfl), BitVec.add_zero] using loaded 7 (by decide)
    have r8 : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
        (fun address => Classical.propDecidable (source.memaddrs address)) source.be (pointer + 8#64) = some (bytes 8) := by simpa only [(show (8 : Fin 52).val = 8 from rfl), BitVec.add_zero] using loaded 8 (by decide)
    have r9 : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
        (fun address => Classical.propDecidable (source.memaddrs address)) source.be (pointer + 9#64) = some (bytes 9) := by simpa only [(show (9 : Fin 52).val = 9 from rfl), BitVec.add_zero] using loaded 9 (by decide)
    have r10 : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
        (fun address => Classical.propDecidable (source.memaddrs address)) source.be (pointer + 10#64) = some (bytes 10) := by simpa only [(show (10 : Fin 52).val = 10 from rfl), BitVec.add_zero] using loaded 10 (by decide)
    have r11 : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
        (fun address => Classical.propDecidable (source.memaddrs address)) source.be (pointer + 11#64) = some (bytes 11) := by simpa only [(show (11 : Fin 52).val = 11 from rfl), BitVec.add_zero] using loaded 11 (by decide)
    have r12 : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
        (fun address => Classical.propDecidable (source.memaddrs address)) source.be (pointer + 12#64) = some (bytes 12) := by simpa only [(show (12 : Fin 52).val = 12 from rfl), BitVec.add_zero] using loaded 12 (by decide)
    have r13 : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
        (fun address => Classical.propDecidable (source.memaddrs address)) source.be (pointer + 13#64) = some (bytes 13) := by simpa only [(show (13 : Fin 52).val = 13 from rfl), BitVec.add_zero] using loaded 13 (by decide)
    have r14 : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
        (fun address => Classical.propDecidable (source.memaddrs address)) source.be (pointer + 14#64) = some (bytes 14) := by simpa only [(show (14 : Fin 52).val = 14 from rfl), BitVec.add_zero] using loaded 14 (by decide)
    have r15 : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
        (fun address => Classical.propDecidable (source.memaddrs address)) source.be (pointer + 15#64) = some (bytes 15) := by simpa only [(show (15 : Fin 52).val = 15 from rfl), BitVec.add_zero] using loaded 15 (by decide)
    have r16 : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
        (fun address => Classical.propDecidable (source.memaddrs address)) source.be (pointer + 16#64) = some (bytes 16) := by simpa only [(show (16 : Fin 52).val = 16 from rfl), BitVec.add_zero] using loaded 16 (by decide)
    have r17 : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
        (fun address => Classical.propDecidable (source.memaddrs address)) source.be (pointer + 17#64) = some (bytes 17) := by simpa only [(show (17 : Fin 52).val = 17 from rfl), BitVec.add_zero] using loaded 17 (by decide)
    have r18 : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
        (fun address => Classical.propDecidable (source.memaddrs address)) source.be (pointer + 18#64) = some (bytes 18) := by simpa only [(show (18 : Fin 52).val = 18 from rfl), BitVec.add_zero] using loaded 18 (by decide)
    have r19 : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
        (fun address => Classical.propDecidable (source.memaddrs address)) source.be (pointer + 19#64) = some (bytes 19) := by simpa only [(show (19 : Fin 52).val = 19 from rfl), BitVec.add_zero] using loaded 19 (by decide)
    have r20 : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
        (fun address => Classical.propDecidable (source.memaddrs address)) source.be (pointer + 20#64) = some (bytes 20) := by simpa only [(show (20 : Fin 52).val = 20 from rfl), BitVec.add_zero] using loaded 20 (by decide)
    have r21 : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
        (fun address => Classical.propDecidable (source.memaddrs address)) source.be (pointer + 21#64) = some (bytes 21) := by simpa only [(show (21 : Fin 52).val = 21 from rfl), BitVec.add_zero] using loaded 21 (by decide)
    have r22 : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
        (fun address => Classical.propDecidable (source.memaddrs address)) source.be (pointer + 22#64) = some (bytes 22) := by simpa only [(show (22 : Fin 52).val = 22 from rfl), BitVec.add_zero] using loaded 22 (by decide)
    have r23 : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
        (fun address => Classical.propDecidable (source.memaddrs address)) source.be (pointer + 23#64) = some (bytes 23) := by simpa only [(show (23 : Fin 52).val = 23 from rfl), BitVec.add_zero] using loaded 23 (by decide)
    have r24 : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
        (fun address => Classical.propDecidable (source.memaddrs address)) source.be (pointer + 24#64) = some (bytes 24) := by simpa only [(show (24 : Fin 52).val = 24 from rfl), BitVec.add_zero] using loaded 24 (by decide)
    have r25 : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
        (fun address => Classical.propDecidable (source.memaddrs address)) source.be (pointer + 25#64) = some (bytes 25) := by simpa only [(show (25 : Fin 52).val = 25 from rfl), BitVec.add_zero] using loaded 25 (by decide)
    have r26 : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
        (fun address => Classical.propDecidable (source.memaddrs address)) source.be (pointer + 26#64) = some (bytes 26) := by simpa only [(show (26 : Fin 52).val = 26 from rfl), BitVec.add_zero] using loaded 26 (by decide)
    have r27 : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
        (fun address => Classical.propDecidable (source.memaddrs address)) source.be (pointer + 27#64) = some (bytes 27) := by simpa only [(show (27 : Fin 52).val = 27 from rfl), BitVec.add_zero] using loaded 27 (by decide)
    have r28 : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
        (fun address => Classical.propDecidable (source.memaddrs address)) source.be (pointer + 28#64) = some (bytes 28) := by simpa only [(show (28 : Fin 52).val = 28 from rfl), BitVec.add_zero] using loaded 28 (by decide)
    have r29 : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
        (fun address => Classical.propDecidable (source.memaddrs address)) source.be (pointer + 29#64) = some (bytes 29) := by simpa only [(show (29 : Fin 52).val = 29 from rfl), BitVec.add_zero] using loaded 29 (by decide)
    have r30 : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
        (fun address => Classical.propDecidable (source.memaddrs address)) source.be (pointer + 30#64) = some (bytes 30) := by simpa only [(show (30 : Fin 52).val = 30 from rfl), BitVec.add_zero] using loaded 30 (by decide)
    have r31 : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
        (fun address => Classical.propDecidable (source.memaddrs address)) source.be (pointer + 31#64) = some (bytes 31) := by simpa only [(show (31 : Fin 52).val = 31 from rfl), BitVec.add_zero] using loaded 31 (by decide)
    have r32 : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
        (fun address => Classical.propDecidable (source.memaddrs address)) source.be (pointer + 32#64) = some (bytes 32) := by simpa only [(show (32 : Fin 52).val = 32 from rfl), BitVec.add_zero] using loaded 32 (by decide)
    have r33 : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
        (fun address => Classical.propDecidable (source.memaddrs address)) source.be (pointer + 33#64) = some (bytes 33) := by simpa only [(show (33 : Fin 52).val = 33 from rfl), BitVec.add_zero] using loaded 33 (by decide)
    have r34 : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
        (fun address => Classical.propDecidable (source.memaddrs address)) source.be (pointer + 34#64) = some (bytes 34) := by simpa only [(show (34 : Fin 52).val = 34 from rfl), BitVec.add_zero] using loaded 34 (by decide)
    have r35 : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
        (fun address => Classical.propDecidable (source.memaddrs address)) source.be (pointer + 35#64) = some (bytes 35) := by simpa only [(show (35 : Fin 52).val = 35 from rfl), BitVec.add_zero] using loaded 35 (by decide)
    have r36 : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
        (fun address => Classical.propDecidable (source.memaddrs address)) source.be (pointer + 36#64) = some (bytes 36) := by simpa only [(show (36 : Fin 52).val = 36 from rfl), BitVec.add_zero] using loaded 36 (by decide)
    have r37 : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
        (fun address => Classical.propDecidable (source.memaddrs address)) source.be (pointer + 37#64) = some (bytes 37) := by simpa only [(show (37 : Fin 52).val = 37 from rfl), BitVec.add_zero] using loaded 37 (by decide)
    have r38 : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
        (fun address => Classical.propDecidable (source.memaddrs address)) source.be (pointer + 38#64) = some (bytes 38) := by simpa only [(show (38 : Fin 52).val = 38 from rfl), BitVec.add_zero] using loaded 38 (by decide)
    have r39 : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
        (fun address => Classical.propDecidable (source.memaddrs address)) source.be (pointer + 39#64) = some (bytes 39) := by simpa only [(show (39 : Fin 52).val = 39 from rfl), BitVec.add_zero] using loaded 39 (by decide)
    have r40 : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
        (fun address => Classical.propDecidable (source.memaddrs address)) source.be (pointer + 40#64) = some (bytes 40) := by simpa only [(show (40 : Fin 52).val = 40 from rfl), BitVec.add_zero] using loaded 40 (by decide)
    have r41 : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
        (fun address => Classical.propDecidable (source.memaddrs address)) source.be (pointer + 41#64) = some (bytes 41) := by simpa only [(show (41 : Fin 52).val = 41 from rfl), BitVec.add_zero] using loaded 41 (by decide)
    have r42 : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
        (fun address => Classical.propDecidable (source.memaddrs address)) source.be (pointer + 42#64) = some (bytes 42) := by simpa only [(show (42 : Fin 52).val = 42 from rfl), BitVec.add_zero] using loaded 42 (by decide)
    have r43 : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
        (fun address => Classical.propDecidable (source.memaddrs address)) source.be (pointer + 43#64) = some (bytes 43) := by simpa only [(show (43 : Fin 52).val = 43 from rfl), BitVec.add_zero] using loaded 43 (by decide)
    have r44 : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
        (fun address => Classical.propDecidable (source.memaddrs address)) source.be (pointer + 44#64) = some (bytes 44) := by simpa only [(show (44 : Fin 52).val = 44 from rfl), BitVec.add_zero] using loaded 44 (by decide)
    have r45 : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
        (fun address => Classical.propDecidable (source.memaddrs address)) source.be (pointer + 45#64) = some (bytes 45) := by simpa only [(show (45 : Fin 52).val = 45 from rfl), BitVec.add_zero] using loaded 45 (by decide)
    have r46 : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
        (fun address => Classical.propDecidable (source.memaddrs address)) source.be (pointer + 46#64) = some (bytes 46) := by simpa only [(show (46 : Fin 52).val = 46 from rfl), BitVec.add_zero] using loaded 46 (by decide)
    have r47 : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
        (fun address => Classical.propDecidable (source.memaddrs address)) source.be (pointer + 47#64) = some (bytes 47) := by simpa only [(show (47 : Fin 52).val = 47 from rfl), BitVec.add_zero] using loaded 47 (by decide)
    have r48 : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
        (fun address => Classical.propDecidable (source.memaddrs address)) source.be (pointer + 48#64) = some (bytes 48) := by simpa only [(show (48 : Fin 52).val = 48 from rfl), BitVec.add_zero] using loaded 48 (by decide)
    have r49 : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
        (fun address => Classical.propDecidable (source.memaddrs address)) source.be (pointer + 49#64) = some (bytes 49) := by simpa only [(show (49 : Fin 52).val = 49 from rfl), BitVec.add_zero] using loaded 49 (by decide)
    have r50 : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
        (fun address => Classical.propDecidable (source.memaddrs address)) source.be (pointer + 50#64) = some (bytes 50) := by simpa only [(show (50 : Fin 52).val = 50 from rfl), BitVec.add_zero] using loaded 50 (by decide)
    have r51 : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
        (fun address => Classical.propDecidable (source.memaddrs address)) source.be (pointer + 51#64) = some (bytes 51) := by simpa only [(show (51 : Fin 52).val = 51 from rfl), BitVec.add_zero] using loaded 51 (by decide)
    simp [Hash.afterLocals, Hash.body, Guest.guestFn_htab_hash, progToHOL, expToHOL, shapeToHOL,
      evaluateHOLFiniteState_seq, evaluateHOLFiniteState_ite, evaluateHOLFiniteState_assign,
      evaluateHOLFiniteState_return, evalHOLExact, evalListHOLExact, toExact, setVarHOLFinite, setKvarHOLFinite,
      lookupKvarHOLFinite, isValidValueHOLFinite, HolFiniteMapExact.update, FUPDATE,
      p, length, hLocal, wLocal, foldAnd, foldXor, unaligned, valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL, wordShiftHOL,
      Flapjack.Compiler.Encoders.Asm.wordCmpHOL, memLoadHOLExact, isWfShapeExactHOL,
      shapeOfHOLExact, shapeEqHOL, fixClockHOLFinite, emptyLocalsHOLFinite, restore, WitnessRadix.QueryBranch.bind,
      resultWord, mixed, tailWord, keySize, wordCount, packedWords, chunkByte, tailBytes,
      Input.WordCodec.word8, Input.WordCodec.word4, BitVec.add_assoc, OrOp.or, BitVec.or_zero, rawAssoc,
      r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51,
      show ofString "h" ≠ ofString "w" from by decide,
      show ofString "h" ≠ ofString "p" from by decide,
      show ofString "h" ≠ ofString "key_len" from by decide,
      show ofString "w" ≠ ofString "h" from by decide,
      show ofString "w" ≠ ofString "p" from by decide,
      show ofString "w" ≠ ofString "key_len" from by decide]
    all_goals simp only [HOr.hOr, OrOp.or, rawAssoc]
    all_goals rfl

end InitECandidate.Solver.MutableTable.HashSized

#print axioms InitECandidate.Solver.MutableTable.HashSized.aligned_core
#print axioms InitECandidate.Solver.MutableTable.HashSized.unaligned_core
