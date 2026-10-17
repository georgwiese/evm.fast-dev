import InitECandidate.Solver.MutableTable.HashCall32
import InitECandidate.Solver.Input.Scalar64

namespace InitECandidate.Solver.MutableTable.Hash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def chunkByte (bytes : Fin 32→UInt8) (block : Fin 4) (byte : Fin 8) : BitVec 64:=
  BitVec.ofNat 64 (bytes ⟨8*block.val+byte.val,by have h:=block.isLt;have k:=byte.isLt;omega⟩).toNat

def packedWords (bytes : Fin 32→UInt8) (block : Fin 4) : BitVec 64:=
  Input.WordCodec.word8 (chunkByte bytes block 0) (chunkByte bytes block 1) (chunkByte bytes block 2) (chunkByte bytes block 3)
    (chunkByte bytes block 4) (chunkByte bytes block 5) (chunkByte bytes block 6) (chunkByte bytes block 7)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
/-- Actual unaligned32-byte hash path, including all32 byte loads, shifts and
folds, from real initial bytes. No body clock or memory write is performed. -/
theorem unaligned32_core (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (bytes : Fin 32→UInt8)
    (p : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (length : source.locals.lookup (ofString "key_len")=some (.val (.word 32#64)))
    (hLocal : source.locals.lookup (ofString "h")=some (.val (.word 14695981039346656037#64)))
    (wLocal : source.locals.lookup (ofString "w")=some (.val (.word 0#64)))
    (unaligned : pointer &&& 7#64≠0#64)
    (loaded : ∀ index : Fin 32,@panMemLoadByteHOL 64 _ source.memory source.memaddrs
      (fun address=>Classical.propDecidable (source.memaddrs address)) source.be
      (pointer+BitVec.ofNat 64 index.val)=some (bytes index)) :
    evaluateHOLFiniteState source afterLocals=(some (.returned (.val (.word (resultWord (packedWords bytes))))),emptyLocalsHOLFinite source) := by
  classical
  have foldAnd (a b : BitVec 64) : AndOp.and a (AndOp.and b (18446744073709551615#64))=a &&& b := by
    change a &&& (b &&& BitVec.allOnes 64)=a &&& b
    rw [BitVec.and_allOnes]
  have foldXor (a b : BitVec 64) : XorOp.xor a (XorOp.xor b 0#64)=a ^^^ b := by
    change a ^^^ (b ^^^ 0#64)=a ^^^ b
    simp
  have r0 : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
      (fun address=>Classical.propDecidable (source.memaddrs address)) source.be pointer=some (bytes 0):=by simpa using loaded 0
  have r1 : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
      (fun address=>Classical.propDecidable (source.memaddrs address)) source.be (pointer+1#64)=some (bytes 1):=loaded 1
  have r2 : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
      (fun address=>Classical.propDecidable (source.memaddrs address)) source.be (pointer+2#64)=some (bytes 2):=loaded 2
  have r3 : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
      (fun address=>Classical.propDecidable (source.memaddrs address)) source.be (pointer+3#64)=some (bytes 3):=loaded 3
  have r4 : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
      (fun address=>Classical.propDecidable (source.memaddrs address)) source.be (pointer+4#64)=some (bytes 4):=loaded 4
  have r5 : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
      (fun address=>Classical.propDecidable (source.memaddrs address)) source.be (pointer+5#64)=some (bytes 5):=loaded 5
  have r6 : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
      (fun address=>Classical.propDecidable (source.memaddrs address)) source.be (pointer+6#64)=some (bytes 6):=loaded 6
  have r7 : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
      (fun address=>Classical.propDecidable (source.memaddrs address)) source.be (pointer+7#64)=some (bytes 7):=loaded 7
  have r8 : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
      (fun address=>Classical.propDecidable (source.memaddrs address)) source.be (pointer+8#64)=some (bytes 8):=loaded 8
  have r9 : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
      (fun address=>Classical.propDecidable (source.memaddrs address)) source.be (pointer+9#64)=some (bytes 9):=loaded 9
  have r10 : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
      (fun address=>Classical.propDecidable (source.memaddrs address)) source.be (pointer+10#64)=some (bytes 10):=loaded 10
  have r11 : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
      (fun address=>Classical.propDecidable (source.memaddrs address)) source.be (pointer+11#64)=some (bytes 11):=loaded 11
  have r12 : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
      (fun address=>Classical.propDecidable (source.memaddrs address)) source.be (pointer+12#64)=some (bytes 12):=loaded 12
  have r13 : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
      (fun address=>Classical.propDecidable (source.memaddrs address)) source.be (pointer+13#64)=some (bytes 13):=loaded 13
  have r14 : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
      (fun address=>Classical.propDecidable (source.memaddrs address)) source.be (pointer+14#64)=some (bytes 14):=loaded 14
  have r15 : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
      (fun address=>Classical.propDecidable (source.memaddrs address)) source.be (pointer+15#64)=some (bytes 15):=loaded 15
  have r16 : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
      (fun address=>Classical.propDecidable (source.memaddrs address)) source.be (pointer+16#64)=some (bytes 16):=loaded 16
  have r17 : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
      (fun address=>Classical.propDecidable (source.memaddrs address)) source.be (pointer+17#64)=some (bytes 17):=loaded 17
  have r18 : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
      (fun address=>Classical.propDecidable (source.memaddrs address)) source.be (pointer+18#64)=some (bytes 18):=loaded 18
  have r19 : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
      (fun address=>Classical.propDecidable (source.memaddrs address)) source.be (pointer+19#64)=some (bytes 19):=loaded 19
  have r20 : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
      (fun address=>Classical.propDecidable (source.memaddrs address)) source.be (pointer+20#64)=some (bytes 20):=loaded 20
  have r21 : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
      (fun address=>Classical.propDecidable (source.memaddrs address)) source.be (pointer+21#64)=some (bytes 21):=loaded 21
  have r22 : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
      (fun address=>Classical.propDecidable (source.memaddrs address)) source.be (pointer+22#64)=some (bytes 22):=loaded 22
  have r23 : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
      (fun address=>Classical.propDecidable (source.memaddrs address)) source.be (pointer+23#64)=some (bytes 23):=loaded 23
  have r24 : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
      (fun address=>Classical.propDecidable (source.memaddrs address)) source.be (pointer+24#64)=some (bytes 24):=loaded 24
  have r25 : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
      (fun address=>Classical.propDecidable (source.memaddrs address)) source.be (pointer+25#64)=some (bytes 25):=loaded 25
  have r26 : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
      (fun address=>Classical.propDecidable (source.memaddrs address)) source.be (pointer+26#64)=some (bytes 26):=loaded 26
  have r27 : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
      (fun address=>Classical.propDecidable (source.memaddrs address)) source.be (pointer+27#64)=some (bytes 27):=loaded 27
  have r28 : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
      (fun address=>Classical.propDecidable (source.memaddrs address)) source.be (pointer+28#64)=some (bytes 28):=loaded 28
  have r29 : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
      (fun address=>Classical.propDecidable (source.memaddrs address)) source.be (pointer+29#64)=some (bytes 29):=loaded 29
  have r30 : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
      (fun address=>Classical.propDecidable (source.memaddrs address)) source.be (pointer+30#64)=some (bytes 30):=loaded 30
  have r31 : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
      (fun address=>Classical.propDecidable (source.memaddrs address)) source.be (pointer+31#64)=some (bytes 31):=loaded 31
  have rawAssoc (a b c : BitVec 64) : BitVec.or (BitVec.or a b) c=BitVec.or a (BitVec.or b c):=BitVec.or_assoc a b c
  simp [afterLocals,body,Guest.guestFn_htab_hash,progToHOL,expToHOL,shapeToHOL,
    evaluateHOLFiniteState_seq,evaluateHOLFiniteState_ite,evaluateHOLFiniteState_assign,
    evaluateHOLFiniteState_return,evalHOLExact,evalListHOLExact,toExact,setVarHOLFinite,setKvarHOLFinite,
    lookupKvarHOLFinite,isValidValueHOLFinite,HolFiniteMapExact.update,FUPDATE,
    p,length,hLocal,wLocal,foldAnd,foldXor,unaligned,valueIsWord,valueWord,wordOpHOL,wordOp,panOpHOL,wordShiftHOL,
    Flapjack.Compiler.Encoders.Asm.wordCmpHOL,shapeOfHOLExact,shapeEqHOL,fixClockHOLFinite,emptyLocalsHOLFinite,
    restore,WitnessRadix.QueryBranch.bind,resultWord,mixed,packedWords,chunkByte,Input.WordCodec.word8,Input.WordCodec.word4,
    BitVec.add_assoc,OrOp.or,BitVec.or_zero,rawAssoc,
    r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,
    show ofString "h"≠ofString "w" from by decide,
    show ofString "h"≠ofString "p" from by decide,
    show ofString "h"≠ofString "key_len" from by decide,
    show ofString "w"≠ofString "h" from by decide,
    show ofString "w"≠ofString "p" from by decide,
    show ofString "w"≠ofString "key_len" from by decide]
  all_goals simp only [HOr.hOr,OrOp.or,rawAssoc]
  all_goals rfl

end InitECandidate.Solver.MutableTable.Hash

#print axioms InitECandidate.Solver.MutableTable.Hash.unaligned32_core
