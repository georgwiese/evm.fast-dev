import InitECandidate.Solver.MutableTable.MaskedPath

namespace InitECandidate.Solver.MutableTable.Hash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def body : ProgHOL 64:=match Guest.guestFn_htab_hash with | .function fn=>progToHOL fn.body | _=>.skip
def formals : List (MlS×ShapeHOL):=[(ofString "p",.one),(ofString "key_len",.one)]
def mixed (words : Fin 4→BitVec 64) : BitVec 64:=
  (((14695981039346656037#64 ^^^ words 0) ^^^ words 1) ^^^ words 2) ^^^ words 3
def resultWord (words : Fin 4→BitVec 64) : BitVec 64:=
  let h:=(mixed words ^^^ (mixed words >>> (32 : Nat)))*1099511628211#64
  h ^^^ (h >>> (29 : Nat))

def afterLocals : ProgHOL 64:=match body with | .dec _ _ _ (.dec _ _ _ tail)=>tail | _=>.skip

theorem body_shape : body=.dec (ofString "h") .one (.const 14695981039346656037#64)
    (.dec (ofString "w") .one (.const 0#64) afterLocals) := by
  simp only [body,afterLocals,Guest.guestFn_htab_hash,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
/-- The actual aligned32-byte hash path is pure and uses no body clocks. -/
theorem aligned32_core (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (words : Fin 4→BitVec 64)
    (p : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (length : source.locals.lookup (ofString "key_len")=some (.val (.word 32#64)))
    (hLocal : source.locals.lookup (ofString "h")=some (.val (.word 14695981039346656037#64)))
    (wLocal : source.locals.lookup (ofString "w")=some (.val (.word 0#64)))
    (aligned : pointer &&& 7#64=0#64)
    (mapped : ∀ i : Fin 4,source.memaddrs (pointer+BitVec.ofNat 64 (8*i.val)))
    (stored : ∀ i : Fin 4,source.memory (pointer+BitVec.ofNat 64 (8*i.val))=.word (words i)) :
    evaluateHOLFiniteState source afterLocals=(some (.returned (.val (.word (resultWord words)))),emptyLocalsHOLFinite source) := by
  classical
  have foldAnd (a b : BitVec 64) : AndOp.and a (AndOp.and b (18446744073709551615#64))=a &&& b := by
    change a &&& (b &&& BitVec.allOnes 64)=a &&& b
    rw [BitVec.and_allOnes]
  have foldXor (a b : BitVec 64) : XorOp.xor a (XorOp.xor b 0#64)=a ^^^ b := by
    change a ^^^ (b ^^^ 0#64)=a ^^^ b
    simp
  have m0 : source.memaddrs pointer:=by simpa using mapped 0
  have m1 : source.memaddrs (pointer+8#64):=mapped 1
  have m2 : source.memaddrs (pointer+16#64):=mapped 2
  have m3 : source.memaddrs (pointer+24#64):=mapped 3
  have s0 : source.memory pointer=.word (words 0):=by simpa using stored 0
  have s1 : source.memory (pointer+8#64)=.word (words 1):=stored 1
  have s2 : source.memory (pointer+16#64)=.word (words 2):=stored 2
  have s3 : source.memory (pointer+24#64)=.word (words 3):=stored 3
  simp [afterLocals,body,Guest.guestFn_htab_hash,progToHOL,expToHOL,shapeToHOL,
    evaluateHOLFiniteState_seq,evaluateHOLFiniteState_ite,evaluateHOLFiniteState_assign,
    evaluateHOLFiniteState_return,evalHOLExact,evalListHOLExact,toExact,setVarHOLFinite,setKvarHOLFinite,
    lookupKvarHOLFinite,isValidValueHOLFinite,HolFiniteMapExact.update,FUPDATE,
    p,length,hLocal,wLocal,foldAnd,foldXor,aligned,valueIsWord,valueWord,wordOpHOL,wordOp,panOpHOL,wordShiftHOL,
    Flapjack.Compiler.Encoders.Asm.wordCmpHOL,memLoadHOLExact,isWfShapeExactHOL,m0,m1,m2,m3,s0,s1,s2,s3,
    shapeOfHOLExact,shapeEqHOL,fixClockHOLFinite,emptyLocalsHOLFinite,restore,WitnessRadix.QueryBranch.bind,resultWord,mixed,
    show ofString "h"≠ofString "w" from by decide,
    show ofString "h"≠ofString "p" from by decide,
    show ofString "h"≠ofString "key_len" from by decide,
    show ofString "w"≠ofString "h" from by decide,
    show ofString "w"≠ofString "p" from by decide,
    show ofString "w"≠ofString "key_len" from by decide]

end InitECandidate.Solver.MutableTable.Hash

#print axioms InitECandidate.Solver.MutableTable.Hash.aligned32_core
