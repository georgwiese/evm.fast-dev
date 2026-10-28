import InitECandidate.Solver.CurrentKeccak.HashSyntax

namespace InitECandidate.Solver.CurrentKeccak.Hash
open Flapjack Flapjack.Pancake.PanLang
open WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def pad : ExpHOL 64 := .var .global (ofString "keccak_pad")
def remainder : ExpHOL 64 := .op .sub [localVar "n",localVar "i"]
def zeroPad : ProgHOL 64 := .call (some (none,none)) (ofString "memzero") [pad,.const 136#64]
def copyPad : ProgHOL 64 := .call (some (none,none)) (ofString "memcpy") [pad,.op .add [localVar "p",localVar "i"],localVar "rem"]
def padFirst : ProgHOL 64 := .storeByte (.op .add [pad,localVar "rem"]) (.const 1#64)
def padLastAddress : ExpHOL 64 := .op .add [pad,.const 135#64]
def padLast : ProgHOL 64 := .storeByte padLastAddress (.op .or [.loadByte padLastAddress,.const 128#64])
def absorbPad : ProgHOL 64 := .call (some (none,none)) (ofString "keccak_absorb_block") [localVar "stp",pad]
def outAlignment : ExpHOL 64 := .cmp .equal (.op .and [localVar "out",.const 7#64]) (.const 0#64)
def outAddress (name : String) (offset : Nat) : ExpHOL 64 :=
  if offset=0 then localVar name else addConst (localVar name) (BitVec.ofNat 64 offset)
def outStore (offset : Nat) : ProgHOL 64 := .store (outAddress "out" offset) (.load .one (outAddress "stp" offset))
def outWords : ProgHOL 64 := .seq (outStore 0) (.seq (outStore 8) (.seq (outStore 16) (outStore 24)))
def outCopy : ProgHOL 64 := .call (some (none,none)) (ofString "memcpy") [localVar "out",localVar "stp",.const 32#64]
def outProgram : ProgHOL 64 := .ite outAlignment outWords outCopy

def paddingTail : ProgHOL 64 := .seq zeroPad (.seq copyPad (.seq padFirst (.seq padLast (.seq absorbPad
  (.seq outProgram (.return (.const 0#64)))))))

theorem afterBlocks_shape : afterBlocks=.dec (ofString "rem") .one remainder paddingTail := by
  simp only [afterBlocks,body,Guest.Software.guestFn_keccak256,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,
    remainder,paddingTail,zeroPad,copyPad,padFirst,padLast,padLastAddress,absorbPad,outProgram,outAlignment,
    outWords,outStore,outAddress,outCopy,pad,localVar,addConst,↓reduceIte]
  rfl

end InitECandidate.Solver.CurrentKeccak.Hash

#print axioms InitECandidate.Solver.CurrentKeccak.Hash.afterBlocks_shape
