import InitECandidate.Solver.CurrentKeccak.PermutationSyntax

namespace InitECandidate.Solver.CurrentKeccak.Absorb
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open WitnessRadix
open Flapjack.Basis.Pure.MlString Input WitnessRadix.QueryBranch

def increment : ProgHOL 64 := .assign .local (ofString "i") (.op .add [localVar "i",.const 8#64])

def body : ProgHOL 64 := match Guest.Software.guestFn_keccak_absorb_block with | .function fn => progToHOL fn.body | _ => .skip
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
  (increment)
def condition : ExpHOL 64 := .cmp .less (localVar "i") (.const 136#64)
def alignment : ExpHOL 64 := .cmp .equal (.op .and [localVar "blk", .const 7#64]) (.const 0#64)
def loop (unaligned : Bool) : ProgHOL 64 := .while condition (laneBody unaligned)
def tail : ProgHOL 64 := .seq (.call (some (none, none)) (ofString "keccak_f1600") [localVar "stp"]) (.return (.const 0#64))

theorem body_shape : body = .dec (ofString "i") .one (.const 0#64)
    (.seq (.ite alignment (loop false) (loop true)) tail) := by
  simp only [body, Guest.Software.guestFn_keccak_absorb_block, progToHOL, expToHOL, shapeToHOL,
    List.map_cons, List.map_nil, alignment, loop, condition, laneBody, address, inputWord, highWord, byte, shifted,
    tail, increment, localVar, addConst, ↓reduceIte]
  rfl

def formals : List (MlS×ShapeHOL) := [(ofString "stp",.one),(ofString "blk",.one)]

theorem original_code (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "keccak_absorb_block")=some (formals,body,.one) := by
  have checked:=OriginalCode.indexed code installed 91 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.Software.guestFn_keccak_absorb_block) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,body,formals,
    Guest.Software.guestFn_keccak_absorb_block,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

end InitECandidate.Solver.CurrentKeccak.Absorb

#print axioms InitECandidate.Solver.CurrentKeccak.Absorb.body_shape
#print axioms InitECandidate.Solver.CurrentKeccak.Absorb.original_code
