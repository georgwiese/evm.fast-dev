import Flapjack.Compiler.Encoders.RiscV.Target
import InitECandidate.Prefix000

/-! Lightweight quantitative bootstrap layout. The list is copied from fixed
Proofs/BootstrapProgram.lean to avoid importing its large compiler/image proof
closure. Equality to the actual first 208 ROM bytes is checked below. This
module proves a byte-level encoding fact only, not execution from any state. -/
namespace InitECandidate.Solver.BootstrapCost
open Flapjack Flapjack.RiscV.L3
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Encoders.RiscV.Target
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def nativePc : Nat := 0x80001190
def initDataRom : Nat := 0x800df000
def initDataRam : Nat := 0xa0020000
def initDataEnd : Nat := 0xa0029048

def bootLoc (reg : Nat) (pc address : Nat) : HolAsm 64 :=
  .loc reg (BitVec.ofNat 64 address - BitVec.ofNat 64 pc)

def bootConst (reg value : Nat) : HolAsm 64 := .inst (.const reg (BitVec.ofNat 64 value))
def bootShift (reg amount : Nat) : HolAsm 64 :=
  .inst (.arith (.shift .lsl reg reg (.imm (BitVec.ofNat 64 amount))))
def bootStore (reg base offset : Nat) : HolAsm 64 :=
  .inst (.mem .store reg (.addr base (BitVec.ofNat 64 offset)))
def bootAdd (reg : Nat) : HolAsm 64 :=
  .inst (.arith (.binop .add reg reg (.imm 8)))

/-- Each instruction is paired with its address in the submitted image. The
five copy-body instructions execute 4617 times; the others execute once. -/
def bootstrapBlocks : List (Nat × HolAsm 64) := [
  (0x80000000, bootLoc 5 0x80000000 initDataRom),
  (0x80000008, bootLoc 6 0x80000008 initDataRam),
  (0x80000010, bootLoc 7 0x80000010 initDataEnd),
  (0x80000018, .inst (.mem .load 28 (.addr 5 0))),
  (0x8000001c, bootStore 28 6 0),
  (0x80000020, bootAdd 5),
  (0x80000024, bootAdd 6),
  (0x80000028, .jumpCmp .lower 6 (.reg 7) (-16)),
  (0x8000002c, bootLoc 5 0x8000002c initDataRam),
  (0x80000034, bootConst 6 161),
  (0x80000038, bootShift 6 24),
  (0x8000003c, bootStore 6 5 0),
  (0x80000040, bootLoc 5 0x80000040 (initDataRam+8)),
  (0x80000048, bootConst 6 2015),
  (0x8000004c, bootShift 6 24),
  (0x80000050, bootStore 6 5 0),
  (0x80000054, bootLoc 5 0x80000054 (initDataRam+16)),
  (0x8000005c, bootConst 6 63),
  (0x80000060, bootShift 6 29),
  (0x80000064, bootStore 6 5 0),
  (0x80000068, bootConst 5 161),
  (0x8000006c, bootShift 5 24),
  (0x80000070, bootLoc 6 0x80000070 (initDataRam+24)),
  (0x80000078, bootStore 6 5 0),
  (0x8000007c, bootLoc 6 0x8000007c initDataEnd),
  (0x80000084, bootStore 6 5 8),
  (0x80000088, bootLoc 6 0x80000088 initDataEnd),
  (0x80000090, bootStore 6 5 16),
  (0x80000094, bootLoc 6 0x80000094 0x800ddd94),
  (0x8000009c, bootStore 6 5 24),
  (0x800000a0, bootLoc 6 0x800000a0 0x800de000),
  (0x800000a8, bootStore 6 5 32),
  (0x800000ac, bootConst 11 161),
  (0x800000b0, bootShift 11 24),
  (0x800000b4, bootConst 12 2015),
  (0x800000b8, bootShift 12 24),
  (0x800000bc, bootConst 13 63),
  (0x800000c0, bootShift 13 29),
  (0x800000c4, bootLoc 10 0x800000c4 nativePc),
  (0x800000cc, .jump (BitVec.ofNat 64 nativePc - 0x800000cc))
]


def prelude : List (HolAsm 64) := (bootstrapBlocks.take 3).map Prod.snd
def body : List (HolAsm 64) := ((bootstrapBlocks.drop 3).take 5).map Prod.snd
def tail : List (HolAsm 64) := (bootstrapBlocks.drop 8).map Prod.snd
def trace : List (HolAsm 64) := prelude ++ (List.replicate 4617 body).flatten ++ tail

theorem bytes_match :
    (bootstrapBlocks.flatMap fun block => riscvEnc block.2) =
      InitECandidate.prefix000.take 208 := by decide

end InitECandidate.Solver.BootstrapCost

#print axioms InitECandidate.Solver.BootstrapCost.bytes_match
