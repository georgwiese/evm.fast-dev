import InitECandidate.Solver.GasBudget.MemoryExtendArithmetic
import InitECandidate.Solver.Arenas.NormalIgnoredCall
import InitECandidate.Solver.GasBudget.FrameNewMapped
import InitECandidate.Solver.WitnessRadix.ZeroNormal

namespace InitECandidate.Solver.GasBudget.MemoryExtend
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def body : ProgHOL 64 := match Guest.guestFn_extend_memory with | .function fn => progToHOL fn.body | _ => .skip
def formals : List (MlS × ShapeHOL) := [(ofString "expand_by", .one)]
def returnZero : ProgHOL 64 := .return (.const 0#64)
def zeroGuard : ProgHOL 64 := .ite (.cmp .equal (localVar "expand_by") (.const 0#64)) returnZero .skip
def clamp : ProgHOL 64 := .ite (.cmp .lower (localVar "ncap") (localVar "nlen"))
  (.assign .local (ofString "ncap") (.op .add [localVar "nlen", .const 1024#64])) .skip
def capacityDifference : ExpHOL 64 := .op .sub [localVar "ncap", localVar "cap"]
def growthClear : ProgHOL 64 := .call (some (none, none)) (ofString "memzero")
  [.op .add [frameLoad 24#64, localVar "cap"], capacityDifference]
def allocate : ProgHOL 64 := .call (some (none, none)) (ofString "frame_mem_alloc") [capacityDifference]
def growTail : ProgHOL 64 := .seq allocate (.seq growthClear (.store (frameAddress 40#64) (localVar "ncap")))
def growBranch : ProgHOL 64 := .dec (ofString "ncap") .one (.panop .mul [localVar "cap", .const 2#64]) (.seq clamp growTail)
def growthGuard : ProgHOL 64 := .ite (.cmp .lower (localVar "cap") (localVar "nlen")) growBranch .skip
def afterGrowth : ProgHOL 64 := .seq (.call (some (none, none)) (ofString "memzero")
  [.op .add [frameLoad 24#64, localVar "len"], localVar "expand_by"])
  (.seq (.store (frameAddress 32#64) (localVar "nlen")) returnZero)
def afterNewLength : ProgHOL 64 := .seq growthGuard afterGrowth
def afterCapacity : ProgHOL 64 := .dec (ofString "nlen") .one (.op .add [localVar "len", localVar "expand_by"]) afterNewLength
def afterLength : ProgHOL 64 := .dec (ofString "cap") .one (frameLoad 40#64) afterCapacity
def afterZero : ProgHOL 64 := .dec (ofString "len") .one (frameLoad 32#64) afterLength

theorem body_shape : body = .seq zeroGuard afterZero := by
  simp only [body, Guest.guestFn_extend_memory, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none,
    zeroGuard, afterZero, afterLength, afterCapacity, afterNewLength, growthGuard, growBranch, clamp, growTail, allocate, growthClear,
    capacityDifference, afterGrowth, returnZero, localVar, frameLoad, frameAddress]

def allocOriginal : Arenas.Direction → Decl (BitVec 64) | .up => Guest.guestFn_frame_mem_alloc | .down => Guest.guestFn_scratch_alloc
def allocIndex : Arenas.Direction → Nat | .up => 5 | .down => 8

set_option maxRecDepth 100000 in
theorem alloc_index (direction : Arenas.Direction) : (functionsHOL Input.OriginalCode.program)[allocIndex direction]? =
    some (OriginalCodeEnvironment.originalEntry (allocOriginal direction)) := by cases direction <;> rfl

theorem alloc_code (direction : Arenas.Direction) (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString (Arenas.functionName direction)) = some (Arenas.formals, Arenas.body direction, .one) := by
  have checked := Input.OriginalCode.indexed code installed (allocIndex direction) _ (alloc_index direction)
  cases direction <;> simpa only [OriginalCodeEnvironment.originalEntry, declToHOL, funDeclToHOL, allocOriginal,
    Arenas.functionName, Arenas.formals, Arenas.body, Guest.guestFn_frame_mem_alloc, Guest.guestFn_scratch_alloc,
    shapeToHOL, List.map_cons, List.map_nil, paramToHOL] using checked

theorem trap_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "trap_with") = some (Input.Trap.formals, Input.Trap.body, .one) := by
  have checked := Input.OriginalCode.indexed code installed 0 (OriginalCodeEnvironment.originalEntry Guest.guestFn_trap_with) (by rfl)
  simpa only [OriginalCodeEnvironment.originalEntry, declToHOL, funDeclToHOL, Input.Trap.formals, Input.Trap.body,
    Guest.guestFn_trap_with, shapeToHOL, List.map_cons, List.map_nil, paramToHOL] using checked

theorem zero_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "memzero") = some (WitnessRadix.Zero.formals, WitnessRadix.Zero.body, .one) := by
  have checked := Input.OriginalCode.indexed code installed 12 (OriginalCodeEnvironment.originalEntry Guest.guestFn_memzero) (by rfl)
  simpa only [OriginalCodeEnvironment.originalEntry, declToHOL, funDeclToHOL, WitnessRadix.Zero.formals, WitnessRadix.Zero.body,
    Guest.guestFn_memzero, shapeToHOL, List.map_cons, List.map_nil, paramToHOL] using checked

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : Input.OriginalCode.Installed code) : code.lookup (ofString "extend_memory") = some (formals, body, .one) := by
  have checked := Input.OriginalCode.indexed code installed 418 (OriginalCodeEnvironment.originalEntry Guest.guestFn_extend_memory) (by rfl)
  simpa only [OriginalCodeEnvironment.originalEntry, declToHOL, funDeclToHOL, formals, body,
    Guest.guestFn_extend_memory, shapeToHOL, List.map_cons, List.map_nil, paramToHOL] using checked

/-- Current active-buffer ownership. Contiguity relates the allocator cursor
to the buffer capacity; older scratch headers lie above the live gap. -/
structure View (source : PanSemStateFiniteExact 64 Guest.HostMemory) (frame base length capacity pointer scratch : BitVec 64) : Prop where
  installed : Input.OriginalCode.Installed source.code
  ev : source.globals.lookup (ofString "ev") = some (.val (.word frame))
  mapped : ∀ offset ∈ ([24, 32, 40] : List Nat), source.memaddrs (frame + BitVec.ofNat 64 offset)
  baseCell : source.memory (frame + 24#64) = .word base
  lengthCell : source.memory (frame + 32#64) = .word length
  capacityCell : source.memory (frame + 40#64) = .word capacity
  depth : length.toNat ≤ capacity.toNat
  slack : capacity.toNat ≤ 2 * length.toNat + 1024
  lengthAligned : length.toNat % 32 = 0
  capacityAligned : capacity.toNat % 32 = 0
  baseAligned : base.toNat % 8 = 0
  pointerGlobal : source.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word pointer))
  scratchGlobal : source.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch))
  cursor : pointer.toNat = base.toNat + capacity.toNat
  ordered : pointer ≤ scratch
  scratchAligned : scratch.toNat % 8 = 0
  frameAbove : scratch.toNat ≤ frame.toNat
  frameFits : frame.toNat + 280 < 2 ^ 64
  arena : FrameNew.ArenaMapped source base scratch

end InitECandidate.Solver.GasBudget.MemoryExtend

#print axioms InitECandidate.Solver.GasBudget.MemoryExtend.body_shape
#print axioms InitECandidate.Solver.GasBudget.MemoryExtend.alloc_code
#print axioms InitECandidate.Solver.GasBudget.MemoryExtend.zero_code
#print axioms InitECandidate.Solver.GasBudget.MemoryExtend.original_code
