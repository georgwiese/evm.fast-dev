import InitECandidate.Solver.GasBudget.McopyExpansionPrefix
import InitECandidate.Solver.GasBudget.MemoryBufferCopy
import InitECandidate.Solver.GasBudget.MemoryBufferHeapView
import InitECandidate.Solver.WitnessRadix.AllocationCallNormal

namespace InitECandidate.Solver.GasBudget.Mcopy
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def copyAddress (name : String) : ExpHOL 64 := .op .add [frameLoad 24#64, localVar name]
def firstCopy : ProgHOL 64 := .call (some (none, none)) (ofString "memcpy") [localVar "tmp", copyAddress "s", localVar "n"]
def secondCopy : ProgHOL 64 := .call (some (none, none)) (ofString "memcpy") [copyAddress "d", localVar "tmp", localVar "n"]
def release : ProgHOL 64 := .call (some (none, none)) (ofString "heap_release") [localVar "mark"]
def copies : ProgHOL 64 := .seq firstCopy (.seq secondCopy release)
def afterMark : ProgHOL 64 := .decCall (ofString "tmp") .one (ofString "alloc") [localVar "n"] copies
def afterSource : ProgHOL 64 := .decCall (ofString "mark") .one (ofString "heap_mark") [] afterMark
def afterDestination : ProgHOL 64 := .decCall (ofString "s") .one (ofString "sat_word") [localVar "src"] afterSource
def copyBranch : ProgHOL 64 := .decCall (ofString "d") .one (ofString "sat_word") [localVar "dst"] afterDestination
def copyGuard : ProgHOL 64 := .ite (.cmp .notEqual (localVar "n") (.const 0#64)) copyBranch .skip
def finish : ProgHOL 64 := .seq (.call (some (none, none)) (ofString "pc_add") [.const 1#64]) (.return (.const 0#64))

theorem afterExpansion_shape : afterExpansion = .seq copyGuard finish := by
  simp only [afterExpansion, suffix, body, Guest.guestFn_op_mcopy, OpcodeChargeSites.stripPops,
    copyGuard, copyBranch, afterDestination, afterSource, afterMark, copies, firstCopy, secondCopy, release, copyAddress, finish,
    progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none, localVar, frameLoad, frameAddress]

set_option maxRecDepth 100000 in
theorem alloc_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "alloc") = some (WitnessRadix.PersistentAlloc.formals, WitnessRadix.PersistentAlloc.body, .one) := by
  have checked := Input.OriginalCode.indexed code installed 2 (OriginalCodeEnvironment.originalEntry Guest.guestFn_alloc) (by rfl)
  simpa only [OriginalCodeEnvironment.originalEntry, declToHOL, funDeclToHOL, WitnessRadix.PersistentAlloc.formals,
    WitnessRadix.PersistentAlloc.body, Guest.guestFn_alloc, shapeToHOL, paramToHOL, List.map_cons, List.map_nil] using checked

set_option maxRecDepth 100000 in
theorem mark_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "heap_mark") = some ([], Input.HeapScope.markBody, .one) := by
  have checked := Input.OriginalCode.indexed code installed 3 (OriginalCodeEnvironment.originalEntry Guest.guestFn_heap_mark) (by rfl)
  simpa only [OriginalCodeEnvironment.originalEntry, declToHOL, funDeclToHOL, Input.HeapScope.markBody,
    Guest.guestFn_heap_mark, shapeToHOL, List.map_nil] using checked

set_option maxRecDepth 100000 in
theorem release_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "heap_release") = some (Input.HeapScope.releaseFormals, Input.HeapScope.releaseBody, .one) := by
  have checked := Input.OriginalCode.indexed code installed 4 (OriginalCodeEnvironment.originalEntry Guest.guestFn_heap_release) (by rfl)
  simpa only [OriginalCodeEnvironment.originalEntry, declToHOL, funDeclToHOL, Input.HeapScope.releaseFormals, Input.HeapScope.releaseBody,
    Guest.guestFn_heap_release, shapeToHOL, paramToHOL, List.map_cons, List.map_nil] using checked

set_option maxRecDepth 100000 in
theorem copy_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "memcpy") = some (WitnessRadix.CopyGeneral.formals, WitnessRadix.Copy32.body, .one) := by
  have checked := Input.OriginalCode.indexed code installed 11 (OriginalCodeEnvironment.originalEntry Guest.guestFn_memcpy) (by rfl)
  simpa only [OriginalCodeEnvironment.originalEntry, declToHOL, funDeclToHOL, WitnessRadix.CopyGeneral.formals, WitnessRadix.Copy32.body,
    Guest.guestFn_memcpy, shapeToHOL, paramToHOL, List.map_cons, List.map_nil] using checked

end InitECandidate.Solver.GasBudget.Mcopy

#print axioms InitECandidate.Solver.GasBudget.Mcopy.afterExpansion_shape
#print axioms InitECandidate.Solver.GasBudget.Mcopy.alloc_code
#print axioms InitECandidate.Solver.GasBudget.Mcopy.mark_code
#print axioms InitECandidate.Solver.GasBudget.Mcopy.release_code
#print axioms InitECandidate.Solver.GasBudget.Mcopy.copy_code
