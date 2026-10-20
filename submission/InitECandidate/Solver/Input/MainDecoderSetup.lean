import InitECandidate.Solver.Input.MainDecoderProgram
import InitECandidate.Solver.Input.MainInputHeap
import InitECandidate.Solver.WitnessRadix.AllocationExpected
import InitECandidate.Solver.WitnessRadix.ZeroCost

namespace InitECandidate.Solver.Input.Main.DecoderSetup
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

def cursor (input : Guest.InputBlob) := (inputCursor input).toNat
def zeroPointer (input : Guest.InputBlob) := BitVec.ofNat 64 (cursor input + 256)
def outState (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) := PersistentAlloc.nextState source "out" (cursor input) (cursor input + 256)
def zeroState (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) := PersistentAlloc.nextState (outState source input) "z32" (cursor input + 256) (cursor input + 288)
def cleared (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) :=
  {zeroState source input with memory := Zero.finalMemory (zeroState source input).memory (zeroPointer input) 32,clock := source.clock - 4}
def entered (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) := QueryBranch.bind (QueryBranch.bind (cleared source input) "si" 0#64) "err_code" 0#64
def restoration (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (target : PanSemStateFiniteExact 64 Guest.HostMemory) :=
  restore source "out" (restore (outState source input) "z32" (restore (cleared source input) "si" (restore (QueryBranch.bind (cleared source input) "si" 0#64) "err_code" target)))

theorem entered_clock (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) : (entered source input).clock = source.clock - 4 := rfl

/-- Actual original out/z32 allocations, mapped32-byte zero call, and both
local declarations, retaining the exact ordered lexical restoration stack. -/
theorem setup (input : Guest.InputBlob) (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (installed : OriginalCode.Installed source.code)
    (heapGlobal : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (inputCursor input))))
    (domain : source.memaddrs = InitE.ordinaryDomain)
    (bounded : input.length % 2 ^ 64 ≤ Guest.maxInputBytes) (enough : 4 ≤ source.clock) :
    ProgramPrefix.Executes source actions (entered source input) (restoration source input) := by
  have geometry := input_cursor_bounds input bounded
  have small : cursor input ≤ 2847949152 := geometry.2.1
  have aligned : cursor input % 8 = 0 := geometry.2.2
  have heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 (cursor input)))) := by
    simpa [cursor,inputCursor] using heapGlobal
  have allocCode := PersistentAlloc.original_code source.code installed
  have zeroCode := Zero.original_code source.code installed
  have outHeap : (outState source input).globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 (cursor input + 256)))) := by
    simp [outState,PersistentAlloc.nextState,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
  have localZero : (zeroState source input).locals.lookup (ofString "z32") = some (.val (.word (zeroPointer input))) := by
    simp [zeroState,PersistentAlloc.nextState,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,zeroPointer]
  have zeroNumber : (zeroPointer input).toNat = cursor input + 256 := by
    unfold zeroPointer
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have arena : AllocatedBytes.Arena (zeroPointer input) 32 := ⟨by rw [zeroNumber]; have := geometry.1; change 2713731432 + input.length % 2 ^ 64 + 8 ≤ cursor input at this; omega,by rw [zeroNumber]; omega⟩
  have zeroAligned : (zeroPointer input).toNat % 8 = 0 := by rw [zeroNumber]; omega
  have zeroArgs : evalListHOLFinite (zeroState source input) (h := fun address => Classical.propDecidable ((zeroState source input).memaddrs address))
      [.var .local (ofString "z32"),.const 32#64] = some (Zero.values (zeroPointer input) 32) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,localZero,Zero.values]
  have zeroClock : (zeroState source input).clock = source.clock - 2 := by change source.clock - 1 - 1 = _; omega
  have clearRun := Zero.call_execute (zeroState source input) _ (zeroPointer input) 32 zeroArgs zeroCode (by decide) (by decide) zeroAligned
    (by intro offset inside multiple; exact AllocatedBytes.word_mapped (zeroState source input) (zeroPointer input) 32 offset domain arena (by omega) zeroAligned multiple)
    (by change 2 ≤ (zeroState source input).clock; rw [zeroClock]; omega)
  have subtract : (zeroState source input).clock - (Zero.price 32 + 1) = source.clock - 4 := by rw [zeroClock]; change source.clock - 2 - 2 = _; omega
  have clearedRun : evaluateHOLFiniteState (zeroState source input) zeroCall = (none,cleared source input) := by
    simpa only [zeroCall,subtract,cleared] using clearRun
  change ProgramPrefix.Executes source
    [.allocate "out" (.const 256#64),.allocate "z32" (.const 32#64),.command zeroCall,.declare "si" (.const 0#64),.declare "err_code" (.const 0#64)]
    (entered source input) (restoration source input)
  refine PersistentAlloc.prefix_allocate source (entered source input) "out" (.const 256#64) _ _ (cursor input) 256 (cursor input + 256) rfl allocCode heap
    (by omega) (Nat.le_refl _) (by omega) (by omega) (by omega) ?_
  change ProgramPrefix.Executes (outState source input)
    [.allocate "z32" (.const 32#64),.command zeroCall,.declare "si" (.const 0#64),.declare "err_code" (.const 0#64)] (entered source input) _
  refine PersistentAlloc.prefix_allocate (outState source input) (entered source input) "z32" (.const 32#64) _ _ (cursor input + 256) 32 (cursor input + 288) rfl allocCode outHeap
    (by omega) (by omega) (by omega) (by omega) (by change 1 ≤ source.clock - 1; omega) ?_
  change ProgramPrefix.Executes (zeroState source input) [.command zeroCall,.declare "si" (.const 0#64),.declare "err_code" (.const 0#64)] (entered source input) _
  refine ProgramPrefix.Executes.command clearedRun (by change source.clock - 4 ≤ (zeroState source input).clock; rw [zeroClock]; omega) ?_
  exact ProgramPrefix.Executes.declare 0#64 rfl (ProgramPrefix.Executes.declare 0#64 rfl (ProgramPrefix.Executes.done _))

end InitECandidate.Solver.Input.Main.DecoderSetup

#print axioms InitECandidate.Solver.Input.Main.DecoderSetup.entered_clock
#print axioms InitECandidate.Solver.Input.Main.DecoderSetup.setup
