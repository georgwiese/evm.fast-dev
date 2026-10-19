import InitECandidate.Solver.Mpt.AccountDecodeLoops
import InitECandidate.Solver.WitnessRadix.ZeroCost
import InitECandidate.Solver.WitnessRadix.ZeroNormal
import InitECandidate.Solver.WitnessRadix.AllocationDomain

namespace InitECandidate.Solver.Mpt.AccountDecode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

structure Output (pointer : BitVec 64) : Prop where
  lower : 2701131776≤pointer.toNat
  upper : pointer.toNat+56≤33806089496
  aligned : pointer.toNat%8=0

def clearCall : ProgHOL 64 := .call (some (none,none)) (ofString "memzero") [.op .add [localVar "acct_out",.const 8#64],.const 32#64]

theorem Output.clear_number (pointer : BitVec 64) (output : Output pointer) : (pointer+8#64).toNat=pointer.toNat+8 := by
  rw [BitVec.toNat_add_of_lt (by change pointer.toNat+8<2^64; have := output.upper; omega)]
  rfl

theorem Output.clear_aligned (pointer : BitVec 64) (output : Output pointer) : (pointer+8#64).toNat%8=0 := by
  rw [output.clear_number pointer]
  have := output.aligned
  omega

theorem Output.clear_mapped (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (output : Output pointer)
    (domain : source.memaddrs=InitE.ordinaryDomain) :
    ∀ offset,offset+8≤32 → offset%8=0 → source.memaddrs (byteAddress (pointer+8#64) offset) := by
  intro offset inside aligned
  have number : (byteAddress (pointer+8#64) offset).toNat=pointer.toNat+8+offset := by
    rw [byteAddress_toNat _ _ (by rw [output.clear_number pointer]; have := output.upper; omega),output.clear_number pointer]
  rw [domain]
  apply BackingLayout.ordinary_mapped
  · rw [number]; have := output.lower; omega
  · rw [number]; have := output.upper; omega
  · rw [number]; have := output.aligned; omega

theorem clear_arguments (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64)
    (cell : source.locals.lookup (ofString "acct_out")=some (.val (.word pointer))) :
    evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query))
      [.op .add [localVar "acct_out",.const 8#64],.const 32#64]=some (Zero.values (pointer+8#64) 32) := by
  simp [Zero.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,cell,valueIsWord,valueWord,wordOpHOL,wordOp]

theorem clear_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64)
    (cell : source.locals.lookup (ofString "acct_out")=some (.val (.word pointer))) (output : Output pointer)
    (domain : source.memaddrs=InitE.ordinaryDomain) (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source clearCall).2.clock≤2 := by
  exact Zero.call_cost source _ (pointer+8#64) 32 (clear_arguments source pointer cell) (Zero.original_code source.code installed)
    (by decide) (by decide) (output.clear_aligned pointer) (output.clear_mapped source pointer domain)

theorem clear_none (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64)
    (cell : source.locals.lookup (ofString "acct_out")=some (.val (.word pointer))) (output : Output pointer)
    (domain : source.memaddrs=InitE.ordinaryDomain) (installed : Input.OriginalCode.Installed source.code)
    (normal : evaluateHOLFiniteState source clearCall=(none,target)) :
    2≤source.clock ∧ target={source with memory:=Zero.finalMemory source.memory (pointer+8#64) 32,clock:=source.clock-2} := by
  exact Zero.call_normal source target _ (pointer+8#64) 32 (clear_arguments source pointer cell) (Zero.original_code source.code installed)
    (by decide) (by decide) (output.clear_aligned pointer) (output.clear_mapped source pointer domain) normal

end InitECandidate.Solver.Mpt.AccountDecode

#print axioms InitECandidate.Solver.Mpt.AccountDecode.Output.clear_number
#print axioms InitECandidate.Solver.Mpt.AccountDecode.Output.clear_aligned
#print axioms InitECandidate.Solver.Mpt.AccountDecode.Output.clear_mapped
#print axioms InitECandidate.Solver.Mpt.AccountDecode.clear_arguments
#print axioms InitECandidate.Solver.Mpt.AccountDecode.clear_cost
#print axioms InitECandidate.Solver.Mpt.AccountDecode.clear_none
