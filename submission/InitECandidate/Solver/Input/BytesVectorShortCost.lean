import InitECandidate.Solver.Input.BytesVectorProgram
import InitECandidate.Solver.Input.ClockCostSequenceReached

namespace InitECandidate.Solver.Input.BytesVector
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def afterZero : ProgHOL 64 := .seq (.call (some (none,none)) (ofString "memcpy") copyArguments) (.return (.const 0#64))

theorem after_zero_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (p out : BitVec 64) (n : Nat)
    (short : n≤32) (installed : OriginalCode.Installed source.code) (domain : source.memaddrs=InitE.ordinaryDomain)
    (pointer : source.locals.lookup (ofString "p")=some (.val (.word p)))
    (count : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 n))))
    (output : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (inputArena : AllocatedBytes.Arena p n) (outArena : AllocatedBytes.Arena out 32) :
    source.clock-(evaluateHOLFiniteState source afterZero).2.clock≤n/8+8 := by
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) copyArguments=some (CopyGeneral.values out p n) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,copyArguments,localVar,pointer,count,output,CopyGeneral.values]
  have price := CopyGeneral.call_cost_blocks source copyArguments p out n args (CopyGeneral.original_code source.code installed)
    (AllocatedBytes.copy_mapped source p out n domain inputArena (AllocatedBytes.Arena.weaken out 32 n outArena short)) (by omega)
  exact ClockCost.sequence_current source _ _ (n/8+8) 0 price (ClockCost.returned source.code _)

theorem short_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (p out : BitVec 64) (n : Nat)
    (short : n≤32) (installed : OriginalCode.Installed source.code) (domain : source.memaddrs=InitE.ordinaryDomain)
    (pointer : source.locals.lookup (ofString "p")=some (.val (.word p)))
    (count : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 n))))
    (output : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (inputArena : AllocatedBytes.Arena p n) (outArena : AllocatedBytes.Arena out 32) (aligned : out.toNat%8=0) :
    source.clock-(evaluateHOLFiniteState source shortBody).2.clock≤n/8+10 := by
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) zeroArguments=some (Zero.values out 32) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,zeroArguments,localVar,output,Zero.values]
  have zeroCost := Zero.call_cost source zeroArguments out 32 args (Zero.original_code source.code installed) (by decide) (by decide) aligned
    (by intro index inside multiple; exact AllocatedBytes.word_mapped source out 32 index domain outArena (by omega) aligned multiple)
  change source.clock-(evaluateHOLFiniteState source (.call (some (none,none)) (ofString "memzero") zeroArguments)).2.clock≤2 at zeroCost
  have price := ClockCost.sequence_reached_current source _ afterZero 2 (n/8+8) zeroCost (by
    intro middle normal
    have other (name : String) : middle.locals.lookup (ofString name)=source.locals.lookup (ofString name) := by
      have safe : LocalPrefix (ofString name) (.call (some (none,none)) (ofString "memzero") zeroArguments) := .call none _ _ (by intro key impossible; cases impossible)
      have summary := safe.summary_full source
      unfold LocalSummary at summary
      rw [normal] at summary
      exact summary.1 rfl
    have fields := evaluation_fields source middle _ none normal
    exact after_zero_cost middle p out n short (fields.2.2.2.symm ▸ installed) (fields.1.trans domain)
      ((other "p").trans pointer) ((other "n").trans count) ((other "out").trans output) inputArena outArena)
  change source.clock-(evaluateHOLFiniteState source (.seq (.call (some (none,none)) (ofString "memzero") zeroArguments) afterZero)).2.clock≤n/8+10
  omega

/-- The actual original <=32byte vector branch stops before the allocating
hash continuation and retains its small all-outcome source-clock bound. -/
theorem short_body_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (p out : BitVec 64) (n : Nat)
    (short : n≤32) (installed : OriginalCode.Installed source.code) (domain : source.memaddrs=InitE.ordinaryDomain)
    (pointer : source.locals.lookup (ofString "p")=some (.val (.word p)))
    (count : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 n))))
    (output : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (inputArena : AllocatedBytes.Arena p n) (outArena : AllocatedBytes.Arena out 32) (aligned : out.toNat%8=0) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤n/8+10 := by
  have price := short_cost source p out n short installed domain pointer count output inputArena outArena aligned
  have read := test_read source n (by omega) count
  simp only [if_pos short,eval] at read
  rw [body_shape.1,evaluateHOLFiniteState_seq_line780,guard,evaluateHOLFiniteState_ite,read]
  simp only [if_neg (show (1#64 : BitVec 64)≠0 from by decide)]
  have never := short_stops source
  generalize observed : evaluateHOLFiniteState source shortBody=response at price never ⊢
  obtain ⟨result,post⟩ := response
  cases result with
  | none=>exact (never rfl).elim
  | some result=>exact price

end InitECandidate.Solver.Input.BytesVector

#print axioms InitECandidate.Solver.Input.BytesVector.after_zero_cost
#print axioms InitECandidate.Solver.Input.BytesVector.short_cost
#print axioms InitECandidate.Solver.Input.BytesVector.short_body_cost
