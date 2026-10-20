import InitECandidate.Solver.Input.SszHashWorkspace
import InitECandidate.Solver.Input.ClockCostSequenceReached

namespace InitECandidate.Solver.Input.U64Hash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def body : ProgHOL 64 := match Guest.guestFn_htr_u64_at with | .function fn=>progToHOL fn.body | _=>.skip
def formals : List (MlS×ShapeHOL) := [(ofString "p",.one),(ofString "out",.one)]
def zeroArguments : List (ExpHOL 64) := [localVar "out",.const 32#64]
def copyArguments : List (ExpHOL 64) := [localVar "out",localVar "p",.const 8#64]
def afterZero : ProgHOL 64 := .seq (.call (some (none,none)) (ofString "memcpy") copyArguments) (.return (.const 0#64))

theorem body_shape : body=.seq (.call (some (none,none)) (ofString "memzero") zeroArguments) afterZero := by
  simp only [body,Guest.guestFn_htr_u64_at,progToHOL,expToHOL,List.map_cons,List.map_nil,Option.map_none,afterZero,zeroArguments,copyArguments,localVar]

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : OriginalCode.Installed code) : code.lookup (ofString "htr_u64_at")=some (formals,body,.one) := by
  have checked := OriginalCode.indexed code installed 184 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_htr_u64_at) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,formals,body,Guest.guestFn_htr_u64_at,
    shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

theorem globals (key : MlS) (code) (installed : OriginalCode.Installed code) : GlobalEffects.Preserves key code body := by
  rw [body_shape]
  unfold afterZero
  exact GlobalEffects.sequence key code _ _
    (GlobalEffects.call_body key code (some none) (ofString "memzero") zeroArguments Zero.formals Zero.body .one (Zero.original_code code installed) (Zero.globals key code))
    (GlobalEffects.sequence key code _ _ (GlobalEffects.call_body key code (some none) (ofString "memcpy") copyArguments CopyGeneral.formals Copy32.body .one (CopyGeneral.original_code code installed) (Copy32.globals key code)) (GlobalEffects.returned key code _))

theorem after_zero_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (p out : BitVec 64)
    (installed : OriginalCode.Installed source.code) (domain : source.memaddrs=InitE.ordinaryDomain)
    (pointer : source.locals.lookup (ofString "p")=some (.val (.word p)))
    (output : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (inputArena : AllocatedBytes.Arena p 8) (outArena : AllocatedBytes.Arena out 32) :
    source.clock-(evaluateHOLFiniteState source afterZero).2.clock≤2 := by
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) copyArguments=some (CopyGeneral.values out p 8) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,copyArguments,localVar,pointer,output,CopyGeneral.values]
  have copyCost := CopyGeneral.call_cost_arena source copyArguments p out 8 args (CopyGeneral.original_code source.code installed) domain inputArena (AllocatedBytes.Arena.weaken out 32 8 outArena (by decide))
  have blocks := CopyGeneral.cost_word_multiple p out 8 (by decide)
  exact ClockCost.sequence_current source _ _ 2 0 (by omega) (ClockCost.returned source.code _)

/-- Unchanged original scalar hash costs4body source ticks for every outcome,
including unaligned input byte copies and failed loads/stores. -/
theorem body_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (p out : BitVec 64)
    (installed : OriginalCode.Installed source.code) (domain : source.memaddrs=InitE.ordinaryDomain)
    (pointer : source.locals.lookup (ofString "p")=some (.val (.word p)))
    (output : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (inputArena : AllocatedBytes.Arena p 8) (outArena : AllocatedBytes.Arena out 32) (aligned : out.toNat%8=0) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤4 := by
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) zeroArguments=some (Zero.values out 32) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,zeroArguments,localVar,output,Zero.values]
  have zeroCost := Zero.call_cost source zeroArguments out 32 args (Zero.original_code source.code installed) (by decide) (by decide) aligned
    (by intro index inside multiple; exact AllocatedBytes.word_mapped source out 32 index domain outArena (by omega) aligned multiple)
  change source.clock-(evaluateHOLFiniteState source (.call (some (none,none)) (ofString "memzero") zeroArguments)).2.clock≤2 at zeroCost
  rw [body_shape]
  apply ClockCost.sequence_reached_current source _ afterZero 2 2 zeroCost
  intro middle normal
  have other (name : String) : middle.locals.lookup (ofString name)=source.locals.lookup (ofString name) := by
    have safe : LocalPrefix (ofString name) (.call (some (none,none)) (ofString "memzero") zeroArguments) := .call none _ _ (by intro key impossible; cases impossible)
    have summary := safe.summary_full source
    unfold LocalSummary at summary
    rw [normal] at summary
    exact summary.1 rfl
  have fields := evaluation_fields source middle _ none normal
  exact after_zero_cost middle p out (fields.2.2.2.symm ▸ installed) (fields.1.trans domain) ((other "p").trans pointer) ((other "out").trans output) inputArena outArena

end InitECandidate.Solver.Input.U64Hash

#print axioms InitECandidate.Solver.Input.U64Hash.body_shape
#print axioms InitECandidate.Solver.Input.U64Hash.original_code
#print axioms InitECandidate.Solver.Input.U64Hash.globals
#print axioms InitECandidate.Solver.Input.U64Hash.after_zero_cost
#print axioms InitECandidate.Solver.Input.U64Hash.body_cost
