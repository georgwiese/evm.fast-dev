import InitECandidate.Solver.Input.ByteOutputFrame
import InitECandidate.Solver.Input.GlobalEffectsScoped
import InitECandidate.Solver.Input.CurrentStartup.Code
import InitECandidate.Solver.CurrentKeccak.MemoryFrame
import InitECandidate.Solver.Input.StraightBody
import InitECandidate.Solver.Input.AssignNormal
import InitECandidate.Solver.Input.ScalarStoreMemory
import InitECandidate.Solver.Input.ConstantCounterCost
import InitECandidate.Solver.Input.ClockCostCurrentValue
import InitECandidate.Solver.Input.CounterStrideCost
import InitECandidate.Solver.Input.LoopNormalExit
import InitECandidate.Solver.Input.WordTripleEnvironment
import InitECandidate.Solver.Input.WordPairLookup
import InitECandidate.Solver.Input.WordEnvironment
import InitECandidate.Solver.Input.MemoryConstantLoop
import InitECandidate.Solver.Input.CounterLoopLocal
import InitECandidate.Solver.Input.ScopedCallNormal
import InitECandidate.Solver.Input.StoppingPrefix
import InitECandidate.Solver.Input.BufferDynamicCost
import InitECandidate.Solver.Input.CopyAwaySubrange

namespace InitECandidate.Solver.Input.CurrentVerify.GeneralSha
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

namespace Code
inductive Routine where | stateInit | block | finish | hash

def declaration : Routine→Decl (BitVec 64)
  | .stateInit=>Guest.Software.guestFn_sha256_state_init
  | .block=>Guest.Software.guestFn_sha256_block
  | .finish=>Guest.Software.guestFn_sha256_finish
  | .hash=>Guest.Software.guestFn_sha256

def entry (routine : Routine):=GasBudget.OriginalCodeEnvironment.originalEntry (declaration routine)
def name (routine : Routine):=(entry routine).1
def formals (routine : Routine):=(entry routine).2.1
def body (routine : Routine):=(entry routine).2.2.1
def shape (routine : Routine):=(entry routine).2.2.2

set_option maxRecDepth 100000 in
theorem installed (code) (installed : OriginalCode.Installed code) (routine : Routine) :
    code.lookup (name routine)=some (formals routine,body routine,shape routine) := by
  cases routine with
  | stateInit=>exact OriginalCode.indexed code installed 84 (entry .stateInit) (by rfl)
  | block=>exact OriginalCode.indexed code installed 85 (entry .block) (by rfl)
  | finish=>exact OriginalCode.indexed code installed 86 (entry .finish) (by rfl)
  | hash=>exact OriginalCode.indexed code installed 87 (entry .hash) (by rfl)
end Code

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem state_supported : StraightBody.accepts (Code.body .stateInit)=true := by
  simp only [Code.body,Code.entry,Code.declaration,GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,
    Guest.Software.guestFn_sha256_state_init,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,Option.map_some]
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem block_supported : StraightBody.accepts (Code.body .block)=true := by
  simp only [Code.body,Code.entry,Code.declaration,GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,
    Guest.Software.guestFn_sha256_block,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,Option.map_some]
  rfl

/-- The actual expanded compression has no source calls or loops. Its
large straight-line target work still needs a separate static allowance. -/
theorem state_cost (code) : ClockCost.Bound code (Code.body .stateInit) 0 :=
  ClockCost.of_quiet code _ (StraightBody.effects (ofString "sha_st") code _ state_supported).1

theorem block_cost (code) : ClockCost.Bound code (Code.body .block) 0 :=
  ClockCost.of_quiet code _ (StraightBody.effects (ofString "sha_st") code _ block_supported).1

theorem state_globals (key : MlS) (code) : GlobalEffects.Preserves key code (Code.body .stateInit) :=
  (StraightBody.effects key code _ state_supported).2

theorem block_globals (key : MlS) (code) : GlobalEffects.Preserves key code (Code.body .block) :=
  (StraightBody.effects key code _ block_supported).2

namespace WordFrame

def scalar : ExpHOL 64→Bool
  | .const _ | .op _ _ | .shift _ _ _=>true
  | _=>false

theorem scalar_length (expression : ExpHOL 64) (checked : scalar expression=true)
    (source : PanSemStateFiniteExact 64 Guest.HostMemory) (value : ValueHOL 64)
    (read : eval source expression=some value) : (flattenHOL value).length≤1 := by
  cases expression with
  | const word=>
    have actual : eval source (.const word)=some (.val (.word word)):=rfl
    have same:=Option.some.inj (read.symm.trans actual)
    rw [same]
    simp [flattenHOL]
  | op operator arguments=>rw [op_length source operator arguments value read]
  | shift operator left right=>rw [MemoryAt.shift_length source operator left right value read]
  | _=>simp only [scalar] at checked; cases checked

/-- Successful scalar stores touch one word; every failed store leaves
memory unchanged. This includes actual read/mapping failures. -/
theorem scalar_store_current (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (address expression : ExpHOL 64) (pointer query : BitVec 64)
    (read : eval source address=some (.val (.word pointer)))
    (small : ∀ value,eval source expression=some value→ (flattenHOL value).length≤1)
    (away : query≠pointer) : (evaluateHOLFiniteState source (.store address expression)).2.memory query=source.memory query := by
  by_cases normal : (evaluateHOLFiniteState source (.store address expression)).1=none
  · exact MemoryAt.scalar_store_normal source _ address expression pointer query read small away (Prod.ext normal rfl)
  · classical
    simp only [eval] at read
    rw [evaluateHOLFiniteState_store,read] at normal ⊢
    dsimp only at normal ⊢
    cases valueRead : evalHOLExact source.toExact expression with
    | none=>simp [valueRead]
    | some value=>
      simp only [valueRead] at normal ⊢
      cases stored : panMemStoresHOL pointer (flattenHOL value) source.memaddrs source.memory with
      | none=>simp [stored]
      | some memory=>simp [stored] at normal

def accepts (key : MlS) (size : Nat) : ProgHOL 64→Bool
  | .skip | .return _=>true
  | .assign .local name _=>decide (name≠key)
  | .store address expression=>match ByteOutputFrame.offset? key address with
    | some offset=>decide (offset.toNat<size) && scalar expression
    | none=>false
  | .seq first second=>accepts key size first && accepts key size second
  | .dec name _ _ body=>decide (name≠key) && accepts key size body
  | _=>false

/-- Reuse the checked straight-prefix composition rules, with scalar
word stores in place of byte stores. No successful body run is supplied. -/
theorem sound (key : MlS) (size : Nat) (program : ProgHOL 64) (checked : accepts key size program=true)
    (pointer query : BitVec 64) (away : ∀ offset : Nat,offset<size→ query≠pointer+BitVec.ofNat 64 offset) :
    ByteOutputFrame.Frame key pointer query program := by
  cases program with
  | skip=>exact ByteOutputFrame.sound key 0 .skip rfl pointer query (by intro offset inside; omega)
  | «return» expression=>exact ByteOutputFrame.sound key 0 (.return expression) rfl pointer query (by intro offset inside; omega)
  | assign kind name expression=>
    cases kind with
    | «global»=>cases checked
    | «local»=>exact ByteOutputFrame.sound key 0 (.assign .local name expression) checked pointer query (by intro offset inside; omega)
  | store address expression=>
    unfold accepts at checked
    cases found : ByteOutputFrame.offset? key address with
    | none=>simp only [found] at checked; cases checked
    | some offset=>
      have parts : offset.toNat<size ∧ scalar expression=true:=by
        simpa only [found,Bool.and_eq_true,decide_eq_true_eq] using checked
      intro source cell
      have read:=ByteOutputFrame.offset_sound key address offset found source pointer cell
      have outside : query≠pointer+offset:=by
        simpa only [BitVec.ofNat_toNat,BitVec.setWidth_eq] using away offset.toNat parts.1
      refine ⟨scalar_store_current source address expression (pointer+offset) query read (fun value evaluated=>scalar_length expression parts.2 source value evaluated) outside,?_⟩
      have locals : (evaluateHOLFiniteState source (.store address expression)).2.locals=source.locals:=by
        rw [evaluateHOLFiniteState_store]
        repeat first | rfl | split
      intro normal
      rw [locals]
      exact cell
  | seq first second=>
    have parts : accepts key size first=true ∧ accepts key size second=true:=by simpa only [accepts,Bool.and_eq_true] using checked
    exact ByteOutputFrame.sequence key pointer query first second (sound key size first parts.1 pointer query away) (sound key size second parts.2 pointer query away)
  | dec name shape expression body=>
    have parts : name≠key ∧ accepts key size body=true:=by simpa only [accepts,Bool.and_eq_true,decide_eq_true_eq] using checked
    exact ByteOutputFrame.declared key name pointer query shape expression body parts.1 (sound key size body parts.2 pointer query away)
  | _=>simp only [accepts] at checked; cases checked
termination_by structural program

end WordFrame

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem state_frame_supported : WordFrame.accepts (ofString "stp") 64 (Code.body .stateInit)=true := by
  simp only [Code.body,Code.entry,Code.declaration,GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,
    Guest.Software.guestFn_sha256_state_init,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,Option.map_some]
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem block_frame_supported : WordFrame.accepts (ofString "stp") 64 (Code.body .block)=true := by
  simp only [Code.body,Code.entry,Code.declaration,GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,
    Guest.Software.guestFn_sha256_block,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,Option.map_some]
  rfl

theorem state_memory (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer query : BitVec 64)
    (cell : source.locals.lookup (ofString "stp")=some (.val (.word pointer)))
    (away : ∀ offset : Nat,offset<64→ query≠pointer+BitVec.ofNat 64 offset) :
    (evaluateHOLFiniteState source (Code.body .stateInit)).2.memory query=source.memory query :=
  (WordFrame.sound (ofString "stp") 64 (Code.body .stateInit) state_frame_supported pointer query away source cell).1

theorem block_memory (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer query : BitVec 64)
    (cell : source.locals.lookup (ofString "stp")=some (.val (.word pointer)))
    (away : ∀ offset : Nat,offset<64→ query≠pointer+BitVec.ofNat 64 offset) :
    (evaluateHOLFiniteState source (Code.body .block)).2.memory query=source.memory query :=
  (WordFrame.sound (ofString "stp") 64 (Code.body .block) block_frame_supported pointer query away source cell).1

set_option maxRecDepth 100000 in
theorem be32_supported : StraightBody.accepts (CurrentStartup.Code.body .st_be32)=true := by
  simp only [CurrentStartup.Code.body,CurrentStartup.Code.entry,CurrentStartup.Code.declaration,GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,
    Guest.Software.guestFn_st_be32,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,Option.map_some]
  rfl

theorem be32_cost (code) : ClockCost.Bound code (CurrentStartup.Code.body .st_be32) 0 :=
  ClockCost.of_quiet code _ (StraightBody.effects (ofString "p") code _ be32_supported).1

def finishArguments : List (ExpHOL 64):=[.op .add [localVar "out",.panop .mul [localVar "i",.const 4#64]],
  .load .one (.op .add [localVar "stp",.panop .mul [localVar "i",.const 8#64]])]
def finishCall : ProgHOL 64:=.call (some (none,none)) (ofString "st_be32") finishArguments
def finishIncrement : ProgHOL 64:=.assign .local (ofString "i") (.op .add [localVar "i",.const 1#64])
def finishIteration : ProgHOL 64:=.seq finishCall finishIncrement
def finishTest : ExpHOL 64:=.cmp .less (localVar "i") (.const 8#64)
def finishTail : ProgHOL 64:=.seq (.while finishTest finishIteration) (.return (.const 0#64))

set_option maxRecDepth 100000 in
theorem finish_shape : Code.body .finish=.dec (ofString "i") .one (.const 0#64) finishTail := by
  simp only [Code.body,Code.entry,Code.declaration,GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,
    Guest.Software.guestFn_sha256_finish,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,Option.map_some,
    finishTail,finishTest,finishIteration,finishCall,finishArguments,finishIncrement,localVar]

theorem finish_iteration_cost (code) (installed : OriginalCode.Installed code) : ClockCost.Bound code finishIteration 1 := by
  have called:=ClockCost.call_body code (some none) (ofString "st_be32") finishArguments
    (CurrentStartup.Code.formals .st_be32) (CurrentStartup.Code.body .st_be32) (CurrentStartup.Code.shape .st_be32) 0
    (CurrentStartup.Code.installed code installed .st_be32) (be32_cost code)
  exact ClockCost.sequence code finishCall finishIncrement 1 0 called (ClockCost.assign code (ofString "i") _)

theorem finish_iteration_advance : CounterFlow.Advances (ofString "i") 1 finishIteration :=
  CounterFlow.sequence (ofString "i") finishCall finishIncrement 0 1
    (CounterFlow.preserved _ _ (.call none _ _ (by simp))) (CounterFlow.increment _)

theorem finish_iteration_local : LocalPrefix (ofString "stp") finishIteration :=
  .seq (.call none _ _ (by simp)) (.assign (ofString "i") _ (by decide))

/-- Every real digest-output outcome costs at most eight loop ticks plus
eight literal st_be32 calls. Failed reads and exhausted clocks are included. -/
theorem finish_cost (code) (installed : OriginalCode.Installed code) : ClockCost.Bound code (Code.body .finish) 16 := by
  intro source codeEq
  have currentInstalled : OriginalCode.Installed source.code:=by rw [codeEq]; exact installed
  rw [finish_shape]
  apply ClockCost.declared_value_current source (ofString "i") .one (.const 0#64) (.val (.word 0#64)) finishTail 16 rfl
  let entered:=bind source "i" 0#64
  have loopPrice:=CounterFlow.constant_loop_cost source.code (ofString "i") (ofString "stp") finishIteration 1 8 (by decide)
    (finish_iteration_cost source.code currentInstalled) finish_iteration_advance finish_iteration_local entered 0#64 rfl (bind_lookup_same _ _ _) (by decide)
  exact ClockCost.sequence_current entered (.while finishTest finishIteration) (.return (.const 0#64)) 16 0 loopPrice (ClockCost.returned source.code (.const 0#64))

def blockArguments : List (ExpHOL 64):=[.var .global (ofString "sha_st"),.op .add [localVar "p",localVar "i"]]
def blockCall : ProgHOL 64:=.call (some (none,none)) (ofString "sha256_block") blockArguments
def blockIncrement : ProgHOL 64:=.assign .local (ofString "i") (.op .add [localVar "i",.const 64#64])
def blockIteration : ProgHOL 64:=.seq blockCall blockIncrement
def blockTest : ExpHOL 64:=.cmp .notLower (localVar "len") (.op .add [localVar "i",.const 64#64])
def blocks : ProgHOL 64:=.while blockTest blockIteration

theorem block_iteration_local : LocalPrefix (ofString "len") blockIteration :=
  .seq (.call none _ _ (by simp)) (.assign (ofString "i") _ (by decide))

theorem block_iteration_advance : CounterFlow.Advances (ofString "i") 64 blockIteration :=
  CounterFlow.sequence (ofString "i") blockCall blockIncrement 0 64
    (CounterFlow.preserved _ _ (.call none _ _ (by simp))) (CounterFlow.increment_by _ 64)

theorem block_iteration_cost (code) (installed : OriginalCode.Installed code) : ClockCost.Bound code blockIteration 1 := by
  have called:=ClockCost.call_body code (some none) (ofString "sha256_block") blockArguments
    (Code.formals .block) (Code.body .block) (Code.shape .block) 0
    (Code.installed code installed .block) (block_cost code)
  exact ClockCost.sequence code blockCall blockIncrement 1 0 called (ClockCost.assign code (ofString "i") _)

theorem block_test_reads (length : Nat) (small : length+64<2^64) :
    CounterFlow.NamedStride.Reads (ofString "len") blockTest 64 length := by
  intro source word counter count bounded
  have encoded : (BitVec.ofNat 64 length).toNat=length:=by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have sum : (word+64#64).toNat=word.toNat+64:=by
    rw [BitVec.toNat_add_of_lt (by change word.toNat+64<2^64; omega)]; rfl
  by_cases active : word.toNat+64≤length
  · have lower : ¬BitVec.ofNat 64 length<word+64#64:=by change ¬(BitVec.ofNat 64 length).toNat<(word+64#64).toNat; rw [encoded,sum]; omega
    simp [evalHOLFinite,evalHOLExact,evalListHOLExact,toExact,blockTest,localVar,counter,count,valueIsWord,valueWord,wordOpHOL,wordOp,
      Flapjack.Compiler.Encoders.Asm.wordCmpHOL,lower,active]
  · have lower : BitVec.ofNat 64 length<word+64#64:=by change (BitVec.ofNat 64 length).toNat<(word+64#64).toNat; rw [encoded,sum]; omega
    simp [evalHOLFinite,evalHOLExact,evalListHOLExact,toExact,blockTest,localVar,counter,count,valueIsWord,valueWord,wordOpHOL,wordOp,
      Flapjack.Compiler.Encoders.Asm.wordCmpHOL,lower,active]

/-- Actual block calls and loop ticks, including failures. Expanded compression
work is accounted for separately when translating to target steps. -/
theorem blocks_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (length : Nat)
    (small : length+64<2^64) (installed : OriginalCode.Installed source.code)
    (valid : CounterFlow.NamedStride.Invariant (ofString "len") length source) :
    source.clock-(evaluateHOLFiniteState source blocks).2.clock≤2*(length/64) := by
  have priced:=CounterFlow.NamedStride.loop_cost (ofString "len") source.code blockTest blockIteration 64 length 1 (by decide) (by omega)
    block_iteration_advance block_iteration_local.summary_full (block_test_reads length small) (block_iteration_cost source.code installed) source rfl valid
  exact Nat.le_trans priced (Nat.mul_le_mul_left 2 (Nat.div_le_div_right (Nat.sub_le _ _)))

/-- The normally completed real loop supplies its own short padding remainder. -/
theorem blocks_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (length : Nat)
    (small : length+64<2^64) (valid : CounterFlow.NamedStride.Invariant (ofString "len") length source)
    (normal : evaluateHOLFiniteState source blocks=(none,post)) :
    ∃ word,post.locals.lookup (ofString "i")=some (.val (.word word)) ∧
      post.locals.lookup (ofString "len")=some (.val (.word (BitVec.ofNat 64 length))) ∧ word.toNat≤length ∧ length-word.toNat<64 := by
  have next:=CounterFlow.NamedStride.loop_normal (ofString "len") source.code blockTest blockIteration 64 length (by decide) (by omega)
    block_iteration_advance block_iteration_local.summary_full (block_test_reads length small) source post rfl valid normal
  obtain ⟨word,counter,count,bounded⟩:=next
  have ended:=loop_normal_exit blockTest blockIteration (fun current=>(block_iteration_local.summary_full current).2.2.1) source post normal
  have read:=block_test_reads length small post word counter count bounded
  have inactive : ¬word.toNat+64≤length:=by
    intro active
    rw [if_pos active] at read
    have contradiction:=ended.symm.trans read
    cases contradiction
  exact ⟨word,counter,count,bounded,by omega⟩

def state : ExpHOL 64:=.var .global (ofString "sha_st")
def pad : ExpHOL 64:=.var .global (ofString "sha_pad")
def remainder : ExpHOL 64:=.op .sub [localVar "len",localVar "i"]
def zeroPad : ProgHOL 64:=.call (some (none,none)) (ofString "memzero") [pad,.const 128#64]
def copyPad : ProgHOL 64:=.call (some (none,none)) (ofString "memcpy") [pad,.op .add [localVar "p",localVar "i"],localVar "rem"]
def padFirst : ProgHOL 64:=.storeByte (.op .add [pad,localVar "rem"]) (.const 128#64)
def selectTotal : ProgHOL 64:=.ite (.cmp .notLower (localVar "rem") (.const 56#64))
  (.assign .local (ofString "total") (.const 128#64)) .skip
def storeLength : ProgHOL 64:=.call (some (none,none)) (ofString "st_be64")
  [.op .sub [.op .add [pad,localVar "total"],.const 8#64],.shift .lsl (localVar "len") (.const 3#64)]
def absorbPad : ProgHOL 64:=.call (some (none,none)) (ofString "sha256_block") [state,pad]
def extraPad : ProgHOL 64:=.ite (.cmp .equal (localVar "total") (.const 128#64))
  (.call (some (none,none)) (ofString "sha256_block") [state,.op .add [pad,.const 64#64]]) .skip
def digestCall : ProgHOL 64:=.call (some (none,none)) (ofString "sha256_finish") [state,localVar "out"]
def finalTail : ProgHOL 64:=.seq selectTotal (.seq storeLength (.seq absorbPad (.seq extraPad (.seq digestCall (.return (.const 0#64))))))
def paddingFinish : ProgHOL 64:=.seq padFirst (.dec (ofString "total") .one (.const 64#64) finalTail)
def paddingTail : ProgHOL 64:=.seq zeroPad (.seq copyPad paddingFinish)
def afterBlocks : ProgHOL 64:=.dec (ofString "rem") .one remainder paddingTail
def initCall : ProgHOL 64:=.call (some (none,none)) (ofString "sha256_state_init") [state]

set_option maxRecDepth 100000 in
theorem hash_shape : Code.body .hash=.seq initCall (.dec (ofString "i") .one (.const 0#64) (.seq blocks afterBlocks)) := by
  simp only [Code.body,Code.entry,Code.declaration,GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,
    Guest.Software.guestFn_sha256,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,Option.map_some,
    initCall,state,blocks,blockTest,blockIteration,blockCall,blockArguments,blockIncrement,afterBlocks,remainder,paddingTail,
    zeroPad,copyPad,paddingFinish,padFirst,pad,finalTail,selectTotal,storeLength,absorbPad,extraPad,digestCall,localVar]

set_option maxRecDepth 100000 in
theorem bswap_supported : StraightBody.accepts (CurrentStartup.Code.body .bswap64)=true := by
  simp only [CurrentStartup.Code.body,CurrentStartup.Code.entry,CurrentStartup.Code.declaration,GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL,funDeclToHOL,Guest.Software.guestFn_bswap64,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none]
  rfl

set_option maxRecDepth 100000 in
/-- Current aligned bswap and two-BE32 fallback paths, including failures. -/
theorem be64_cost (code) (installed : OriginalCode.Installed code) : ClockCost.Bound code (CurrentStartup.Code.body .st_be64) 3 := by
  have swap : ClockCost.Bound code (CurrentStartup.Code.body .bswap64) 0:=
    ClockCost.of_quiet code _ (StraightBody.effects (ofString "x") code _ bswap_supported).1
  have be32 (args : List (ExpHOL 64)) : ClockCost.Bound code (.call (some (none,none)) (ofString "st_be32") args) 1:=
    ClockCost.call_body code (some none) (ofString "st_be32") args
      (CurrentStartup.Code.formals .st_be32) (CurrentStartup.Code.body .st_be32) (CurrentStartup.Code.shape .st_be32) 0
      (CurrentStartup.Code.installed code installed .st_be32) (be32_cost code)
  simp only [CurrentStartup.Code.body,CurrentStartup.Code.entry,CurrentStartup.Code.declaration,GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL,funDeclToHOL,Guest.Software.guestFn_st_be64,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none]
  refine ClockCost.sequence code _ _ 1 2 ?_ ?_
  · apply ClockCost.conditional code _ _ _ 1 0
    · apply ClockCost.scoped_body code _ _ (ofString "bswap64") _ _
        (CurrentStartup.Code.formals .bswap64) (CurrentStartup.Code.body .bswap64) (CurrentStartup.Code.shape .bswap64) 0 0
        (CurrentStartup.Code.installed code installed .bswap64) swap
      exact ClockCost.sequence code _ _ 0 0 (ClockCost.store code _ _) (ClockCost.returned code _)
    · exact ClockCost.skip code
  · exact ClockCost.sequence code _ _ 1 1 (be32 _) (ClockCost.sequence code _ _ 1 0 (be32 _) (ClockCost.returned code _))

theorem compression_call_cost (code) (installed : OriginalCode.Installed code) (args : List (ExpHOL 64)) :
    ClockCost.Bound code (.call (some (none,none)) (ofString "sha256_block") args) 1 :=
  ClockCost.call_body code (some none) (ofString "sha256_block") args
    (Code.formals .block) (Code.body .block) (Code.shape .block) 0 (Code.installed code installed .block) (block_cost code)

theorem final_tail_cost (code) (installed : OriginalCode.Installed code) : ClockCost.Bound code finalTail 23 := by
  have digest:=ClockCost.call_body code (some none) (ofString "sha256_finish") [state,localVar "out"]
    (Code.formals .finish) (Code.body .finish) (Code.shape .finish) 16 (Code.installed code installed .finish) (finish_cost code installed)
  have last : ClockCost.Bound code (.seq digestCall (.return (.const 0#64))) 17:=
    ClockCost.sequence code _ _ 17 0 digest (ClockCost.returned code _)
  have extra : ClockCost.Bound code extraPad 1:=by
    simpa only [extraPad,Nat.max_zero] using ClockCost.conditional code _ _ _ 1 0
      (compression_call_cost code installed _) (ClockCost.skip code)
  have two : ClockCost.Bound code (.seq extraPad (.seq digestCall (.return (.const 0#64)))) 18:=
    ClockCost.sequence code _ _ 1 17 extra last
  have three : ClockCost.Bound code (.seq absorbPad (.seq extraPad (.seq digestCall (.return (.const 0#64))))) 19:=
    ClockCost.sequence code _ _ 1 18 (compression_call_cost code installed _) two
  have stored:=ClockCost.call_body code (some none) (ofString "st_be64")
    [.op .sub [.op .add [pad,localVar "total"],.const 8#64],.shift .lsl (localVar "len") (.const 3#64)]
    (CurrentStartup.Code.formals .st_be64) (CurrentStartup.Code.body .st_be64) (CurrentStartup.Code.shape .st_be64) 3
    (CurrentStartup.Code.installed code installed .st_be64) (be64_cost code installed)
  have four : ClockCost.Bound code (.seq storeLength (.seq absorbPad (.seq extraPad (.seq digestCall (.return (.const 0#64)))))) 23:=
    ClockCost.sequence code _ _ 4 19 stored three
  have select : ClockCost.Bound code selectTotal 0:=ClockCost.conditional code _ _ _ 0 0
    (ClockCost.assign code (ofString "total") _) (ClockCost.skip code)
  exact ClockCost.sequence code _ _ 0 23 select four

theorem padding_finish_cost (code) (installed : OriginalCode.Installed code) : ClockCost.Bound code paddingFinish 23 := by
  have tail:=ClockCost.declared code (ofString "total") .one (.const 64#64) finalTail 23 (final_tail_cost code installed)
  exact ClockCost.sequence code _ _ 0 23 (ClockCost.of_quiet code _ (QuietClock.store_byte code _ _)) tail

/-- The genuine short remainder suffices, including invalid pointer/read/store
outcomes. Neither memory mapping nor a later successful hash is assumed. -/
theorem padding_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (rem : Nat)
    (small : rem<64) (installed : OriginalCode.Installed source.code)
    (remCell : source.locals.lookup (ofString "rem")=some (.val (.word (BitVec.ofNat 64 rem)))) :
    source.clock-(evaluateHOLFiniteState source paddingTail).2.clock≤267 := by
  have zero:=BufferDynamicCost.zero_cost source pad (.const 128#64) 128 installed (by decide) rfl
  have zeroPrice : source.clock-(evaluateHOLFiniteState source zeroPad).2.clock≤165:=zero
  apply ClockCost.sequence_reached_current source zeroPad _ 165 102 zeroPrice
  intro middle normal
  have codeEq:=(evaluation_fields source middle zeroPad none normal).2.2.2
  have nextInstalled : OriginalCode.Installed middle.code:=by rw [codeEq]; exact installed
  have nextRem : middle.locals.lookup (ofString "rem")=some (.val (.word (BitVec.ofNat 64 rem))):=
    (CallNormal.ignored_lookup source middle (ofString "rem") (ofString "memzero") [pad,.const 128#64] normal).trans remCell
  have remRead : eval middle (localVar "rem")=some (.val (.word (BitVec.ofNat 64 rem))):=by
    simp [eval,evalHOLExact,toExact,localVar,nextRem]
  have copy:=BufferDynamicCost.copy_cost middle pad (.op .add [localVar "p",localVar "i"]) (localVar "rem") rem
    nextInstalled (by omega) remRead
  have copyBound : CopyAny.price rem+1≤79:=by unfold CopyAny.price; omega
  have copyPrice : middle.clock-(evaluateHOLFiniteState middle copyPad).2.clock≤79:=Nat.le_trans copy copyBound
  exact ClockCost.sequence_current middle copyPad paddingFinish 79 23 copyPrice (padding_finish_cost middle.code nextInstalled)

theorem after_blocks_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (length : Nat) (word : BitVec 64)
    (small : length+64<2^64) (installed : OriginalCode.Installed source.code)
    (counter : source.locals.lookup (ofString "i")=some (.val (.word word)))
    (count : source.locals.lookup (ofString "len")=some (.val (.word (BitVec.ofNat 64 length))))
    (bounded : word.toNat≤length) (short : length-word.toNat<64) :
    source.clock-(evaluateHOLFiniteState source afterBlocks).2.clock≤267 := by
  have number : (BitVec.ofNat 64 length).toNat=length:=by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have difference : BitVec.ofNat 64 length-word=BitVec.ofNat 64 (length-word.toNat):=by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub_of_le (by change word.toNat≤(BitVec.ofNat 64 length).toNat; rw [number]; exact bounded),number,
      BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have read : eval source remainder=some (.val (.word (BitVec.ofNat 64 (length-word.toNat)))):=by
    simp [eval,evalHOLExact,evalListHOLExact,toExact,remainder,localVar,counter,count,valueIsWord,valueWord,wordOpHOL,wordOp,difference]
  exact ClockCost.declared_current source "rem" remainder (BitVec.ofNat 64 (length-word.toNat)) paddingTail 267 read
    (padding_cost (QueryBranch.bind source "rem" (BitVec.ofNat 64 (length-word.toNat))) (length-word.toNat) short installed (bind_lookup_same _ _ _))

def bodyPrice (length : Nat) : Nat:=2*(length/64)+268

theorem loop_tail_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (length : Nat)
    (small : length+64<2^64) (installed : OriginalCode.Installed source.code)
    (valid : CounterFlow.NamedStride.Invariant (ofString "len") length source) :
    source.clock-(evaluateHOLFiniteState source (.seq blocks afterBlocks)).2.clock≤2*(length/64)+267 := by
  apply ClockCost.sequence_reached_current source blocks afterBlocks (2*(length/64)) 267 (blocks_cost source length small installed valid)
  intro middle normal
  obtain ⟨word,counter,count,bounded,short⟩:=blocks_normal source middle length small valid normal
  have sameCode:=(evaluation_fields source middle blocks none normal).2.2.2
  exact after_blocks_cost middle length word small (by rw [sameCode]; exact installed) counter count bounded short

/-- Complete unchanged general SHA on every outcome. This prices source
calls/loop ticks; expanded straight-line target work remains separate. -/
theorem body_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (length : Nat)
    (small : length+64<2^64) (installed : OriginalCode.Installed source.code)
    (count : source.locals.lookup (ofString "len")=some (.val (.word (BitVec.ofNat 64 length)))) :
    source.clock-(evaluateHOLFiniteState source (Code.body .hash)).2.clock≤bodyPrice length := by
  rw [hash_shape]
  have initial:=ClockCost.call_body source.code (some none) (ofString "sha256_state_init") [state]
    (Code.formals .stateInit) (Code.body .stateInit) (Code.shape .stateInit) 0 (Code.installed source.code installed .stateInit) (state_cost source.code)
  have first : source.clock-(evaluateHOLFiniteState source initCall).2.clock≤1:=initial source rfl
  have combined:=ClockCost.sequence_reached_current source initCall _ 1 (2*(length/64)+267) first (by
    intro middle normal
    have nextCount : middle.locals.lookup (ofString "len")=some (.val (.word (BitVec.ofNat 64 length))):=
      (CallNormal.ignored_lookup source middle (ofString "len") (ofString "sha256_state_init") [state] normal).trans count
    have sameCode:=(evaluation_fields source middle initCall none normal).2.2.2
    have nextInstalled : OriginalCode.Installed middle.code:=by rw [sameCode]; exact installed
    apply ClockCost.declared_current middle "i" (.const 0#64) 0#64 (.seq blocks afterBlocks) (2*(length/64)+267) rfl
    exact loop_tail_cost (QueryBranch.bind middle "i" 0#64) length small nextInstalled
      ⟨0#64,bind_lookup_same _ _ _,(bind_lookup_other middle "i" "len" 0#64 (by decide)).trans nextCount,by simp⟩)
  have total : 1+(2*(length/64)+267)=bodyPrice length:=by unfold bodyPrice; omega
  rw [total] at combined
  exact combined

def values (pointer out : BitVec 64) (length : Nat) : List (ValueHOL 64):=
  [.val (.word pointer),.val (.word (BitVec.ofNat 64 length)),.val (.word out)]
theorem hash_code (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "sha256")=some ([(ofString "p",.one),(ofString "len",.one),(ofString "out",.one)],Code.body .hash,.one) := by
  simpa only [Code.name,Code.formals,Code.shape,Code.entry,Code.declaration,GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL,funDeclToHOL,Guest.Software.guestFn_sha256,paramToHOL,shapeToHOL,List.map_cons,List.map_nil]
    using Code.installed code installed .hash

theorem environment (codeFn : MlS→Option (List (MlS×ShapeHOL)×ProgHOL 64×ShapeHOL)) (pointer out : BitVec 64) (length : Nat)
    (code : codeFn (ofString "sha256")=some ([(ofString "p",.one),(ofString "len",.one),(ofString "out",.one)],Code.body .hash,.one)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),
      lookupCodeHOLFinite codeFn (ofString "sha256") (values pointer out length)=some (Code.body .hash,callee,.one) ∧
      callee.lookup (ofString "p")=some (.val (.word pointer)) ∧
      callee.lookup (ofString "len")=some (.val (.word (BitVec.ofNat 64 length))) ∧
      callee.lookup (ofString "out")=some (.val (.word out)) :=
  word_triple_environment codeFn (ofString "sha256") (ofString "p") (ofString "len") (ofString "out")
    (Code.body .hash) .one pointer (BitVec.ofNat 64 length) out (by decide) (by decide) (by decide) code

theorem call_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (arguments : List (ExpHOL 64))
    (pointer out : BitVec 64) (length : Nat) (small : length+64<2^64)
    (installed : OriginalCode.Installed source.code)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (values pointer out length)) :
    source.clock-(evaluateHOLFiniteState source (.call (some (none,none)) (ofString "sha256") arguments)).2.clock≤bodyPrice length+1 := by
  obtain ⟨callee,called,pointerCell,count,outCell⟩:=environment source.code.lookup pointer out length (hash_code source.code installed)
  exact ClockCost.call_current source (some none) (ofString "sha256") arguments (values pointer out length) (Code.body .hash) callee .one (bodyPrice length)
    args called (body_cost (callEntryStateHOLFinite source callee) length small installed count)

/-- Price the real size expression alone; failed or ill-typed pointer reads
stop before the body and remain covered by the same allowance. -/
theorem dynamic_call_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer size out : ExpHOL 64) (length : Nat)
    (installed : OriginalCode.Installed source.code) (small : length+64<2^64)
    (sizeRead : eval source size=some (.val (.word (BitVec.ofNat 64 length)))) :
    source.clock-(evaluateHOLFiniteState source (.call (some (none,none)) (ofString "sha256") [pointer,size,out])).2.clock≤bodyPrice length+1 := by
  have code:=hash_code source.code installed
  cases pointerRead : eval source pointer with
  | none=>
    have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) [pointer,size,out]=none:=by
      simp only [eval] at pointerRead
      simp [evalListHOLFinite,evalListHOLExact,pointerRead]
    rw [evaluateHOLFiniteState_call,args]; simp
  | some pointerValue=>
    cases outRead : eval source out with
    | none=>
      have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) [pointer,size,out]=none:=by
        simp only [eval] at pointerRead sizeRead outRead
        simp [evalListHOLFinite,evalListHOLExact,pointerRead,sizeRead,outRead]
      rw [evaluateHOLFiniteState_call,args]; simp
    | some outValue=>
      have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) [pointer,size,out]=
          some [pointerValue,.val (.word (BitVec.ofNat 64 length)),outValue]:=by
        simp only [eval] at pointerRead sizeRead outRead
        simp [evalListHOLFinite,evalListHOLExact,pointerRead,sizeRead,outRead]
      cases called : lookupCodeHOLFinite source.code.lookup (ofString "sha256") [pointerValue,.val (.word (BitVec.ofNat 64 length)),outValue] with
      | none=>rw [evaluateHOLFiniteState_call,args]; simp only; rw [called]; simp
      | some data=>
        obtain ⟨actual,callee,shape⟩:=data
        obtain ⟨pointerWord,sizeWord,outWord,pointerEq,sizeEq,outEq⟩:=CallNormal.three_scalar_words source.code.lookup (ofString "sha256")
          (ofString "p") (ofString "len") (ofString "out") (Code.body .hash) actual .one shape code pointerValue (.val (.word (BitVec.ofNat 64 length))) outValue callee called
        rw [pointerEq,outEq] at args
        exact call_cost source [pointer,size,out] pointerWord outWord length small installed args

theorem be32_globals (key : MlS) (code) : GlobalEffects.Preserves key code (CurrentStartup.Code.body .st_be32) :=
  (StraightBody.effects key code _ be32_supported).2

set_option maxRecDepth 100000 in
theorem be64_globals (key : MlS) (code) (installed : OriginalCode.Installed code) : GlobalEffects.Preserves key code (CurrentStartup.Code.body .st_be64) := by
  have swap : GlobalEffects.Preserves key code (CurrentStartup.Code.body .bswap64):=(StraightBody.effects key code _ bswap_supported).2
  have be32 (args : List (ExpHOL 64)) : GlobalEffects.Preserves key code (.call (some (none,none)) (ofString "st_be32") args):=
    GlobalEffects.call_body key code (some none) (ofString "st_be32") args
      (CurrentStartup.Code.formals .st_be32) (CurrentStartup.Code.body .st_be32) (CurrentStartup.Code.shape .st_be32)
      (CurrentStartup.Code.installed code installed .st_be32) (be32_globals key code)
  simp only [CurrentStartup.Code.body,CurrentStartup.Code.entry,CurrentStartup.Code.declaration,GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL,funDeclToHOL,Guest.Software.guestFn_st_be64,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none]
  apply GlobalEffects.sequence
  · apply GlobalEffects.conditional
    · apply GlobalEffects.scoped_body key code _ _ (ofString "bswap64") _ _
        (CurrentStartup.Code.formals .bswap64) (CurrentStartup.Code.body .bswap64) (CurrentStartup.Code.shape .bswap64)
        (CurrentStartup.Code.installed code installed .bswap64) swap
      exact GlobalEffects.sequence key code _ _ (GlobalEffects.store key code _ _) (GlobalEffects.returned key code _)
    · exact GlobalEffects.skip key code
  · exact GlobalEffects.sequence key code _ _ (be32 _) (GlobalEffects.sequence key code _ _ (be32 _) (GlobalEffects.returned key code _))

theorem finish_globals (key : MlS) (code) (installed : OriginalCode.Installed code) :
    GlobalEffects.Preserves key code (Code.body .finish) := by
  rw [finish_shape]
  apply GlobalEffects.declared
  apply GlobalEffects.sequence
  · apply GlobalEffects.loop
    exact GlobalEffects.sequence key code finishCall finishIncrement
      (GlobalEffects.call_body key code (some none) (ofString "st_be32") finishArguments
        (CurrentStartup.Code.formals .st_be32) (CurrentStartup.Code.body .st_be32) (CurrentStartup.Code.shape .st_be32)
        (CurrentStartup.Code.installed code installed .st_be32) (be32_globals key code))
      (GlobalEffects.assign key code (ofString "i") _)
  · exact GlobalEffects.returned key code _

theorem compression_call_globals (key : MlS) (code) (installed : OriginalCode.Installed code) (args : List (ExpHOL 64)) :
    GlobalEffects.Preserves key code (.call (some (none,none)) (ofString "sha256_block") args) :=
  GlobalEffects.call_body key code (some none) (ofString "sha256_block") args
    (Code.formals .block) (Code.body .block) (Code.shape .block) (Code.installed code installed .block) (block_globals key code)

theorem digest_call_globals (key : MlS) (code) (installed : OriginalCode.Installed code) (args : List (ExpHOL 64)) :
    GlobalEffects.Preserves key code (.call (some (none,none)) (ofString "sha256_finish") args) :=
  GlobalEffects.call_body key code (some none) (ofString "sha256_finish") args
    (Code.formals .finish) (Code.body .finish) (Code.shape .finish) (Code.installed code installed .finish) (finish_globals key code installed)

theorem final_tail_globals (key : MlS) (code) (installed : OriginalCode.Installed code) : GlobalEffects.Preserves key code finalTail := by
  unfold finalTail selectTotal storeLength absorbPad extraPad digestCall
  repeat' first
    | apply GlobalEffects.sequence
    | apply GlobalEffects.conditional
    | exact GlobalEffects.assign key code _ _
    | exact GlobalEffects.skip key code
    | exact GlobalEffects.returned key code _
    | exact compression_call_globals key code installed _
    | exact digest_call_globals key code installed _
    | exact GlobalEffects.call_body key code (some none) (ofString "st_be64") _
        (CurrentStartup.Code.formals .st_be64) (CurrentStartup.Code.body .st_be64) (CurrentStartup.Code.shape .st_be64)
        (CurrentStartup.Code.installed code installed .st_be64) (be64_globals key code installed)

theorem body_globals (key : MlS) (code) (installed : OriginalCode.Installed code) : GlobalEffects.Preserves key code (Code.body .hash) := by
  rw [hash_shape]
  have padding : GlobalEffects.Preserves key code afterBlocks:=by
    unfold afterBlocks paddingTail paddingFinish zeroPad copyPad padFirst
    repeat' first
      | exact final_tail_globals key code installed
      | apply GlobalEffects.sequence
      | apply GlobalEffects.declared
      | exact GlobalEffects.byte_store key code _ _
      | exact CurrentKeccak.Hash.zero_call_globals key code installed _
      | exact CurrentKeccak.Hash.copy_call_globals key code installed _
  have loop : GlobalEffects.Preserves key code blocks:=GlobalEffects.loop key code blockTest blockIteration
    (GlobalEffects.sequence key code blockCall blockIncrement (compression_call_globals key code installed blockArguments) (GlobalEffects.assign key code (ofString "i") _))
  exact GlobalEffects.sequence key code initCall _
    (GlobalEffects.call_body key code (some none) (ofString "sha256_state_init") [state]
      (Code.formals .stateInit) (Code.body .stateInit) (Code.shape .stateInit) (Code.installed code installed .stateInit) (state_globals key code))
    (GlobalEffects.declared key code (ofString "i") .one (.const 0#64) _ (GlobalEffects.sequence key code blocks afterBlocks loop padding))

theorem call_globals (key : MlS) (code) (installed : OriginalCode.Installed code) (args : List (ExpHOL 64)) :
    GlobalEffects.Preserves key code (.call (some (none,none)) (ofString "sha256") args) :=
  GlobalEffects.call_body key code (some none) (ofString "sha256") args
    (Code.formals .hash) (Code.body .hash) (Code.shape .hash) (Code.installed code installed .hash) (body_globals key code installed)

/-- Use the same actual two-argument lookup to identify the first scalar
formal. The second expression may read the current compression workspace. -/
theorem first_word_call_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (function firstName secondName : MlS) (body : ProgHOL 64) (shape : ShapeHOL)
    (first second : ExpHOL 64) (pointer query : BitVec 64) (different : firstName≠secondName)
    (code : source.code.lookup function=some ([(firstName,.one),(secondName,.one)],body,shape))
    (read : eval source first=some (.val (.word pointer)))
    (frame : ∀ callee : HolFiniteMapExact MlS (ValueHOL 64),∀ target value,
      callee.lookup firstName=some (.val (.word pointer))→
      evaluateHOLFiniteState (callEntryStateHOLFinite source callee) body=(some (.returned value),target)→ target.memory query=source.memory query)
    (actual : evaluateHOLFiniteState source (.call (some (none,none)) function [first,second])=(none,post)) : post.memory query=source.memory query := by
  classical
  obtain ⟨positive,args,actualBody,callee,actualShape,target,value,arguments,called,bodyRun,checked,endpoint,fields⟩:=
    CallNormal.ignored_data source post function [first,second] actual
  have argsEq : ∃ stored,args=[.val (.word pointer),stored]:=by
    simp only [eval] at read
    change evalListHOLExact source.toExact [first,second]=some args at arguments
    cases valueRead : evalHOLExact source.toExact second with
    | none=>simp [evalListHOLExact,read,valueRead] at arguments
    | some stored=>exact ⟨stored,Option.some.inj (by simpa [evalListHOLExact,read,valueRead] using arguments.symm)⟩
  obtain ⟨stored,rfl⟩:=argsEq
  obtain ⟨bodyEq,binding⟩:=checked_pair_left source.code.lookup function firstName secondName body shape pointer stored different code actualBody callee actualShape called
  rw [bodyEq] at bodyRun
  rw [endpoint]
  exact frame callee target value binding bodyRun

set_option maxRecDepth 100000 in
theorem be32_frame_supported : ByteOutputFrame.accepts (ofString "p") 4 (CurrentStartup.Code.body .st_be32)=true := by
  simp only [CurrentStartup.Code.body,CurrentStartup.Code.entry,CurrentStartup.Code.declaration,GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL,funDeclToHOL,Guest.Software.guestFn_st_be32,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none]
  rfl

theorem be32_call_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (first second : ExpHOL 64) (pointer query : BitVec 64)
    (installed : OriginalCode.Installed source.code) (read : eval source first=some (.val (.word pointer)))
    (away : CopyGeneral.Away pointer query 4)
    (normal : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "st_be32") [first,second])=(none,post)) : post.memory query=source.memory query := by
  have code : source.code.lookup (ofString "st_be32")=some ([(ofString "p",.one),(ofString "v",.one)],CurrentStartup.Code.body .st_be32,.one):=by
    simpa only [CurrentStartup.Code.name,CurrentStartup.Code.formals,CurrentStartup.Code.shape,CurrentStartup.Code.entry,CurrentStartup.Code.declaration,
      GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,Guest.Software.guestFn_st_be32,paramToHOL,shapeToHOL,List.map_cons,List.map_nil]
      using CurrentStartup.Code.installed source.code installed .st_be32
  apply first_word_call_memory source post (ofString "st_be32") (ofString "p") (ofString "v") (CurrentStartup.Code.body .st_be32) .one
    first second pointer query (by decide) code read ?_ normal
  intro callee target value cell run
  have bodyFrame:=(ByteOutputFrame.sound (ofString "p") 4 (CurrentStartup.Code.body .st_be32) be32_frame_supported pointer query
    (fun offset inside=>(away offset inside).2) (callEntryStateHOLFinite source callee) cell).1
  rw [run] at bodyFrame
  exact bodyFrame

theorem finish_other (key : MlS) (different : key≠ofString "i") : LocalPrefix key finishIteration :=
  .seq (.call none _ _ (by simp)) (.assign _ _ different)

theorem finish_step_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer query : BitVec 64) (index : Nat)
    (installed : OriginalCode.Installed source.code) (active : index<8)
    (output : source.locals.lookup (ofString "out")=some (.val (.word pointer)))
    (position : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index))))
    (away : CopyGeneral.Away pointer query 32) (run : evaluateHOLFiniteState source finishIteration=(none,post)) : post.memory query=source.memory query := by
  obtain ⟨middle,normal,remaining⟩:=sequence_none source post finishCall finishIncrement run
  let address : ExpHOL 64:=.op .add [localVar "out",.panop .mul [localVar "i",.const 4#64]]
  let expression : ExpHOL 64:=.load .one (.op .add [localVar "stp",.panop .mul [localVar "i",.const 8#64]])
  have read : eval source address=some (.val (.word (pointer+BitVec.ofNat 64 (4*index)))):=by
    simp [eval,address,evalHOLExact,evalListHOLExact,toExact,localVar,output,position,valueIsWord,valueWord,wordOpHOL,wordOp,panOpHOL,BitVec.ofNat_mul,Nat.mul_comm]
  have called:=be32_call_memory source middle address expression (pointer+BitVec.ofNat 64 (4*index)) query installed read
    (CopyGeneral.Away.subrange pointer query 32 (4*index) 4 away (by omega)) normal
  have assigned:=MemoryAt.assign_current middle .local (ofString "i") (.op .add [localVar "i",.const 1#64]) query
  change evaluateHOLFiniteState middle (.assign .local (ofString "i") (.op .add [localVar "i",.const 1#64]))=(none,post) at remaining
  rw [remaining] at assigned
  exact assigned.trans called

theorem finish_loop_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer query : BitVec 64)
    (installed : OriginalCode.Installed source.code)
    (output : source.locals.lookup (ofString "out")=some (.val (.word pointer)))
    (position : source.locals.lookup (ofString "i")=some (.val (.word 0#64)))
    (away : CopyGeneral.Away pointer query 32)
    (run : evaluateHOLFiniteState source (.while finishTest finishIteration)=(none,post)) : post.memory query=source.memory query := by
  have summary:=MemoryAt.constant_loop_normal source.code (ofString "i") (ofString "stp") finishIteration 8 query (by decide)
    finish_iteration_local.summary_full finish_iteration_advance
    (fun current=>current.locals.lookup (ofString "out")=some (.val (.word pointer))) (by intro current actual; exact actual)
    (by intro current codeEq currentOutput index active currentPosition target bodyRun
        have localFrame:=(finish_other (ofString "out") (by decide)).summary_full current
        unfold LocalSummary at localFrame
        rw [bodyRun] at localFrame
        exact ⟨(localFrame.1 rfl).trans currentOutput,finish_step_memory current target pointer query index (codeEq.symm ▸ installed) active currentOutput currentPosition away bodyRun⟩)
    source post 0 rfl output (by decide) position run
  exact summary.2.2

/-- Normal original digest output touches only its32 output bytes. The actual
BE32 calls supply their own successful scalar reads. -/
theorem finish_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer query : BitVec 64)
    (installed : OriginalCode.Installed source.code)
    (output : source.locals.lookup (ofString "out")=some (.val (.word pointer))) (away : CopyGeneral.Away pointer query 32)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source (Code.body .finish)=(some (.returned value),post)) : post.memory query=source.memory query := by
  rw [finish_shape] at run
  refine MemoryAt.declaration_returned source post "i" (.const 0#64) 0#64 query finishTail value rfl ?_ run
  intro inner remaining
  let entry:=QueryBranch.bind source "i" 0#64
  have nextOutput : entry.locals.lookup (ofString "out")=some (.val (.word pointer)):=
    (bind_lookup_other source "i" "out" 0#64 (by decide)).trans output
  have safe : LocalPrefix (ofString "out") (.while finishTest finishIteration):=.loop _ (finish_other (ofString "out") (by decide))
  obtain ⟨middle,normal,returned⟩:=sequence_returned entry inner _ (.return (.const 0#64)) value (safe.summary_full entry).2.1 remaining
  have frame:=finish_loop_memory entry middle pointer query installed nextOutput (bind_lookup_same _ _ _) away normal
  have finalFrame:=MemoryAt.return_current middle (.const 0#64) query
  rw [returned] at finalFrame
  exact finalFrame.trans frame

theorem state_call_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (stp query : BitVec 64)
    (installed : OriginalCode.Installed source.code) (args : List (ExpHOL 64))
    (read : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) args=some [.val (.word stp)])
    (away : ∀ offset : Nat,offset<64→ query≠stp+BitVec.ofNat 64 offset)
    (normal : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "sha256_state_init") args)=(none,post)) :
    post.memory query=source.memory query := by
  have code : source.code.lookup (ofString "sha256_state_init")=some ([(ofString "stp",.one)],Code.body .stateInit,.one):=by
    simpa only [Code.name,Code.formals,Code.shape,Code.entry,Code.declaration,GasBudget.OriginalCodeEnvironment.originalEntry,
      declToHOL,funDeclToHOL,Guest.Software.guestFn_sha256_state_init,paramToHOL,shapeToHOL,List.map_cons,List.map_nil]
      using Code.installed source.code installed .stateInit
  obtain ⟨callee,called,cell⟩:=word_environment source.code.lookup (ofString "sha256_state_init") (ofString "stp") (Code.body .stateInit) .one stp code
  apply MemoryAt.call_normal source post (ofString "sha256_state_init") args [.val (.word stp)] (Code.body .stateInit) callee .one query read called ?_ normal
  intro target value run
  have frame:=state_memory (callEntryStateHOLFinite source callee) stp query cell away
  rw [run] at frame
  exact frame

set_option maxRecDepth 100000 in
theorem compression_call_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (stp blk query : BitVec 64)
    (installed : OriginalCode.Installed source.code) (args : List (ExpHOL 64))
    (read : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) args=some [.val (.word stp),.val (.word blk)])
    (away : ∀ offset : Nat,offset<64→ query≠stp+BitVec.ofNat 64 offset)
    (normal : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "sha256_block") args)=(none,post)) :
    post.memory query=source.memory query := by
  have code : source.code.lookup (ofString "sha256_block")=some ([(ofString "stp",.one),(ofString "blk",.one)],Code.body .block,.one):=by
    simpa only [Code.name,Code.formals,Code.shape,Code.entry,Code.declaration,GasBudget.OriginalCodeEnvironment.originalEntry,
      declToHOL,funDeclToHOL,Guest.Software.guestFn_sha256_block,paramToHOL,shapeToHOL,List.map_cons,List.map_nil]
      using Code.installed source.code installed .block
  obtain ⟨callee,called,cell,blockCell⟩:=word_pair_environment source.code.lookup (ofString "sha256_block") (ofString "stp") (ofString "blk")
    (Code.body .block) .one stp blk (by decide) code
  apply MemoryAt.call_normal source post (ofString "sha256_block") args [.val (.word stp),.val (.word blk)] (Code.body .block) callee .one query read called ?_ normal
  intro target value run
  have frame:=block_memory (callEntryStateHOLFinite source callee) stp query cell away
  rw [run] at frame
  exact frame

theorem digest_call_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (stp out query : BitVec 64)
    (installed : OriginalCode.Installed source.code) (args : List (ExpHOL 64))
    (read : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) args=some [.val (.word stp),.val (.word out)])
    (away : CopyGeneral.Away out query 32)
    (normal : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "sha256_finish") args)=(none,post)) :
    post.memory query=source.memory query := by
  have code : source.code.lookup (ofString "sha256_finish")=some ([(ofString "stp",.one),(ofString "out",.one)],Code.body .finish,.one):=by
    simpa only [Code.name,Code.formals,Code.shape,Code.entry,Code.declaration,GasBudget.OriginalCodeEnvironment.originalEntry,
      declToHOL,funDeclToHOL,Guest.Software.guestFn_sha256_finish,paramToHOL,shapeToHOL,List.map_cons,List.map_nil]
      using Code.installed source.code installed .finish
  obtain ⟨callee,called,stateCell,cell⟩:=word_pair_environment source.code.lookup (ofString "sha256_finish") (ofString "stp") (ofString "out")
    (Code.body .finish) .one stp out (by decide) code
  exact MemoryAt.call_normal source post (ofString "sha256_finish") args [.val (.word stp),.val (.word out)] (Code.body .finish) callee .one query read called
    (fun target value run=>finish_memory (callEntryStateHOLFinite source callee) target out query installed cell away value run) normal

set_option maxRecDepth 100000 in
/-- Only the compression-state pointer is needed to frame a normal block
call; its other argument may be any actual successful scalar expression. -/
theorem compression_first_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (first second : ExpHOL 64) (stp query : BitVec 64)
    (installed : OriginalCode.Installed source.code) (read : eval source first=some (.val (.word stp)))
    (away : ∀ offset : Nat,offset<64→ query≠stp+BitVec.ofNat 64 offset)
    (normal : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "sha256_block") [first,second])=(none,post)) :
    post.memory query=source.memory query := by
  have code : source.code.lookup (ofString "sha256_block")=some ([(ofString "stp",.one),(ofString "blk",.one)],Code.body .block,.one):=by
    simpa only [Code.name,Code.formals,Code.shape,Code.entry,Code.declaration,GasBudget.OriginalCodeEnvironment.originalEntry,
      declToHOL,funDeclToHOL,Guest.Software.guestFn_sha256_block,paramToHOL,shapeToHOL,List.map_cons,List.map_nil]
      using Code.installed source.code installed .block
  apply first_word_call_memory source post (ofString "sha256_block") (ofString "stp") (ofString "blk") (Code.body .block) .one
    first second stp query (by decide) code read ?_ normal
  intro callee target value cell run
  have frame:=block_memory (callEntryStateHOLFinite source callee) stp query cell away
  rw [run] at frame
  exact frame

theorem blocks_globals (key : MlS) (code) (installed : OriginalCode.Installed code) : GlobalEffects.Preserves key code blocks :=
  GlobalEffects.loop key code blockTest blockIteration (GlobalEffects.sequence key code blockCall blockIncrement
    (compression_call_globals key code installed blockArguments) (GlobalEffects.assign key code (ofString "i") _))

/-- Every real normal block loop only writes the64-byte state. No initialized
input block contents, fixed counter, digest value or later success is needed. -/
theorem blocks_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (stp query : BitVec 64)
    (installed : OriginalCode.Installed source.code)
    (stateCell : source.globals.lookup (ofString "sha_st")=some (.val (.word stp)))
    (away : ∀ offset : Nat,offset<64→ query≠stp+BitVec.ofNat 64 offset)
    (normal : evaluateHOLFiniteState source blocks=(none,post)) : post.memory query=source.memory query := by
  let invariant:=fun current : PanSemStateFiniteExact 64 Guest.HostMemory=>current.globals.lookup (ofString "sha_st")=some (.val (.word stp))
  apply MemoryAt.loop_normal source.code (ofString "len") blockTest blockIteration query block_iteration_local.summary_full invariant ?_
    source post rfl stateCell normal
  intro current codeEq ready observed read nonzero funded target bodyRun
  change evaluateHOLFiniteState (decClockHOLFinite current) (.seq blockCall blockIncrement)=(none,target) at bodyRun
  have currentInstalled : OriginalCode.Installed current.code:=by rw [codeEq]; exact installed
  have kept:=(GlobalEffects.sequence (ofString "sha_st") current.code blockCall blockIncrement
    (compression_call_globals (ofString "sha_st") current.code currentInstalled blockArguments) (GlobalEffects.assign (ofString "sha_st") current.code (ofString "i") _))
    (decClockHOLFinite current) rfl
  rw [bodyRun] at kept
  have nextState : invariant target:=(congrArg Prod.snd kept).trans ready
  obtain ⟨middle,front,back⟩:=sequence_none (decClockHOLFinite current) target blockCall blockIncrement bodyRun
  have firstRead : eval (decClockHOLFinite current) (.var .global (ofString "sha_st"))=some (.val (.word stp)):=by
    simpa only [eval,evalHOLExact,toExact,invariant,decClockHOLFinite,decClockHOLExact] using ready
  have frame:=compression_first_memory (decClockHOLFinite current) middle (.var .global (ofString "sha_st")) (.op .add [localVar "p",localVar "i"])
    stp query currentInstalled firstRead away front
  have assigned:=MemoryAt.assign_current middle .local (ofString "i") (.op .add [localVar "i",.const 64#64]) query
  change (evaluateHOLFiniteState middle blockIncrement).2.memory query=middle.memory query at assigned
  rw [back] at assigned
  exact ⟨nextState,assigned.trans frame⟩

theorem blocks_local (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (key : MlS) (different : key≠ofString "i")
    (normal : evaluateHOLFiniteState source blocks=(none,post)) : post.locals.lookup key=source.locals.lookup key :=
  counter_loop_local source post blockTest (ofString "sha256_block") blockArguments "i" (.op .add [localVar "i",.const 64#64]) key different normal

/-- Actual allocated SHA workspace. No hash value, mapped input read or
future successful call is included. -/
structure Environment (source : PanSemStateFiniteExact 64 Guest.HostMemory) (stp pad : BitVec 64) : Prop where
  installed : OriginalCode.Installed source.code
  domain : source.memaddrs=InitE.ordinaryDomain
  stateGlobal : source.globals.lookup (ofString "sha_st")=some (.val (.word stp))
  padGlobal : source.globals.lookup (ofString "sha_pad")=some (.val (.word pad))
  stateArena : AllocatedBytes.Arena stp 64
  padArena : AllocatedBytes.Arena pad 128
  stateAligned : stp.toNat%8=0
  padAligned : pad.toNat%8=0

theorem Environment.of_frame {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {stp pad : BitVec 64}
    (ready : Environment source stp pad) (same : LocalEffects.erase target=LocalEffects.erase source) : Environment target stp pad := by
  have code:=congrArg PanSemStateFiniteExact.code same
  have domain:=congrArg PanSemStateFiniteExact.memaddrs same
  have globals:=congrArg PanSemStateFiniteExact.globals same
  change target.code=source.code at code
  change target.memaddrs=source.memaddrs at domain
  change target.globals=source.globals at globals
  exact ⟨by rw [code]; exact ready.installed,domain.trans ready.domain,by rw [globals]; exact ready.stateGlobal,
    by rw [globals]; exact ready.padGlobal,ready.stateArena,ready.padArena,ready.stateAligned,ready.padAligned⟩

theorem Environment.after {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {stp pad : BitVec 64}
    (ready : Environment source stp pad) (program : ProgHOL 64) (result : Option (PanSemResultExact 64))
    (globals : ∀ key,GlobalEffects.Preserves key source.code program)
    (run : evaluateHOLFiniteState source program=(result,target)) : Environment target stp pad := by
  have fields:=evaluation_fields source target program result run
  have state:=globals (ofString "sha_st") source rfl
  have padding:=globals (ofString "sha_pad") source rfl
  rw [run] at state padding
  exact ⟨by rw [fields.2.2.2]; exact ready.installed,fields.1.trans ready.domain,
    (congrArg Prod.snd state).trans ready.stateGlobal,(congrArg Prod.snd padding).trans ready.padGlobal,
    ready.stateArena,ready.padArena,ready.stateAligned,ready.padAligned⟩

structure Frame (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (stp pad query : BitVec 64) : Prop where
  environment : Environment target stp pad
  memory : target.memory query=source.memory query
  locals : ∀ key,target.locals.lookup key=source.locals.lookup key

theorem Frame.cell {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {stp pad query : BitVec 64}
    (frame : Frame source target stp pad query) (key : MlS) (value : ValueHOL 64)
    (cell : source.locals.lookup key=some value) : target.locals.lookup key=some value := (frame.locals key).trans cell

theorem zero_frame (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (stp pad dst query : BitVec 64) (length : Nat)
    (environment : Environment source stp pad) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (Zero.values dst length))
    (arena : AllocatedBytes.Arena dst length) (aligned : dst.toNat%8=0) (multiple : length%8=0)
    (away : ∀ offset<length,query≠byteAddress dst offset)
    (run : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "memzero") arguments)=(none,post)) : Frame source post stp pad query :=
  ⟨environment.after _ _ (fun key=>CurrentKeccak.Hash.zero_call_globals key source.code environment.installed arguments) run,
   MemoryAt.zero_normal source post arguments dst query length args environment.installed environment.domain arena aligned multiple away run,
   fun key=>CallNormal.ignored_lookup source post key (ofString "memzero") arguments run⟩

theorem copy_frame (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (stp pad src dst query : BitVec 64) (length : Nat)
    (environment : Environment source stp pad) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (CopyGeneral.values dst src length))
    (inputArena : AllocatedBytes.Arena src length) (outArena : AllocatedBytes.Arena dst length) (away : CopyGeneral.Away dst query length)
    (run : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "memcpy") arguments)=(none,post)) : Frame source post stp pad query :=
  ⟨environment.after _ _ (fun key=>CurrentKeccak.Hash.copy_call_globals key source.code environment.installed arguments) run,
   MemoryAt.copy_normal source post arguments src dst query length args environment.installed environment.domain inputArena outArena away run,
   fun key=>CallNormal.ignored_lookup source post key (ofString "memcpy") arguments run⟩

theorem compression_frame (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (stp pad blk query : BitVec 64)
    (environment : Environment source stp pad) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some [.val (.word stp),.val (.word blk)])
    (away : ∀ offset : Nat,offset<64→ query≠stp+BitVec.ofNat 64 offset)
    (run : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "sha256_block") arguments)=(none,post)) : Frame source post stp pad query :=
  ⟨environment.after _ _ (fun key=>compression_call_globals key source.code environment.installed arguments) run,
   compression_call_memory source post stp blk query environment.installed arguments args away run,
   fun key=>CallNormal.ignored_lookup source post key (ofString "sha256_block") arguments run⟩

theorem byte_frame (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (stp pad address query : BitVec 64)
    (environment : Environment source stp pad) (destination expression : ExpHOL 64)
    (read : eval source destination=some (.val (.word address))) (away : query≠panByteAlignHOL (width:=64) address)
    (run : evaluateHOLFiniteState source (.storeByte destination expression)=(none,post)) : Frame source post stp pad query := by
  have frame:=byte_store_normal_frame source post destination expression address read run
  exact ⟨environment.after _ _ (fun key=>GlobalEffects.byte_store key source.code destination expression) run,
    frame.2 query away,by intro key; rw [frame.1]⟩

theorem digest_frame (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (stp pad out query : BitVec 64)
    (environment : Environment source stp pad) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some [.val (.word stp),.val (.word out)])
    (away : CopyGeneral.Away out query 32)
    (run : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "sha256_finish") arguments)=(none,post)) : Frame source post stp pad query :=
  ⟨environment.after _ _ (fun key=>digest_call_globals key source.code environment.installed arguments) run,
   digest_call_memory source post stp out query environment.installed arguments args away run,
   fun key=>CallNormal.ignored_lookup source post key (ofString "sha256_finish") arguments run⟩

def be64Test : ExpHOL 64:=.cmp .equal (.op .and [localVar "p",.const 7#64]) (.const 0#64)
def be64FastTail : ProgHOL 64:=.seq (.store (localVar "p") (localVar "w")) (.return (.const 0#64))
def be64Fast : ProgHOL 64:=.decCall (ofString "w") .one (ofString "bswap64") [localVar "v"] be64FastTail
def be64SlowFirst : ProgHOL 64:=.call (some (none,none)) (ofString "st_be32") [localVar "p",.shift .lsr (localVar "v") (.const 32#64)]
def be64SlowSecond : ProgHOL 64:=.call (some (none,none)) (ofString "st_be32") [.op .add [localVar "p",.const 4#64],localVar "v"]
def be64Slow : ProgHOL 64:=.seq be64SlowFirst (.seq be64SlowSecond (.return (.const 0#64)))

set_option maxRecDepth 100000 in
theorem be64_shape : CurrentStartup.Code.body .st_be64=.seq (.ite be64Test be64Fast .skip) be64Slow := by
  simp only [CurrentStartup.Code.body,CurrentStartup.Code.entry,CurrentStartup.Code.declaration,GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL,funDeclToHOL,Guest.Software.guestFn_st_be64,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,
    be64Test,be64Fast,be64FastTail,be64Slow,be64SlowFirst,be64SlowSecond,localVar]

set_option maxRecDepth 100000 in
theorem bswap_local (code) : LocalEffects.Preserves code (CurrentStartup.Code.body .bswap64) := by
  simp only [CurrentStartup.Code.body,CurrentStartup.Code.entry,CurrentStartup.Code.declaration,GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL,funDeclToHOL,Guest.Software.guestFn_bswap64,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none]
  repeat' first | apply LocalEffects.sequence | exact LocalEffects.assign code _ _ | exact LocalEffects.returned code _

theorem be64_fast_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer input query : BitVec 64)
    (installed : OriginalCode.Installed source.code)
    (pCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (vCell : source.locals.lookup (ofString "v")=some (.val (.word input)))
    (away : query≠pointer) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source be64Fast=(some (.returned value),post)) : post.memory query=source.memory query := by
  have code : source.code.lookup (ofString "bswap64")=some ([(ofString "x",.one)],CurrentStartup.Code.body .bswap64,.one):=by
    simpa only [CurrentStartup.Code.name,CurrentStartup.Code.formals,CurrentStartup.Code.shape,CurrentStartup.Code.entry,CurrentStartup.Code.declaration,
      GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,Guest.Software.guestFn_bswap64,paramToHOL,shapeToHOL,List.map_cons,List.map_nil]
      using CurrentStartup.Code.installed source.code installed .bswap64
  obtain ⟨callee,called,cell⟩:=word_environment source.code.lookup (ofString "bswap64") (ofString "x") (CurrentStartup.Code.body .bswap64) .one input code
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) [localVar "v"]=some [.val (.word input)]:=by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,vCell]
  obtain ⟨funded,target,returned,inner,run,checked,remaining,endpoint⟩:=CallNormal.scoped_normal source post "w" .one (ofString "bswap64")
    [localVar "v"] [.val (.word input)] (CurrentStartup.Code.body .bswap64) be64FastTail callee .one args called value normal
  have typed : shapeOfHOLExact returned=.one:=(shapeEqHOL_eq_true _ _).mp (Bool.and_eq_true_iff.mp checked).1
  obtain ⟨word,rfl⟩:=ScalarShape.word returned typed
  have pure:=(bswap_local source.code) (callEntryStateHOLFinite source callee) rfl
  rw [run] at pure
  have memory : target.memory query=source.memory query:=congrFun (LocalEffects.memory_of_erase (callEntryStateHOLFinite source callee) target pure) query
  let entered:=CallNormal.continuationEntry source target "w" (.val (.word word))
  have pointerCell : entered.locals.lookup (ofString "p")=some (.val (.word pointer)):=by
    simpa only [entered,CallNormal.continuationEntry] using
      (MemoryAt.set_lookup_other {target with locals:=source.locals} (ofString "w") (ofString "p") (.val (.word word)) (by decide)).trans pCell
  have wordCell : entered.locals.lookup (ofString "w")=some (.val (.word word)):=by
    simp [entered,CallNormal.continuationEntry,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
  have address : eval entered (localVar "p")=some (.val (.word pointer)):=by simp [eval,evalHOLExact,toExact,localVar,pointerCell]
  have storedValue : eval entered (localVar "w")=some (.val (.word word)):=by simp [eval,evalHOLExact,toExact,localVar,wordCell]
  obtain ⟨middle,stored,finished⟩:=sequence_returned entered inner (.store (localVar "p") (localVar "w")) (.return (.const 0#64)) value
    ((LocalPrefix.store (key:=ofString "p") _ _).summary_full entered).2.1 remaining
  have first:=MemoryAt.scalar_store_normal entered middle (localVar "p") (localVar "w") pointer query address
    (by intro actual read; rw [storedValue] at read; cases read; simp [flattenHOL]) away stored
  have last:=MemoryAt.return_current middle (.const 0#64) query
  rw [finished] at last
  rw [endpoint]
  exact last.trans (first.trans memory)

theorem be64_slow_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer query : BitVec 64)
    (installed : OriginalCode.Installed source.code)
    (pCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (away : CopyGeneral.Away pointer query 8) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source be64Slow=(some (.returned value),post)) : post.memory query=source.memory query := by
  have safe : LocalPrefix (ofString "p") be64SlowFirst:=.call none _ _ (by simp)
  obtain ⟨middle,first,remaining⟩:=sequence_returned source post be64SlowFirst _ value (safe.summary_full source).2.1 normal
  have firstRead : eval source (localVar "p")=some (.val (.word pointer)):=by simp [eval,evalHOLExact,toExact,localVar,pCell]
  have firstFrame:=be32_call_memory source middle (localVar "p") (.shift .lsr (localVar "v") (.const 32#64)) pointer query installed firstRead
    (by simpa only [BitVec.add_zero] using CopyGeneral.Away.subrange pointer query 8 0 4 away (by decide)) first
  have nextP : middle.locals.lookup (ofString "p")=some (.val (.word pointer)):=
    (CallNormal.ignored_lookup source middle (ofString "p") (ofString "st_be32") [localVar "p",.shift .lsr (localVar "v") (.const 32#64)] first).trans pCell
  have nextInstalled : OriginalCode.Installed middle.code:=by rw [(evaluation_fields source middle be64SlowFirst none first).2.2.2]; exact installed
  have secondSafe : LocalPrefix (ofString "p") be64SlowSecond:=.call none _ _ (by simp)
  obtain ⟨last,second,finished⟩:=sequence_returned middle post be64SlowSecond (.return (.const 0#64)) value (secondSafe.summary_full middle).2.1 remaining
  have secondRead : eval middle (.op .add [localVar "p",.const 4#64])=some (.val (.word (pointer+4#64))):=by
    simp [eval,evalHOLExact,evalListHOLExact,toExact,localVar,nextP,valueIsWord,valueWord,wordOpHOL,wordOp]
  have secondFrame:=be32_call_memory middle last (.op .add [localVar "p",.const 4#64]) (localVar "v") (pointer+4#64) query nextInstalled secondRead
    (CopyGeneral.Away.subrange pointer query 8 4 4 away (by decide)) second
  have finalFrame:=MemoryAt.return_current last (.const 0#64) query
  rw [finished] at finalFrame
  exact finalFrame.trans (secondFrame.trans firstFrame)

/-- Both actual writer paths retain every word outside the eight output bytes.
Normal return supplies any successful reads/stores; no mapping is assumed. -/
theorem be64_body_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer input query : BitVec 64)
    (installed : OriginalCode.Installed source.code)
    (pCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (vCell : source.locals.lookup (ofString "v")=some (.val (.word input)))
    (away : CopyGeneral.Away pointer query 8) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (CurrentStartup.Code.body .st_be64)=(some (.returned value),post)) : post.memory query=source.memory query := by
  have test : eval source be64Test=some (.val (.word (if pointer &&& 7#64=0#64 then 1#64 else 0#64))):=by
    by_cases aligned : pointer &&& 7#64=0#64
    all_goals simp [eval,evalHOLExact,evalListHOLExact,toExact,be64Test,localVar,pCell,valueIsWord,valueWord,wordOpHOL,wordOp,AndOp.and,
      Flapjack.Compiler.Encoders.Asm.wordCmpHOL,aligned]
  simp only [eval] at test
  rw [be64_shape] at normal
  by_cases aligned : pointer &&& 7#64=0#64
  · have gate : evaluateHOLFiniteState source (.ite be64Test be64Fast .skip)=evaluateHOLFiniteState source be64Fast:=by
      rw [evaluateHOLFiniteState_ite,test,if_pos aligned]
      simp
    have whole : evaluateHOLFiniteState source (.seq be64Fast be64Slow)=(some (.returned value),post):=by
      rw [evaluateHOLFiniteState_seq_line780]
      rwa [evaluateHOLFiniteState_seq_line780,gate] at normal
    have stops : NoFallthrough be64Fast:=NoFallthrough.scoped _ _ _ _ _ (NoFallthrough.sequence _ _ (NoFallthrough.returned _))
    have actual:=NoFallthrough.returning_prefix source post be64Fast be64Slow stops value whole
    have different : query≠pointer:=by simpa only [byteAddress,BitVec.add_zero] using (away 0 (by decide)).1
    exact be64_fast_memory source post pointer input query installed pCell vCell different value actual
  · have gate : evaluateHOLFiniteState source (.ite be64Test be64Fast .skip)=(none,source):=by
      rw [evaluateHOLFiniteState_ite,test,if_neg aligned]
      simp [evaluateHOLFiniteState_skip]
    rw [StateSteps.next_sequence source source _ _ gate (Nat.le_refl _)] at normal
    exact be64_slow_memory source post pointer query installed pCell away value normal

theorem be64_call_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer input query : BitVec 64)
    (installed : OriginalCode.Installed source.code) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some [.val (.word pointer),.val (.word input)])
    (away : CopyGeneral.Away pointer query 8)
    (normal : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "st_be64") arguments)=(none,post)) : post.memory query=source.memory query := by
  have code : source.code.lookup (ofString "st_be64")=some ([(ofString "p",.one),(ofString "v",.one)],CurrentStartup.Code.body .st_be64,.one):=by
    simpa only [CurrentStartup.Code.name,CurrentStartup.Code.formals,CurrentStartup.Code.shape,CurrentStartup.Code.entry,CurrentStartup.Code.declaration,
      GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,Guest.Software.guestFn_st_be64,paramToHOL,shapeToHOL,List.map_cons,List.map_nil]
      using CurrentStartup.Code.installed source.code installed .st_be64
  obtain ⟨callee,called,pCell,vCell⟩:=word_pair_environment source.code.lookup (ofString "st_be64") (ofString "p") (ofString "v")
    (CurrentStartup.Code.body .st_be64) .one pointer input (by decide) code
  exact MemoryAt.call_normal source post (ofString "st_be64") arguments [.val (.word pointer),.val (.word input)] (CurrentStartup.Code.body .st_be64) callee .one query args called
    (fun target value run=>be64_body_memory (callEntryStateHOLFinite source callee) target pointer input query installed pCell vCell away value run) normal

theorem be64_frame (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (stp pad pointer input query : BitVec 64)
    (environment : Environment source stp pad) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some [.val (.word pointer),.val (.word input)])
    (away : CopyGeneral.Away pointer query 8)
    (run : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "st_be64") arguments)=(none,post)) : Frame source post stp pad query :=
  ⟨environment.after _ _ (fun key=>GlobalEffects.call_body key source.code (some none) (ofString "st_be64") arguments
      (CurrentStartup.Code.formals .st_be64) (CurrentStartup.Code.body .st_be64) (CurrentStartup.Code.shape .st_be64)
      (CurrentStartup.Code.installed source.code environment.installed .st_be64) (be64_globals key source.code environment.installed)) run,
   be64_call_memory source post pointer input query environment.installed arguments args away run,
   fun key=>CallNormal.ignored_lookup source post key (ofString "st_be64") arguments run⟩

theorem select_local (key : MlS) (different : key≠ofString "total") : LocalPrefix key selectTotal :=
  .ite _ (.assign _ _ different) .skip

theorem select_pure (code) : LocalEffects.Preserves code selectTotal :=
  LocalEffects.conditional code _ _ _ (LocalEffects.assign code (ofString "total") _) (LocalEffects.skip code)

/-- The real normal branch supplies one of the two actual padding sizes. -/
theorem select_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (totalCell : source.locals.lookup (ofString "total")=some (.val (.word 64#64)))
    (normal : evaluateHOLFiniteState source selectTotal=(none,post)) :
    ∃ total : Nat,(total=64 ∨ total=128) ∧ post.locals.lookup (ofString "total")=some (.val (.word (BitVec.ofNat 64 total))) := by
  rcases conditional_none source post _ _ _ normal with assigned|skipped
  · have same:=assign_none source post "total" (.const 128#64) 128#64 rfl assigned
    refine ⟨128,Or.inr rfl,?_⟩
    rw [same]
    exact bind_lookup_same _ _ _
  · rw [evaluateHOLFiniteState_skip] at skipped
    have same : source=post:=congrArg Prod.snd skipped
    exact ⟨64,Or.inl rfl,same ▸ totalCell⟩

theorem extra_globals (key : MlS) (code) (installed : OriginalCode.Installed code) : GlobalEffects.Preserves key code extraPad :=
  GlobalEffects.conditional key code _ _ _ (compression_call_globals key code installed _) (GlobalEffects.skip key code)

theorem extra_frame (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (stp pad query : BitVec 64)
    (environment : Environment source stp pad)
    (away : ∀ offset : Nat,offset<64→ query≠stp+BitVec.ofNat 64 offset)
    (normal : evaluateHOLFiniteState source extraPad=(none,post)) : Frame source post stp pad query := by
  have memory : post.memory query=source.memory query:=by
    rcases conditional_none source post _ _ _ normal with called|skipped
    · have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address))
          [state,.op .add [GeneralSha.pad,.const 64#64]]=some [.val (.word stp),.val (.word (pad+64#64))]:=by
        simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,state,GeneralSha.pad,environment.stateGlobal,environment.padGlobal,
          valueIsWord,valueWord,wordOpHOL,wordOp]
      exact compression_call_memory source post stp (pad+64#64) query environment.installed _ args away called
    · rw [evaluateHOLFiniteState_skip] at skipped
      exact (congrArg (fun result=>result.2.memory query) skipped).symm
  refine ⟨environment.after _ _ (fun key=>extra_globals key source.code environment.installed) normal,memory,?_⟩
  intro key
  have safe : LocalPrefix key extraPad:=.ite _ (.call none _ _ (by simp)) .skip
  have summary:=safe.summary_full source
  unfold LocalSummary at summary
  rw [normal] at summary
  exact summary.1 rfl

/-- The selected64/128-byte padding size determines a real final eight-byte
subrange. All arguments are the actual current global/local reads. -/
theorem length_frame (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (stp pad query : BitVec 64) (length total : Nat)
    (environment : Environment source stp pad) (size : total=64 ∨ total=128)
    (lenCell : source.locals.lookup (ofString "len")=some (.val (.word (BitVec.ofNat 64 length))))
    (totalCell : source.locals.lookup (ofString "total")=some (.val (.word (BitVec.ofNat 64 total))))
    (away : CopyGeneral.Away pad query 128)
    (normal : evaluateHOLFiniteState source storeLength=(none,post)) : Frame source post stp pad query := by
  have bounds : 8≤total ∧ total≤128:=by rcases size with rfl|rfl <;> decide
  have difference : (pad+BitVec.ofNat 64 total)-8#64=pad+BitVec.ofNat 64 (total-8):=by
    rw [BitVec.sub_eq_add_neg,BitVec.add_assoc,←BitVec.sub_eq_add_neg]
    exact congrArg (fun offset=>pad+offset) (BitVec.ofNat_sub_ofNat_of_le total 8 (by decide) bounds.1)
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address))
      [.op .sub [.op .add [GeneralSha.pad,localVar "total"],.const 8#64],.shift .lsl (localVar "len") (.const 3#64)]=
      some [.val (.word (pad+BitVec.ofNat 64 (total-8))),.val (.word ((BitVec.ofNat 64 length)<<<3))]:=by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,GeneralSha.pad,localVar,environment.padGlobal,totalCell,lenCell,
      valueIsWord,valueWord,wordOpHOL,wordOp,wordShiftHOL,difference]
  exact be64_frame source post stp pad (pad+BitVec.ofNat 64 (total-8)) ((BitVec.ofNat 64 length)<<<3) query environment _ args
    (CopyGeneral.Away.subrange pad query 128 (total-8) 8 away (by omega)) normal

theorem final_tail_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (stp pad out query : BitVec 64) (length : Nat)
    (environment : Environment source stp pad)
    (lenCell : source.locals.lookup (ofString "len")=some (.val (.word (BitVec.ofNat 64 length))))
    (outCell : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (totalCell : source.locals.lookup (ofString "total")=some (.val (.word 64#64)))
    (stateAway : ∀ offset : Nat,offset<64→ query≠stp+BitVec.ofNat 64 offset)
    (padAway : CopyGeneral.Away pad query 128) (outAway : CopyGeneral.Away out query 32)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source finalTail=(some (.returned value),post)) : post.memory query=source.memory query := by
  have selectSafe:=select_local (ofString "len") (by decide)
  obtain ⟨selected,selectedRun,afterSelect⟩:=sequence_returned source post selectTotal _ value (selectSafe.summary_full source).2.1 normal
  obtain ⟨total,size,totalRead⟩:=select_normal source selected totalCell selectedRun
  have pure:=select_pure source.code source rfl
  rw [selectedRun] at pure
  have selectedEnvironment:=environment.of_frame pure
  have selectedLen : selected.locals.lookup (ofString "len")=some (.val (.word (BitVec.ofNat 64 length))):=by
    have kept:=selectSafe.summary_full source
    unfold LocalSummary at kept
    rw [selectedRun] at kept
    exact (kept.1 rfl).trans lenCell
  have selectedOut : selected.locals.lookup (ofString "out")=some (.val (.word out)):=by
    have kept:=(select_local (ofString "out") (by decide)).summary_full source
    unfold LocalSummary at kept
    rw [selectedRun] at kept
    exact (kept.1 rfl).trans outCell
  have first : selected.memory query=source.memory query:=congrFun (LocalEffects.memory_of_erase source selected pure) query
  obtain ⟨written,lengthRun,afterLength⟩:=sequence_returned selected post storeLength _ value
    ((LocalPrefix.call (key:=ofString "out") none _ _ (by simp)).summary_full selected).2.1 afterSelect
  have second:=length_frame selected written stp pad query length total selectedEnvironment size selectedLen totalRead padAway lengthRun
  obtain ⟨absorbed,absorbRun,afterAbsorb⟩:=sequence_returned written post absorbPad _ value
    ((LocalPrefix.call (key:=ofString "out") none _ _ (by simp)).summary_full written).2.1 afterLength
  have absorbArgs : evalListHOLFinite written (h:=fun address=>Classical.propDecidable (written.memaddrs address)) [state,GeneralSha.pad]=
      some [.val (.word stp),.val (.word pad)]:=by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,state,GeneralSha.pad,second.environment.stateGlobal,second.environment.padGlobal]
  have third:=compression_frame written absorbed stp pad pad query second.environment _ absorbArgs stateAway absorbRun
  have extraSafe : LocalPrefix (ofString "out") extraPad:=.ite _ (.call none _ _ (by simp)) .skip
  obtain ⟨padded,extraRun,afterExtra⟩:=sequence_returned absorbed post extraPad _ value (extraSafe.summary_full absorbed).2.1 afterAbsorb
  have fourth:=extra_frame absorbed padded stp pad query third.environment stateAway extraRun
  have finalOut:=fourth.cell _ _ (third.cell _ _ (second.cell _ _ selectedOut))
  obtain ⟨finished,digestRun,returned⟩:=sequence_returned padded post digestCall (.return (.const 0#64)) value
    ((LocalPrefix.call (key:=ofString "out") none _ _ (by simp)).summary_full padded).2.1 afterExtra
  have digestArgs : evalListHOLFinite padded (h:=fun address=>Classical.propDecidable (padded.memaddrs address)) [state,localVar "out"]=
      some [.val (.word stp),.val (.word out)]:=by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,state,localVar,fourth.environment.stateGlobal,finalOut]
  have fifth:=digest_frame padded finished stp pad out query fourth.environment _ digestArgs outAway digestRun
  have last:=MemoryAt.return_current finished (.const 0#64) query
  rw [returned] at last
  exact last.trans (fifth.memory.trans (fourth.memory.trans (third.memory.trans (second.memory.trans first))))

structure PaddingLocals (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer index out : BitVec 64) (length rem : Nat) : Prop where
  pointer : source.locals.lookup (ofString "p")=some (.val (.word pointer))
  index : source.locals.lookup (ofString "i")=some (.val (.word index))
  out : source.locals.lookup (ofString "out")=some (.val (.word out))
  length : source.locals.lookup (ofString "len")=some (.val (.word (BitVec.ofNat 64 length)))
  remainder : source.locals.lookup (ofString "rem")=some (.val (.word (BitVec.ofNat 64 rem)))

theorem PaddingLocals.after {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer index out stp pad query : BitVec 64} {length rem : Nat}
    (cells : PaddingLocals source pointer index out length rem) (frame : Frame source target stp pad query) : PaddingLocals target pointer index out length rem :=
  ⟨frame.cell _ _ cells.pointer,frame.cell _ _ cells.index,frame.cell _ _ cells.out,frame.cell _ _ cells.length,frame.cell _ _ cells.remainder⟩

/-- The real short remainder and owned input suffix suffice for the original
padding path. Every normal phase supplies its own reads and mapped stores. -/
theorem padding_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (stp pad pointer index out query : BitVec 64) (length rem : Nat)
    (environment : Environment source stp pad) (cells : PaddingLocals source pointer index out length rem)
    (short : rem<64) (inputArena : AllocatedBytes.Arena (pointer+index) rem)
    (stateAway : ∀ offset : Nat,offset<64→ query≠stp+BitVec.ofNat 64 offset)
    (padAway : CopyGeneral.Away pad query 128) (outAway : CopyGeneral.Away out query 32)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source paddingTail=(some (.returned value),post)) : post.memory query=source.memory query := by
  obtain ⟨zeroed,zeroRun,afterZero⟩:=sequence_returned source post zeroPad _ value
    ((LocalPrefix.call (key:=ofString "p") none _ _ (by simp)).summary_full source).2.1 normal
  have zeroArgs : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) [GeneralSha.pad,.const 128#64]=some (Zero.values pad 128):=by
    simp [GeneralSha.pad,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,environment.padGlobal,Zero.values]
  have first:=zero_frame source zeroed stp pad pad query 128 environment _ zeroArgs environment.padArena environment.padAligned (by decide)
    (fun offset inside=>(padAway offset inside).1) zeroRun
  have cells1:=cells.after first
  obtain ⟨copied,copyRun,afterCopy⟩:=sequence_returned zeroed post copyPad _ value
    ((LocalPrefix.call (key:=ofString "p") none _ _ (by simp)).summary_full zeroed).2.1 afterZero
  have copyArgs : evalListHOLFinite zeroed (h:=fun address=>Classical.propDecidable (zeroed.memaddrs address))
      [GeneralSha.pad,.op .add [localVar "p",localVar "i"],localVar "rem"]=some (CopyGeneral.values pad (pointer+index) rem):=by
    simp [GeneralSha.pad,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,first.environment.padGlobal,cells1.pointer,cells1.index,cells1.remainder,
      localVar,CopyGeneral.values,valueIsWord,valueWord,wordOpHOL,wordOp]
  have padRem:=AllocatedBytes.Arena.weaken pad 128 rem environment.padArena (by omega)
  have second:=copy_frame zeroed copied stp pad (pointer+index) pad query rem first.environment _ copyArgs inputArena padRem
    (fun offset inside=>padAway offset (by omega)) copyRun
  have cells2:=cells1.after second
  obtain ⟨marked,markRun,afterMark⟩:=sequence_returned copied post padFirst _ value
    ((LocalPrefix.storeByte (key:=ofString "p") _ _).summary_full copied).2.1 afterCopy
  have markAddress : eval copied (.op .add [GeneralSha.pad,localVar "rem"])=some (.val (.word (pad+BitVec.ofNat 64 rem))):=by
    simp [eval,GeneralSha.pad,evalHOLExact,evalListHOLExact,toExact,second.environment.padGlobal,cells2.remainder,
      localVar,valueIsWord,valueWord,wordOpHOL,wordOp]
  have third:=byte_frame copied marked stp pad (pad+BitVec.ofNat 64 rem) query second.environment _ _ markAddress
    (padAway rem (by omega)).2 markRun
  have cells3:=cells2.after third
  have final : post.memory query=marked.memory query:=by
    refine MemoryAt.declaration_returned marked post "total" (.const 64#64) 64#64 query finalTail value rfl ?_ afterMark
    intro inner remaining
    let entered:=QueryBranch.bind marked "total" 64#64
    have enteredEnvironment : Environment entered stp pad:=third.environment.of_frame rfl
    have enteredLen : entered.locals.lookup (ofString "len")=some (.val (.word (BitVec.ofNat 64 length))):=
      (bind_lookup_other marked "total" "len" 64#64 (by decide)).trans cells3.length
    have enteredOut : entered.locals.lookup (ofString "out")=some (.val (.word out)):=
      (bind_lookup_other marked "total" "out" 64#64 (by decide)).trans cells3.out
    exact final_tail_memory entered inner stp pad out query length enteredEnvironment enteredLen enteredOut (bind_lookup_same _ _ _)
      stateAway padAway outAway value remaining
  exact final.trans (third.memory.trans (second.memory.trans first.memory))

/-- Complete actual general SHA preserves all memory outside its state,
padding and32-byte output. The loop supplies its own short remainder and
normal phases supply their own read/store successes. -/
theorem body_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (stp pad pointer out query : BitVec 64) (length : Nat)
    (small : length+64<2^64) (environment : Environment source stp pad)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (countCell : source.locals.lookup (ofString "len")=some (.val (.word (BitVec.ofNat 64 length))))
    (outCell : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (inputArena : AllocatedBytes.Arena pointer length)
    (stateAway : ∀ offset : Nat,offset<64→ query≠stp+BitVec.ofNat 64 offset)
    (padAway : CopyGeneral.Away pad query 128) (outAway : CopyGeneral.Away out query 32)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source (Code.body .hash)=(some (.returned value),post)) : post.memory query=source.memory query := by
  rw [hash_shape] at normal
  obtain ⟨initialized,initRun,afterInit⟩:=sequence_returned source post initCall _ value
    ((LocalPrefix.call (key:=ofString "p") none _ _ (by simp)).summary_full source).2.1 normal
  have initArgs : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) [state]=some [.val (.word stp)]:=by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,state,environment.stateGlobal]
  have first:=state_call_memory source initialized stp query environment.installed [state] initArgs stateAway initRun
  have initializedEnvironment : Environment initialized stp pad:=environment.after initCall none
    (fun key=>GlobalEffects.call_body key source.code (some none) (ofString "sha256_state_init") [state]
      (Code.formals .stateInit) (Code.body .stateInit) (Code.shape .stateInit) (Code.installed source.code environment.installed .stateInit) (state_globals key source.code)) initRun
  have initLocal (key : MlS) : initialized.locals.lookup key=source.locals.lookup key:=
    CallNormal.ignored_lookup source initialized key (ofString "sha256_state_init") [state] initRun
  have done : post.memory query=initialized.memory query:=by
    refine MemoryAt.declaration_returned initialized post "i" (.const 0#64) 0#64 query (.seq blocks afterBlocks) value rfl ?_ afterInit
    intro inner afterI
    let entered:=QueryBranch.bind initialized "i" 0#64
    have entryEnvironment : Environment entered stp pad:=initializedEnvironment.of_frame rfl
    have entryCount : entered.locals.lookup (ofString "len")=some (.val (.word (BitVec.ofNat 64 length))):=
      (bind_lookup_other initialized "i" "len" 0#64 (by decide)).trans ((initLocal _).trans countCell)
    have entryPointer : entered.locals.lookup (ofString "p")=some (.val (.word pointer)):=
      (bind_lookup_other initialized "i" "p" 0#64 (by decide)).trans ((initLocal _).trans pointerCell)
    have entryOut : entered.locals.lookup (ofString "out")=some (.val (.word out)):=
      (bind_lookup_other initialized "i" "out" 0#64 (by decide)).trans ((initLocal _).trans outCell)
    have valid : CounterFlow.NamedStride.Invariant (ofString "len") length entered:=
      ⟨0#64,bind_lookup_same _ _ _,entryCount,by simp⟩
    have safe : LocalPrefix (ofString "len") blocks:=.loop _ block_iteration_local
    obtain ⟨looped,loopRun,afterLoop⟩:=sequence_returned entered inner blocks afterBlocks value (safe.summary_full entered).2.1 afterI
    have loopMemory:=blocks_memory entered looped stp query entryEnvironment.installed entryEnvironment.stateGlobal stateAway loopRun
    have loopEnvironment:=entryEnvironment.after blocks none (fun key=>blocks_globals key entered.code entryEnvironment.installed) loopRun
    obtain ⟨word,counter,count,bounded,short⟩:=blocks_normal entered looped length small valid loopRun
    have loopPointer : looped.locals.lookup (ofString "p")=some (.val (.word pointer)):=
      (blocks_local entered looped (ofString "p") (by decide) loopRun).trans entryPointer
    have loopOut : looped.locals.lookup (ofString "out")=some (.val (.word out)):=
      (blocks_local entered looped (ofString "out") (by decide) loopRun).trans entryOut
    have number : (BitVec.ofNat 64 length).toNat=length:=by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
    have difference : BitVec.ofNat 64 length-word=BitVec.ofNat 64 (length-word.toNat):=by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_sub_of_le (by change word.toNat≤(BitVec.ofNat 64 length).toNat; rw [number]; exact bounded),number,
        BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
    have remRead : eval looped remainder=some (.val (.word (BitVec.ofNat 64 (length-word.toNat)))):=by
      simp [eval,evalHOLExact,evalListHOLExact,toExact,remainder,localVar,counter,count,valueIsWord,valueWord,wordOpHOL,wordOp,difference]
    have restArena : AllocatedBytes.Arena (pointer+word) (length-word.toNat):=by
      simpa only [byteAddress,BitVec.ofNat_toNat,BitVec.setWidth_eq] using
        AllocatedBytes.Arena.subrange pointer length word.toNat (length-word.toNat) inputArena (by omega)
    have paddingDone : inner.memory query=looped.memory query:=by
      refine MemoryAt.declaration_returned looped inner "rem" remainder (BitVec.ofNat 64 (length-word.toNat)) query paddingTail value remRead ?_ afterLoop
      intro finished remaining
      let remEntry:=QueryBranch.bind looped "rem" (BitVec.ofNat 64 (length-word.toNat))
      have remEnvironment : Environment remEntry stp pad:=loopEnvironment.of_frame rfl
      have cells : PaddingLocals remEntry pointer word out length (length-word.toNat):=
        ⟨(bind_lookup_other looped "rem" "p" _ (by decide)).trans loopPointer,
         (bind_lookup_other looped "rem" "i" _ (by decide)).trans counter,
         (bind_lookup_other looped "rem" "out" _ (by decide)).trans loopOut,
         (bind_lookup_other looped "rem" "len" _ (by decide)).trans count,bind_lookup_same _ _ _⟩
      exact padding_memory remEntry finished stp pad pointer word out query length (length-word.toNat) remEnvironment cells short restArena
        stateAway padAway outAway value remaining
    exact paddingDone.trans loopMemory
  exact done.trans first

/-- Same-call three-word ABI and real owned input retain the full normal SHA
memory frame through ordinary caller restoration. -/
theorem call_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (stp pad pointer out query : BitVec 64) (length : Nat)
    (small : length+64<2^64) (environment : Environment source stp pad) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (values pointer out length))
    (inputArena : AllocatedBytes.Arena pointer length)
    (stateAway : ∀ offset : Nat,offset<64→ query≠stp+BitVec.ofNat 64 offset)
    (padAway : CopyGeneral.Away pad query 128) (outAway : CopyGeneral.Away out query 32)
    (normal : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "sha256") arguments)=(none,post)) : post.memory query=source.memory query := by
  obtain ⟨callee,called,pointerCell,countCell,outCell⟩:=GeneralSha.environment source.code.lookup pointer out length (hash_code source.code environment.installed)
  have calleeEnvironment : Environment (callEntryStateHOLFinite source callee) stp pad:=environment.of_frame rfl
  exact MemoryAt.call_normal source post (ofString "sha256") arguments (values pointer out length) (Code.body .hash) callee .one query args called
    (fun target value run=>body_memory (callEntryStateHOLFinite source callee) target stp pad pointer out query length small calleeEnvironment
      pointerCell countCell outCell inputArena stateAway padAway outAway value run) normal

end InitECandidate.Solver.Input.CurrentVerify.GeneralSha

#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.Code.installed
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.state_supported
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.block_supported
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.state_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.block_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.state_globals
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.block_globals
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.WordFrame.scalar_length
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.WordFrame.scalar_store_current
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.WordFrame.sound
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.state_frame_supported
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.block_frame_supported
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.state_memory
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.block_memory
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.be32_supported
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.be32_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.finish_shape
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.finish_iteration_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.finish_iteration_advance
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.finish_iteration_local
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.finish_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.block_iteration_local
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.block_iteration_advance
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.block_iteration_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.block_test_reads
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.blocks_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.blocks_normal
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.hash_shape
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.bswap_supported
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.be64_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.compression_call_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.final_tail_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.padding_finish_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.padding_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.after_blocks_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.loop_tail_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.body_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.hash_code
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.environment
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.call_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.dynamic_call_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.be32_globals
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.be64_globals
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.finish_globals
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.compression_call_globals
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.digest_call_globals
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.final_tail_globals
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.body_globals
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.call_globals
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.first_word_call_memory
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.be32_frame_supported
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.be32_call_memory
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.finish_other
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.finish_step_memory
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.finish_loop_memory
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.finish_memory
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.state_call_memory
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.compression_call_memory
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.digest_call_memory
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.compression_first_memory
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.blocks_globals
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.blocks_memory
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.blocks_local
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.Environment.of_frame
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.Environment.after
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.Frame.cell
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.zero_frame
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.copy_frame
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.compression_frame
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.byte_frame
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.digest_frame
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.be64_shape
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.bswap_local
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.be64_fast_memory
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.be64_slow_memory
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.be64_body_memory
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.be64_call_memory
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.be64_frame
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.select_local
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.select_pure
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.select_normal
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.extra_globals
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.extra_frame
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.length_frame
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.final_tail_memory
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.PaddingLocals.after
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.padding_memory
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.body_memory
#print axioms InitECandidate.Solver.Input.CurrentVerify.GeneralSha.call_memory
