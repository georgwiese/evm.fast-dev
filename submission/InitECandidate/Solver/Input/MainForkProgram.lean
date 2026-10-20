import InitECandidate.Solver.Input.InitializerZeroBuffer

namespace InitECandidate.Solver.Input.Main.ForkInitialization
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

def body : ProgHOL 64 := match Guest.guestFn_fork_init with | .function fn => progToHOL fn.body | _ => .skip
def zeroAction := InitializerAllocations.constant "zero32" 32
def precompileAction : InitializerAllocations.Action := ⟨"precompile_addrs",360,.panop .mul [.const 18#64,.const 20#64]⟩
def signatureAction := InitializerAllocations.constant "deposit_event_signature_hash" 32

structure Address where
  name : String
  hi : BitVec 64
  mid : BitVec 64
  lo : BitVec 64
def addresses : List Address :=
  [⟨"beacon_roots_address",998902#64,15506597749690834871#64,13311379508201171970#64⟩,
   ⟨"history_storage_address",63752#64,2878298490047003138#64,3700577164601600309#64⟩,
   ⟨"withdrawal_request_address",2401#64,17242047345525313946#64,15579492241104728066#64⟩,
   ⟨"consolidation_request_address",48093#64,14397524800236640159#64,10016273463683084881#64⟩,
   ⟨"builder_deposit_address",49140#64,7603452151126424148#64,760111669195932290#64⟩,
   ⟨"builder_exit_address",25814#64,8669529151676140297#64,4307224735379260034#64⟩,
   ⟨"deposit_contract_address",0#64,2421447037043915651#64,11294470620239562234#64⟩]
def Address.action (address : Address) := InitializerAllocations.constant address.name 24
def Address.call (address : Address) : ProgHOL 64 := .call (some (none,none)) (ofString "addr_from_words")
  [.var .global (ofString address.name),.const address.hi,.const address.mid,.const address.lo]
def addressProgram : List Address → ProgHOL 64 → ProgHOL 64
  | [],tail => tail
  | address :: rest,tail => InitializerAllocations.withTail [address.action] (.seq address.call (addressProgram rest tail))

def signatureWords : List (BitVec 64) := [7249595157780304706#64,12676030261858484297#64,16708898399860066458#64,12074291595689605317#64]
def signatureStores : Nat → List (BitVec 64) → ProgHOL 64
  | _,[] => .return (.const 0#64)
  | offset,word :: rest => .seq (.call (some (none,none)) (ofString "st_be64")
      [.op .add [.var .global (ofString "deposit_event_signature_hash"),.const (BitVec.ofNat 64 offset)],.const word]) (signatureStores (offset + 8) rest)
def signatureProgram := InitializerAllocations.withTail [signatureAction] (signatureStores 0 signatureWords)
def finalByte : ProgHOL 64 := .storeByte
  (.op .add [.var .global (ofString "precompile_addrs"),.panop .mul [.const 17#64,.const 20#64],.const 18#64]) (.const 1#64)
def afterLoop : ProgHOL 64 := .seq finalByte (addressProgram addresses signatureProgram)
def loopBody : ProgHOL 64 := .seq
  (.storeByte (.op .add [.var .global (ofString "precompile_addrs"),.panop .mul [.var .local (ofString "i"),.const 20#64],.const 19#64])
    (.op .add [.var .local (ofString "i"),.const 1#64]))
  (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"),.const 1#64]))
def loop : ProgHOL 64 := .while (.cmp .less (.var .local (ofString "i")) (.const 17#64)) loopBody
def afterPrecompile : ProgHOL 64 := .dec (ofString "i") .one (.const 0#64) (.seq loop afterLoop)
def afterZero := InitializerZeroBuffer.program precompileAction afterPrecompile

theorem body_shape : body = InitializerZeroBuffer.program zeroAction afterZero := by
  simp only [body,afterZero,afterPrecompile,loop,loopBody,afterLoop,finalByte,addressProgram,addresses,Address.action,Address.call,
    signatureProgram,signatureStores,signatureWords,zeroAction,precompileAction,signatureAction,InitializerZeroBuffer.program,InitializerZeroBuffer.call,
    InitializerAllocations.withTail,InitializerAllocations.call,InitializerAllocations.constant,
    Guest.guestFn_fork_init,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none] <;> rfl

def symbols := ["zero32","precompile_addrs"] ++ addresses.map Address.name ++ ["deposit_event_signature_hash"]
open scoped InitE.MetadataComputation InitE.NameComputation in
theorem symbols_checked : (symbols.map ofString).all (fun key => OriginalScalarGlobals.names.contains key) = true := by decide_cbv

theorem symbol_member (name : String) (member : name ∈ symbols) : ofString name ∈ OriginalScalarGlobals.names :=
  List.contains_iff_mem.mp (List.all_eq_true.mp symbols_checked (ofString name) (List.mem_map.mpr ⟨name,member,rfl⟩))

theorem initial_valid : InitializerAllocations.Valid zeroAction ∧ InitializerAllocations.Valid precompileAction ∧ InitializerAllocations.Valid signatureAction := by
  refine ⟨InitializerAllocations.valid_constant _ _ (symbol_member _ (by simp [symbols])) (by decide) (by decide),?_,
    InitializerAllocations.valid_constant _ _ (symbol_member _ (by simp [symbols])) (by decide) (by decide)⟩
  exact ⟨symbol_member _ (by simp [symbols,precompileAction]),by decide,by decide,fun _ => rfl⟩

theorem address_valid (address : Address) (member : address ∈ addresses) : InitializerAllocations.Valid address.action :=
  InitializerAllocations.valid_constant _ _ (symbol_member _ (by simp only [symbols,List.mem_append,List.mem_map]; exact Or.inl (Or.inr ⟨address,member,rfl⟩)))
    (by simp only [addresses,List.mem_cons,List.not_mem_nil,or_false] at member; rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide) (by decide)

theorem original_code (code) (installed : OriginalCode.Installed code) : code.lookup (ofString "fork_init") = some ([],body,.one) := by
  have checked := OriginalCode.indexed code installed 798 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_fork_init) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,body,Guest.guestFn_fork_init,shapeToHOL,List.map_cons,List.map_nil] using checked

end InitECandidate.Solver.Input.Main.ForkInitialization

#print axioms InitECandidate.Solver.Input.Main.ForkInitialization.body_shape
#print axioms InitECandidate.Solver.Input.Main.ForkInitialization.symbols_checked
#print axioms InitECandidate.Solver.Input.Main.ForkInitialization.symbol_member
#print axioms InitECandidate.Solver.Input.Main.ForkInitialization.initial_valid
#print axioms InitECandidate.Solver.Input.Main.ForkInitialization.address_valid
#print axioms InitECandidate.Solver.Input.Main.ForkInitialization.original_code
