import InitECandidate.Solver.Input.MainBlsFpProgram

namespace InitECandidate.Solver.Input.Main.BlsInitialization
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 500000

def libBody : ProgHOL 64 := match Guest.guestFn_bls_lib_init with | .function fn => progToHOL fn.body | _ => .skip
def fpCall : ProgHOL 64 := .call (some (none,none)) (ofString "fp_accel_init") []
def fp2Call : ProgHOL 64 := .call (some (none,none)) (ofString "fp2_accel_init") []
def g1Call : ProgHOL 64 := .call (some (none,none)) (ofString "bls_g1_accel_init") []
def afterFp2 : ProgHOL 64 := .seq g1Call (.return (.const 0#64))
def afterFp : ProgHOL 64 := .seq fp2Call afterFp2
def afterConstants : ProgHOL 64 := .seq fpCall afterFp

theorem lib_body_shape : libBody = .seq BlsPairInitialization.constantsCall afterConstants := by
  simp only [libBody,BlsPairInitialization.constantsCall,afterConstants,afterFp,afterFp2,fpCall,fp2Call,g1Call,
    Guest.guestFn_bls_lib_init,progToHOL,expToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none]

def body : ProgHOL 64 := match Guest.guestFn_bls_precompiles_init with | .function fn => progToHOL fn.body | _ => .skip
def libCall : ProgHOL 64 := .call (some (none,none)) (ofString "bls_lib_init") []
def discountAction : InitializerAllocations.Action := ⟨"bls_discount",2048,.panop .mul [.const 256#64,.const 8#64]⟩
def discountWords : List (BitVec 64) :=
  [1000#64,949#64,848#64,797#64,764#64,750#64,738#64,728#64,
   719#64,712#64,705#64,698#64,692#64,687#64,682#64,677#64,
   673#64,669#64,665#64,661#64,658#64,654#64,651#64,648#64,
   645#64,642#64,640#64,637#64,635#64,632#64,630#64,627#64,
   625#64,623#64,621#64,619#64,617#64,615#64,613#64,611#64,
   609#64,608#64,606#64,604#64,603#64,601#64,599#64,598#64,
   596#64,595#64,593#64,592#64,591#64,589#64,588#64,586#64,
   585#64,584#64,582#64,581#64,580#64,579#64,577#64,576#64,
   575#64,574#64,573#64,572#64,570#64,569#64,568#64,567#64,
   566#64,565#64,564#64,563#64,562#64,561#64,560#64,559#64,
   558#64,557#64,556#64,555#64,554#64,553#64,552#64,551#64,
   550#64,549#64,548#64,547#64,547#64,546#64,545#64,544#64,
   543#64,542#64,541#64,540#64,540#64,539#64,538#64,537#64,
   536#64,536#64,535#64,534#64,533#64,532#64,532#64,531#64,
   530#64,529#64,528#64,528#64,527#64,526#64,525#64,525#64,
   524#64,523#64,522#64,522#64,521#64,520#64,520#64,519#64,
   1000#64,1000#64,923#64,884#64,855#64,832#64,812#64,796#64,
   782#64,770#64,759#64,749#64,740#64,732#64,724#64,717#64,
   711#64,704#64,699#64,693#64,688#64,683#64,679#64,674#64,
   670#64,666#64,663#64,659#64,655#64,652#64,649#64,646#64,
   643#64,640#64,637#64,634#64,632#64,629#64,627#64,624#64,
   622#64,620#64,618#64,615#64,613#64,611#64,609#64,607#64,
   606#64,604#64,602#64,600#64,598#64,597#64,595#64,593#64,
   592#64,590#64,589#64,587#64,586#64,584#64,583#64,582#64,
   580#64,579#64,578#64,576#64,575#64,574#64,573#64,571#64,
   570#64,569#64,568#64,567#64,566#64,565#64,563#64,562#64,
   561#64,560#64,559#64,558#64,557#64,556#64,555#64,554#64,
   553#64,552#64,552#64,551#64,550#64,549#64,548#64,547#64,
   546#64,545#64,545#64,544#64,543#64,542#64,541#64,541#64,
   540#64,539#64,538#64,537#64,537#64,536#64,535#64,535#64,
   534#64,533#64,532#64,532#64,531#64,530#64,530#64,529#64,
   528#64,528#64,527#64,526#64,526#64,525#64,524#64,524#64]

def discountStores : ProgHOL 64 := WordTableInitialization.stores "bls_discount" discountWords
def afterLib : ProgHOL 64 := InitializerAllocations.withTail [discountAction] discountStores
def afterGuard : ProgHOL 64 := .seq libCall afterLib

theorem body_shape : body = .seq (WordTableInitialization.guard "bls_discount") afterGuard := by
  simp only [body,WordTableInitialization.guard,afterGuard,libCall,afterLib,discountStores,discountAction,discountWords,
    WordTableInitialization.stores,InitializerWords.stores,InitializerAllocations.withTail,InitializerAllocations.call,
    Guest.guestFn_bls_precompiles_init,progToHOL,expToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none]

theorem discount_length : discountWords.length = 256 := by decide_cbv

open scoped InitE.MetadataComputation InitE.NameComputation in
theorem discount_member : ofString "bls_discount" ∈ OriginalScalarGlobals.names := by decide_cbv

theorem discount_valid : InitializerAllocations.Valid discountAction := ⟨discount_member,by decide,by decide,fun _ => rfl⟩

theorem lib_original_code (code) (installed : OriginalCode.Installed code) : code.lookup (ofString "bls_lib_init") = some ([],libBody,.one) := by
  have checked := OriginalCode.indexed code installed 755 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_bls_lib_init) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,libBody,Guest.guestFn_bls_lib_init,shapeToHOL,List.map_cons,List.map_nil] using checked

theorem original_code (code) (installed : OriginalCode.Installed code) : code.lookup (ofString "bls_precompiles_init") = some ([],body,.one) := by
  have checked := OriginalCode.indexed code installed 764 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_bls_precompiles_init) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,body,Guest.guestFn_bls_precompiles_init,shapeToHOL,List.map_cons,List.map_nil] using checked

end InitECandidate.Solver.Input.Main.BlsInitialization

#print axioms InitECandidate.Solver.Input.Main.BlsInitialization.lib_body_shape
#print axioms InitECandidate.Solver.Input.Main.BlsInitialization.body_shape
#print axioms InitECandidate.Solver.Input.Main.BlsInitialization.discount_length
#print axioms InitECandidate.Solver.Input.Main.BlsInitialization.discount_member
#print axioms InitECandidate.Solver.Input.Main.BlsInitialization.discount_valid
#print axioms InitECandidate.Solver.Input.Main.BlsInitialization.lib_original_code
#print axioms InitECandidate.Solver.Input.Main.BlsInitialization.original_code
