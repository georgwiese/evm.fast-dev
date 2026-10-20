import InitECandidate.Solver.Input.MainBnAccelInitialization
import InitECandidate.Solver.Input.InitializerQuads
import InitECandidate.Solver.Input.InitializerWords

namespace InitECandidate.Solver.Input.Main.BnInitialization
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

def body : ProgHOL 64 := match Guest.guestFn_bn254_init with | .function fn => progToHOL fn.body | _ => .skip
def quad (a b c d : BitVec 64) : InitializerQuads.Words := fun index => match index.val with | 0 => a | 1 => b | 2 => c | _ => d
-- Literal original gamma and exponent data; body_shape checks every value.
def gamma : List InitializerQuads.Words :=
  [quad 1#64 0#64 0#64 0#64,
   quad 0#64 0#64 0#64 0#64,
   quad 15423480562983756912#64 6652412619979170166#64 16769610461022161760#64 1334392721173227487#64,
   quad 14581793986494816940#64 8392900422778406885#64 11975771789798476686#64 2623794231377586150#64,
   quad 11088870908804158781#64 13226160682434769676#64 5479733118184829251#64 3437169660107756023#64,
   quad 1613930359396748194#64 3651902652079185358#64 5450706350010664852#64 1642095672556236320#64,
   quad 15876315988453495642#64 15828711151707445656#64 15879347695360604601#64 449501266848708060#64,
   quad 9427018508834943203#64 2414067704922266578#64 505728791003885355#64 558513134835401882#64,
   quad 9550480412176721762#64 15218619680543796338#64 9291982349918543492#64 411322207813150721#64,
   quad 13923800814728216870#64 3928778152882390883#64 11473624495072943250#64 3176267935786044142#64,
   quad 3360468246954731823#64 4781773437820083155#64 16805804752481107956#64 109144015201994313#64,
   quad 2650008764942134347#64 12718389207422085824#64 11709273573250211709#64 1345717340070545013#64]
def exponent : List (BitVec 64) :=
  [9698021743855595808#64,4658111487712502692#64,9475478476403788475#64,3895898136474990872#64,
   13897688294677189338#64,13692288569157338976#64,15521367811043670911#64,13992850401411864641#64,
   6609620042336070051#64,9167096575297741460#64,3006977925533509404#64,13799376210358020352#64,
   7213564696215919148#64,12108970941387295838#64,14800348210198864764#64,5333217130945090002#64,
   17191330154042290397#64,7728981312468502308#64,13479501571575199621#64,4632319730382815766#64,
   6183408236485651195#64,2344383644319854215#64,9541507823907846048#64,5234407941292577173#64,
   16529975799043132950#64,12351756573642376427#64,9426269327694809050#64,7379223421642392714#64,
   5792417538046516732#64,9162926010144764881#64,8644015420738790472#64,18370314904686314414#64,
   17975984934167627464#64,8719923968173632426#64,6379321585415610019#64,1402842025008175984#64,
   888598832447275954#64,4522688638863333623#64,15776483769708984925#64,16276864970431725248#64,
   7646110518075161570#64,9524343276244152831#64,2377296829910687932#64,203128949104#64]
def inverse82 : InitializerQuads.Words := quad 2101474240800967975#64 11918193690587271358#64 11796765086790633677#64 1148157965898539121#64
def gammaAction : InitializerAllocations.Action := ⟨"bn_gamma",384,.panop .mul [.const 6#64,.const 64#64]⟩
def b2Action := InitializerAllocations.constant "bn_b2" 64
def exponentAction : InitializerAllocations.Action := ⟨"bn_expw",352,.panop .mul [.const 44#64,.const 8#64]⟩
def exponentStores : ProgHOL 64 :=
  .seq (.store (.var .global (ofString "bn_expw")) (.const 9698021743855595808#64))
    (InitializerWords.stores "bn_expw" 8 exponent.tail (.return (.const 0#64)))
def afterB2Stores := InitializerAllocations.withTail [exponentAction] exponentStores
def b2Stores : ProgHOL 64 :=
  .seq (.store (.var .global (ofString "bn_b2")) (.var .local (ofString "b2r")))
    (.seq (.store (.op .add [.var .global (ofString "bn_b2"),.const 32#64]) (.var .local (ofString "b2i"))) afterB2Stores)
def afterB2Allocation : ProgHOL 64 :=
  .dec (ofString "inv82") RlpWrite.U256Value.tupleShape (InitializerQuads.expression inverse82)
    (.decCall (ofString "b2r") RlpWrite.U256Value.tupleShape (ofString "fq_mul")
      [InitializerQuads.expression (quad 27#64 0#64 0#64 0#64),.var .local (ofString "inv82")]
      (.decCall (ofString "b2i0") RlpWrite.U256Value.tupleShape (ofString "fq_mul")
        [InitializerQuads.expression (quad 3#64 0#64 0#64 0#64),.var .local (ofString "inv82")]
        (.decCall (ofString "b2i") RlpWrite.U256Value.tupleShape (ofString "fq_neg")
          [.var .local (ofString "b2i0")] b2Stores)))
def afterGamma := InitializerAllocations.withTail [b2Action] afterB2Allocation
def gammaStores := InitializerQuads.stores "bn_gamma" 0 gamma afterGamma
def afterAccelerator := InitializerAllocations.withTail [gammaAction] gammaStores
def acceleratorCall : ProgHOL 64 := .call (some (none,none)) (ofString "bn254_accel_init") []
def afterGuard : ProgHOL 64 := .seq acceleratorCall afterAccelerator
def guard : ProgHOL 64 := .ite (.cmp .notEqual (.var .global (ofString "bn_gamma")) (.const 0#64)) (.return (.const 0#64)) .skip

theorem body_shape : body = .seq guard afterGuard := by
  simp only [body,guard,afterGuard,acceleratorCall,afterAccelerator,gammaStores,gamma,afterGamma,b2Action,afterB2Allocation,inverse82,b2Stores,afterB2Stores,
    exponentAction,exponentStores,exponent,quad,gammaAction,InitializerAllocations.withTail,InitializerAllocations.call,InitializerAllocations.constant,
    InitializerQuads.stores,InitializerQuads.expression,InitializerQuads.address,InitializerWords.stores,RlpWrite.U256Value.tupleShape,
    Guest.guestFn_bn254_init,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none]
  rfl

theorem gamma_length : gamma.length = 12 := by decide_cbv
theorem exponent_length : exponent.length = 44 := by decide_cbv

open scoped InitE.MetadataComputation InitE.NameComputation in
theorem symbol_members : ofString "bn_gamma" ∈ OriginalScalarGlobals.names ∧ ofString "bn_b2" ∈ OriginalScalarGlobals.names ∧ ofString "bn_expw" ∈ OriginalScalarGlobals.names := by decide_cbv

theorem gamma_valid : InitializerAllocations.Valid gammaAction := ⟨symbol_members.1,by decide,by decide,fun _ => rfl⟩
theorem b2_valid : InitializerAllocations.Valid b2Action := InitializerAllocations.valid_constant _ _ symbol_members.2.1 (by decide) (by decide)
theorem exponent_valid : InitializerAllocations.Valid exponentAction := ⟨symbol_members.2.2,by decide,by decide,fun _ => rfl⟩

theorem original_code (code) (installed : OriginalCode.Installed code) : code.lookup (ofString "bn254_init") = some ([],body,.one) := by
  have checked := OriginalCode.indexed code installed 598 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_bn254_init) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,body,Guest.guestFn_bn254_init,shapeToHOL,List.map_cons,List.map_nil] using checked

end InitECandidate.Solver.Input.Main.BnInitialization

#print axioms InitECandidate.Solver.Input.Main.BnInitialization.body_shape

#print axioms InitECandidate.Solver.Input.Main.BnInitialization.gamma_length

#print axioms InitECandidate.Solver.Input.Main.BnInitialization.exponent_length

#print axioms InitECandidate.Solver.Input.Main.BnInitialization.symbol_members

#print axioms InitECandidate.Solver.Input.Main.BnInitialization.gamma_valid

#print axioms InitECandidate.Solver.Input.Main.BnInitialization.b2_valid

#print axioms InitECandidate.Solver.Input.Main.BnInitialization.exponent_valid

#print axioms InitECandidate.Solver.Input.Main.BnInitialization.original_code
