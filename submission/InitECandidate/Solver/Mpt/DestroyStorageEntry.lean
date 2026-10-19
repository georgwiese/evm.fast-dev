import InitECandidate.Solver.Mpt.DestroyStoragePresent
import InitECandidate.Solver.MutableTable.GetCallOrigin
import InitECandidate.Solver.MutableTable.OccupiedValueProperty

namespace InitECandidate.Solver.Mpt.DestroyStorage
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch MutableTable NaturalLayout GasBudget

def lookupEntry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (paid : Nat) (flag value : BitVec 64) :=
  setVarHOLFinite (ofString "m") (Get.pair flag value) {bind source "outer" pointer with clock := source.clock - paid}

theorem lookup_normal {ι : Type}
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (address transaction : BitVec 64)
    (cursor : Nat) (objects : ι → TableFamily.Object) (outer : ι)
    (family : TableFamily.Model source cursor objects) (environment : WarmKeys.Environment source)
    (installed : Input.OriginalCode.Installed source.code) (outerKind : (objects outer).kind = .account)
    (property : ι → BitVec 64 → Prop) (values : TableFamily.ValuesHave source objects property)
    (addressArena : AllocatedBytes.Arena address 20)
    (addressLocal : source.locals.lookup (ofString "addr") = some (.val (.word address)))
    (transactionGlobal : source.globals.lookup (ofString "ts") = some (.val (.word transaction)))
    (tableMapped : source.memaddrs (transaction + 32#64))
    (tableStored : source.memory (transaction + 32#64) = .word (objects outer).pointer)
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source body = (some (.returned returned),post)) :
    ∃ (paid : Nat) (flag value : BitVec 64) (finish : PanSemStateFiniteExact 64 Guest.HostMemory),
      1 ≤ paid ∧ paid ≤ Get.bodyPrice (objects outer).kind (objects outer).slots.length + 1 ∧ paid ≤ source.clock ∧
      (flag = 0#64 ∨ flag = 1#64) ∧ (flag = 0#64 ∨ property outer value) ∧
      evaluateHOLFiniteState (lookupEntry source (objects outer).pointer paid flag value) afterGet = (some (.returned returned),finish) ∧
      emptyLocalsHOLFinite post = emptyLocalsHOLFinite finish := by
  classical
  let entered := bind source "outer" (objects outer).pointer
  let getter : ProgHOL 64 := .decCall (ofString "m") Get.pairShape (ofString "htab_get") [localVar "outer",localVar "addr"] afterGet
  have tableRead : eval source (transactionTable 32#64) = some (.val (.word (objects outer).pointer)) := by
    simp [eval,transactionTable,evalHOLExact,evalListHOLExact,toExact,transactionGlobal,valueIsWord,valueWord,wordOpHOL,wordOp,
      memLoadHOLExact,isWfShapeExactHOL,tableMapped,tableStored]
  have setup : BuildEntry.Initializes source [("outer",transactionTable 32#64)] entered (restore source "outer") := .step _ tableRead (.done _)
  rw [body_shape] at normal
  change evaluateHOLFiniteState source (BuildEntry.declarations [("outer",transactionTable 32#64)] getter) = _ at normal
  rw [BuildEntry.declarations_execute setup getter] at normal
  let target := (evaluateHOLFiniteState entered getter).2
  have resultEq := congrArg Prod.fst normal
  change (evaluateHOLFiniteState entered getter).1 = some (.returned returned) at resultEq
  have getterRun : evaluateHOLFiniteState entered getter = (some (.returned returned),target) := Prod.ext resultEq rfl
  have postEq := congrArg Prod.snd normal
  change restore source "outer" target = post at postEq
  have enteredFamily : TableFamily.Model entered cursor objects := family.of_control rfl rfl rfl rfl
  have enteredAddress : entered.locals.lookup (ofString "addr") = some (.val (.word address)) :=
    (bind_lookup_other source "outer" "addr" (objects outer).pointer (by decide)).trans addressLocal
  have enteredOuter : entered.locals.lookup (ofString "outer") = some (.val (.word (objects outer).pointer)) := bind_lookup_same _ _ _
  have args : evalListHOLFinite entered (h := fun query => Classical.propDecidable (entered.memaddrs query)) [localVar "outer",localVar "addr"] =
      some [.val (.word (objects outer).pointer),.val (.word address)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,enteredAddress,enteredOuter]
  have queryFits : address.toNat + KeyHash.keySize (objects outer).kind < 2^64 := by
    rw [outerKind]
    change address.toNat + 20 < 2^64
    have := addressArena.upper
    omega
  have queryMapped : ∀ offset < KeyHash.keySize (objects outer).kind,
      entered.memaddrs (panByteAlignHOL (width := 64) (byteAddress address offset)) := by
    rw [outerKind]
    intro offset inside
    exact AllocatedBytes.byte_mapped entered address 20 offset environment.domain addressArena inside
  obtain ⟨paid,flag,value,finish,positive,bounded,funded,binary,origin,tailRun,scope⟩ := Get.model_normal_entry_origin entered target (objects outer).kind (objects outer).plan
    (objects outer).slots cursor (objects outer).floor (enteredFamily.tables outer) (environment.of_fields rfl rfl rfl) address queryFits queryMapped
    (Get.original_code source.code installed) "m" _ afterGet args returned getterRun
  have owned := origin.occupied_property entered (cell (objects outer).plan .values 0) (BitVec.ofNat 64 (objects outer).plan.capacity)
    flag value (objects outer).slots (property outer) (values outer)
  refine ⟨paid,flag,value,finish,positive,bounded,funded,binary,owned,tailRun,?_⟩
  rw [← postEq,scope]
  rfl

theorem after_get_dispatch (source : PanSemStateFiniteExact 64 Guest.HostMemory) (flag value : BitVec 64)
    (pairLocal : source.locals.lookup (ofString "m") = some (Get.pair flag value)) :
    evaluateHOLFiniteState source afterGet = if flag = 0#64 then
      (some (.returned (.val (.word 0#64))),emptyLocalsHOLFinite source) else evaluateHOLFiniteState source present := by
  classical
  by_cases absent : flag = 0#64
  all_goals simp [afterGet,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,evaluateHOLFiniteState_skip,evaluateHOLFiniteState_return,
    evalHOLExact,localVar,toExact,pairLocal,Get.pair,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,absent,shapeOfHOLExact]

end InitECandidate.Solver.Mpt.DestroyStorage

#print axioms InitECandidate.Solver.Mpt.DestroyStorage.lookup_normal
#print axioms InitECandidate.Solver.Mpt.DestroyStorage.after_get_dispatch
