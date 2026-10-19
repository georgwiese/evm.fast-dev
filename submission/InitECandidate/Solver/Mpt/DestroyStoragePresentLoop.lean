import InitECandidate.Solver.Mpt.DestroyStorageCode
import InitECandidate.Solver.PanDeclarations

namespace InitECandidate.Solver.Mpt.DestroyStorage
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch MutableTable NaturalLayout GasBudget

theorem present_loop {ι : Type} [DecidableEq ι]
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (address scratch transaction : BitVec 64)
    (cursor cutoff : Nat) (objects : ι → TableFamily.Object) (writer reader : ι)
    (base cap count : Nat) (entries : Nat → Journal.Entry ι)
    (family : TableFamily.Model source cursor objects) (image : Journal.Image source objects base count entries)
    (zone : Journal.Zone objects base cap cursor) (countBound : count ≤ cap)
    (environment : WarmKeys.Environment source) (installed : Input.OriginalCode.Installed source.code)
    (accounts : List (BitVec 64)) (registry : AccountDecode.Registry source cutoff cursor objects accounts)
    (property : ι → BitVec 64 → Prop) (values : TableFamily.ValuesHave source objects property) (owned : property writer 1#64)
    (writerKind : (objects writer).kind = .storage) (readerKind : (objects reader).kind = .word)
    (addressArena : AllocatedBytes.Arena address 20) (scratchArena : AllocatedBytes.Arena scratch 52)
    (floors : ∀ index, cutoff ≤ (objects index).floor) (scratchBelow : scratch.toNat + 52 ≤ cutoff)
    (small : cutoff < 2^64) (journalAbove : cutoff ≤ base)
    (addressLocal : source.locals.lookup (ofString "addr") = some (.val (.word address)))
    (pairLocal : source.locals.lookup (ofString "m") = some (Get.pair 1#64 (objects reader).pointer))
    (scratchGlobal : source.globals.lookup (ofString "sk_buf") = some (.val (.word scratch)))
    (transactionGlobal : source.globals.lookup (ofString "ts") = some (.val (.word transaction)))
    (tableMapped : source.memaddrs (transaction + 24#64))
    (tableStored : source.memory (transaction + 24#64) = .word (objects writer).pointer)
    (tableAbove : cutoff ≤ (transaction + 24#64).toNat)
    (tableBefore : (transaction + 24#64).toNat < cursor) (tableOutside : TableFamily.Outside objects (transaction + 24#64))
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source present = (some (.returned returned),post)) :
    ∃ (paid nextCursor : Nat) (next : ι → TableFamily.Object) (middle finish : PanSemStateFiniteExact 64 Guest.HostMemory),
      paid ≤ source.clock ∧ middle.clock = source.clock - paid ∧ cursor ≤ nextCursor ∧
      TableFamily.Model middle nextCursor next ∧ Journal.Image middle next base count entries ∧ Journal.Zone next base cap nextCursor ∧
      paid + GrowRuntime.growthPotential (objects writer).kind (objects writer).plan.capacity ≤
        loopPrice (objects writer).slots.length (objects reader).slots.length + GrowRuntime.growthPotential (objects writer).kind (next writer).plan.capacity ∧
      (next writer).slots.length ≤ (objects writer).slots.length + (objects reader).slots.length ∧ next reader = objects reader ∧
      middle.code = source.code ∧ WarmKeys.Environment middle ∧ HeapGlobals source middle ∧ TableFamily.ValuesHave middle next property ∧
      AccountDecode.Registry middle cutoff nextCursor next accounts ∧ TableFamily.PersistentFrame cutoff cursor objects next source middle ∧ TableFamily.Metadata objects next ∧
      (∀ table, table ≠ writer → next table = objects table) ∧
      middle.locals.lookup (ofString "outer") = source.locals.lookup (ofString "outer") ∧ middle.locals.lookup (ofString "addr") = some (.val (.word address)) ∧
      evaluateHOLFiniteState middle (.seq removeCall (.return (.const 0#64))) = (some (.returned returned),finish) ∧
      emptyLocalsHOLFinite post = emptyLocalsHOLFinite finish := by
  classical
  let countExpression : ExpHOL 64 := .load .one (.op .add [localVar "inner",.const 24#64])
  let bindings : List (String × ExpHOL 64) := [("inner",.rfield 1 (localVar "m")),("cap",countExpression),("i",.const 0#64)]
  let withInner := bind source "inner" (objects reader).pointer
  let withCount := bind withInner "cap" (BitVec.ofNat 64 (objects reader).slots.length)
  let ready := bind withCount "i" 0#64
  let restoreStack := fun finish => restore source "inner" (restore withInner "cap" (restore withCount "i" finish))
  have pointerRead : eval source (.rfield 1 (localVar "m")) = some (.val (.word (objects reader).pointer)) := by
    simp [eval,evalHOLExact,localVar,toExact,pairLocal,Get.pair]
  have withInnerFamily : TableFamily.Model withInner cursor objects := family.of_control rfl rfl rfl rfl
  have countRead : eval withInner countExpression = some (.val (.word (BitVec.ofNat 64 (objects reader).slots.length))) :=
    live_count_read withInner (objects reader) cursor (withInnerFamily.tables reader) environment.domain (bind_lookup_same _ _ _)
  have setup : BuildEntry.Initializes source bindings ready restoreStack := .step _ pointerRead (.step _ countRead (.step _ (by rfl) (.done _)))
  have expanded := BuildEntry.declarations_execute setup (.seq loop (.seq removeCall (.return (.const 0#64))))
  change evaluateHOLFiniteState source (BuildEntry.declarations bindings (.seq loop (.seq removeCall (.return (.const 0#64))))) = _ at normal
  rw [expanded] at normal
  let finish := (evaluateHOLFiniteState ready (.seq loop (.seq removeCall (.return (.const 0#64))))).2
  have resultEq := congrArg Prod.fst normal
  change (evaluateHOLFiniteState ready (.seq loop (.seq removeCall (.return (.const 0#64))))).1 = some (.returned returned) at resultEq
  have actualTail : evaluateHOLFiniteState ready (.seq loop (.seq removeCall (.return (.const 0#64)))) = (some (.returned returned),finish) :=
    Prod.ext resultEq rfl
  have postEq := congrArg Prod.snd normal
  change restoreStack finish = post at postEq
  have postFrame : emptyLocalsHOLFinite post = emptyLocalsHOLFinite finish := by
    rw [← postEq]
    exact BuildEntry.restoration_frame setup finish
  have safe : Input.LocalPrefix (ofString "outer") loop := .loop _ (loop_body_safe _ (by decide) (by decide) (by decide))
  obtain ⟨middle,loopRun,tailRun,keepOuter⟩ := safe.normal_continue ready finish (.seq removeCall (.return (.const 0#64))) returned actualTail
  have readyFamily : TableFamily.Model ready cursor objects := family.of_control rfl rfl rfl rfl
  have readyImage : Journal.Image ready objects base count entries := image.transfer rfl (fun _ => rfl) (fun _ => rfl) (fun _ _ _ => rfl) image.separate
  have readyRegistry := registry.framed source ready cutoff cursor cursor objects objects accounts
    (TableFamily.PersistentFrame.of_memory cutoff cursor objects source ready rfl) (Nat.le_refl _) rfl
  have readyReader : ready.locals.lookup (ofString "inner") = some (.val (.word (objects reader).pointer)) := by
    exact (bind_lookup_other withCount "i" "inner" _ (by decide)).trans
      ((bind_lookup_other withInner "cap" "inner" _ (by decide)).trans (bind_lookup_same _ _ _))
  have readyCount : ready.locals.lookup (ofString "cap") = some (.val (.word (BitVec.ofNat 64 (objects reader).slots.length))) :=
    (bind_lookup_other withCount "i" "cap" _ (by decide)).trans (bind_lookup_same _ _ _)
  have readyAddress : ready.locals.lookup (ofString "addr") = some (.val (.word address)) :=
    (bind_lookup_other withCount "i" "addr" _ (by decide)).trans ((bind_lookup_other withInner "cap" "addr" _ (by decide)).trans
      ((bind_lookup_other source "inner" "addr" _ (by decide)).trans addressLocal))
  have readyOuter : ready.locals.lookup (ofString "outer") = source.locals.lookup (ofString "outer") :=
    (bind_lookup_other withCount "i" "outer" _ (by decide)).trans ((bind_lookup_other withInner "cap" "outer" _ (by decide)).trans
      (bind_lookup_other source "inner" "outer" _ (by decide)))
  obtain ⟨paid,nextCursor,next,funded,clock,forward,models,nextImage,nextZone,price,population,readerSame,lastIndex,codes,nextEnvironment,globals,
    nextValues,nextRegistry,frame,metadata,others⟩ := loop_normal (objects reader).slots.length ready middle address scratch transaction cursor cutoff objects writer reader base cap count entries
      readyFamily readyImage zone countBound (environment.of_fields rfl rfl rfl) installed accounts readyRegistry property values owned writerKind readerKind addressArena scratchArena
      floors scratchBelow small journalAbove readyAddress readyReader scratchGlobal transactionGlobal tableMapped tableStored tableAbove 0 (by omega) (bind_lookup_same _ _ _)
      readyCount tableBefore tableOutside loopRun
  have keepAddress := ((Input.LocalPrefix.loop condition (loop_body_safe (ofString "addr") (by decide) (by decide) (by decide))).summary ready)
  have concreteLoopRun : evaluateHOLFiniteState ready (.while condition loopBody) = (none,middle) := loopRun
  rw [concreteLoopRun] at keepAddress
  exact ⟨paid,nextCursor,next,middle,finish,funded,clock,forward,models,nextImage,nextZone,price,population,readerSame,codes,nextEnvironment,globals,
    nextValues,nextRegistry,⟨frame.words⟩,metadata,others,keepOuter.trans readyOuter,(keepAddress.1 rfl).trans readyAddress,tailRun,postFrame⟩

end InitECandidate.Solver.Mpt.DestroyStorage

#print axioms InitECandidate.Solver.Mpt.DestroyStorage.present_loop
