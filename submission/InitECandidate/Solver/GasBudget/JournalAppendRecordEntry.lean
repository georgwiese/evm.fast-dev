import InitECandidate.Solver.GasBudget.JournalAppendSetTail

namespace InitECandidate.Solver.GasBudget.Journal.Append
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch MutableTable

def afterCopy (deleting : Bool) : ProgHOL 64 := if deleting then deleteAfterCopy else setAfterCopy
def storeTail (deleting : Bool) : ProgHOL 64 := if deleting then afterStores deleteAfterCopy else afterStores setAfterCopy
def recorded {ι : Type} (source : PanSemStateFiniteExact 64 Guest.HostMemory) (objects : ι → TableFamily.Object)
    (base count : Nat) (entry : Entry ι) := recordState (bind source "r" (entryAddress base count 0)) objects base count entry

theorem record_program_shape (deleting : Bool) : afterCopy deleting =
    .dec (ofString "r") .one recordExpression (storesProgram deleting (storeTail deleting)) := by
  cases deleting
  · exact set_stores_shape
  · exact delete_stores_shape

/-- The actual declaration and four stores reach the canonical record state
and retain the real lexical restoration, for both original append functions. -/
theorem record_execute {ι : Type} (source : PanSemStateFiniteExact 64 Guest.HostMemory) (objects : ι → TableFamily.Object)
    (base cap count cursor : Nat) (entry : Entry ι) (flag : BitVec 64) (deleting : Bool)
    (zone : Zone objects base cap cursor) (room : count < cap) (domain : source.memaddrs = InitE.ordinaryDomain)
    (journal : source.globals.lookup (ofString "journal") = some (.val (.word (BitVec.ofNat 64 base))))
    (counter : source.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 count))))
    (tableLocal : source.locals.lookup (ofString "t") = some (.val (.word (objects entry.writer).pointer)))
    (copyLocal : source.locals.lookup (ofString "kc") = some (.val (.word entry.key)))
    (old : source.locals.lookup (ofString "old") = some (Get.pair flag entry.value))
    (flagEq : entry.flag = if deleting then 1#64 else flag) :
    evaluateHOLFiniteState source (afterCopy deleting) =
      (let output := evaluateHOLFiniteState (recorded source objects base count entry) (storeTail deleting)
       (output.1, restore source "r" output.2)) := by
  let declared := bind source "r" (entryAddress base count 0)
  have tableDeclared : declared.locals.lookup (ofString "t") = some (.val (.word (objects entry.writer).pointer)) :=
    (bind_lookup_other _ "r" "t" _ (by decide)).trans tableLocal
  have copyDeclared : declared.locals.lookup (ofString "kc") = some (.val (.word entry.key)) :=
    (bind_lookup_other _ "r" "kc" _ (by decide)).trans copyLocal
  have oldDeclared : declared.locals.lookup (ofString "old") = some (Get.pair flag entry.value) :=
    (bind_lookup_other _ "r" "old" _ (by decide)).trans old
  have stores := stores_execute declared objects base count entry flag deleting (storeTail deleting) (bind_lookup_same _ _ _)
    tableDeclared copyDeclared oldDeclared flagEq (fun field => zone.mapped source domain count room field)
  have setup : ProgramPrefix.Executes source [.declare "r" recordExpression] declared (fun post => restore source "r" post) :=
    .declare _ (record_expression_read source base count journal counter) (.done _)
  have actual := ProgramPrefix.execute setup (storesProgram deleting (storeTail deleting))
  rw [stores] at actual
  rw [record_program_shape]
  exact actual

theorem recorded_models {ι : Type} (source : PanSemStateFiniteExact 64 Guest.HostMemory) (objects : ι → TableFamily.Object)
    (base cap count cursor : Nat) (entry : Entry ι) (family : TableFamily.Model source cursor objects)
    (zone : Zone objects base cap cursor) (room : count < cap) :
    TableFamily.Model (recorded source objects base count entry) cursor objects := by
  have declaredFamily : TableFamily.Model (bind source "r" (entryAddress base count 0)) cursor objects :=
    ⟨fun table => (family.tables table).of_fields rfl rfl rfl rfl, family.apart⟩
  exact record_models _ objects base cap count cursor entry declaredFamily zone room

theorem recorded_image {ι : Type} (source : PanSemStateFiniteExact 64 Guest.HostMemory) (objects : ι → TableFamily.Object)
    (base cap count cursor : Nat) (entry : Entry ι) (entries : Nat → Entry ι)
    (image : Image source objects base count entries) (zone : Zone objects base cap cursor) (room : count < cap)
    (domain : source.memaddrs = InitE.ordinaryDomain)
    (queryFits : entry.key.toNat + KeyHash.keySize (objects entry.writer).kind < 2 ^ 64)
    (queryMapped : ∀ offset < KeyHash.keySize (objects entry.writer).kind, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress entry.key offset))) :
    Image (recorded source objects base count entry) objects base (count + 1) (Function.update entries count entry) := by
  have declaredImage : Image (bind source "r" (entryAddress base count 0)) objects base count entries :=
    image.transfer rfl (fun _ => rfl) (fun _ => rfl) (fun _ _ _ => rfl) image.separate
  exact record_image _ objects base cap count cursor entry entries declaredImage zone room domain queryFits queryMapped

end InitECandidate.Solver.GasBudget.Journal.Append

#print axioms InitECandidate.Solver.GasBudget.Journal.Append.record_program_shape
#print axioms InitECandidate.Solver.GasBudget.Journal.Append.record_execute
#print axioms InitECandidate.Solver.GasBudget.Journal.Append.recorded_models
#print axioms InitECandidate.Solver.GasBudget.Journal.Append.recorded_image
