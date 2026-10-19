import InitECandidate.Solver.MutableTable.FamilyDeleteValues

namespace InitECandidate.Solver.MutableTable.TableFamily
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix NaturalLayout

/-- Actual deletion retains every live table and its stable pointer. The
deleted table changes only its population/occupied representation; no heap
allocation or entry-clock allowance is assumed. -/
theorem delete_normal {ι : Type} [DecidableEq ι] (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (cursor : Nat) (objects : ι → Object) (writer : ι) (family : Model source cursor objects)
    (environment : GasBudget.WarmKeys.Environment source) (query : BitVec 64)
    (queryFits : query.toNat + KeyHash.keySize (objects writer).kind < 2 ^ 64)
    (queryMapped : ∀ offset < KeyHash.keySize (objects writer).kind, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress query offset)))
    (deleteCode : source.code.lookup (ofString "htab_del") = some (Find.formals, Delete.body, .one))
    (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some [.val (.word (objects writer).pointer), .val (.word query)])
    (normal : evaluateHOLFiniteState source (.call (some (none, none)) (ofString "htab_del") arguments) = (none, target)) :
    ∃ (paid : Nat) (next : Object),
      paid ≤ Delete.modelPrice (objects writer).kind (objects writer).slots.length + 1 ∧
      paid ≤ source.clock ∧ target.clock = source.clock - paid ∧
      next.kind = (objects writer).kind ∧ next.plan = (objects writer).plan ∧ next.floor = (objects writer).floor ∧
      Model target cursor (Function.update objects writer next) ∧
      (∀ index, (Function.update objects writer next index).pointer = (objects index).pointer) ∧
      (objects writer).slots.length - 1 ≤ next.slots.length ∧ next.slots.length ≤ (objects writer).slots.length ∧
      target.locals = source.locals ∧ target.globals = source.globals ∧ target.code = source.code ∧
      GasBudget.WarmKeys.Environment target ∧
      (∀ address, TableFootprint.Outside (objects writer).kind (objects writer).plan address → target.memory address = source.memory address) := by
  obtain ⟨paid,next,bounded,fits,clock,kind,plan,floor,models,pointers,lower,upper,locals,globals,codes,nextEnvironment,protectedWords,nextValues⟩ :=
    delete_normal_values source target cursor objects writer family environment query (fun _ _=>True) (fun _ _ _ _ _ _=>True.intro) queryFits queryMapped deleteCode arguments args normal
  exact ⟨paid,next,bounded,fits,clock,kind,plan,floor,models,pointers,lower,upper,locals,globals,codes,nextEnvironment,protectedWords⟩

end InitECandidate.Solver.MutableTable.TableFamily

#print axioms InitECandidate.Solver.MutableTable.TableFamily.delete_normal
