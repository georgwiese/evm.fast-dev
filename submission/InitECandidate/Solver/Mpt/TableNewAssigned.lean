import InitECandidate.Solver.Mpt.TableNewOwnership
import InitECandidate.Solver.MutableTable.TableRuntime.AssignedNormal

namespace InitECandidate.Solver.Mpt.TableNewOwnership
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix MutableTable NaturalLayout GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem assigned_registered {ι : Type} (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (cursor cutoff capacity bits : Nat) (kind : KeyHash.Kind) (objects : ι → TableFamily.Object) (anchor : ι)
    (base cap count : Nat) (entries : Nat → Journal.Entry ι)
    (family : TableFamily.Model source cursor objects) (image : Journal.Image source objects base count entries)
    (zone : Journal.Zone objects base cap cursor) (countBound : count ≤ cap) (environment : WarmKeys.Environment source)
    (accounts : List (BitVec 64)) (registry : AccountDecode.Registry source cutoff cursor objects accounts)
    (property : ι → BitVec 64 → Prop) (values : TableFamily.ValuesHave source objects property) (savedValues : Journal.EntryValues entries count property)
    (freshProperty : BitVec 64 → Prop) (power : capacity = 2 ^ bits) (minimum : 3 ≤ bits) (capBound : capacity ≤ 2 ^ 32)
    (newCode : source.code.lookup (ofString "htab_new") = some (TableNew.formals,TableNew.body,.one))
    (name : String) (arguments : List (ExpHOL 64)) (old : BitVec 64)
    (binding : source.locals.lookup (ofString name) = some (.val (.word old)))
    (args : evalListHOLFinite source (h := fun query => Classical.propDecidable (source.memaddrs query)) arguments = some (TableRuntime.values kind capacity))
    (normal : evaluateHOLFiniteState source (.call (some (some (.local,ofString name),none)) (ofString "htab_new") arguments) = (none,post)) :
    TableRuntime.price capacity + 1 ≤ source.clock ∧ post = TableRuntime.callState source name kind cursor capacity ∧
      TableFamily.Model post (freshEnd kind cursor capacity) (TableFamily.extend objects (Journal.newObject kind cursor capacity)) ∧
      Journal.Image post (TableFamily.extend objects (Journal.newObject kind cursor capacity)) base count (fun index => (entries index).lift) ∧
      Journal.Zone (TableFamily.extend objects (Journal.newObject kind cursor capacity)) base cap (freshEnd kind cursor capacity) ∧
      AccountDecode.Registry post cutoff (freshEnd kind cursor capacity) (TableFamily.extend objects (Journal.newObject kind cursor capacity)) accounts ∧
      TableFamily.ValuesHave post (TableFamily.extend objects (Journal.newObject kind cursor capacity)) (liftProperty property freshProperty) ∧
      Journal.EntryValues (fun index => (entries index).lift) count (liftProperty property freshProperty) ∧
      WarmKeys.Environment post ∧ HeapGlobals source post ∧
      (∀ query : BitVec 64, query.toNat < cursor → TableFamily.Outside objects query →
        TableFamily.Outside (TableFamily.extend objects (Journal.newObject kind cursor capacity)) query ∧ post.memory query = source.memory query) := by
  have table := family.tables anchor
  have lower : 2701131776 ≤ cursor := by
    have begin := table.valid.lower .header
    have before := table.earlier .header
    change (objects anchor).plan.base .header + 72 ≤ cursor at before
    omega
  obtain ⟨positive,multiple,keySmall,wordSmall,capSmall⟩ := Journal.new_capacity_bounds kind capacity bits power minimum capBound
  obtain ⟨funded,valid,postEq⟩ := TableRuntime.assigned_normal source post kind cursor capacity name arguments old positive lower table.bounded table.aligned
    keySmall wordSmall capSmall multiple environment.domain args newCode table.heap environment.allocCode environment.trapCode environment.zeroCode binding normal
  obtain ⟨familyNext,imageNext,zoneNext,environmentNext,globals⟩ := Journal.new_models source name cursor capacity bits kind objects base cap count entries family image zone countBound
    environment table.bounded power (by omega) multiple valid
  obtain ⟨registryNext,valuesNext,savedNext,frame⟩ := models source name cursor cutoff capacity kind objects family accounts registry property values entries count savedValues freshProperty valid
  rw [postEq]
  exact ⟨funded,rfl,familyNext,imageNext,zoneNext,registryNext,valuesNext,savedNext,environmentNext,globals,frame⟩

end InitECandidate.Solver.Mpt.TableNewOwnership

#print axioms InitECandidate.Solver.Mpt.TableNewOwnership.assigned_registered
