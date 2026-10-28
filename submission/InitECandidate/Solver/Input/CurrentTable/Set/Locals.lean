import InitECandidate.Solver.Input.CurrentTable.Set.LookupEntry
import InitECandidate.Solver.Input.CallResumeLookup

namespace InitECandidate.Solver.Input.CurrentTable.Set
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix QueryBranch

/-- The real scalar bindings retained across set's helper calls. -/
structure Locals (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table pointer value : BitVec 64) : Prop where
  tableCell : source.locals.lookup (ofString "t") = some (.val (.word table))
  keyCell : source.locals.lookup (ofString "key") = some (.val (.word pointer))
  valueCell : source.locals.lookup (ofString "value") = some (.val (.word value))
  lengthCell : source.locals.lookup (ofString "klen") = some (.val (.word 32#64))
  strideCell : source.locals.lookup (ofString "stride") = some (.val (.word 32#64))

theorem Locals.with_local {source : PanSemStateFiniteExact 64 Guest.HostMemory} {table pointer value : BitVec 64}
    (ready : Locals source table pointer value) (name : String) (word : BitVec 64)
    (notTable : ofString name ≠ ofString "t") (notKey : ofString name ≠ ofString "key")
    (notValue : ofString name ≠ ofString "value") (notLength : ofString name ≠ ofString "klen")
    (notStride : ofString name ≠ ofString "stride") : Locals (bind source name word) table pointer value :=
  ⟨(bind_lookup_other source name "t" word notTable).trans ready.tableCell,
    (bind_lookup_other source name "key" word notKey).trans ready.keyCell,
    (bind_lookup_other source name "value" word notValue).trans ready.valueCell,
    (bind_lookup_other source name "klen" word notLength).trans ready.lengthCell,
    (bind_lookup_other source name "stride" word notStride).trans ready.strideCell⟩

theorem Locals.after_call {source : PanSemStateFiniteExact 64 Guest.HostMemory} {table pointer value : BitVec 64}
    (ready : Locals source table pointer value) (target : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String) (returned : ValueHOL 64)
    (notTable : ofString name ≠ ofString "t") (notKey : ofString name ≠ ofString "key")
    (notValue : ofString name ≠ ofString "value") (notLength : ofString name ≠ ofString "klen")
    (notStride : ofString name ≠ ofString "stride") : Locals (CallNormal.continuationEntry source target name returned) table pointer value :=
  ⟨(CallNormal.continuation_lookup_other source target name "t" returned notTable).trans ready.tableCell,
    (CallNormal.continuation_lookup_other source target name "key" returned notKey).trans ready.keyCell,
    (CallNormal.continuation_lookup_other source target name "value" returned notValue).trans ready.valueCell,
    (CallNormal.continuation_lookup_other source target name "klen" returned notLength).trans ready.lengthCell,
    (CallNormal.continuation_lookup_other source target name "stride" returned notStride).trans ready.strideCell⟩

theorem initial_locals (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table pointer value : BitVec 64)
    (tableCell : source.locals.lookup (ofString "t") = some (.val (.word table)))
    (keyCell : source.locals.lookup (ofString "key") = some (.val (.word pointer)))
    (valueCell : source.locals.lookup (ofString "value") = some (.val (.word value))) :
    Locals (strideEntry source) table pointer value := by
  have other (name : String) (notLength : ofString "klen" ≠ ofString name) (notStride : ofString "stride" ≠ ofString name) :=
    (bind_lookup_other (lengthEntry source) "stride" name 32#64 notStride).trans (bind_lookup_other source "klen" name 32#64 notLength)
  exact ⟨(other "t" (by decide) (by decide)).trans tableCell,(other "key" (by decide) (by decide)).trans keyCell,
    (other "value" (by decide) (by decide)).trans valueCell,
    (bind_lookup_other (lengthEntry source) "stride" "klen" 32#64 (by decide)).trans (bind_lookup_same _ _ _),bind_lookup_same _ _ _⟩

structure LookupLocals (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table pointer value leaf : BitVec 64) : Prop where
  locals : Locals source table pointer value
  leafCell : source.locals.lookup (ofString "leaf") = some (.val (.word leaf))
  keysCell : source.locals.lookup (ofString "keys") = some (.val (.word (New.keysPointer table)))

theorem LookupLocals.after_keys {source : PanSemStateFiniteExact 64 Guest.HostMemory} {table pointer value leaf : BitVec 64}
    (ready : Locals source table pointer value)
    (leafCell : source.locals.lookup (ofString "leaf") = some (.val (.word leaf))) :
    LookupLocals (bind source "keys" (New.keysPointer table)) table pointer value leaf :=
  ⟨ready.with_local "keys" _ (by decide) (by decide) (by decide) (by decide) (by decide),
    (bind_lookup_other source "keys" "leaf" _ (by decide)).trans leafCell,bind_lookup_same _ _ _⟩

theorem LookupLocals.after_call {source : PanSemStateFiniteExact 64 Guest.HostMemory} {table pointer value leaf : BitVec 64}
    (ready : LookupLocals source table pointer value leaf) (target : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String) (returned : ValueHOL 64)
    (notTable : ofString name ≠ ofString "t") (notKey : ofString name ≠ ofString "key")
    (notValue : ofString name ≠ ofString "value") (notLength : ofString name ≠ ofString "klen")
    (notStride : ofString name ≠ ofString "stride") (notLeaf : ofString name ≠ ofString "leaf") (notKeys : ofString name ≠ ofString "keys") :
    LookupLocals (CallNormal.continuationEntry source target name returned) table pointer value leaf :=
  ⟨ready.locals.after_call target name returned notTable notKey notValue notLength notStride,
    (CallNormal.continuation_lookup_other source target name "leaf" returned notLeaf).trans ready.leafCell,
    (CallNormal.continuation_lookup_other source target name "keys" returned notKeys).trans ready.keysCell⟩

end InitECandidate.Solver.Input.CurrentTable.Set

#print axioms InitECandidate.Solver.Input.CurrentTable.Set.Locals.after_call
#print axioms InitECandidate.Solver.Input.CurrentTable.Set.initial_locals
#print axioms InitECandidate.Solver.Input.CurrentTable.Set.LookupLocals.after_call
