import InitECandidate.Solver.Mpt.NodeConstructorProgram
import InitECandidate.Solver.PanFieldStoresFrame

namespace InitECandidate.Solver.Mpt.NodeConstructor
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

def fields (kind : Kind) (words : String→BitVec 64) : List FieldStores.Field := match kind with
  | .hashed=>[⟨0,.literal 0#64⟩,⟨8,.literal 0#64⟩,⟨16,.literal 0#64⟩,⟨24,.saved "hash" (words "hash")⟩]
  | .leaf=>[⟨0,.literal 1#64⟩,⟨8,.literal 0#64⟩,⟨16,.literal 0#64⟩,⟨24,.literal 0#64⟩,
      ⟨32,.saved "nib" (words "nib")⟩,⟨40,.saved "nlen" (words "nlen")⟩,⟨48,.saved "vptr" (words "vptr")⟩,⟨56,.saved "vlen" (words "vlen")⟩]
  | .extension=>[⟨0,.literal 2#64⟩,⟨8,.literal 0#64⟩,⟨16,.literal 0#64⟩,⟨24,.literal 0#64⟩,
      ⟨32,.saved "nib" (words "nib")⟩,⟨40,.saved "nlen" (words "nlen")⟩,⟨48,.saved "child" (words "child")⟩]
  | .branch=>[]

def Inputs (kind : Kind) (source : PanSemStateFiniteExact 64 Guest.HostMemory) (words : String→BitVec 64) : Prop :=
  let cell:=fun name=>source.locals.lookup (ofString name)=some (.val (.word (words name)))
  match kind with
  | .hashed=>cell "hash"
  | .leaf=>cell "nib" ∧ cell "nlen" ∧ cell "vptr" ∧ cell "vlen"
  | .extension=>cell "nib" ∧ cell "nlen" ∧ cell "child"
  | .branch=>True

set_option maxRecDepth 100000 in
theorem scalar_tail_shape (kind : Kind) (scalar : kind≠.branch) (words : String→BitVec 64) :
    tail kind=FieldStores.program "nd" "" (fields kind words) (.return (QueryBranch.localVar "nd")) := by
  cases kind <;> try exact (scalar rfl).elim
  all_goals simp only [tail,body,original,fields,FieldStores.program,FieldStores.address,FieldStores.Value.expression,QueryBranch.addConst,QueryBranch.localVar,
    Guest.guestFn_node_new_hashed,Guest.guestFn_node_new_leaf,Guest.guestFn_node_new_ext,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil]

theorem fields_ready (kind : Kind) (source : PanSemStateFiniteExact 64 Guest.HostMemory) (words : String→BitVec 64)
    (inputs : Inputs kind source words) : ∀ field∈fields kind words,field.value.Ready source "" 0#64 := by
  cases kind <;> simpa [fields,FieldStores.Value.Ready,Inputs] using inputs

theorem fields_geometry (kind : Kind) (words : String→BitVec 64) :
    ∀ field∈fields kind words,field.offset<bytes kind ∧ field.offset%8=0 := by
  cases kind <;> simp [fields,bytes]

theorem fields_avoid (kind : Kind) (words : String→BitVec 64) (message address : BitVec 64) :
    ∀ field∈fields kind words,field.value.Avoid message address := by
  cases kind <;> simp [fields,FieldStores.Value.Avoid]

theorem inputs_allocation (kind : Kind) (source : PanSemStateFiniteExact 64 Guest.HostMemory) (words : String→BitVec 64)
    (heap amount : BitVec 64) (inputs : Inputs kind source words) :
    Inputs kind (QueryBranch.bind (PersistentAlloc.post {source with clock:=source.clock-1} heap amount) "nd" heap) words := by
  have hashName : ofString "nd"≠ofString "hash":=by decide
  have nibName : ofString "nd"≠ofString "nib":=by decide
  have lengthName : ofString "nd"≠ofString "nlen":=by decide
  have valueName : ofString "nd"≠ofString "vptr":=by decide
  have valueLengthName : ofString "nd"≠ofString "vlen":=by decide
  have childName : ofString "nd"≠ofString "child":=by decide
  cases kind <;> simpa [Inputs,QueryBranch.bind,PersistentAlloc.post,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,
    hashName,nibName,lengthName,valueName,valueLengthName,childName] using inputs

end InitECandidate.Solver.Mpt.NodeConstructor

#print axioms InitECandidate.Solver.Mpt.NodeConstructor.scalar_tail_shape
#print axioms InitECandidate.Solver.Mpt.NodeConstructor.fields_ready
#print axioms InitECandidate.Solver.Mpt.NodeConstructor.fields_geometry
#print axioms InitECandidate.Solver.Mpt.NodeConstructor.fields_avoid
#print axioms InitECandidate.Solver.Mpt.NodeConstructor.inputs_allocation
