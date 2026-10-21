import InitECandidate.Solver.Input.RunAttemptStateFields

namespace InitECandidate.Solver.Input
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- Original run_attempt's database prefix changes the persistent heap and
publishes only its two block-hash globals. Runtime metadata stays fixed. -/
structure ConstructorRuntimeFrame (source target : PanSemStateFiniteExact 64 Guest.HostMemory) : Prop where
  code : target.code=source.code
  domain : target.memaddrs=source.memaddrs
  endian : target.be=source.be
  exceptions : target.eshapes=source.eshapes
  oracle : target.ffi.oracle=source.ffi.oracle
  globals : ∀ key,key≠ofString "heap_ptr" → key≠ofString "block_hashes" → key≠ofString "block_hashes_n" →
    target.globals.lookup key=source.globals.lookup key

theorem ConstructorRuntimeFrame.refl (source : PanSemStateFiniteExact 64 Guest.HostMemory) : ConstructorRuntimeFrame source source :=
  ⟨rfl,rfl,rfl,rfl,rfl,by intro key h b n; rfl⟩

theorem ConstructorRuntimeFrame.trans (source middle target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (first : ConstructorRuntimeFrame source middle) (second : ConstructorRuntimeFrame middle target) : ConstructorRuntimeFrame source target :=
  ⟨second.code.trans first.code,second.domain.trans first.domain,second.endian.trans first.endian,
    second.exceptions.trans first.exceptions,second.oracle.trans first.oracle,
    fun key h b n=>(second.globals key h b n).trans (first.globals key h b n)⟩

theorem CallNormal.continuation_runtime (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String) (value : ValueHOL 64) :
    ConstructorRuntimeFrame target (continuationEntry source target name value) := ⟨rfl,rfl,rfl,rfl,rfl,by intro key h b n; rfl⟩

theorem RunAttempt.constructor_runtime (source : PanSemStateFiniteExact 64 Guest.HostMemory) (count hashes : BitVec 64) (parent : ValueHOL 64) :
    ConstructorRuntimeFrame source (constructorEntry source count hashes parent) := by
  refine ⟨rfl,rfl,rfl,rfl,rfl,?_⟩
  intro key h b n
  simp [constructorEntry,putGlobal,parentEntry,countEntry,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,Ne.symm b,Ne.symm n]

theorem ConstructorRuntimeFrame.of_constructor (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (array heap : BitVec 64) (count : Nat) (stp pad scratch : BitVec 64)
    (actual : MutableTable.WitnessBuild.Normal source target array heap count stp pad scratch) : ConstructorRuntimeFrame source target := by
  obtain ⟨code,domain,endian,exceptions,oracle,globals⟩ := actual.fields source target array heap count stp pad scratch
  exact ⟨code,domain,endian,exceptions,oracle,fun key h b n=>globals key h⟩

end InitECandidate.Solver.Input

#print axioms InitECandidate.Solver.Input.ConstructorRuntimeFrame.refl
#print axioms InitECandidate.Solver.Input.ConstructorRuntimeFrame.trans
#print axioms InitECandidate.Solver.Input.CallNormal.continuation_runtime
#print axioms InitECandidate.Solver.Input.RunAttempt.constructor_runtime
#print axioms InitECandidate.Solver.Input.ConstructorRuntimeFrame.of_constructor
