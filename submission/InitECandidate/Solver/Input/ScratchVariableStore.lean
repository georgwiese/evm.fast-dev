import InitECandidate.Solver.Input.ScratchStore
import InitECandidate.Solver.Input.ScopedCallNone

namespace InitECandidate.Solver.Input.ScratchStore
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- A real scratch allocation also fails at a scalar store whose value is
an existing caller word. Its caller binding survives the actual callee. -/
theorem after_normal_variable_error {F : Type} (source target : PanSemStateFiniteExact 64 F)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (pointer limit : BitVec 64)
    (length offset : Nat) (name valueName : String) (word : BitVec 64) (rest : ProgHOL 64) (returned : ValueHOL 64)
    (different : ofString name≠ofString valueName)
    (valueCell : source.locals.lookup (ofString valueName)=some (.val (.word word)))
    (small : length<2^64) (inside : offset<length)
    (pointerBound : pointer.toNat≤InitE.scratchEnd) (ordered : limit≤pointer) (aligned : limit.toNat%8=0)
    (domain : source.memaddrs=InitE.ordinaryDomain) (installed : OriginalCode.Installed source.code)
    (pointerGlobal : source.globals.lookup (ofString "scratch_ptr")=some (.val (.word pointer)))
    (limitGlobal : source.globals.lookup (ofString "frame_mem_ptr")=some (.val (.word limit)))
    (amountCell : callee.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 length))))
    (normal : evaluateHOLFiniteState (callEntryStateHOLFinite source callee) (Arenas.body .down)=(some (.returned returned),target)) :
    let ready:=CallNormal.continuationEntry source target name returned
    evaluateHOLFiniteState ready (.seq (.store (Scalar.plus (localVar name) offset) (localVar valueName)) rest)=(some .error,ready) := by
  classical
  let ready:=CallNormal.continuationEntry source target name returned
  have literal:=after_normal_error source target callee pointer limit length offset name word rest returned small inside
    pointerBound ordered aligned domain installed pointerGlobal limitGlobal amountCell normal
  have cell : ready.locals.lookup (ofString valueName)=some (.val (.word word)) := by
    simpa [ready,CallNormal.continuationEntry,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,different,Ne.symm different] using valueCell
  have read : eval ready (localVar valueName)=some (.val (.word word)) := by
    simp [eval,localVar,evalHOLExact,toExact,cell]
  have same : evaluateHOLFiniteState ready (.store (Scalar.plus (localVar name) offset) (localVar valueName))=
      evaluateHOLFiniteState ready (.store (Scalar.plus (localVar name) offset) (.const word)) := by
    simp only [eval] at read
    rw [evaluateHOLFiniteState_store,evaluateHOLFiniteState_store,read]
    rfl
  change evaluateHOLFiniteState ready (.seq (.store (Scalar.plus (localVar name) offset) (localVar valueName)) rest)=(some .error,ready)
  rw [evaluateHOLFiniteState_seq_line780,same]
  change evaluateHOLFiniteState ready (.seq (.store (Scalar.plus (localVar name) offset) (.const word)) rest)=(some .error,ready) at literal
  rw [evaluateHOLFiniteState_seq_line780] at literal
  exact literal

/-- Such a real allocation/store cannot continue its caller's loop. This
retains all actual allocation/trap outcomes without assuming future room. -/
theorem allocated_variable_not_none (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer limit : BitVec 64) (length offset : Nat) (name valueName : String) (word : BitVec 64) (rest : ProgHOL 64)
    (different : ofString name≠ofString valueName)
    (valueCell : source.locals.lookup (ofString valueName)=some (.val (.word word)))
    (small : length<2^64) (inside : offset<length)
    (pointerBound : pointer.toNat≤InitE.scratchEnd) (ordered : limit≤pointer) (aligned : limit.toNat%8=0)
    (domain : source.memaddrs=InitE.ordinaryDomain) (installed : OriginalCode.Installed source.code)
    (pointerGlobal : source.globals.lookup (ofString "scratch_ptr")=some (.val (.word pointer)))
    (limitGlobal : source.globals.lookup (ofString "frame_mem_ptr")=some (.val (.word limit)))
    (actual : evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "scratch_alloc") [.const (BitVec.ofNat 64 length)]
      (.seq (.store (Scalar.plus (localVar name) offset) (localVar valueName)) rest))=(none,post)) : False := by
  obtain ⟨callee,called,amountCell⟩ := CallNormal.unary_environment source.code.lookup (ofString "scratch_alloc") "n"
    (Arenas.body .down) (BitVec.ofNat 64 length) (ScratchClear.allocator_installed source.code installed)
  obtain ⟨funded,target,returned,inner,normal,checked,remaining,endpoint⟩ := CallNormal.scoped_none source post name .one (ofString "scratch_alloc")
    [.const (BitVec.ofNat 64 length)] [.val (.word (BitVec.ofNat 64 length))] (Arenas.body .down)
    (.seq (.store (Scalar.plus (localVar name) offset) (localVar valueName)) rest) callee .one rfl called actual
  have failed:=after_normal_variable_error source target callee pointer limit length offset name valueName word rest returned different valueCell small inside
    pointerBound ordered aligned domain installed pointerGlobal limitGlobal amountCell normal
  rw [failed] at remaining
  cases remaining

end InitECandidate.Solver.Input.ScratchStore

#print axioms InitECandidate.Solver.Input.ScratchStore.after_normal_variable_error
#print axioms InitECandidate.Solver.Input.ScratchStore.allocated_variable_not_none
