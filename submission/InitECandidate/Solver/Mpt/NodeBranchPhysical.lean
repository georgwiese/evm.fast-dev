import InitECandidate.Solver.Mpt.NodeBranchCells
import InitECandidate.Solver.Mpt.NodeConstructorPhysical

namespace InitECandidate.Solver.Mpt.NodeConstructor
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

structure BranchPhysical (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64) : Prop where
  allocation : Physical .branch source target heap (fun _=>0#64)
  tag : target.memory heap=.word 3#64
  zeros : ∀ offset : Nat,0<offset → offset<176 → offset%8=0 → target.memory (heap+BitVec.ofNat 64 offset)=.word 0#64

theorem branch_physical_of_fields (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64)
    (arena : AllocatedBytes.Arena heap 176) (aligned : heap.toNat%8=0)
    (domain : target.memaddrs=source.memaddrs) (endian : target.be=source.be)
    (globals : target.globals=source.globals.update (ofString "heap_ptr",.val (.word (PersistentAlloc.rounded heap 176#64))))
    (memory : target.memory=StoreWord.put (Zero.finalMemory source.memory heap 176) heap 3#64) : BranchPhysical source target heap := by
  have growth:=rounded_ordinary heap 176#64 arena.upper
  have nextArena : AllocatedBytes.Arena (PersistentAlloc.rounded heap 176#64) 0:=
    ⟨by have first:=arena.lower; have grows:=growth.1; omega,by have last:=growth.2.1; omega⟩
  refine ⟨⟨arena,domain,endian,?_,nextArena,growth.2.2,growth.1,?_,?_⟩,?_,?_⟩
  · change target.globals.lookup (ofString "heap_ptr")=some (.val (.word (PersistentAlloc.rounded heap 176#64)))
    rw [globals]
    simp [HolFiniteMapExact.update,FUPDATE]
  · intro field member
    simp [fields] at member
  · intro query outside
    change query.toNat<heap.toNat ∨ heap.toNat+176≤query.toNat at outside
    have away : query≠heap:=by intro same; subst query; omega
    rw [memory,StoreWord.put,if_neg away]
    apply Zero.final_memory_away
    intro offset inside same
    have number:=congrArg BitVec.toNat same
    rw [byteAddress_toNat heap offset (by have upper:=arena.upper; omega)] at number
    omega
  · rw [memory,StoreWord.put,if_pos rfl]
  · intro offset nonzero inside offsetAligned
    have away : heap+BitVec.ofNat 64 offset≠heap:=by
      intro equal
      have offsets : BitVec.ofNat 64 offset=0#64:=(BitVec.add_right_inj heap).mp (equal.trans (BitVec.add_zero heap).symm)
      have number:=congrArg BitVec.toNat offsets
      rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)] at number
      change offset=0 at number
      omega
    rw [memory,StoreWord.put,if_neg away]
    exact branch_zero_cells source.memory heap offset inside offsetAligned

theorem branch_physical (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64)
    (domain : source.memaddrs=InitE.ordinaryDomain)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (frontier : AllocatedBytes.Arena heap 0) (aligned : heap.toNat%8=0)
    (installed : Input.OriginalCode.Installed source.code) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (body .branch)=(some (.returned value),target)) :
    value=.val (.word heap) ∧ BranchPhysical source target heap := by
  obtain ⟨answer,arena,positive,frame⟩:=branch_normal source target heap domain heapCell frontier aligned installed value normal
  exact ⟨answer,branch_physical_of_fields source target heap arena aligned
    (by have same:=congrArg PanSemStateFiniteExact.memaddrs frame; exact same)
    (by have same:=congrArg PanSemStateFiniteExact.be frame; exact same)
    (congrArg PanSemStateFiniteExact.globals frame) (congrArg PanSemStateFiniteExact.memory frame)⟩

/-- The assigned original branch call retains the same real physical
contract after restoring caller locals and binding its actual result. -/
theorem branch_assigned_physical (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64) (name : MlS)
    (domain : source.memaddrs=InitE.ordinaryDomain)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (frontier : AllocatedBytes.Arena heap 0) (aligned : heap.toNat%8=0)
    (installed : Input.OriginalCode.Installed source.code)
    (normal : evaluateHOLFiniteState source (.call (some (some (.local,name),none)) (ofString "node_new_branch") [])=(none,target)) :
    BranchPhysical source target heap := by
  obtain ⟨funded,values,actualBody,callee,shape,childTarget,returned,args,called,run,checked,endpoint⟩:=
    Input.CallNormal.local_data source target name (ofString "node_new_branch") [] normal
  have empty : values=[]:=Option.some.inj args.symm
  subst values
  have lookup : source.code.lookup (ofString "node_new_branch")=some ([],body .branch,.one):=original_code .branch source.code installed
  have raw : lookupCodeHOLExact source.code.lookup (ofString "node_new_branch") []=some (body .branch,(fun _=>none),.one):=by
    simp [lookupCodeHOLExact,lookup]
  obtain ⟨fixedCallee,fixed,calleeLocals⟩:=CodeEnvironment.finite_lookup source.code.lookup _ _ _ _ _ raw
  have same:=Option.some.inj (called.symm.trans fixed)
  have bodyEq:=congrArg Prod.fst same
  have mapEq:=congrArg (fun triple : ProgHOL 64×HolFiniteMapExact MlS (ValueHOL 64)×ShapeHOL=>triple.2.1) same
  have shapeEq:=congrArg (fun triple : ProgHOL 64×HolFiniteMapExact MlS (ValueHOL 64)×ShapeHOL=>triple.2.2) same
  change actualBody=body .branch at bodyEq
  subst actualBody
  change callee=fixedCallee at mapEq
  change shape=.one at shapeEq
  subst callee
  subst shape
  obtain ⟨answer,arena,positive,frame⟩:=branch_normal (callEntryStateHOLFinite source fixedCallee) childTarget heap domain heapCell frontier aligned installed returned run
  have restored:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>setVarHOLFinite name returned {state with locals:=source.locals}) frame
  have current : target=setVarHOLFinite name (.val (.word heap))
      {PersistentAlloc.post {source with clock:=source.clock-10} heap 176#64 with
        memory:=StoreWord.put (Zero.finalMemory source.memory heap 176) heap 3#64}:=by
    rw [endpoint]
    simpa only [answer,callEntryStateHOLFinite,emptyLocalsHOLFinite,Nat.sub_sub,PersistentAlloc.post] using restored
  exact branch_physical_of_fields source target heap arena aligned
    (by have same:=congrArg PanSemStateFiniteExact.memaddrs current; exact same)
    (by have same:=congrArg PanSemStateFiniteExact.be current; exact same)
    (congrArg PanSemStateFiniteExact.globals current) (congrArg PanSemStateFiniteExact.memory current)

end InitECandidate.Solver.Mpt.NodeConstructor

#print axioms InitECandidate.Solver.Mpt.NodeConstructor.branch_physical_of_fields
#print axioms InitECandidate.Solver.Mpt.NodeConstructor.branch_physical
#print axioms InitECandidate.Solver.Mpt.NodeConstructor.branch_assigned_physical
