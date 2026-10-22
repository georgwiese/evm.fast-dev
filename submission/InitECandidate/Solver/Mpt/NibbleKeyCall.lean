import InitECandidate.Solver.Mpt.NibbleKeyUnsecured

namespace InitECandidate.Solver.Mpt.NibbleKey
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The real scoped original caller receives the derived nibble tuple and
view while retaining its saved ABI locals, heap update and old memory. -/
theorem scoped_normal {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    (name : MlS) (arguments : List (ExpHOL 64)) (m key heap : BitVec 64) (length : Nat)
    (small : length≤32) (installed : Input.OriginalCode.Installed source.code)
    (domain : source.memaddrs=InitE.ordinaryDomain) (little : source.be=false)
    (argsRead : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=
      some [.val (.word m),.val (.word key),.val (.word (BitVec.ofNat 64 length))])
    (mapped : source.memaddrs (m+8#64)) (cell : source.memory (m+8#64)=.word 0#64)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (frontier : AllocatedBytes.Arena heap 0) (aligned : heap.toNat%8=0)
    (inputArena : AllocatedBytes.Arena key length) (before : key.toNat+length≤heap.toNat)
    (reached : Input.CallPrefix.Reaches source (.scoped name returnShape (ofString "mpt_nibble_key") arguments) target) :
    AllocatedBytes.Arena heap (2*length) ∧ target.locals.lookup name=some (output heap length) ∧
      (∀ other,name≠other→target.locals.lookup other=source.locals.lookup other) ∧
      TrieWalk.KeyView target.memory target.memaddrs target.be heap (2*length) ∧
      source.clock-target.clock≤length/4+6 ∧
      KeyToNibbles.writeMetadata target=KeyToNibbles.writeMetadata (PersistentAlloc.post source heap (BitVec.ofNat 64 (2*length))) ∧
      ∀ query : BitVec 64,query.toNat<heap.toNat ∨ heap.toNat+2*length≤query.toNat→target.memory query=source.memory query := by
  cases reached with
  | «scoped» _ _ _ _ actualValues actualBody callee actualShape returned childTarget args called funded run checked=>
    have sameValues : actualValues=[.val (.word m),.val (.word key),.val (.word (BitVec.ofNat 64 length))]:=
      Option.some.inj (args.symm.trans argsRead)
    subst actualValues
    obtain ⟨expected,expectedCall,mLocal,keyLocal,lengthLocal⟩:=environment source.code.lookup m key (BitVec.ofNat 64 length) (original_code source.code installed)
    have same:=Option.some.inj (called.symm.trans expectedCall)
    have bodyEq:=congrArg Prod.fst same
    have mapEq:=congrArg (fun triple : ProgHOL 64×HolFiniteMapExact MlS (ValueHOL 64)×ShapeHOL=>triple.2.1) same
    have shapeEq:=congrArg (fun triple : ProgHOL 64×HolFiniteMapExact MlS (ValueHOL 64)×ShapeHOL=>triple.2.2) same
    change actualBody=body at bodyEq
    change callee=expected at mapEq
    change actualShape=returnShape at shapeEq
    subst actualBody
    subst callee
    subst actualShape
    obtain ⟨arena,answer,view,cost,frame,memory⟩:=unsecured_normal (callEntryStateHOLFinite source expected) childTarget m key heap length
      small installed domain little mLocal keyLocal lengthLocal mapped cell heapCell frontier aligned inputArena before returned run
    refine ⟨arena,?_,?_,view,?_,frame,memory⟩
    · simp [setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,answer]
    · intro other different
      simp [setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,different]
    · change source.clock-1-childTarget.clock≤length/4+5 at cost
      change source.clock-childTarget.clock≤length/4+6
      omega

end InitECandidate.Solver.Mpt.NibbleKey

#print axioms InitECandidate.Solver.Mpt.NibbleKey.scoped_normal
