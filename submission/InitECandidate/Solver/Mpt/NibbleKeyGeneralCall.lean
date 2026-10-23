import InitECandidate.Solver.Mpt.NibbleKeyGeneral

namespace InitECandidate.Solver.Mpt.NibbleKey
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- The actual original scoped caller, for both current secure flags.
Its genuine child return supplies the real nibble tuple and complete
physical frame; no future query success or allocation is assumed. -/
theorem scoped_general_normal {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    (name : MlS) (arguments : List (ExpHOL 64)) (m flag key stp pad hash heap : BitVec 64) (length : Nat) (small : length≤32)
    (installed : Input.OriginalCode.Installed source.code) (domain : source.memaddrs=InitE.ordinaryDomain) (little : source.be=false)
    (argsRead : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=
      some [.val (.word m),.val (.word key),.val (.word (BitVec.ofNat 64 length))])
    (mapped : source.memaddrs (m+8#64)) (cell : source.memory (m+8#64)=.word flag)
    (hashCell : source.globals.lookup (ofString "mpt_hash_scratch")=some (.val (.word hash)))
    (data : Keccak256.EntryData source stp key pad hash length)
    (hashArena : AllocatedBytes.Arena hash 32) (hashBefore : hash.toNat+32≤heap.toNat)
    (inputArena : AllocatedBytes.Arena key length) (inputBefore : key.toNat+length≤heap.toNat)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (frontier : AllocatedBytes.Arena heap 0) (aligned : heap.toNat%8=0)
    (reached : Input.CallPrefix.Reaches source (.scoped name returnShape (ofString "mpt_nibble_key") arguments) target) :
    AllocatedBytes.Arena heap (nibbleLength flag length) ∧
      target.locals.lookup name=some (nibbleValue heap (nibbleLength flag length)) ∧
      (∀ other,name≠other→target.locals.lookup other=source.locals.lookup other) ∧
      TrieWalk.KeyView target.memory target.memaddrs target.be heap (nibbleLength flag length) ∧
      source.clock-target.clock≤218 ∧
      KeccakAbsorb.hashControl target=KeccakAbsorb.hashControl (PersistentAlloc.post source heap (BitVec.ofNat 64 (nibbleLength flag length))) ∧
      ∀ query : BitVec 64,Keccak256.Protected stp pad hash query→
        (query.toNat<heap.toNat ∨ heap.toNat+nibbleLength flag length≤query.toNat)→target.memory query=source.memory query := by
  cases reached with
  | «scoped» _ _ _ _ actualValues actualBody callee actualShape returned childTarget args called _funded run checked=>
    have sameValues : actualValues=[.val (.word m),.val (.word key),.val (.word (BitVec.ofNat 64 length))]:=Option.some.inj (args.symm.trans argsRead)
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
    have entryData:=Keccak256.EntryData.of_control source (callEntryStateHOLFinite source expected) stp key pad hash length rfl data
    obtain ⟨arena,answer,view,cost,frame,memory⟩:=general_normal (callEntryStateHOLFinite source expected) childTarget m flag key stp pad hash heap length small installed domain little
      mLocal keyLocal lengthLocal mapped cell hashCell entryData hashArena hashBefore inputArena inputBefore heapCell frontier aligned returned run
    refine ⟨arena,?_,?_,view,?_,frame,memory⟩
    · simp [setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,answer]
    · intro other different
      simp [setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,different]
    · change source.clock-1-childTarget.clock≤217 at cost
      change source.clock-childTarget.clock≤218
      omega

end InitECandidate.Solver.Mpt.NibbleKey

#print axioms InitECandidate.Solver.Mpt.NibbleKey.scoped_general_normal
