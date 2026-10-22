import InitECandidate.Solver.Mpt.SetEmptyDispatch
import InitECandidate.Solver.Mpt.NibbleKeyCost

namespace InitECandidate.Solver.Mpt.SetTrie
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The complete original setter, inserting a nonempty payload into a
current empty unsecured trie. Actual key conversion protects the older
root word before the real insertion call. All failed outcomes are covered;
no future allocation success, converted-key model or clock funding is
assumed. This is a source call/loop bound, not target instruction work. -/
theorem empty_unsecured_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (m key heap pointer size : BitVec 64) (length : Nat) (small : length≤32)
    (installed : Input.OriginalCode.Installed source.code)
    (domain : source.memaddrs=InitE.ordinaryDomain) (little : source.be=false)
    (mCell : source.locals.lookup (ofString "m")=some (.val (.word m)))
    (keyCell : source.locals.lookup (ofString "key")=some (.val (.word key)))
    (lengthCell : source.locals.lookup (ofString "klen")=some (.val (.word (BitVec.ofNat 64 length))))
    (pointerCell : source.locals.lookup (ofString "vptr")=some (.val (.word pointer)))
    (sizeCell : source.locals.lookup (ofString "vlen")=some (.val (.word size)))
    (pointerActive : pointer≠0#64) (sizeActive : size≠0#64)
    (rootMapped : source.memaddrs m) (emptyRoot : source.memory m=.word 0#64) (older : m.toNat<heap.toNat)
    (securedMapped : source.memaddrs (m+8#64)) (unsecured : source.memory (m+8#64)=.word 0#64)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (frontier : AllocatedBytes.Arena heap 0) (aligned : heap.toNat%8=0)
    (inputArena : AllocatedBytes.Arena key length) (before : key.toNat+length≤heap.toNat) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤length/4+12 := by
  have args:=key_arguments source m key length mCell keyCell lengthCell
  obtain ⟨callee,called,mLocal,keyLocal,lengthLocal⟩:=NibbleKey.environment source.code.lookup m key (BitVec.ofNat 64 length)
    (NibbleKey.original_code source.code installed)
  let entry:=callEntryStateHOLFinite source callee
  have keyPrice:=NibbleKey.unsecured_cost entry m key length (by omega) installed mLocal keyLocal lengthLocal securedMapped unsecured
  rw [body_shape]
  apply Input.ClockCost.scoped_reached_current source "nk" NibbleKey.returnShape (ofString "mpt_nibble_key") keyArguments _
    NibbleKey.body afterKey callee NibbleKey.returnShape (length/4+6) 5 args called keyPrice
  intro post returned normal checked
  obtain ⟨arena,answer,view,cost,frame,memory⟩:=NibbleKey.unsecured_normal entry post m key heap length small installed domain little
    mLocal keyLocal lengthLocal securedMapped unsecured heapCell frontier aligned inputArena before returned normal
  let ready:=Input.CallNormal.continuationEntry source post "nk" returned
  have fields:=Input.evaluation_fields entry post NibbleKey.body (some (.returned returned)) normal
  have readyCode : ready.code=source.code:=fields.2.2.2
  have readyDomain : ready.memaddrs=source.memaddrs:=fields.1
  have saved (name : MlS) (different : ofString "nk"≠name) : ready.locals.lookup name=source.locals.lookup name:=by
    simp [ready,Input.CallNormal.continuationEntry,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,different]
  have nk : ready.locals.lookup (ofString "nk")=some (.rStruct [.val (.word heap),.val (.word (BitVec.ofNat 64 (2*length)))]):=by
    simp [ready,Input.CallNormal.continuationEntry,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,answer,NibbleKey.output]
  exact after_key_empty_cost ready m heap (BitVec.ofNat 64 (2*length)) pointer size (by rw [readyCode]; exact installed)
    ((saved _ (by decide)).trans mCell) (by rw [readyDomain]; exact rootMapped)
    ((memory m (Or.inl older)).trans emptyRoot) nk
    ((saved _ (by decide)).trans pointerCell) ((saved _ (by decide)).trans sizeCell) pointerActive sizeActive

end InitECandidate.Solver.Mpt.SetTrie

#print axioms InitECandidate.Solver.Mpt.SetTrie.empty_unsecured_cost
