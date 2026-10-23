import InitECandidate.Solver.Mpt.NodeRlpBeginPathScope

namespace InitECandidate.Solver.Mpt.NodeRlpBegin
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open KeyToNibbles (writeMetadata)

def preparationBase (source : PanSemStateFiniteExact 64 Guest.HostMemory) (node heap : BitVec 64) :=
  if wordAt source.memory node=3#64 then source else PersistentAlloc.post source heap (allocationAmount (wordAt source.memory (node+40#64)))

/-- Derived current descriptors at the real footer entry, before its
three frame stores. The heap update and all older-word preservation come
from actual preparation, not from a supplied completed serializer result. -/
structure Prepared (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (node heap : BitVec 64) (limit : Nat) where
  buffer : BitVec 64
  length : BitVec 64
  payload : BitVec 64
  bufferCell : target.locals.lookup (ofString "cbuf")=some (.val (.word buffer))
  lengthCell : target.locals.lookup (ofString "clen")=some (.val (.word length))
  payloadCell : target.locals.lookup (ofString "payload")=some (.val (.word payload))
  branch : wordAt source.memory node=3#64→buffer=0#64 ∧ length=0#64 ∧ payload=0#64
  path : wordAt source.memory node≠3#64→buffer=heap ∧ length.toNat=(wordAt source.memory (node+40#64)).toNat/2+1 ∧
    length.toNat≤payload.toNat ∧ payload.toNat≤(wordAt source.memory (node+40#64)).toNat/2+limit+19 ∧
    heap.toNat+(wordAt source.memory (node+40#64)).toNat/2+2≤33806089496
  fields : writeMetadata target=writeMetadata (preparationBase source node heap)
  older : ∀ query : BitVec 64,query.toNat<heap.toNat→target.memory query=source.memory query

theorem path_choice_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (node heap : BitVec 64) (lower limit : Nat)
    (property : BitVec 64→BitVec 64→Prop) (data : Entry source node heap lower limit property)
    (valueFits : limit+19≤2^63) (installed : Input.OriginalCode.Installed source.code)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node)))
    (tagCell : source.locals.lookup (ofString "k")=some (.val (.word (wordAt source.memory node))))
    (bufferCell : source.locals.lookup (ofString "cbuf")=some (.val (.word 0#64)))
    (lengthCell : source.locals.lookup (ofString "clen")=some (.val (.word 0#64)))
    (payloadCell : source.locals.lookup (ofString "payload")=some (.val (.word 0#64)))
    (normal : evaluateHOLFiniteState source pathChoice=(none,target)) :
    Nonempty (Prepared source target node heap limit) := by
  have selected : evaluateHOLFiniteState source pathChoice=
      if wordAt source.memory node=3#64 then (none,source) else evaluateHOLFiniteState source pathScope:=by
    rw [body_shapes.2.2.2.2.2,evaluateHOLFiniteState_ite]
    simp [evalHOLExact,toExact,localVar,tagCell,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,evaluateHOLFiniteState_skip]
  by_cases branch : wordAt source.memory node=3#64
  · rw [if_pos branch] at selected
    have same : target=source:=congrArg Prod.snd (normal.symm.trans selected)
    rw [same]
    exact ⟨{
      buffer:=0#64,length:=0#64,payload:=0#64,bufferCell:=bufferCell,lengthCell:=lengthCell,payloadCell:=payloadCell
      branch:=by intro; exact ⟨rfl,rfl,rfl⟩
      path:=by intro other; exact (other branch).elim
      fields:=by simp only [preparationBase,if_pos branch]
      older:=by intro query older; rfl }⟩
  · rw [if_neg branch] at selected
    have pathTag : wordAt source.memory node=1#64 ∨ wordAt source.memory node=2#64:=by
      rcases tag_cases source node heap lower limit property data with leaf|extension|other
      · exact Or.inl leaf
      · exact Or.inr extension
      · exact (branch other).elim
    obtain ⟨⟨length,payload,clen,size,pay,lowerPayload,upperPayload⟩,buffer,room,frame,older⟩:=path_scope_normal source target node heap 0#64 lower limit property
      data pathTag valueFits installed nodeCell tagCell bufferCell (selected.symm.trans normal)
    exact ⟨{
      buffer:=heap,length:=length,payload:=payload,bufferCell:=buffer,lengthCell:=clen,payloadCell:=pay
      branch:=by intro other; exact (branch other).elim
      path:=by intro; exact ⟨rfl,size,by rw [size]; exact lowerPayload,upperPayload,room⟩
      fields:=by simpa only [preparationBase,if_neg branch] using frame.fields
      older:=older }⟩

end InitECandidate.Solver.Mpt.NodeRlpBegin

#print axioms InitECandidate.Solver.Mpt.NodeRlpBegin.path_choice_normal
