import InitECandidate.Solver.Mpt.NodeRlpBeginEncodedNormal
import InitECandidate.Solver.Input.RlpLength.BytesSizeGeneralCall
import InitECandidate.Solver.Input.RlpWrite.Access
import InitECandidate.Solver.Input.ScalarProgram
import InitECandidate.Solver.Input.ClockCostScopedReached

namespace InitECandidate.Solver.Mpt.NodeRlpBegin
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def lengthArguments : List (ExpHOL 64):=[.loadByte (localVar "cbuf"),localVar "clen"]

theorem length_arguments_exact (source : PanSemStateFiniteExact 64 Guest.HostMemory) (buffer length : BitVec 64)
    (bufferCell : source.locals.lookup (ofString "cbuf")=some (.val (.word buffer)))
    (lengthCell : source.locals.lookup (ofString "clen")=some (.val (.word length)))
    (mapped : source.memaddrs (panByteAlignHOL (width:=64) buffer)) :
    ∃ first : BitVec 64,eval source (.loadByte (.const buffer))=some (.val (.word first)) ∧ evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) lengthArguments=
      some [.val (.word first),.val (.word length)] := by
  obtain ⟨byte,loaded⟩:=Input.RlpWrite.byte_read_exists source buffer mapped
  have pointerRead : eval source (localVar "cbuf")=some (.val (.word buffer)):=by simpa only [eval,evalHOLExact,toExact,localVar] using bufferCell
  have read:=Input.Scalar.byte_read source (localVar "cbuf") buffer byte pointerRead loaded
  refine ⟨BitVec.ofNat 64 byte.toNat,Input.Scalar.byte_read source (.const buffer) buffer byte rfl loaded,?_⟩
  simp only [eval] at read
  simp [lengthArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,bufferCell,lengthCell,loaded]

theorem length_arguments (source : PanSemStateFiniteExact 64 Guest.HostMemory) (buffer length : BitVec 64)
    (bufferCell : source.locals.lookup (ofString "cbuf")=some (.val (.word buffer)))
    (lengthCell : source.locals.lookup (ofString "clen")=some (.val (.word length)))
    (mapped : source.memaddrs (panByteAlignHOL (width:=64) buffer)) :
    ∃ first : BitVec 64,evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) lengthArguments=
      some [.val (.word first),.val (.word length)] := by
  obtain ⟨first,_read,args⟩:=length_arguments_exact source buffer length bufferCell lengthCell mapped
  exact ⟨first,args⟩

/-- The actual el scope and optional leaf value consume at most23 ticks.
Only the already allocated compact buffer's first backing word is needed;
the concrete current byte is derived rather than supplied as an oracle. -/
theorem length_scope_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (node tag buffer length : BitVec 64) (limit : Nat)
    (property : BitVec 64→BitVec 64→Prop)
    (view : tag=1#64→TrieWalk.ValueView source.memory source.memaddrs node 48#64 56#64 limit property)
    (lengthFits : length.toNat+9<2^64) (valueFits : limit+9<2^64) (installed : Input.OriginalCode.Installed source.code)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node)))
    (tagCell : source.locals.lookup (ofString "k")=some (.val (.word tag)))
    (bufferCell : source.locals.lookup (ofString "cbuf")=some (.val (.word buffer)))
    (lengthCell : source.locals.lookup (ofString "clen")=some (.val (.word length)))
    (mapped : source.memaddrs (panByteAlignHOL (width:=64) buffer)) :
    source.clock-(evaluateHOLFiniteState source lengthScope).2.clock≤23 := by
  obtain ⟨first,args⟩:=length_arguments source buffer length bufferCell lengthCell mapped
  obtain ⟨callee,called,firstCell,nCell⟩:=Input.RlpLength.BytesSize.environment source.code.lookup first length (Input.OriginalRlp.rlp_bytes_encoded_len source.code installed)
  have price:=Input.RlpLength.BytesSize.body_cost (callEntryStateHOLFinite source callee) first length lengthFits firstCell nCell
    (Input.OriginalRlp.rlp_header_len source.code installed) (Input.OriginalRlp.rlp_be_len source.code installed)
  rw [path_shapes.2.2.2.2.2]
  apply Input.ClockCost.scoped_reached_current source "el" .one (ofString "rlp_bytes_encoded_len") lengthArguments _
    Input.RlpLength.BytesSize.body afterEncoded callee .one 10 12 args called price
  intro built returned run checked
  obtain ⟨encoded,_lower,_upper,_number,answer,_price,frame⟩:=Input.RlpLength.BytesSize.body_normal (callEntryStateHOLFinite source callee) built first length lengthFits firstCell nCell
    (Input.OriginalRlp.rlp_header_len source.code installed) (Input.OriginalRlp.rlp_be_len source.code installed) returned run
  let ready:=Input.CallNormal.continuationEntry source built "el" returned
  have memory : ready.memory=source.memory:=Input.LocalEffects.memory_of_erase (callEntryStateHOLFinite source callee) built frame
  have domain:=congrArg PanSemStateFiniteExact.memaddrs frame
  change ready.memaddrs=source.memaddrs at domain
  have codes : ready.code=source.code:=Input.LocalEffects.code_of_erase (callEntryStateHOLFinite source callee) built frame
  have currentView (leaf : tag=1#64) : TrieWalk.ValueView ready.memory ready.memaddrs node 48#64 56#64 limit property:=
    (view leaf).of_agreement source.memory ready.memory source.memaddrs ready.memaddrs node 48#64 56#64 limit domain (congrFun memory _) (congrFun memory _)
  have currentNode : ready.locals.lookup (ofString "node")=some (.val (.word node)):=by
    simp [ready,Input.CallNormal.continuationEntry,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,show ofString "el"≠ofString "node" from by decide,nodeCell]
  have currentTag : ready.locals.lookup (ofString "k")=some (.val (.word tag)):=by
    simp [ready,Input.CallNormal.continuationEntry,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,show ofString "el"≠ofString "k" from by decide,tagCell]
  have encodedCell : ready.locals.lookup (ofString "el")=some (.val (.word (BitVec.ofNat 64 encoded))):=by
    simp [ready,Input.CallNormal.continuationEntry,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,answer]
  exact after_encoded_cost ready node tag (BitVec.ofNat 64 encoded) limit property currentView valueFits (by rw [codes]; exact installed) currentNode currentTag encodedCell

end InitECandidate.Solver.Mpt.NodeRlpBegin

#print axioms InitECandidate.Solver.Mpt.NodeRlpBegin.length_arguments
#print axioms InitECandidate.Solver.Mpt.NodeRlpBegin.length_scope_cost

#print axioms InitECandidate.Solver.Mpt.NodeRlpBegin.length_arguments_exact
