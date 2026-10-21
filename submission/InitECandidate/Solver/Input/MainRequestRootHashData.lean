import InitECandidate.Solver.Input.MainPayloadHashLayout

namespace InitECandidate.Solver.Input.Main.RequestRootHashData
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def description (input : Guest.InputBlob) (counts : Nat→BitVec 64) : RequestRootHash.Description where
  si := RequestPrefix.cursor input
  payload := PayloadHashData.description input
  blobs := inputPointer+18#64+Request.requestWords input 1
  blobCount := (Guest.GasLimit.le32 input 58-Guest.GasLimit.le32 input 22)/32
  parent := inputPointer+26#64
  requests := PayloadPrefix.finalCursor input
  requestPointer := fun kind=>(inputPointer+BitVec.ofNat 64 (DecoderCall.requestStart input))+Requests.offsetWord input (DecoderCall.requestStart input) kind.tag
  requestCount := fun kind=>(counts kind.tag).toNat

/-- The actual main decoder's SI cells and request decoder image supply
all five request-root phases' input metadata, including real request counts. -/
theorem image (input : Guest.InputBlob) (caller current : PanSemStateFiniteExact 64 Guest.HostMemory) (counts : Nat→BitVec 64)
    (actual : DecoderCall.DecoderReady input caller current) (domain : current.memaddrs=InitE.ordinaryDomain)
    (requests : Requests.Image current (inputPointer+BitVec.ofNat 64 (DecoderCall.requestStart input)) (PayloadPrefix.finalCursor input)
      (BitVec.ofNat 64 (DecoderCall.requestLength input)) (Requests.offsetWord input (DecoderCall.requestStart input)) counts) :
    (description input counts).Image current := by
  constructor
  · intro cell member
    simp only [RequestRootHash.Description.cells,description,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl|rfl|rfl
    · simpa only [description,PayloadHashData.description,BitVec.add_zero] using actual.hashes.payload
    · exact actual.hashes.hashes
    · exact actual.hashes.count
    · exact actual.hashes.parent
    · exact actual.requests.1
  · exact PayloadHashData.image input caller current actual domain
  · constructor
    intro kind
    have cells := requests.cells kind.tag (RequestsHash.tag_bound kind)
    exact ⟨cells.1,by simpa only [description,BitVec.ofNat_toNat,BitVec.setWidth_eq] using cells.2⟩

end InitECandidate.Solver.Input.Main.RequestRootHashData
#print axioms InitECandidate.Solver.Input.Main.RequestRootHashData.image
