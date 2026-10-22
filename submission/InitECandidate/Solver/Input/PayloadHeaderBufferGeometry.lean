import InitECandidate.Solver.Input.PayloadHeaderCompleted

namespace InitECandidate.Solver.Input.PayloadHeader
open Flapjack PanSemStateFiniteExact WitnessRadix

private theorem rounded_number (pointer amount : BitVec 64) (aligned : pointer.toNat%8=0) (multiple : amount.toNat%8=0)
    (room : pointer.toNat+amount.toNat≤33806089496) :
    (PersistentAlloc.rounded pointer amount).toNat=pointer.toNat+amount.toNat := by
  rw [PersistentAlloc.rounded_nat pointer amount (by omega)]
  have sumAligned : (pointer.toNat+amount.toNat)%8=0:=by omega
  omega

structure BufferNumbers (heap : BitVec 64) : Prop where
  ommer : (ommerBase heap).toNat=heap.toNat+248
  temporary : (temporaryBase heap).toNat=heap.toNat+280
  transactions : (afterOmmerHeap heap).toNat=heap.toNat+288
  nonce : (zeroBase heap).toNat=heap.toNat+320
  withdrawals : (withdrawalBase heap).toNat=heap.toNat+328
  requests : (requestsBase heap).toNat=heap.toNat+360
  balance : (balanceBase heap).toNat=heap.toNat+392
  frontier : (headerFrontier heap).toNat=heap.toNat+424

/-- The eight original allocations reserve exactly424bytes. All natural
equalities follow from their real derived rooms and alignments. -/
theorem HeaderBuffers.numbers (heap : BitVec 64) (buffers : HeaderBuffers heap) : BufferNumbers heap := by
  have headerAligned:=buffers.ommer.headerAligned
  have ommer:=rounded_number heap 248#64 headerAligned (by decide) buffers.ommer.headerArena.upper
  change (ommerBase heap).toNat=heap.toNat+248 at ommer
  have temporary:=rounded_number (ommerBase heap) 32#64 buffers.ommer.ommerAligned (by decide) buffers.ommer.ommerArena.upper
  change (temporaryBase heap).toNat=(ommerBase heap).toNat+32 at temporary
  have transactions:=rounded_number (temporaryBase heap) 8#64 buffers.ommer.temporaryAligned (by decide) buffers.ommer.temporaryArena.upper
  change (afterOmmerHeap heap).toNat=(temporaryBase heap).toNat+8 at transactions
  have transactionAligned : (afterOmmerHeap heap).toNat%8=0:=by omega
  have nonce:=rounded_number (afterOmmerHeap heap) 32#64 transactionAligned (by decide) buffers.transactions.upper
  change (zeroBase heap).toNat=(afterOmmerHeap heap).toNat+32 at nonce
  have nonceAligned : (zeroBase heap).toNat%8=0:=by omega
  have withdrawals:=rounded_number (zeroBase heap) 8#64 nonceAligned (by decide) buffers.nonce.upper
  change (withdrawalBase heap).toNat=(zeroBase heap).toNat+8 at withdrawals
  have withdrawalAligned : (withdrawalBase heap).toNat%8=0:=by omega
  have requests:=rounded_number (withdrawalBase heap) 32#64 withdrawalAligned (by decide) buffers.withdrawals.upper
  change (requestsBase heap).toNat=(withdrawalBase heap).toNat+32 at requests
  have requestsAligned : (requestsBase heap).toNat%8=0:=by omega
  have balance:=rounded_number (requestsBase heap) 32#64 requestsAligned (by decide) buffers.requests.upper
  change (balanceBase heap).toNat=(requestsBase heap).toNat+32 at balance
  have balanceAligned : (balanceBase heap).toNat%8=0:=by omega
  have frontier:=rounded_number (balanceBase heap) 32#64 balanceAligned (by decide) buffers.balance.upper
  change (headerFrontier heap).toNat=(balanceBase heap).toNat+32 at frontier
  exact ⟨ommer,by omega,by omega,by omega,by omega,by omega,by omega,by omega⟩

end InitECandidate.Solver.Input.PayloadHeader

#print axioms InitECandidate.Solver.Input.PayloadHeader.HeaderBuffers.numbers
