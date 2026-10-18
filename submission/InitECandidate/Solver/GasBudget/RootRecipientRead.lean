import InitECandidate.Solver.PanFieldStores
import Guest.Model

namespace InitECandidate.Solver.GasBudget.RootMessage
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- One actual transaction recipient field before the fresh message. -/
structure TxRecipient (source : PanSemStateFiniteExact 64 Guest.HostMemory) (start : Nat) (tx recipient : BitVec 64) : Prop where
  binding : source.locals.lookup (ofString "tx") = some (.val (.word tx))
  mapped : source.memaddrs (tx + 152#64)
  word : source.memory (tx + 152#64) = .word recipient
  earlier : (tx + 152#64).toNat < start

def CopiesRecipient (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (start : Nat) : Prop :=
  ∀ tx recipient, TxRecipient source start tx recipient → target.memory (BitVec.ofNat 64 start + 24#64) = .word recipient

theorem TxRecipient.of_frame {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {start : Nat} {tx recipient : BitVec 64}
    (read : TxRecipient source start tx recipient)
    (binding : target.locals.lookup (ofString "tx") = source.locals.lookup (ofString "tx"))
    (domain : target.memaddrs = source.memaddrs)
    (memory : ∀ query : BitVec 64, query.toNat < start → target.memory query = source.memory query) :
    TxRecipient target start tx recipient := by
  exact ⟨binding.trans read.binding, by rw [domain]; exact read.mapped, (memory _ read.earlier).trans read.word, read.earlier⟩

end InitECandidate.Solver.GasBudget.RootMessage

#print axioms InitECandidate.Solver.GasBudget.RootMessage.TxRecipient.of_frame
