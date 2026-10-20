import InitECandidate.Solver.Mpt.AccountBalanceMutationPrice
import InitECandidate.Solver.Mpt.AccountEtherCreateProgram

namespace InitECandidate.Solver.Mpt.AccountEtherMove
open AccountBalanceSet

def senderPrice (population : Nat) (destroyed found : Bool) (iterations : Nat) : Nat :=
  43 * population + 31152 + (9 + commitPrice (population + 3) (population + 3) (population + 3) destroyed found iterations)

def receiverPopulation (population iterations : Nat) : Nat := population + iterations + 5

def wholePrice (population : Nat) (destroyedSender foundSender : Bool) (senderIterations : Nat)
    (destroyedRecipient foundRecipient : Bool) (recipientIterations : Nat) : Nat :=
  senderPrice population destroyedSender foundSender senderIterations +
    AccountEtherCreate.wholePrice (receiverPopulation population senderIterations) destroyedRecipient foundRecipient recipientIterations

end InitECandidate.Solver.Mpt.AccountEtherMove
