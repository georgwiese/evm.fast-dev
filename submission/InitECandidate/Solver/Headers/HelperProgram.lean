import InitECandidate.Solver.Headers.HelperSyntax
import InitECandidate.Solver.Headers.NumericFrame

namespace InitECandidate.Solver.Headers.Helper

def Kind.overhead : Kind→Nat | .word=>51 | .u256=>76 | _=>42
def Kind.bodyPrice (kind : Kind) (bytes : Nat) := 60*bytes+kind.overhead

end InitECandidate.Solver.Headers.Helper
