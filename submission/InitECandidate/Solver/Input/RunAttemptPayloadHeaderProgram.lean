import InitECandidate.Solver.Input.RunAttemptTransactionProgram
import InitECandidate.Solver.Input.PayloadHeaderEnvironment

namespace InitECandidate.Solver.Input.RunAttempt
open Flapjack Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def payloadHeaderCall : ProgHOL 64:=match afterTransactionScan with | .seq _ rest=>rest | _=>.skip
def afterPayloadHeader : ProgHOL 64:=match payloadHeaderCall with | .decCall _ _ _ _ rest=>rest | _=>.skip
def payloadHeaderArguments : List (ExpHOL 64):=[localVar "si"]

set_option maxRecDepth 100000 in
theorem payload_header_shapes :
    afterTransactionScan=.seq .skip payloadHeaderCall ∧
    payloadHeaderCall=.decCall (ofString "hdr") .one (ofString "payload_header") payloadHeaderArguments afterPayloadHeader := by
  simp only [afterTransactionScan,transactionScanTail,afterTransactionCount,afterTransactionArray,transactionDeclarations,
    afterStateInit,afterCodes,afterNodes,constructors,afterParent,afterCount,afterHeaders,headerCall,afterPayload,body,
    Guest.guestFn_run_attempt,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none,
    payloadHeaderCall,afterPayloadHeader,payloadHeaderArguments,localVar]
  trivial

end InitECandidate.Solver.Input.RunAttempt

#print axioms InitECandidate.Solver.Input.RunAttempt.payload_header_shapes
