import InitECandidate.Solver.GasBudget.DispatchSyntax

namespace InitECandidate.Solver.GasBudget.OpcodeDispatch
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Literal proof description of the unchanged dispatcher. Its equality to
Guest.guestFn_op_dispatch is checked below; the text parser is untrusted. -/
def tree : Syntax :=
  .seq
    (.branch (.lower 32)
      (.seq
        (.branch (.lower 16)
          (.seq
            (.branch (.equal 0)
              (.action (.invoke "op_stop" []))
              (.action .skip))
            (.seq
              (.branch (.equal 1)
                (.action (.invoke "op_add" []))
                (.action .skip))
              (.seq
                (.branch (.equal 2)
                  (.action (.invoke "op_mul" []))
                  (.action .skip))
                (.seq
                  (.branch (.equal 3)
                    (.action (.invoke "op_sub" []))
                    (.action .skip))
                  (.seq
                    (.branch (.equal 4)
                      (.action (.invoke "op_div" []))
                      (.action .skip))
                    (.seq
                      (.branch (.equal 5)
                        (.action (.invoke "op_sdiv" []))
                        (.action .skip))
                      (.seq
                        (.branch (.equal 6)
                          (.action (.invoke "op_mod" []))
                          (.action .skip))
                        (.seq
                          (.branch (.equal 7)
                            (.action (.invoke "op_smod" []))
                            (.action .skip))
                          (.seq
                            (.branch (.equal 8)
                              (.action (.invoke "op_addmod" []))
                              (.action .skip))
                            (.seq
                              (.branch (.equal 9)
                                (.action (.invoke "op_mulmod" []))
                                (.action .skip))
                              (.seq
                                (.branch (.equal 10)
                                  (.action (.invoke "op_exp" []))
                                  (.action .skip))
                                (.branch (.equal 11)
                                  (.action (.invoke "op_signextend" []))
                                  (.action .skip)))))))))))))
          (.seq
            (.branch (.equal 16)
              (.action (.invoke "op_lt" []))
              (.action .skip))
            (.seq
              (.branch (.equal 17)
                (.action (.invoke "op_gt" []))
                (.action .skip))
              (.seq
                (.branch (.equal 18)
                  (.action (.invoke "op_slt" []))
                  (.action .skip))
                (.seq
                  (.branch (.equal 19)
                    (.action (.invoke "op_sgt" []))
                    (.action .skip))
                  (.seq
                    (.branch (.equal 20)
                      (.action (.invoke "op_eq" []))
                      (.action .skip))
                    (.seq
                      (.branch (.equal 21)
                        (.action (.invoke "op_iszero" []))
                        (.action .skip))
                      (.seq
                        (.branch (.equal 22)
                          (.action (.invoke "op_and" []))
                          (.action .skip))
                        (.seq
                          (.branch (.equal 23)
                            (.action (.invoke "op_or" []))
                            (.action .skip))
                          (.seq
                            (.branch (.equal 24)
                              (.action (.invoke "op_xor" []))
                              (.action .skip))
                            (.seq
                              (.branch (.equal 25)
                                (.action (.invoke "op_not" []))
                                (.action .skip))
                              (.seq
                                (.branch (.equal 26)
                                  (.action (.invoke "op_byte" []))
                                  (.action .skip))
                                (.seq
                                  (.branch (.equal 27)
                                    (.action (.invoke "op_shl" []))
                                    (.action .skip))
                                  (.seq
                                    (.branch (.equal 28)
                                      (.action (.invoke "op_shr" []))
                                      (.action .skip))
                                    (.seq
                                      (.branch (.equal 29)
                                        (.action (.invoke "op_sar" []))
                                        (.action .skip))
                                      (.branch (.equal 30)
                                        (.action (.invoke "op_clz" []))
                                        (.action .skip)))))))))))))))))
        (.action .failed))
      (.action .skip))
    (.seq
      (.branch (.lower 96)
        (.seq
          (.branch (.lower 64)
            (.seq
              (.branch (.equal 32)
                (.action (.invoke "op_keccak" []))
                (.action .skip))
              (.seq
                (.branch (.equal 48)
                  (.action (.invoke "op_address" []))
                  (.action .skip))
                (.seq
                  (.branch (.equal 49)
                    (.action (.invoke "op_balance" []))
                    (.action .skip))
                  (.seq
                    (.branch (.equal 50)
                      (.action (.invoke "op_origin" []))
                      (.action .skip))
                    (.seq
                      (.branch (.equal 51)
                        (.action (.invoke "op_caller" []))
                        (.action .skip))
                      (.seq
                        (.branch (.equal 52)
                          (.action (.invoke "op_callvalue" []))
                          (.action .skip))
                        (.seq
                          (.branch (.equal 53)
                            (.action (.invoke "op_calldataload" []))
                            (.action .skip))
                          (.seq
                            (.branch (.equal 54)
                              (.action (.invoke "op_calldatasize" []))
                              (.action .skip))
                            (.seq
                              (.branch (.equal 55)
                                (.action (.invoke "op_calldatacopy" []))
                                (.action .skip))
                              (.seq
                                (.branch (.equal 56)
                                  (.action (.invoke "op_codesize" []))
                                  (.action .skip))
                                (.seq
                                  (.branch (.equal 57)
                                    (.action (.invoke "op_codecopy" []))
                                    (.action .skip))
                                  (.seq
                                    (.branch (.equal 58)
                                      (.action (.invoke "op_gasprice" []))
                                      (.action .skip))
                                    (.seq
                                      (.branch (.equal 59)
                                        (.action (.invoke "op_extcodesize" []))
                                        (.action .skip))
                                      (.seq
                                        (.branch (.equal 60)
                                          (.action (.invoke "op_extcodecopy" []))
                                          (.action .skip))
                                        (.seq
                                          (.branch (.equal 61)
                                            (.action (.invoke "op_returndatasize" []))
                                            (.action .skip))
                                          (.seq
                                            (.branch (.equal 62)
                                              (.action (.invoke "op_returndatacopy" []))
                                              (.action .skip))
                                            (.branch (.equal 63)
                                              (.action (.invoke "op_extcodehash" []))
                                              (.action .skip))))))))))))))))))
            (.seq
              (.branch (.equal 64)
                (.action (.invoke "op_blockhash" []))
                (.action .skip))
              (.seq
                (.branch (.equal 65)
                  (.action (.invoke "op_coinbase" []))
                  (.action .skip))
                (.seq
                  (.branch (.equal 66)
                    (.action (.invoke "op_timestamp" []))
                    (.action .skip))
                  (.seq
                    (.branch (.equal 67)
                      (.action (.invoke "op_number" []))
                      (.action .skip))
                    (.seq
                      (.branch (.equal 68)
                        (.action (.invoke "op_prevrandao" []))
                        (.action .skip))
                      (.seq
                        (.branch (.equal 69)
                          (.action (.invoke "op_gaslimit" []))
                          (.action .skip))
                        (.seq
                          (.branch (.equal 70)
                            (.action (.invoke "op_chainid" []))
                            (.action .skip))
                          (.seq
                            (.branch (.equal 71)
                              (.action (.invoke "op_selfbalance" []))
                              (.action .skip))
                            (.seq
                              (.branch (.equal 72)
                                (.action (.invoke "op_basefee" []))
                                (.action .skip))
                              (.seq
                                (.branch (.equal 73)
                                  (.action (.invoke "op_blobhash" []))
                                  (.action .skip))
                                (.seq
                                  (.branch (.equal 74)
                                    (.action (.invoke "op_blobbasefee" []))
                                    (.action .skip))
                                  (.seq
                                    (.branch (.equal 75)
                                      (.action (.invoke "op_slotnum" []))
                                      (.action .skip))
                                    (.seq
                                      (.branch (.equal 80)
                                        (.action (.invoke "op_pop" []))
                                        (.action .skip))
                                      (.seq
                                        (.branch (.equal 81)
                                          (.action (.invoke "op_mload" []))
                                          (.action .skip))
                                        (.seq
                                          (.branch (.equal 82)
                                            (.action (.invoke "op_mstore" []))
                                            (.action .skip))
                                          (.seq
                                            (.branch (.equal 83)
                                              (.action (.invoke "op_mstore8" []))
                                              (.action .skip))
                                            (.seq
                                              (.branch (.equal 84)
                                                (.action (.invoke "op_sload" []))
                                                (.action .skip))
                                              (.seq
                                                (.branch (.equal 85)
                                                  (.action (.invoke "op_sstore" []))
                                                  (.action .skip))
                                                (.seq
                                                  (.branch (.equal 86)
                                                    (.action (.invoke "op_jump" []))
                                                    (.action .skip))
                                                  (.seq
                                                    (.branch (.equal 87)
                                                      (.action (.invoke "op_jumpi" []))
                                                      (.action .skip))
                                                    (.seq
                                                      (.branch (.equal 88)
                                                        (.action (.invoke "op_pc" []))
                                                        (.action .skip))
                                                      (.seq
                                                        (.branch (.equal 89)
                                                          (.action (.invoke "op_msize" []))
                                                          (.action .skip))
                                                        (.seq
                                                          (.branch (.equal 90)
                                                            (.action (.invoke "op_gas" []))
                                                            (.action .skip))
                                                          (.seq
                                                            (.branch (.equal 91)
                                                              (.action (.invoke "op_jumpdest" []))
                                                              (.action .skip))
                                                            (.seq
                                                              (.branch (.equal 92)
                                                                (.action (.invoke "op_tload" []))
                                                                (.action .skip))
                                                              (.seq
                                                                (.branch (.equal 93)
                                                                  (.action (.invoke "op_tstore" []))
                                                                  (.action .skip))
                                                                (.seq
                                                                  (.branch (.equal 94)
                                                                    (.action (.invoke "op_mcopy" []))
                                                                    (.action .skip))
                                                                  (.branch (.equal 95)
                                                                    (.action (.invoke "op_push" [.const (BitVec.ofNat 64 0)]))
                                                                    (.action .skip))))))))))))))))))))))))))))))
          (.action .failed))
        (.action .skip))
      (.seq
        (.branch (.lower 160)
          (.seq
            (.branch (.lower 128)
              (.action (.invoke "op_push" [.op .sub [localVar "op", .const (BitVec.ofNat 64 95)]]))
              (.action .skip))
            (.seq
              (.branch (.lower 144)
                (.action (.invoke "op_dup" [.op .sub [localVar "op", .const (BitVec.ofNat 64 128)]]))
                (.action .skip))
              (.action (.invoke "op_swap" [.op .sub [localVar "op", .const (BitVec.ofNat 64 143)]]))))
          (.action .skip))
        (.seq
          (.branch (.lower 165)
            (.action (.invoke "op_log" [.op .sub [localVar "op", .const (BitVec.ofNat 64 160)]]))
            (.action .skip))
          (.seq
            (.branch (.equal 230)
              (.action (.invoke "op_dupn" []))
              (.action .skip))
            (.seq
              (.branch (.equal 231)
                (.action (.invoke "op_swapn" []))
                (.action .skip))
              (.seq
                (.branch (.equal 232)
                  (.action (.invoke "op_exchange" []))
                  (.action .skip))
                (.seq
                  (.branch (.equal 240)
                    (.action (.invoke "op_create" []))
                    (.action .skip))
                  (.seq
                    (.branch (.equal 241)
                      (.action (.invoke "op_call" []))
                      (.action .skip))
                    (.seq
                      (.branch (.equal 242)
                        (.action (.invoke "op_callcode" []))
                        (.action .skip))
                      (.seq
                        (.branch (.equal 243)
                          (.action (.invoke "op_return" []))
                          (.action .skip))
                        (.seq
                          (.branch (.equal 244)
                            (.action (.invoke "op_delegatecall" []))
                            (.action .skip))
                          (.seq
                            (.branch (.equal 245)
                              (.action (.invoke "op_create2" []))
                              (.action .skip))
                            (.seq
                              (.branch (.equal 250)
                                (.action (.invoke "op_staticcall" []))
                                (.action .skip))
                              (.seq
                                (.branch (.equal 253)
                                  (.action (.invoke "op_revert" []))
                                  (.action .skip))
                                (.seq
                                  (.branch (.equal 255)
                                    (.action (.invoke "op_selfdestruct" []))
                                    (.action .skip))
                                  (.seq
                                    (.action .failed)
                                    (.action .returned)))))))))))))))))

def body : ProgHOL 64 := match Guest.guestFn_op_dispatch with | .function fn => progToHOL fn.body | _ => .skip
def formals : List (MlS × ShapeHOL) := [(ofString "op", .one)]

theorem body_shape : body = tree.program := by
  simp only [body, Guest.guestFn_op_dispatch, progToHOL, expToHOL,
    List.map_cons, List.map_nil, Option.map_none, tree, Syntax.program, Action.program, Guard.expression, localVar]

theorem body_choice (source : PanSemStateFiniteExact 64 Guest.HostMemory) (op : BitVec 64)
    (opLocal : source.locals.lookup (ofString "op") = some (.val (.word op))) :
    evaluateHOLFiniteState source body = evaluateHOLFiniteState source (tree.choose op).program := by
  rw [body_shape]
  exact tree.choose_execution source op opLocal

end InitECandidate.Solver.GasBudget.OpcodeDispatch

#print axioms InitECandidate.Solver.GasBudget.OpcodeDispatch.body_shape
#print axioms InitECandidate.Solver.GasBudget.OpcodeDispatch.body_choice
