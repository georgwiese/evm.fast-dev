-- Candidate radix witness routines; NOT the fixed challenge source.
-- Generated from work/agent-notes/witness-radix.pnk using the pinned parser.
-- Source SHA-256: c21fa1449df9511da94b617b5a6318489adbb46ba577651632daafb3b15ad7bc
-- Parser output is a proposed literal program, not refinement evidence.
import Flapjack.Pancake.PanLang

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace InitECandidate.Solver.WitnessRadix.RawProgram

open Flapjack

def guestGlobal_mpt_hash_scratch : Decl (BitVec 64) :=
  Decl.decl Shape.one "mpt_hash_scratch" (Exp.const (BitVec.ofNat 64 0))

def guestFn_solver_radix_index : Decl (BitVec 64) :=
  Decl.function
    { name := "solver_radix_index"
      inline := false
      exported := false
      params := [("t", Shape.one), ("n", Shape.one)]
      body :=
        (Prog.dec "keys" Shape.one (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "t"), (Exp.const (BitVec.ofNat 64 32))]))
          (Prog.dec "vals" Shape.one (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "t"), (Exp.const (BitVec.ofNat 64 40))]))
            (Prog.dec "src" Shape.one (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "t"), (Exp.const (BitVec.ofNat 64 56))]))
              (Prog.dec "dst" Shape.one (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "t"), (Exp.const (BitVec.ofNat 64 64))]))
                (Prog.dec "pending_start" Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "src"), (Exp.panOp PanOp.mul [(Exp.var VarKind.local "n"), (Exp.const (BitVec.ofNat 64 8))])])
                  (Prog.dec "pending_count" Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "dst"), (Exp.panOp PanOp.mul [(Exp.var VarKind.local "n"), (Exp.const (BitVec.ofNat 64 8))])])
                    (Prog.dec "pending_node" Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "vals"), (Exp.panOp PanOp.mul [(Exp.var VarKind.local "n"), (Exp.const (BitVec.ofNat 64 8))])])
                      (Prog.dec "node_next" Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "keys"), (Exp.panOp PanOp.mul [(Exp.var VarKind.local "n"), (Exp.const (BitVec.ofNat 64 32))])])
                        (Prog.dec "dest" Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "t"), (Exp.const (BitVec.ofNat 64 24))])
                          (Prog.dec "start" Shape.one (Exp.const (BitVec.ofNat 64 0))
                            (Prog.dec "count" Shape.one (Exp.var VarKind.local "n")
                              (Prog.dec "bit" Shape.one (Exp.const (BitVec.ofNat 64 0))
                                (Prog.dec "depth" Shape.one (Exp.const (BitVec.ofNat 64 0))
                                  (Prog.seq
                                    (Prog.ite (Exp.cmp Cmp.equal (Exp.var VarKind.local "n") (Exp.const (BitVec.ofNat 64 0)))
                                      (Prog.seq
                                        (Prog.store (Exp.var VarKind.local "dest") (Exp.const (BitVec.ofNat 64 0)))
                                        (Prog.return (Exp.const (BitVec.ofNat 64 0))))
                                      Prog.skip)
                                    (Prog.seq
                                    (Prog.while (Exp.const (BitVec.ofNat 64 1))
                                      (Prog.seq
                                        (Prog.ite (Exp.cmp Cmp.notEqual (Exp.const (BitVec.ofNat 64 0)) (Exp.op BinOp.or [(Exp.cmp Cmp.equal (Exp.var VarKind.local "count") (Exp.const (BitVec.ofNat 64 1))), (Exp.cmp Cmp.equal (Exp.var VarKind.local "bit") (Exp.const (BitVec.ofNat 64 256)))]))
                                          (Prog.dec "ordinal" Shape.one (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "src"), (Exp.panOp PanOp.mul [(Exp.op BinOp.sub [(Exp.op BinOp.add [(Exp.var VarKind.local "start"), (Exp.var VarKind.local "count")]), (Exp.const (BitVec.ofNat 64 1))]), (Exp.const (BitVec.ofNat 64 8))])]))
                                            (Prog.seq
                                              (Prog.store (Exp.var VarKind.local "dest") (Exp.op BinOp.add [(Exp.panOp PanOp.mul [(Exp.var VarKind.local "ordinal"), (Exp.const (BitVec.ofNat 64 2))]), (Exp.const (BitVec.ofNat 64 1))]))
                                              (Prog.seq
                                              (Prog.ite (Exp.cmp Cmp.equal (Exp.var VarKind.local "depth") (Exp.const (BitVec.ofNat 64 0)))
                                                (Prog.return (Exp.const (BitVec.ofNat 64 0)))
                                                Prog.skip)
                                              (Prog.seq
                                              (Prog.assign VarKind.local "depth" (Exp.op BinOp.sub [(Exp.var VarKind.local "depth"), (Exp.const (BitVec.ofNat 64 1))]))
                                              (Prog.seq
                                              (Prog.assign VarKind.local "start" (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "pending_start"), (Exp.panOp PanOp.mul [(Exp.var VarKind.local "depth"), (Exp.const (BitVec.ofNat 64 8))])])))
                                              (Prog.seq
                                              (Prog.assign VarKind.local "count" (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "pending_count"), (Exp.panOp PanOp.mul [(Exp.var VarKind.local "depth"), (Exp.const (BitVec.ofNat 64 8))])])))
                                              (Prog.dec "parent" Shape.one (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "pending_node"), (Exp.panOp PanOp.mul [(Exp.var VarKind.local "depth"), (Exp.const (BitVec.ofNat 64 8))])]))
                                                (Prog.seq
                                                  (Prog.assign VarKind.local "bit" (Exp.op BinOp.add [(Exp.load Shape.one (Exp.var VarKind.local "parent")), (Exp.const (BitVec.ofNat 64 1))]))
                                                  (Prog.seq
                                                  (Prog.assign VarKind.local "dest" (Exp.op BinOp.add [(Exp.var VarKind.local "parent"), (Exp.const (BitVec.ofNat 64 16))]))
                                                  Prog.continue)))))))))
                                          Prog.skip)
                                        (Prog.dec "zeros" Shape.one (Exp.const (BitVec.ofNat 64 0))
                                          (Prog.dec "i" Shape.one (Exp.const (BitVec.ofNat 64 0))
                                            (Prog.seq
                                              (Prog.while (Exp.cmp Cmp.lower (Exp.var VarKind.local "i") (Exp.var VarKind.local "count"))
                                                (Prog.dec "ordinal" Shape.one (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "src"), (Exp.panOp PanOp.mul [(Exp.op BinOp.add [(Exp.var VarKind.local "start"), (Exp.var VarKind.local "i")]), (Exp.const (BitVec.ofNat 64 8))])]))
                                                  (Prog.dec "digit" Shape.one (Exp.op BinOp.and [(Exp.shift Shift.lsr (Exp.loadByte (Exp.op BinOp.add [(Exp.var VarKind.local "keys"), (Exp.panOp PanOp.mul [(Exp.var VarKind.local "ordinal"), (Exp.const (BitVec.ofNat 64 32))]), (Exp.shift Shift.lsr (Exp.var VarKind.local "bit") (Exp.const (BitVec.ofNat 64 3)))])) (Exp.op BinOp.and [(Exp.var VarKind.local "bit"), (Exp.const (BitVec.ofNat 64 7))])), (Exp.const (BitVec.ofNat 64 1))])
                                                    (Prog.seq
                                                      (Prog.ite (Exp.cmp Cmp.equal (Exp.var VarKind.local "digit") (Exp.const (BitVec.ofNat 64 0)))
                                                        (Prog.assign VarKind.local "zeros" (Exp.op BinOp.add [(Exp.var VarKind.local "zeros"), (Exp.const (BitVec.ofNat 64 1))]))
                                                        Prog.skip)
                                                      (Prog.assign VarKind.local "i" (Exp.op BinOp.add [(Exp.var VarKind.local "i"), (Exp.const (BitVec.ofNat 64 1))]))))))
                                              (Prog.seq
                                              (Prog.ite (Exp.cmp Cmp.notEqual (Exp.const (BitVec.ofNat 64 0)) (Exp.op BinOp.or [(Exp.cmp Cmp.equal (Exp.var VarKind.local "zeros") (Exp.const (BitVec.ofNat 64 0))), (Exp.cmp Cmp.equal (Exp.var VarKind.local "zeros") (Exp.var VarKind.local "count"))]))
                                                (Prog.seq
                                                  (Prog.assign VarKind.local "bit" (Exp.op BinOp.add [(Exp.var VarKind.local "bit"), (Exp.const (BitVec.ofNat 64 1))]))
                                                  Prog.continue)
                                                Prog.skip)
                                              (Prog.dec "zero_cursor" Shape.one (Exp.var VarKind.local "start")
                                                (Prog.dec "one_cursor" Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "start"), (Exp.var VarKind.local "zeros")])
                                                  (Prog.seq
                                                    (Prog.assign VarKind.local "i" (Exp.const (BitVec.ofNat 64 0)))
                                                    (Prog.seq
                                                    (Prog.while (Exp.cmp Cmp.lower (Exp.var VarKind.local "i") (Exp.var VarKind.local "count"))
                                                      (Prog.dec "ordinal" Shape.one (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "src"), (Exp.panOp PanOp.mul [(Exp.op BinOp.add [(Exp.var VarKind.local "start"), (Exp.var VarKind.local "i")]), (Exp.const (BitVec.ofNat 64 8))])]))
                                                        (Prog.dec "digit" Shape.one (Exp.op BinOp.and [(Exp.shift Shift.lsr (Exp.loadByte (Exp.op BinOp.add [(Exp.var VarKind.local "keys"), (Exp.panOp PanOp.mul [(Exp.var VarKind.local "ordinal"), (Exp.const (BitVec.ofNat 64 32))]), (Exp.shift Shift.lsr (Exp.var VarKind.local "bit") (Exp.const (BitVec.ofNat 64 3)))])) (Exp.op BinOp.and [(Exp.var VarKind.local "bit"), (Exp.const (BitVec.ofNat 64 7))])), (Exp.const (BitVec.ofNat 64 1))])
                                                          (Prog.seq
                                                            (Prog.ite (Exp.cmp Cmp.equal (Exp.var VarKind.local "digit") (Exp.const (BitVec.ofNat 64 0)))
                                                              (Prog.seq
                                                                (Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "dst"), (Exp.panOp PanOp.mul [(Exp.var VarKind.local "zero_cursor"), (Exp.const (BitVec.ofNat 64 8))])]) (Exp.var VarKind.local "ordinal"))
                                                                (Prog.assign VarKind.local "zero_cursor" (Exp.op BinOp.add [(Exp.var VarKind.local "zero_cursor"), (Exp.const (BitVec.ofNat 64 1))])))
                                                              (Prog.seq
                                                                (Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "dst"), (Exp.panOp PanOp.mul [(Exp.var VarKind.local "one_cursor"), (Exp.const (BitVec.ofNat 64 8))])]) (Exp.var VarKind.local "ordinal"))
                                                                (Prog.assign VarKind.local "one_cursor" (Exp.op BinOp.add [(Exp.var VarKind.local "one_cursor"), (Exp.const (BitVec.ofNat 64 1))]))))
                                                            (Prog.assign VarKind.local "i" (Exp.op BinOp.add [(Exp.var VarKind.local "i"), (Exp.const (BitVec.ofNat 64 1))]))))))
                                                    (Prog.seq
                                                    (Prog.assign VarKind.local "i" (Exp.const (BitVec.ofNat 64 0)))
                                                    (Prog.seq
                                                    (Prog.while (Exp.cmp Cmp.lower (Exp.var VarKind.local "i") (Exp.var VarKind.local "count"))
                                                      (Prog.seq
                                                        (Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "src"), (Exp.panOp PanOp.mul [(Exp.op BinOp.add [(Exp.var VarKind.local "start"), (Exp.var VarKind.local "i")]), (Exp.const (BitVec.ofNat 64 8))])]) (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "dst"), (Exp.panOp PanOp.mul [(Exp.op BinOp.add [(Exp.var VarKind.local "start"), (Exp.var VarKind.local "i")]), (Exp.const (BitVec.ofNat 64 8))])])))
                                                        (Prog.assign VarKind.local "i" (Exp.op BinOp.add [(Exp.var VarKind.local "i"), (Exp.const (BitVec.ofNat 64 1))]))))
                                                    (Prog.dec "node" Shape.one (Exp.var VarKind.local "node_next")
                                                      (Prog.seq
                                                        (Prog.assign VarKind.local "node_next" (Exp.op BinOp.add [(Exp.var VarKind.local "node_next"), (Exp.const (BitVec.ofNat 64 24))]))
                                                        (Prog.seq
                                                        (Prog.store (Exp.var VarKind.local "node") (Exp.var VarKind.local "bit"))
                                                        (Prog.seq
                                                        (Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "node"), (Exp.const (BitVec.ofNat 64 8))]) (Exp.const (BitVec.ofNat 64 0)))
                                                        (Prog.seq
                                                        (Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "node"), (Exp.const (BitVec.ofNat 64 16))]) (Exp.const (BitVec.ofNat 64 0)))
                                                        (Prog.seq
                                                        (Prog.store (Exp.var VarKind.local "dest") (Exp.var VarKind.local "node"))
                                                        (Prog.seq
                                                        (Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "pending_start"), (Exp.panOp PanOp.mul [(Exp.var VarKind.local "depth"), (Exp.const (BitVec.ofNat 64 8))])]) (Exp.op BinOp.add [(Exp.var VarKind.local "start"), (Exp.var VarKind.local "zeros")]))
                                                        (Prog.seq
                                                        (Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "pending_count"), (Exp.panOp PanOp.mul [(Exp.var VarKind.local "depth"), (Exp.const (BitVec.ofNat 64 8))])]) (Exp.op BinOp.sub [(Exp.var VarKind.local "count"), (Exp.var VarKind.local "zeros")]))
                                                        (Prog.seq
                                                        (Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "pending_node"), (Exp.panOp PanOp.mul [(Exp.var VarKind.local "depth"), (Exp.const (BitVec.ofNat 64 8))])]) (Exp.var VarKind.local "node"))
                                                        (Prog.seq
                                                        (Prog.assign VarKind.local "depth" (Exp.op BinOp.add [(Exp.var VarKind.local "depth"), (Exp.const (BitVec.ofNat 64 1))]))
                                                        (Prog.seq
                                                        (Prog.assign VarKind.local "count" (Exp.var VarKind.local "zeros"))
                                                        (Prog.seq
                                                        (Prog.assign VarKind.local "dest" (Exp.op BinOp.add [(Exp.var VarKind.local "node"), (Exp.const (BitVec.ofNat 64 8))]))
                                                        (Prog.assign VarKind.local "bit" (Exp.op BinOp.add [(Exp.var VarKind.local "bit"), (Exp.const (BitVec.ofNat 64 1))]))))))))))))))))))))))))))
                                    (Prog.return (Exp.const (BitVec.ofNat 64 0))))))))))))))))))
      returnShape := Shape.one }

def guestFn_nodedb_build : Decl (BitVec 64) :=
  Decl.function
    { name := "nodedb_build"
      inline := false
      exported := false
      params := [("slice_arr", Shape.one), ("n", Shape.one)]
      body :=
        (Prog.dec "cap" Shape.one (Exp.const (BitVec.ofNat 64 4))
          (Prog.seq
            (Prog.while (Exp.cmp Cmp.lower (Exp.var VarKind.local "cap") (Exp.op BinOp.add [(Exp.panOp PanOp.mul [(Exp.const (BitVec.ofNat 64 2)), (Exp.var VarKind.local "n")]), (Exp.const (BitVec.ofNat 64 2))]))
              (Prog.assign VarKind.local "cap" (Exp.panOp PanOp.mul [(Exp.var VarKind.local "cap"), (Exp.const (BitVec.ofNat 64 2))])))
            (Prog.decCall "t" Shape.one "htab_new" [(Exp.const (BitVec.ofNat 64 32)), (Exp.var VarKind.local "cap")]
              (Prog.dec "keys" Shape.one (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "t"), (Exp.const (BitVec.ofNat 64 32))]))
                (Prog.dec "vals" Shape.one (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "t"), (Exp.const (BitVec.ofNat 64 40))]))
                  (Prog.dec "order" Shape.one (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "t"), (Exp.const (BitVec.ofNat 64 56))]))
                    (Prog.dec "i" Shape.one (Exp.const (BitVec.ofNat 64 0))
                      (Prog.seq
                        (Prog.while (Exp.cmp Cmp.lower (Exp.var VarKind.local "i") (Exp.var VarKind.local "n"))
                          (Prog.seq
                            (Prog.call (some (none, none)) "keccak256" [(Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "slice_arr"), (Exp.panOp PanOp.mul [(Exp.var VarKind.local "i"), (Exp.const (BitVec.ofNat 64 16))])])), (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "slice_arr"), (Exp.panOp PanOp.mul [(Exp.var VarKind.local "i"), (Exp.const (BitVec.ofNat 64 16))]), (Exp.const (BitVec.ofNat 64 8))])), (Exp.var VarKind.global "mpt_hash_scratch")])
                            (Prog.seq
                            (Prog.call (some (none, none)) "memcpy" [(Exp.op BinOp.add [(Exp.var VarKind.local "keys"), (Exp.panOp PanOp.mul [(Exp.var VarKind.local "i"), (Exp.const (BitVec.ofNat 64 32))])]), (Exp.var VarKind.global "mpt_hash_scratch"), (Exp.const (BitVec.ofNat 64 32))])
                            (Prog.seq
                            (Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "vals"), (Exp.panOp PanOp.mul [(Exp.var VarKind.local "i"), (Exp.const (BitVec.ofNat 64 8))])]) (Exp.op BinOp.add [(Exp.var VarKind.local "slice_arr"), (Exp.panOp PanOp.mul [(Exp.var VarKind.local "i"), (Exp.const (BitVec.ofNat 64 16))])]))
                            (Prog.seq
                            (Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "order"), (Exp.panOp PanOp.mul [(Exp.var VarKind.local "i"), (Exp.const (BitVec.ofNat 64 8))])]) (Exp.var VarKind.local "i"))
                            (Prog.assign VarKind.local "i" (Exp.op BinOp.add [(Exp.var VarKind.local "i"), (Exp.const (BitVec.ofNat 64 1))])))))))
                        (Prog.seq
                        (Prog.call (some (none, none)) "solver_radix_index" [(Exp.var VarKind.local "t"), (Exp.var VarKind.local "n")])
                        (Prog.return (Exp.var VarKind.local "t")))))))))))
      returnShape := Shape.one }

def guestFn_nodedb_lookup : Decl (BitVec 64) :=
  Decl.function
    { name := "nodedb_lookup"
      inline := false
      exported := false
      params := [("db", Shape.one), ("hash", Shape.one)]
      body :=
        (Prog.dec "node" Shape.one (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "db"), (Exp.const (BitVec.ofNat 64 24))]))
          (Prog.seq
            (Prog.while (Exp.cmp Cmp.notEqual (Exp.var VarKind.local "node") (Exp.const (BitVec.ofNat 64 0)))
              (Prog.seq
                (Prog.ite (Exp.cmp Cmp.notEqual (Exp.op BinOp.and [(Exp.var VarKind.local "node"), (Exp.const (BitVec.ofNat 64 1))]) (Exp.const (BitVec.ofNat 64 0)))
                  (Prog.dec "ordinal" Shape.one (Exp.shift Shift.lsr (Exp.var VarKind.local "node") (Exp.const (BitVec.ofNat 64 1)))
                    (Prog.dec "keys" Shape.one (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "db"), (Exp.const (BitVec.ofNat 64 32))]))
                      (Prog.decCall "equal" Shape.one "memeq" [(Exp.op BinOp.add [(Exp.var VarKind.local "keys"), (Exp.panOp PanOp.mul [(Exp.var VarKind.local "ordinal"), (Exp.const (BitVec.ofNat 64 32))])]), (Exp.var VarKind.local "hash"), (Exp.const (BitVec.ofNat 64 32))]
                        (Prog.seq
                          (Prog.ite (Exp.cmp Cmp.equal (Exp.var VarKind.local "equal") (Exp.const (BitVec.ofNat 64 0)))
                            (Prog.return (Exp.rStruct [(Exp.const (BitVec.ofNat 64 0)), (Exp.const (BitVec.ofNat 64 0)), (Exp.const (BitVec.ofNat 64 0))]))
                            Prog.skip)
                          (Prog.dec "record" Shape.one (Exp.load Shape.one (Exp.op BinOp.add [(Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "db"), (Exp.const (BitVec.ofNat 64 40))])), (Exp.panOp PanOp.mul [(Exp.var VarKind.local "ordinal"), (Exp.const (BitVec.ofNat 64 8))])]))
                            (Prog.return (Exp.rStruct [(Exp.const (BitVec.ofNat 64 1)), (Exp.load Shape.one (Exp.var VarKind.local "record")), (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "record"), (Exp.const (BitVec.ofNat 64 8))]))])))))))
                  Prog.skip)
                (Prog.dec "bit" Shape.one (Exp.load Shape.one (Exp.var VarKind.local "node"))
                  (Prog.dec "digit" Shape.one (Exp.op BinOp.and [(Exp.shift Shift.lsr (Exp.loadByte (Exp.op BinOp.add [(Exp.var VarKind.local "hash"), (Exp.shift Shift.lsr (Exp.var VarKind.local "bit") (Exp.const (BitVec.ofNat 64 3)))])) (Exp.op BinOp.and [(Exp.var VarKind.local "bit"), (Exp.const (BitVec.ofNat 64 7))])), (Exp.const (BitVec.ofNat 64 1))])
                    (Prog.ite (Exp.cmp Cmp.equal (Exp.var VarKind.local "digit") (Exp.const (BitVec.ofNat 64 0)))
                      (Prog.assign VarKind.local "node" (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "node"), (Exp.const (BitVec.ofNat 64 8))])))
                      (Prog.assign VarKind.local "node" (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "node"), (Exp.const (BitVec.ofNat 64 16))]))))))))
            (Prog.return (Exp.rStruct [(Exp.const (BitVec.ofNat 64 0)), (Exp.const (BitVec.ofNat 64 0)), (Exp.const (BitVec.ofNat 64 0))]))))
      returnShape := (Shape.comb [Shape.one, Shape.one, Shape.one]) }

/-- Candidate routines plus the parser-only global declaration. -/
def guestAst : List (Decl (BitVec 64)) :=
  [ guestGlobal_mpt_hash_scratch,
    guestFn_solver_radix_index,
    guestFn_nodedb_build,
    guestFn_nodedb_lookup ]

end InitECandidate.Solver.WitnessRadix.RawProgram

#print axioms InitECandidate.Solver.WitnessRadix.RawProgram.guestFn_solver_radix_index
#print axioms InitECandidate.Solver.WitnessRadix.RawProgram.guestFn_nodedb_build
#print axioms InitECandidate.Solver.WitnessRadix.RawProgram.guestFn_nodedb_lookup
