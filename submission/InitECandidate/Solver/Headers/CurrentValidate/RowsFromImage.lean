import InitECandidate.Solver.Input.CurrentStartup.WitnessRows

namespace InitECandidate.Solver.Headers.CurrentValidate
open Validate
open Flapjack PanSemStateFiniteExact Input WitnessRadix

/-- The actual bounded witness-array image supplies every validator row.
An empty list requires no readable zero pointer or invented sentinel record. -/
theorem rows_from_image {input : Guest.InputBlob} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si array : BitVec 64} {start length boundary : Nat}
    (data : CurrentStartup.WitnessArrays.Image input source pointer si array start length boundary 72 1024 256)
    (domain : source.memaddrs=InitE.ordinaryDomain) :
    Rows source (VarList.decodedArray array length) (VarList.recordPointer input pointer start)
      (VarList.recordLength input start length (VarList.decodedCount input start length))
      (VarList.decodedCount input start length) 2701134824 boundary :=
  data.rows domain (by decide)

end InitECandidate.Solver.Headers.CurrentValidate

#print axioms InitECandidate.Solver.Headers.CurrentValidate.rows_from_image
