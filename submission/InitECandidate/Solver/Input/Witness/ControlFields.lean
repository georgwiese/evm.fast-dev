import InitECandidate.Solver.Input.Witness.Environment

namespace InitECandidate.Solver.Input.Witness
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

theorem Environment.of_control (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (control : BackingLayout.control target=BackingLayout.control source) (environment : Environment source) : Environment target := by
  have domains:=congrArg (fun state=>state.memaddrs) control
  have codes:=congrArg (fun state=>state.code) control
  have shapes:=congrArg (fun state=>state.eshapes) control
  change target.memaddrs=source.memaddrs at domains
  change target.code=source.code at codes
  change target.eshapes=source.eshapes at shapes
  refine ⟨domains.trans environment.domain,?_,?_,?_,?_,?_⟩
  · rw [codes];exact environment.allocCode
  · rw [codes];exact environment.failCode
  · rw [shapes];exact environment.exceptionShape
  · rw [codes];exact environment.varCode
  · rw [codes];exact environment.code

theorem global_of_control (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (name : MlS) (value : ValueHOL 64)
    (control : BackingLayout.control target=BackingLayout.control source)
    (present : source.globals.lookup name=some value) : target.globals.lookup name=some value := by
  have globals:=congrArg (fun state=>state.globals.lookup name) control
  change target.globals.lookup name=source.globals.lookup name at globals
  exact globals.trans present

end InitECandidate.Solver.Input.Witness

#print axioms InitECandidate.Solver.Input.Witness.Environment.of_control
#print axioms InitECandidate.Solver.Input.Witness.global_of_control
