import KernelR.HybridConstructedCadenceChainStage

/-! Transport a constructed physical cadence stage across an exact change of
its parameter function, initial snapshot and routing function. The returned
stage retains the same endpoint and every ordered local emission list. -/
namespace KernelR.Hybrid

private noncomputable def cadence_execution_cast {k θ θ' route route' s s' u}
    (e : @Execution k θ route s u) (hp : θ=θ') (hr : route=route') (hs : s=s') :
    Execution θ' route' s' u := by
  cases hp
  cases hr
  cases hs
  exact e

private theorem cadence_execution_cast_ledger {k θ θ' route route' s s' u}
    (e : @Execution k θ route s u) (hp : θ=θ') (hr : route=route') (hs : s=s') :
    (cadence_execution_cast e hp hr hs).ledger=e.ledger := by
  cases hp
  cases hr
  cases hs
  rfl

private noncomputable def cadence_cell_cast {parameter parameter' s T}
    (c : FiniteCausalCell parameter s T) (hp : parameter=parameter') :
    FiniteCausalCell parameter' s T := by
  cases hp
  exact c

private theorem cadence_cell_cast_final {parameter parameter' s T}
    (c : FiniteCausalCell parameter s T) (hp : parameter=parameter') :
    (cadence_cell_cast c hp).final=c.final := by cases hp; rfl

private theorem cadence_cell_cast_times {parameter parameter' s T}
    (c : FiniteCausalCell parameter s T) (hp : parameter=parameter') :
    (cadence_cell_cast c hp).execution.emissionTimes 0=c.execution.emissionTimes 0 := by
  cases hp
  rfl

namespace FiniteCausalChainStage
variable {d d' : FiniteCausalChainData} {T : ℝ} {depth : ℕ}

noncomputable def transport (c : FiniteCausalChainStage d T depth)
    (hp : d.parameters depth=d'.parameters depth)
    (hr : d.route depth=d'.route depth) (hs : d.source depth=d'.source depth) :
    FiniteCausalChainStage d' T depth := by
  let execution := cadence_execution_cast c.execution hp hr hs
  have hledger : execution.ledger=c.execution.ledger := cadence_execution_cast_ledger _ hp hr hs
  have htimes (i : Fin (depth+1)) : execution.emissionTimes i=c.execution.emissionTimes i := by
    simp only [Execution.emissionTimes,hledger]
  refine {
    final:=c.final,execution:=execution,complete:=?_,ready:=c.ready,charge:=c.charge
    raw_none:=c.raw_none,pending:=c.pending,physical:=?_,raw_valid:=c.raw_valid
    cells:=fun i => ⟨(c.cells i).1,cadence_cell_cast (c.cells i).2 (congrFun hp i)⟩
    emission_times:=?_,cell_values:=?_
  }
  · simpa only [CompleteThrough,hr] using c.complete
  · simpa only [hp] using c.physical
  · intro i
    change execution.emissionTimes i=(cadence_cell_cast (c.cells i).2 (congrFun hp i)).execution.emissionTimes 0
    rw [htimes,cadence_cell_cast_times]
    exact c.emission_times i
  · intro i
    change c.final.x i=(cadence_cell_cast (c.cells i).2 (congrFun hp i)).final.x 0
    rw [cadence_cell_cast_final]
    exact c.cell_values i

theorem transport_final (c : FiniteCausalChainStage d T depth)
    (hp : d.parameters depth=d'.parameters depth)
    (hr : d.route depth=d'.route depth) (hs : d.source depth=d'.source depth) :
    (c.transport hp hr hs).final=c.final := rfl

theorem transport_times (c : FiniteCausalChainStage d T depth)
    (hp : d.parameters depth=d'.parameters depth)
    (hr : d.route depth=d'.route depth) (hs : d.source depth=d'.source depth)
    (i : Fin (depth+1)) :
    (c.transport hp hr hs).execution.emissionTimes i=c.execution.emissionTimes i := by
  change (cadence_execution_cast c.execution hp hr hs).emissionTimes i=c.execution.emissionTimes i
  simp only [Execution.emissionTimes,cadence_execution_cast_ledger]

end FiniteCausalChainStage

namespace ConstructedCadenceChainStage
variable {d d' : FiniteCausalChainData} {K depth m L : ℕ} {T J : ℝ}

noncomputable def reindex {m' L' : ℕ} {J' : ℝ}
    (c : ConstructedCadenceChainStage d K T depth m L J)
    (hm : m=m') (hL : L=L') (hJ : J=J') :
    ConstructedCadenceChainStage d K T depth m' L' J' := by
  cases hm
  cases hL
  cases hJ
  exact c

theorem reindex_stage {m' L' : ℕ} {J' : ℝ}
    (c : ConstructedCadenceChainStage d K T depth m L J)
    (hm : m=m') (hL : L=L') (hJ : J=J') :
    (c.reindex hm hL hJ).stage=c.stage := by
  cases hm
  cases hL
  cases hJ
  rfl

noncomputable def transport (c : ConstructedCadenceChainStage d K T depth m L J)
    (hp : d.parameters depth=d'.parameters depth)
    (hr : d.route depth=d'.route depth) (hs : d.source depth=d'.source depth) :
    ConstructedCadenceChainStage d' K T depth m L J where
  stage:=c.stage.transport hp hr hs
  packet:=c.packet
  calendar:=(c.stage.transport_times hp hr hs 0).trans c.calendar
  envelope:=c.envelope
  counts:=fun i => by rw [c.stage.transport_times hp hr hs i]; exact c.counts i
  gain_target:=fun i => by
    change c.stage.final.x i _=(d'.source depth).x i _+_
    rw [←hs]
    exact c.gain_target i
  gain_other:=fun i p h => by
    change c.stage.final.x i _=(d'.source depth).x i _
    rw [←hs]
    exact c.gain_other i p h
  recovery:=fun i => by
    change c.stage.final.x i .b=(d'.source depth).x i .b+1/5
    rw [←hs]
    exact c.recovery i

theorem transport_times (c : ConstructedCadenceChainStage d K T depth m L J)
    (hp : d.parameters depth=d'.parameters depth)
    (hr : d.route depth=d'.route depth) (hs : d.source depth=d'.source depth)
    (i : Fin (depth+1)) :
    (c.transport hp hr hs).stage.execution.emissionTimes i=c.stage.execution.emissionTimes i :=
  c.stage.transport_times hp hr hs i

end ConstructedCadenceChainStage
end KernelR.Hybrid
