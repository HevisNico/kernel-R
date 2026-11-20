import Gate6_2x_frozen

namespace LearnedCoincidence.MonotoneDNF.PremiseCheck.Campaign4

#eval ("Gate6_2x_frozen K0: conjunctions (layer 1), Disjunctions.check (layer 2), reachable",
  checkConjunctions cascade_2x_K0.first, cascade_2x_K0.second.check, cascade_2x_K0.reachable)
#eval ("Gate6_2x_frozen K0: checkCascadeValid, checkTrainingSeparation, checkCascadeCalibrationOneSided, checks",
  checkCascadeValid cascade_2x_K0,
  checkTrainingSeparation cascade_2x_K0 left right trace_2x_K0.observations,
  checkCascadeCalibrationOneSided cascade_2x_K0 left right trace_2x_K0.observations trace_2x_K0.scoreAt,
  checks cascade_2x_K0 trace_2x_K0)

#eval ("Gate6_2x_frozen K3: conjunctions (layer 1), Disjunctions.check (layer 2), reachable",
  checkConjunctions cascade_2x_K3.first, cascade_2x_K3.second.check, cascade_2x_K3.reachable)
#eval ("Gate6_2x_frozen K3: checkCascadeValid, checkTrainingSeparation, checkCascadeCalibrationOneSided, checks",
  checkCascadeValid cascade_2x_K3,
  checkTrainingSeparation cascade_2x_K3 left right trace_2x_K3.observations,
  checkCascadeCalibrationOneSided cascade_2x_K3 left right trace_2x_K3.observations trace_2x_K3.scoreAt,
  checks cascade_2x_K3 trace_2x_K3)

end LearnedCoincidence.MonotoneDNF.PremiseCheck.Campaign4
