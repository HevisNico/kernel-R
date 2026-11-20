import Gate6_1x_oneport

namespace LearnedCoincidence.MonotoneDNF.PremiseCheck.Campaign4

#eval ("Gate6_1x_oneport K0: conjunctions (layer 1), Disjunctions.check (layer 2), reachable",
  checkConjunctions cascade_1x_K0.first, cascade_1x_K0.second.check, cascade_1x_K0.reachable)
#eval ("Gate6_1x_oneport K0: checkCascadeValid, checkTrainingSeparation, checkCascadeCalibrationOneSided, checks",
  checkCascadeValid cascade_1x_K0,
  checkTrainingSeparation cascade_1x_K0 left right trace_1x_K0.observations,
  checkCascadeCalibrationOneSided cascade_1x_K0 left right trace_1x_K0.observations trace_1x_K0.scoreAt,
  checks cascade_1x_K0 trace_1x_K0)

#eval ("Gate6_1x_oneport K3: conjunctions (layer 1), Disjunctions.check (layer 2), reachable",
  checkConjunctions cascade_1x_K3.first, cascade_1x_K3.second.check, cascade_1x_K3.reachable)
#eval ("Gate6_1x_oneport K3: checkCascadeValid, checkTrainingSeparation, checkCascadeCalibrationOneSided, checks",
  checkCascadeValid cascade_1x_K3,
  checkTrainingSeparation cascade_1x_K3 left right trace_1x_K3.observations,
  checkCascadeCalibrationOneSided cascade_1x_K3 left right trace_1x_K3.observations trace_1x_K3.scoreAt,
  checks cascade_1x_K3 trace_1x_K3)

end LearnedCoincidence.MonotoneDNF.PremiseCheck.Campaign4
