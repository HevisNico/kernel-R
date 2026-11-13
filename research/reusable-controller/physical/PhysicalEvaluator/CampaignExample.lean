import PhysicalEvaluator.CampaignData

/-! A concrete composition of two eligible campaign entries. Both physical
transfer premise records are still required; this file does not instantiate
them from a noiseless residual measurement or a matching observed count. -/
namespace ReusableController.PhysicalEvaluator.CampaignExample
open RecursiveLearning ReusableController.Adaptive CampaignData

theorem t6032_oracle_accurate
    (preparationPhysical : CampaignTransferPremises t6032p1)
    (practicePhysical : CampaignTransferPremises t6032p2) :
    LessonAccurate ⟨3, 4⟩
      (marginOracle (decodedCount t6032p1.readings) (decodedCount t6032p2.readings)) 0 :=
  campaign_oracle_accurate t6032p1 t6032p2 preparationPhysical practicePhysical

theorem t6032_controller_contract {P : Type}
    (preparationPhysical : CampaignTransferPremises t6032p1)
    (practicePhysical : CampaignTransferPremises t6032p2)
    (lesson : Lesson) (policies : P → Policy) (overhead deployments validationOverhead : Nat)
    (menu : PolicyMenu P) (passes : (lesson.train ⟨3, 4⟩).retained = true) :
    let fixed := certifiedEnvironment
      (t6032p1.certificate preparationPhysical).toProbeCertificate
      (t6032p2.certificate practicePhysical).toProbeCertificate
      lesson policies overhead deployments validationOverhead
    Ready ⟨3, 4⟩ (adaptAndSearch fixed menu).memory.live ∧
      referenceCost 3 4 lesson policies overhead deployments
        (adaptAndSearch fixed menu).memory.incumbent ≤
          referenceCost 3 4 lesson policies overhead deployments menu.seed :=
  campaign_controller_contract t6032p1 t6032p2 preparationPhysical practicePhysical
    lesson policies overhead deployments validationOverhead menu passes

end ReusableController.PhysicalEvaluator.CampaignExample
