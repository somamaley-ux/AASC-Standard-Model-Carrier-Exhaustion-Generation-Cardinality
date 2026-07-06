import SM6.PredictionRegister

namespace SM6

structure SM6PaperRecognition (Arena : StandardModelCarrierArena) where
  recognizesSM1ClassifierFeed : Prop
  recognizesSM2GaugeFeed : Prop
  recognizesSM3MatterFeed : Prop
  recognizesSM4CCRFeed : Prop
  recognizesSM5FlavorFeed : Prop
  recognizesGlobalCarrierArena : Prop
  recognizesConstructorPartition : Prop
  recognizesHostileBranchClosure : Prop
  recognizesFinalCarrierExhaustion : Prop
  recognizesSM1ClassifierFeed_holds : recognizesSM1ClassifierFeed
  recognizesSM2GaugeFeed_holds : recognizesSM2GaugeFeed
  recognizesSM3MatterFeed_holds : recognizesSM3MatterFeed
  recognizesSM4CCRFeed_holds : recognizesSM4CCRFeed
  recognizesSM5FlavorFeed_holds : recognizesSM5FlavorFeed
  recognizesGlobalCarrierArena_holds : recognizesGlobalCarrierArena
  recognizesConstructorPartition_holds : recognizesConstructorPartition
  recognizesHostileBranchClosure_holds : recognizesHostileBranchClosure
  recognizesFinalCarrierExhaustion_holds : recognizesFinalCarrierExhaustion

def SM6PaperRecognition.recognizesPaper (R : SM6PaperRecognition Arena) : Prop :=
  R.recognizesSM1ClassifierFeed /\ R.recognizesSM2GaugeFeed /\ R.recognizesSM3MatterFeed /\
  R.recognizesSM4CCRFeed /\ R.recognizesSM5FlavorFeed /\ R.recognizesGlobalCarrierArena /\
  R.recognizesConstructorPartition /\ R.recognizesHostileBranchClosure /\
  R.recognizesFinalCarrierExhaustion

theorem sm6_carrier_exhaustion_paper_recognized
    (R : SM6PaperRecognition Arena) :
    R.recognizesPaper := by
  constructor
  · exact R.recognizesSM1ClassifierFeed_holds
  constructor
  · exact R.recognizesSM2GaugeFeed_holds
  constructor
  · exact R.recognizesSM3MatterFeed_holds
  constructor
  · exact R.recognizesSM4CCRFeed_holds
  constructor
  · exact R.recognizesSM5FlavorFeed_holds
  constructor
  · exact R.recognizesGlobalCarrierArena_holds
  constructor
  · exact R.recognizesConstructorPartition_holds
  constructor
  · exact R.recognizesHostileBranchClosure_holds
  · exact R.recognizesFinalCarrierExhaustion_holds

end SM6
