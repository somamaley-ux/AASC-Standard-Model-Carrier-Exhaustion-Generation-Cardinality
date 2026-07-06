import SM5.PredictionRegister

namespace SM5

structure SM5PaperRecognition (Arena : FlavorArena) where
  recognizesSM1ClassifierFeed : Prop
  recognizesSM2GaugeFeed : Prop
  recognizesSM3MatterFeed : Prop
  recognizesSM4CCRFeed : Prop
  recognizesFlavorArena : Prop
  recognizesPrimitiveFlavorPackage : Prop
  recognizesRegisteredFlavorPackage : Prop
  recognizesGenerationGovernance : Prop
  recognizesBSMBranchLogic : Prop
  handsOffOpenGenerationCardinalityEndpoint : Prop
  recognizesSM1ClassifierFeed_holds : recognizesSM1ClassifierFeed
  recognizesSM2GaugeFeed_holds : recognizesSM2GaugeFeed
  recognizesSM3MatterFeed_holds : recognizesSM3MatterFeed
  recognizesSM4CCRFeed_holds : recognizesSM4CCRFeed
  recognizesFlavorArena_holds : recognizesFlavorArena
  recognizesPrimitiveFlavorPackage_holds : recognizesPrimitiveFlavorPackage
  recognizesRegisteredFlavorPackage_holds : recognizesRegisteredFlavorPackage
  recognizesGenerationGovernance_holds : recognizesGenerationGovernance
  recognizesBSMBranchLogic_holds : recognizesBSMBranchLogic
  handsOffOpenGenerationCardinalityEndpoint_holds : handsOffOpenGenerationCardinalityEndpoint

def SM5PaperRecognition.recognizesPaper (R : SM5PaperRecognition Arena) : Prop :=
  R.recognizesSM1ClassifierFeed /\ R.recognizesSM2GaugeFeed /\ R.recognizesSM3MatterFeed /\
  R.recognizesSM4CCRFeed /\ R.recognizesFlavorArena /\ R.recognizesPrimitiveFlavorPackage /\
  R.recognizesRegisteredFlavorPackage /\ R.recognizesGenerationGovernance /\
  R.recognizesBSMBranchLogic /\ R.handsOffOpenGenerationCardinalityEndpoint

theorem sm5_flavor_paper_recognized
    (R : SM5PaperRecognition Arena) :
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
  · exact R.recognizesFlavorArena_holds
  constructor
  · exact R.recognizesPrimitiveFlavorPackage_holds
  constructor
  · exact R.recognizesRegisteredFlavorPackage_holds
  constructor
  · exact R.recognizesGenerationGovernance_holds
  constructor
  · exact R.recognizesBSMBranchLogic_holds
  · exact R.handsOffOpenGenerationCardinalityEndpoint_holds

end SM5
