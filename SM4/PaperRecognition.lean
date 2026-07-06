import SM4.PredictionRegister

namespace SM4

structure SM4PaperRecognition (Arena : CCRArena) where
  recognizesSM1ClassifierFeed : Prop
  recognizesSM2GaugeFeed : Prop
  recognizesSM3MatterFeed : Prop
  recognizesCCRArena : Prop
  recognizesPrimitiveCarrierPackage : Prop
  recognizesRegisteredStatusPackage : Prop
  recognizesRGTransport : Prop
  recognizesBSMBranchLogic : Prop
  handsOffToSM5SM6 : Prop
  recognizesSM1ClassifierFeed_holds : recognizesSM1ClassifierFeed
  recognizesSM2GaugeFeed_holds : recognizesSM2GaugeFeed
  recognizesSM3MatterFeed_holds : recognizesSM3MatterFeed
  recognizesCCRArena_holds : recognizesCCRArena
  recognizesPrimitiveCarrierPackage_holds : recognizesPrimitiveCarrierPackage
  recognizesRegisteredStatusPackage_holds : recognizesRegisteredStatusPackage
  recognizesRGTransport_holds : recognizesRGTransport
  recognizesBSMBranchLogic_holds : recognizesBSMBranchLogic
  handsOffToSM5SM6_holds : handsOffToSM5SM6

def SM4PaperRecognition.recognizesPaper (R : SM4PaperRecognition Arena) : Prop :=
  R.recognizesSM1ClassifierFeed /\ R.recognizesSM2GaugeFeed /\ R.recognizesSM3MatterFeed /\
  R.recognizesCCRArena /\ R.recognizesPrimitiveCarrierPackage /\
  R.recognizesRegisteredStatusPackage /\ R.recognizesRGTransport /\
  R.recognizesBSMBranchLogic /\ R.handsOffToSM5SM6

theorem sm4_ccr_paper_recognized
    (R : SM4PaperRecognition Arena) :
    R.recognizesPaper := by
  constructor
  · exact R.recognizesSM1ClassifierFeed_holds
  constructor
  · exact R.recognizesSM2GaugeFeed_holds
  constructor
  · exact R.recognizesSM3MatterFeed_holds
  constructor
  · exact R.recognizesCCRArena_holds
  constructor
  · exact R.recognizesPrimitiveCarrierPackage_holds
  constructor
  · exact R.recognizesRegisteredStatusPackage_holds
  constructor
  · exact R.recognizesRGTransport_holds
  constructor
  · exact R.recognizesBSMBranchLogic_holds
  · exact R.handsOffToSM5SM6_holds

end SM4
