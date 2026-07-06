import SM3.PredictionRegister

namespace SM3

structure SM3PaperRecognition (Arena : MatterSectorArena) where
  recognizesSM1ClassifierFeed : Prop
  recognizesSM2GaugeFeed : Prop
  recognizesMatterArena : Prop
  recognizesMatterCarrierNetwork : Prop
  recognizesQuarkStanding : Prop
  recognizesChargedLeptonStanding : Prop
  recognizesNeutrinoStanding : Prop
  recognizesMassResponseSlot : Prop
  recognizesBSMBranchLogic : Prop
  handsOffToSM4SM5SM6 : Prop
  recognizesSM1ClassifierFeed_holds : recognizesSM1ClassifierFeed
  recognizesSM2GaugeFeed_holds : recognizesSM2GaugeFeed
  recognizesMatterArena_holds : recognizesMatterArena
  recognizesMatterCarrierNetwork_holds : recognizesMatterCarrierNetwork
  recognizesQuarkStanding_holds : recognizesQuarkStanding
  recognizesChargedLeptonStanding_holds : recognizesChargedLeptonStanding
  recognizesNeutrinoStanding_holds : recognizesNeutrinoStanding
  recognizesMassResponseSlot_holds : recognizesMassResponseSlot
  recognizesBSMBranchLogic_holds : recognizesBSMBranchLogic
  handsOffToSM4SM5SM6_holds : handsOffToSM4SM5SM6

def SM3PaperRecognition.recognizesPaper (R : SM3PaperRecognition Arena) : Prop :=
  R.recognizesSM1ClassifierFeed /\
  R.recognizesSM2GaugeFeed /\
  R.recognizesMatterArena /\
  R.recognizesMatterCarrierNetwork /\
  R.recognizesQuarkStanding /\
  R.recognizesChargedLeptonStanding /\
  R.recognizesNeutrinoStanding /\
  R.recognizesMassResponseSlot /\
  R.recognizesBSMBranchLogic /\
  R.handsOffToSM4SM5SM6

theorem sm3_matter_carriers_paper_recognized
    (R : SM3PaperRecognition Arena) :
    R.recognizesPaper := by
  constructor
  · exact R.recognizesSM1ClassifierFeed_holds
  constructor
  · exact R.recognizesSM2GaugeFeed_holds
  constructor
  · exact R.recognizesMatterArena_holds
  constructor
  · exact R.recognizesMatterCarrierNetwork_holds
  constructor
  · exact R.recognizesQuarkStanding_holds
  constructor
  · exact R.recognizesChargedLeptonStanding_holds
  constructor
  · exact R.recognizesNeutrinoStanding_holds
  constructor
  · exact R.recognizesMassResponseSlot_holds
  constructor
  · exact R.recognizesBSMBranchLogic_holds
  · exact R.handsOffToSM4SM5SM6_holds

end SM3
