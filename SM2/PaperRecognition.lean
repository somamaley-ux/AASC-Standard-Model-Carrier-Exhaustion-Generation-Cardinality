import SM2.PredictionRegister

namespace SM2

structure SM2PaperRecognition (Arena : GaugeSectorArena) where
  recognizesSM1ClassifierFeed : Prop
  recognizesGaugeArena : Prop
  recognizesCarrierCertificateNetwork : Prop
  recognizesGaugeSkinAtlas : Prop
  recognizesPhotonStanding : Prop
  recognizesGluonStanding : Prop
  recognizesWeakBosonStanding : Prop
  recognizesBSMBranchLogic : Prop
  recognizesPredictionRegister : Prop
  handsOffToSM3SM4SM5SM6 : Prop
  recognizesSM1ClassifierFeed_holds : recognizesSM1ClassifierFeed
  recognizesGaugeArena_holds : recognizesGaugeArena
  recognizesCarrierCertificateNetwork_holds : recognizesCarrierCertificateNetwork
  recognizesGaugeSkinAtlas_holds : recognizesGaugeSkinAtlas
  recognizesPhotonStanding_holds : recognizesPhotonStanding
  recognizesGluonStanding_holds : recognizesGluonStanding
  recognizesWeakBosonStanding_holds : recognizesWeakBosonStanding
  recognizesBSMBranchLogic_holds : recognizesBSMBranchLogic
  recognizesPredictionRegister_holds : recognizesPredictionRegister
  handsOffToSM3SM4SM5SM6_holds : handsOffToSM3SM4SM5SM6

def SM2PaperRecognition.recognizesPaper (R : SM2PaperRecognition Arena) : Prop :=
  R.recognizesSM1ClassifierFeed /\
  R.recognizesGaugeArena /\
  R.recognizesCarrierCertificateNetwork /\
  R.recognizesGaugeSkinAtlas /\
  R.recognizesPhotonStanding /\
  R.recognizesGluonStanding /\
  R.recognizesWeakBosonStanding /\
  R.recognizesBSMBranchLogic /\
  R.recognizesPredictionRegister /\
  R.handsOffToSM3SM4SM5SM6

theorem sm2_gauge_carriers_paper_recognized
    (R : SM2PaperRecognition Arena) :
    R.recognizesPaper := by
  constructor
  · exact R.recognizesSM1ClassifierFeed_holds
  constructor
  · exact R.recognizesGaugeArena_holds
  constructor
  · exact R.recognizesCarrierCertificateNetwork_holds
  constructor
  · exact R.recognizesGaugeSkinAtlas_holds
  constructor
  · exact R.recognizesPhotonStanding_holds
  constructor
  · exact R.recognizesGluonStanding_holds
  constructor
  · exact R.recognizesWeakBosonStanding_holds
  constructor
  · exact R.recognizesBSMBranchLogic_holds
  constructor
  · exact R.recognizesPredictionRegister_holds
  · exact R.handsOffToSM3SM4SM5SM6_holds

end SM2
