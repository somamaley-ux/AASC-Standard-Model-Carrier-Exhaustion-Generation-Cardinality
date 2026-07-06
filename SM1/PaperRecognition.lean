import SM1.PredictionRegister

namespace SM1

structure SM1PaperRecognition (Arena : StandardModelArena) where
  recognizesKernelStatus : Prop
  recognizesStandingArena : Prop
  recognizesCarrierAdmission : Prop
  recognizesSkinIdentification : Prop
  recognizesComponentNormalForm : Prop
  recognizesMasterClassifier : Prop
  recognizesMainTheoremFamily : Prop
  recognizesDependencyLedger : Prop
  recognizesPredictionRegister : Prop
  feedsSectorSequence : Prop
  recognizesKernelStatus_holds : recognizesKernelStatus
  recognizesStandingArena_holds : recognizesStandingArena
  recognizesCarrierAdmission_holds : recognizesCarrierAdmission
  recognizesSkinIdentification_holds : recognizesSkinIdentification
  recognizesComponentNormalForm_holds : recognizesComponentNormalForm
  recognizesMasterClassifier_holds : recognizesMasterClassifier
  recognizesMainTheoremFamily_holds : recognizesMainTheoremFamily
  recognizesDependencyLedger_holds : recognizesDependencyLedger
  recognizesPredictionRegister_holds : recognizesPredictionRegister
  feedsSectorSequence_holds : feedsSectorSequence

def SM1PaperRecognition.recognizesPaper (R : SM1PaperRecognition Arena) : Prop :=
  R.recognizesKernelStatus /\
  R.recognizesStandingArena /\
  R.recognizesCarrierAdmission /\
  R.recognizesSkinIdentification /\
  R.recognizesComponentNormalForm /\
  R.recognizesMasterClassifier /\
  R.recognizesMainTheoremFamily /\
  R.recognizesDependencyLedger /\
  R.recognizesPredictionRegister /\
  R.feedsSectorSequence

theorem sm1_primitive_carriers_paper_recognized
    (R : SM1PaperRecognition Arena) :
    R.recognizesPaper := by
  constructor
  · exact R.recognizesKernelStatus_holds
  constructor
  · exact R.recognizesStandingArena_holds
  constructor
  · exact R.recognizesCarrierAdmission_holds
  constructor
  · exact R.recognizesSkinIdentification_holds
  constructor
  · exact R.recognizesComponentNormalForm_holds
  constructor
  · exact R.recognizesMasterClassifier_holds
  constructor
  · exact R.recognizesMainTheoremFamily_holds
  constructor
  · exact R.recognizesDependencyLedger_holds
  constructor
  · exact R.recognizesPredictionRegister_holds
  · exact R.feedsSectorSequence_holds

end SM1
