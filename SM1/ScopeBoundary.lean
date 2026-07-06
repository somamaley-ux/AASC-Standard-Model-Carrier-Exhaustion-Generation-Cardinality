import SM1.PaperRecognition

namespace SM1

structure SM1ScopeBoundary where
  classifierDisciplineClosed : Prop
  noPrimitiveSkinPromotionClosed : Prop
  targetUpdateSeparationClosed : Prop
  burdenNonSurvivorClosed : Prop
  futureClaimClassifiabilityClosed : Prop
  finalSectorClosureNotClaimed : Prop
  numericalParameterClosureNotClaimed : Prop
  bsmFalsityNotClaimed : Prop
  classifierDisciplineClosed_holds : classifierDisciplineClosed
  noPrimitiveSkinPromotionClosed_holds : noPrimitiveSkinPromotionClosed
  targetUpdateSeparationClosed_holds : targetUpdateSeparationClosed
  burdenNonSurvivorClosed_holds : burdenNonSurvivorClosed
  futureClaimClassifiabilityClosed_holds : futureClaimClassifiabilityClosed
  finalSectorClosureNotClaimed_holds : finalSectorClosureNotClaimed
  numericalParameterClosureNotClaimed_holds : numericalParameterClosureNotClaimed
  bsmFalsityNotClaimed_holds : bsmFalsityNotClaimed

def SM1ScopeBoundary.manuscriptFaithful (B : SM1ScopeBoundary) : Prop :=
  B.classifierDisciplineClosed /\
  B.noPrimitiveSkinPromotionClosed /\
  B.targetUpdateSeparationClosed /\
  B.burdenNonSurvivorClosed /\
  B.futureClaimClassifiabilityClosed /\
  B.finalSectorClosureNotClaimed /\
  B.numericalParameterClosureNotClaimed /\
  B.bsmFalsityNotClaimed

theorem sm1_scope_boundary
    (B : SM1ScopeBoundary) :
    B.manuscriptFaithful := by
  constructor
  · exact B.classifierDisciplineClosed_holds
  constructor
  · exact B.noPrimitiveSkinPromotionClosed_holds
  constructor
  · exact B.targetUpdateSeparationClosed_holds
  constructor
  · exact B.burdenNonSurvivorClosed_holds
  constructor
  · exact B.futureClaimClassifiabilityClosed_holds
  constructor
  · exact B.finalSectorClosureNotClaimed_holds
  constructor
  · exact B.numericalParameterClosureNotClaimed_holds
  · exact B.bsmFalsityNotClaimed_holds

end SM1
