import GenerationCardinality.PredictionRegister

namespace GenerationCardinality

structure CardinalityPaperRecognition (Arena : OpenGenerationArena) where
  recognizesSM6ClosureFeed : Prop
  recognizesOpenGenerationArena : Prop
  recognizesRoleOccupancyEndpoint : Prop
  recognizesClosedGenCertIffThree : Prop
  recognizesArcHandoff : Prop
  recognizesSM6ClosureFeed_holds : recognizesSM6ClosureFeed
  recognizesOpenGenerationArena_holds : recognizesOpenGenerationArena
  recognizesRoleOccupancyEndpoint_holds : recognizesRoleOccupancyEndpoint
  recognizesClosedGenCertIffThree_holds : recognizesClosedGenCertIffThree
  recognizesArcHandoff_holds : recognizesArcHandoff

def CardinalityPaperRecognition.recognizesPaper
    (R : CardinalityPaperRecognition Arena) : Prop :=
  R.recognizesSM6ClosureFeed /\ R.recognizesOpenGenerationArena /\
  R.recognizesRoleOccupancyEndpoint /\ R.recognizesClosedGenCertIffThree /\
  R.recognizesArcHandoff

theorem generation_cardinality_paper_recognized
    (R : CardinalityPaperRecognition Arena) :
    R.recognizesPaper := by
  constructor
  · exact R.recognizesSM6ClosureFeed_holds
  constructor
  · exact R.recognizesOpenGenerationArena_holds
  constructor
  · exact R.recognizesRoleOccupancyEndpoint_holds
  constructor
  · exact R.recognizesClosedGenCertIffThree_holds
  · exact R.recognizesArcHandoff_holds

end GenerationCardinality
