import MaleyLean.Papers.FormalizationSmokeTest.PaperStatements

namespace MaleyLean
namespace Papers
namespace FormalizationSmokeTest
namespace Surface

/--
Summary theorem exposing the smoke-test paper surface.
-/
theorem SummaryStatement
    {Act : Type}
    (S : SmokeSystem Act) :
    LocallyStable S /\ NoSameActRepair S := by
  exact PaperSmokeTestCoreStatement S

end Surface
end FormalizationSmokeTest
end Papers
end MaleyLean
