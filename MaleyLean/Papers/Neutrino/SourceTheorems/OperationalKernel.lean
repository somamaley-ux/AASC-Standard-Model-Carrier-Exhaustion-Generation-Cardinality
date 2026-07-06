import MaleyLean.Papers.Neutrino.SourceTheorems.Rows

namespace MaleyLean

namespace Neutrino

/--
Operational UEAP/kernel theorem bundle for the neutrino branch audit.

This is the layer that turns the no-eleventh-route census into the pointwise
branch audit: the joint survivor is UEAP-legitimate, every non-current branch
has a forced UEAP failure coordinate, and the current carrier identifies the
standing ratio.
-/
structure OperationalKernelCorpusTheorems
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H) where
  audit :
    MaleyLean.Papers.ClaimStandingAndLegitimacy.ClaimAudit
      NeutrinoDraftCandidateIndex Unit
  currentPointIdentification :
    forall r : C.Ratio,
      C.inMinimalInterval r ->
        H.modular.ModularRestriction r ->
          H.spectral.spectralRestriction r ->
            H.scoto.scotoRestriction r ->
              routeCarrierDraftClass (N.carrierOf r) =
                NeutrinoDraftCandidateIndex.currentStandingRatio ->
                r = C.ratio
  jointSurvivorUEAPLegitimacy :
    forall r : C.Ratio,
      C.inMinimalInterval r ->
        H.modular.ModularRestriction r ->
          H.spectral.spectralRestriction r ->
            H.scoto.scotoRestriction r ->
              MaleyLean.Papers.ClaimStandingAndLegitimacy.SigmaLegitimacy
                audit
                (routeCarrierDraftClass (N.carrierOf r))
  kernelForcedUEAPFailure :
    forall i : NeutrinoDraftCandidateIndex,
      forall hne :
        Not (i = NeutrinoDraftCandidateIndex.currentStandingRatio),
        AASCUEAPLegitimacyFailureHolds
          audit
          i
          (defaultUEAPFailureKindForNoncurrentBranch i hne)

def OperationalPrimaryRowTheorems.asCorpusTheorems
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {N : AASCNoEleventhNeutrinoRoute C M H}
  (R : OperationalPrimaryRowTheorems C M H N) :
  OperationalKernelCorpusTheorems C M H N :=
  { audit := R.audit
    currentPointIdentification :=
      R.currentPointIdentification.proof
    jointSurvivorUEAPLegitimacy :=
      R.jointSurvivorUEAPLegitimacy.proof
    kernelForcedUEAPFailure :=
      R.kernelForcedUEAPFailure.proof }

end Neutrino

end MaleyLean
