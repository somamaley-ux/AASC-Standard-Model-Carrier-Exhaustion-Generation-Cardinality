import SM1.StandingArena

namespace SM1

/-- Closed carrier certificates are the local obligations passed to sector papers. -/
structure ClosedCarrierCertificate (x : ComponentClaim Arena) where
  fixedInputs : Prop
  rolePreservation : Prop
  redescriptionInvariant : Prop
  licensingRelation : Prop
  noHiddenSelector : Prop
  fixedInputs_holds : fixedInputs
  rolePreservation_holds : rolePreservation
  redescriptionInvariant_holds : redescriptionInvariant
  licensingRelation_holds : licensingRelation
  noHiddenSelector_holds : noHiddenSelector

def CarrierAdmissionCriterion (x : ComponentClaim Arena) : Prop :=
  x.carrierCertified

theorem carrier_certificate_suffices_for_admission
    {x : ComponentClaim Arena}
    (_cert : ClosedCarrierCertificate x)
    (h : x.carrierCertified) :
    CarrierAdmissionCriterion x := h

inductive LocalClosureStatus where
  | closed
  | sectorRelative
  | burden
  | targetUpdate
  deriving DecidableEq, Repr

structure SectorClosureObligation where
  sector : SMSector
  localCarrierClosure : Prop
  closureStatus : LocalClosureStatus

end SM1
