import SM1.MainTheorems

namespace SM1

inductive DependencyStatus where
  | received
  | exemplar
  | operational
  | futureDeliverable
  deriving DecidableEq, Repr

inductive DependencyFamily where
  | aascKernel
  | interfaceAMetric
  | anchorTensorSkin
  | realizedPhysicalInterior
  | gaugeRealizationPSMSR
  | standaloneSMSpine
  | higgsBridgeCarrierArc
  | higgsExtensionClassifier
  | queryPackControlMatrix
  | sectorPapersSM2ThroughSM6
  deriving DecidableEq, Repr

structure DependencyLedgerRow where
  family : DependencyFamily
  importedOutput : String
  useInSM1 : String
  status : DependencyStatus

def dependencyDiscipline (row : DependencyLedgerRow) : Prop :=
  row.status = DependencyStatus.received \/
  row.status = DependencyStatus.exemplar \/
  row.status = DependencyStatus.operational \/
  row.status = DependencyStatus.futureDeliverable

theorem dependency_rows_are_statused
    (row : DependencyLedgerRow)
    (h : dependencyDiscipline row) :
    dependencyDiscipline row := h

end SM1
