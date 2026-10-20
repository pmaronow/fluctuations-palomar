module

public import ComparisonActualHighOnlyFiniteWeakMatrixHistory
public import ComparisonActualHighOnlyHistoryReindex

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option autoImplicit false

namespace ActualHighOnlyOverlapMinimum
variable {m delta cl cu Az C0 Ct D Bclock c0 : ℝ} {dim : ℕ→ℕ}

theorem ActualFiniteHighOnlyMatrixHistory.comp
    {root M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1)
      m delta cl cu Az C0 Ct D Bclock}
    {q : ℕ} (H : ActualFiniteHighOnlyMatrixHistory c0 root q M)
    (phi : ℕ→ℕ) (hphi : Tendsto phi atTop atTop) :
    ActualFiniteHighOnlyMatrixHistory c0
      (fun n=>root (phi n)) q (fun n=>M (phi n)) := by
  induction H with
  | root => exact .root
  | child history x hunit hd hs hb ih =>
    exact .child ih (fun n=>x (phi n))
      (hphi.eventually hunit) (hphi.eventually hd)
      (hphi.eventually hs) (hphi.eventually hb)

theorem ActualFiniteWeakHighOnlyHistory.comp
    {root M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1)
      m delta cl cu Az C0 Ct D Bclock}
    {q : ℕ} (H : ActualFiniteWeakHighOnlyHistory c0 root q M)
    (phi : ℕ→ℕ) (hphi : Tendsto phi atTop atTop) :
    ActualFiniteWeakHighOnlyHistory c0
      (fun n=>root (phi n)) q (fun n=>M (phi n)) :=
  ⟨H.weak.comp phi hphi,H.matrix.comp phi hphi⟩

end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
