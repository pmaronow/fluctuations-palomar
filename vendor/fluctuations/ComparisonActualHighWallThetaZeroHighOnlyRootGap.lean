module

public import ComparisonActualHighOnlyFiniteMatrixGapRoom
public import ComparisonActualHighWallThetaZeroFirstHighOnlyChild
public import ComparisonActualHighWallThetaZeroMacroscopicAllMassExclusion

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option autoImplicit false
set_option maxHeartbeats 12000000

namespace ActualThetaZeroOverlapMinimum
variable {m delta cl cu Az C0 Ct D Bclock T c0 : ℝ} {dim : ℕ → ℕ}

theorem eventually_first_high_only_root_positive_omission
    (P : (n : ℕ) → ActualThetaZeroOverlapMinimum (dim n+1)
      m delta cl cu Az C0 Ct D Bclock)
    (root : (n : ℕ) → ActualHighOnlyOverlapMinimum (dim n+1)
      m delta cl cu Az C0 Ct D Bclock)
    (hs : ∀ᶠn in atTop,(root n).data.s=(P n).data.s) :
    ∀ᶠn in atTop,0<(root n).data.s := by
  filter_upwards [hs] with n hn
  rw [hn]
  exact (P n).data.hs.1

theorem eventually_first_high_only_root_gap
    (P : (n : ℕ) → ActualThetaZeroOverlapMinimum (dim n+1)
      m delta cl cu Az C0 Ct D Bclock)
    (root : (n : ℕ) → ActualHighOnlyOverlapMinimum (dim n+1)
      m delta cl cu Az C0 Ct D Bclock)
    (hT : ∀ᶠn in atTop,(P n).data.T=T)
    (heps : ∀ᶠn in atTop,T/4≤(P n).data.epsilon)
    (hd : ∀ᶠn in atTop,(P n).data.d^2≤T/8)
    (hs : ∀ᶠn in atTop,(root n).data.s=(P n).data.s)
    (hb : ∀ᶠn in atTop,∀u,(root n).b u=(P n).changedBare u) :
    ∀ᶠn in atTop,∀u∈Ico (0:ℝ) (root n).data.s,
      (root n).b u+T/8≤(root n).b (root n).data.s := by
  filter_upwards [hT,heps,hd,hs,hb] with n hnT hnE hnD hnS hnB
  intro u hu
  have huP : u<(P n).data.s := by rw [←hnS]; exact hu.2
  have Hlow := (P n).data.theta_zero_changed_low_matrix
    (P n).lam (P n).hlam (P n).hld (P n).alpha huP
  have Hhigh := (P n).data.theta_zero_changed_high_matrix
    (P n).lam (P n).hlam (P n).hld (P n).alpha (le_refl (P n).data.s)
  change (P n).changedBare u=(P n).data.T-(P n).data.epsilon at Hlow
  change (P n).data.T-(P n).lam≤(P n).changedBare (P n).data.s at Hhigh
  rw [hnB u,hnS,hnB (P n).data.s,Hlow,hnT]
  rw [hnT] at Hhigh
  linarith only [Hhigh,hnE,hnD,(P n).hld]

theorem eventually_first_high_only_root_radius_cap
    (hc0 : 0≤c0)
    (P : (n : ℕ) → ActualThetaZeroOverlapMinimum (dim n+1)
      m delta cl cu Az C0 Ct D Bclock)
    (root : (n : ℕ) → ActualHighOnlyOverlapMinimum (dim n+1)
      m delta cl cu Az C0 Ct D Bclock)
    (hunit : ∀ᶠn in atTop,(P n).xs≤1)
    (hd : ∀ᶠn in atTop,(root n).context.d=c0*(P n).xs) :
    ∀ᶠn in atTop,(root n).context.d≤c0 := by
  filter_upwards [hunit,hd] with n hn hdn
  rw [hdn]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hn hc0

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
