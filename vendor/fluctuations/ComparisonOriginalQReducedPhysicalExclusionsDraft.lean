module

public import ComparisonActualHighWallThetaZeroFixedTStoppingCarrierDraft

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Filter Set
open scoped Topology NNReal
set_option autoImplicit false

namespace OriginalQPhysicalReducedDraft
open OriginalQFixedTStoppingDraft

def MacroscopicRatioVanishing
    (T m cl cu Az C0 Ct D Bclock : ℝ) : Prop :=
  ∀ (dim : ℕ → ℕ) (_hdim : StrictMono dim)
    (Q : (n : ℕ) → ActualThetaZeroOverlapMinimum (dim n+1)
      m (m/10000) cl cu Az C0 Ct D Bclock),
    (∀ n, RetainedBadQ T (dim n) (Q n)) →
    ∀ eta : ℝ, 0 < eta → ∀ phi : ℕ → ℕ, StrictMono phi →
      (∀ n, eta ≤ (Q (phi n)).xs) →
      Tendsto (fun n => laplaceComparisonStrength
        (Q (phi n)).data.d (Q (phi n)).lam (Q (phi n)).xs /
        (Q (phi n)).xs^2) atTop (𝓝 0)

structure RemainingPhysicalInputs
    (T m cl cu Az C0 Ct D Bclock : ℝ) : Prop where
  hT : 1 < T
  hm : 0 < m
  hmmax : m < 1/300
  hcl : 0 < cl
  hcl1 : cl ≤ 1
  hcu1 : 1 ≤ cu
  macroWeak : ∀ (dim : ℕ → ℕ) (_hdim : StrictMono dim)
      (Q : (n : ℕ) → ActualThetaZeroOverlapMinimum (dim n+1)
        m (m/10000) cl cu Az C0 Ct D Bclock),
      (∀ n, RetainedBadQ T (dim n) (Q n)) →
      ∀ eta : ℝ, 0 < eta → ∀ phi : ℕ → ℕ, StrictMono phi →
        (∀ n, eta ≤ (Q (phi n)).xs) →
        Tendsto (fun n => laplaceComparisonStrength
          (Q (phi n)).data.d (Q (phi n)).lam (Q (phi n)).xs /
          (Q (phi n)).xs^2) atTop (𝓝 0) → False
  strong : ∀ (dim : ℕ → ℕ) (_hdim : StrictMono dim)
      (Q : (n : ℕ) → ActualThetaZeroOverlapMinimum (dim n+1)
        m (m/10000) cl cu Az C0 Ct D Bclock),
      (∀ n, RetainedBadQ T (dim n) (Q n)) →
      Tendsto (fun n => (Q n).xs) atTop (𝓝 0) →
      ∀ eta : ℝ, 0 < eta → ∀ phi : ℕ → ℕ, StrictMono phi →
        (∀ n, eta ≤ laplaceComparisonStrength
          (Q (phi n)).data.d (Q (phi n)).lam (Q (phi n)).xs /
          (Q (phi n)).xs^2) → False
  weak : ∀ (dim : ℕ → ℕ) (_hdim : StrictMono dim)
      (Q : (n : ℕ) → ActualThetaZeroOverlapMinimum (dim n+1)
        m (m/10000) cl cu Az C0 Ct D Bclock),
      (∀ n, RetainedBadQ T (dim n) (Q n)) →
      Tendsto (fun n => (Q n).xs) atTop (𝓝 0) →
      Tendsto (fun n => laplaceComparisonStrength
        (Q n).data.d (Q n).lam (Q n).xs / (Q n).xs^2)
        atTop (𝓝 0) → False

theorem physical_exclusions_of_reduced
    {T m cl cu Az C0 Ct D Bclock : ℝ}
    (hRatio : MacroscopicRatioVanishing T m cl cu Az C0 Ct D Bclock)
    (H : RemainingPhysicalInputs T m cl cu Az C0 Ct D Bclock) :
    PhysicalExclusions T m cl cu Az C0 Ct D Bclock := by
  refine {
    hT := H.hT
    hm := H.hm
    hmmax := H.hmmax
    hcl := H.hcl
    hcl1 := H.hcl1
    hcu1 := H.hcu1
    macroGate := ?_
    strong := H.strong
    weak := H.weak }
  intro dim hdim Q hQ eta heta phi hphi hxs
  exact H.macroWeak dim hdim Q hQ eta heta phi hphi hxs
    (hRatio dim hdim Q hQ eta heta phi hphi hxs)

end OriginalQPhysicalReducedDraft
end OAI.SKFluctuations.LaplaceWindowFormalization
