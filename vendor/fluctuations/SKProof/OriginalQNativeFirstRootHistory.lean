module

public import SKProof.OriginalQNativeRootHistory

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy NativeOverlapMinimum
open scoped Topology NNReal

namespace NativeOverlapMinimum

def first_native_root_history_original_q
    {m delta cl cu Az C0 Ct D Bclock T c0 : ℝ} {dim : ℕ → ℕ}
    (P : (n : ℕ) → ActualThetaZeroOverlapMinimum (dim n+1)
      m delta cl cu Az C0 Ct D Bclock)
    (root : (n : ℕ) → NativeOverlapMinimum (dim n+1)
      m delta cl cu Az C0 Ct D Bclock)
    (hT : ∀ᶠn in atTop, (P n).data.T = T)
    (hunit : ∀ᶠn in atTop, (P n).xs ≤ 1)
    (htarget : ∀ᶠn in atTop,
      comparisonConditionalScale (P n).data.N delta
        (P n).data.E (P n).lam ≤ (P n).xs)
    (hweak : Tendsto (fun n => laplaceComparisonStrength
      (P n).data.d (P n).lam (P n).xs/(P n).xs^2)
      atTop (𝓝 0))
    (hsZero : Tendsto (fun n => (P n).data.s) atTop (𝓝 0))
    (hsCut : Tendsto (fun n => (P n).data.s/
      actualChildCutoff (dim n+1) delta c0
        (P n).data.d (P n).lam (P n).xs) atTop (𝓝 0))
    (hd : ∀ᶠn in atTop, (root n).context.d = c0*(P n).xs)
    (hE : ∀ᶠn in atTop,
      (root n).context.E = actualChildErrorBudget
        (dim n+1) delta c0 (P n).data.d (P n).lam (P n).xs)
    (hb : ∀ᶠn in atTop, ∀u,
      (root n).b u = (P n).changedBare u)
    (hh : ∀ᶠn in atTop, ∀u,
      (root n).h u = (P n).changedField u)
    (hTpos : 0 < T) :
    OriginalQNativeRootHistory root T c0 where
  wall := P
  root := root
  history := .root
  hTemp := hT
  hunit := hunit
  htarget := htarget
  hweak := hweak
  hsZero := hsZero
  hsCut := hsCut
  hcut := by
    filter_upwards [hd,hE] with n hnd hnE
    simp only [comparisonLowerScale,NativeOverlapContext.N,
      hnd,hnE,actualChildCutoff]
    exact le_rfl
  hb := hb
  hh := hh
  hT := hTpos

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
