module

public import ComparisonNativeStarActualAllOrder
public import ComparisonNativeCavityPolynomialGoodStar

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy NativeOverlapMinimum
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 4000000

def ActualNativeStarFiniteDegreeSaving
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (A : ℕ) (Craw saving : ℝ)
    (M : (n:ℕ)→NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) : Prop :=
  ∀ᶠn : ℕ in atTop,
    ∀extra : List PositiveMass,(∀u∈extra,u.val ≤ 1) →
    ∃us : List PositiveMass,(∀u∈us,u.val ≤ 1) ∧ (∀u∈extra,u∈us) ∧ (w n).star∈us ∧
      ∀ᶠj : ℕ in atTop,
        let as := finiteCutMasses us j
        let q := completedPathClock (n+1) (M n).bf (M n).hf
        let steps := sampleClockSteps q 0 as
        (physicalRawRatio (n+1) A steps 0 (M n).xs
          (Measure.pi fun i=>gaussianReal 0 (q 0 i)) id measurable_id)^2 ≤ 2*Craw ∧
        ∀l : ℕ,0 < l → l ≤ A →
          nativeRetainedCenteredMoment n l (M n).bf (M n).hf as (w n).star.val
            (orderedPathS (n+1) (M n).bf (M n).hf (w n).star.val) ≤
              (((n+1:ℕ):ℝ)^(-saving)*W n)^(2*l)

theorem actual_native_star_order_to_finite_degrees
    {m delta cl cu Az C0 Ct D Bclock Craw saving : ℝ}
    (A : ℕ) (hA : 0 < A)
    (M : (n:ℕ)→NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hW : ∀n,0 ≤ W n) (w : ℕ→ActualSlowWindowChoice)
    (H : ActualNativeStarOrderSaving (A-1) Craw saving M W w) :
    ActualNativeStarFiniteDegreeSaving A Craw saving M W w := by
  have horder : A-1+1=A := by omega
  unfold ActualNativeStarOrderSaving at H
  simp only [horder] at H
  filter_upwards [H] with n hn
  intro extra hextra
  obtain ⟨us,hus,hretain,hstar,Hj⟩ := hn extra hextra
  refine ⟨us,hus,hretain,hstar,?_⟩
  filter_upwards [Hj] with j hj
  refine ⟨hj.1,?_⟩
  intro l hl hlA
  exact nativeRetainedCenteredMoment_lower_order n l A hl hlA (M n).bf (M n).hf
    (finiteCutMasses us j) (finiteCutMasses_ordered us hus j) (w n).star.val
    (orderedPathS (n+1) (M n).bf (M n).hf (w n).star.val)
    (((n+1:ℕ):ℝ)^(-saving)*W n)
    (mul_nonneg (Real.rpow_nonneg (by positivity) _) (hW n)) hj.2

theorem exists_actual_bare_native_star_finite_degrees
    {m delta cl cu Az C0 Ct D Bclock T L Ccal : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hT : 0 < T) (hL : 0 < L) (hCcal : 1 ≤ Ccal)
    (M : (n:ℕ)→NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ)
    (hcanonical : ∀n,W n=max (M n).xs
      (Real.sqrt (laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)))
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (hb : ∀n u,(M n).b u=T) (hh : ∀n u,(M n).h u=0) :
    let saving := actualSlowWindowExponent m delta/64
    0 < saving ∧ ∃Cs : ℝ,0 < Cs ∧ ∃w : ℕ→ActualSlowWindowChoice,
      (∀ᶠn : ℕ in atTop,IsActualCalibratedSlowWindow (M n) (W n) T L Cs (w n)) ∧
      ∀A : ℕ,0 < A → ∃Craw : ℝ,0 < Craw ∧ ActualNativeStarFiniteDegreeSaving A Craw saving M W w := by
  obtain ⟨hs,Cs,hCs,w,hw,H⟩ := exists_actual_bare_native_star_all_orders
    hm hdelta hroom hcl hcu hAz hC0 hCt hT hL hCcal M W hcanonical hWlim hcompare hb hh
  refine ⟨hs,Cs,hCs,w,hw,?_⟩
  intro A hA
  obtain ⟨Craw,hCraw,Horder⟩ := H (A-1)
  refine ⟨Craw,hCraw,actual_native_star_order_to_finite_degrees A hA M W ?_ w Horder⟩
  intro n
  rw [hcanonical]
  exact (M n).hxs.le.trans (le_max_left _ _)

end OAI.SKFluctuations.LaplaceWindowFormalization
