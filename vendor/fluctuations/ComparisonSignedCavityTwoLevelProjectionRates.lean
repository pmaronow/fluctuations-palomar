module

public import ComparisonSignedCavityNativeRootVectorLaw
public import ComparisonSignedCavityTwoLevelAnchorMoments
public import ComparisonSignedCavityObservedInnovationWitness

@[expose] public section

noncomputable section
set_option maxHeartbeats 2000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal RealInnerProductSpace
namespace OAI.SKFluctuations.Cavity
open Hierarchy LaplaceWindowFormalization

def nativeTwoLevelProjectionFourth (n : ℕ) {ias sas das : List PositiveMass}
    (Ei : ClockTree (Spin n) ias) (Es : ClockTree (Spin n) sas)
    (D : ClockTree (Spin n) das) (H : Ei.Assignment → Es.Assignment → ℝ)
    (e : Ei.Slot) (s t : D.Slot) (qi qs qD : ℕ → RestCoordinate n → ℝ≥0)
    (xi xs xD : RestCoordinate n → ℝ) : ℝ :=
  D.expect (restWeight n) (restFeature n) qD (fun σ=>
    (inner ℝ (WithLp.toLp 2 (normalizedSpin n (D.atSlot σ t))-
      WithLp.toLp 2 (normalizedSpin n (D.atSlot σ s)))
      (nativeTwoLevelWeightedAnchor n Ei Es H e qi qs xi xs))^4) xD

theorem eventually_native_two_level_fourth_from_primitives
    (B ca c₀ : ℝ) (hca : 0 < ca) (hc₀ : 0 < c₀)
    {m delta : ℝ} (hgap : 2*delta < 6*m) :
    ∀ᶠn : ℕ in atTop,∀(ias sas das : List PositiveMass) (ai ast aD : ℝ)
      (hoi : MassOrdered ai ias) (hos : MassOrdered ast sas) (hoD : MassOrdered aD das)
      (Ei : ClockTree (Spin n) ias) (Es : ClockTree (Spin n) sas) (T : ClockTree (Spin n) das)
      (H : Ei.Assignment → Es.Assignment → ℝ) (e : Ei.Slot) (s t : T.Slot),s ≠ t →
      ∀(qi qs qD : ℕ → RestCoordinate n → ℝ≥0)
      (pre skip : List (GaussianStep (FeatureIndex n))) (a duration sj r W v : ℝ),
      (clockSteps das (fun j=>restFiniteVariance n (qD j))).take (T.splitIndex s t)=skip++pre →
      0 < a → 0 < duration → duration ≤ B → 0 ≤ sj → 0 < r → 0 < W → 0 < v →
      ca*v ≤ a → c₀*W^3/Real.log (n:ℝ) ≤ duration → (n:ℝ)^(-(1:ℝ)/6+m) ≤ r →
      OrderedSteps a (pre++(clockSteps das (fun j=>restFiniteVariance n (qD j))).drop (T.splitIndex s t)) →
      ∀(P : Type) [MeasurableSpace P] (μ : Measure P) [IsFiniteMeasure μ]
      (xi xs xD : P → RestCoordinate n → ℝ) (hxi : Measurable xi) (hxs : Measurable xs) (hxD : Measurable xD)
      (d : Fin pre.length → ℝ), (∀j,0 ≤ d j) → (∑j,d j=duration) →
      (∀j i,(hierarchyClocks pre j (Sum.inl i):ℝ)=d j) →
      (∫z,(Ei.fork Ei).expect (restWeight n) (restFeature n) qi (fun η=>
        |deletedOverlap n (joinSpin (Ei.atSlot η.1 e,false))
          (joinSpin (Ei.atSlot η.2 e,false))|^4) (xi z) ∂μ) ≤ sj^4 →
      (∫z,nativeTwoLevelProjectionFourth n Ei Es T H e s t qi qs qD (xi z) (xs z) (xD z) ∂μ) ≤
        (2*(n:ℝ)^(-delta)*savedWeightedExteriorScale r W v sj)^4*
          Real.sqrt (∫z,nativeExteriorForestMean Ei Es (restWeight n) (restFeature n) qi qs
            (fun η ζ=>|H η ζ|^8) (xi z) (xs z) ∂μ) := by
  filter_upwards [eventually_physical_root_vector_resampling 0 B,
    eventually_weighted_projection_coefficient (projectionLpConstant 1) ca c₀ hca hc₀ hgap,
    eventually_gt_atTop (0:ℕ)] with n hn hsav hn0
  intro ias sas das ai ast aD hoi hos hoD Ei Es T H e s t hst qi qs qD pre skip a duration sj r W v
    hprefix ha hdur hB hsj hr hW hv hmass hclock hlow hpre P _ μ _ xi xs xD hxi hxs hxD d hd hds hdc hraw
  let V : P → EuclideanSpace ℝ (Fin n):=fun z=>nativeTwoLevelWeightedAnchor n Ei Es H e qi qs (xi z) (xs z)
  have hV : Measurable V := by
    have hcont := nativeTwoLevelWeightedAnchor_continuous n Ei Es hoi hos H e qi qs
    have hmeas := hcont.measurable.comp (hxi.prodMk hxs)
    exact hmeas
  obtain ⟨R,hR,hVR⟩:=nativeTwoLevelWeightedAnchor_exists_bound n Ei Es hoi hos H e qi qs
  have hVbound z : ‖V z‖ ≤ R:=hVR (xi z) (xs z)
  let steps:=clockSteps das (fun j=>restFiniteVariance n (qD j))
  let tail:=steps.drop (T.splitIndex s t)
  have hfull : OrderedSteps aD ((skip++pre)++tail) := by
    rw [←hprefix]
    simpa only [tail,steps,List.take_append_drop] using clockSteps_ordered hoD
      (fun j=>restFiniteVariance n (qD j))
  have HP:=hn P V hV R hVbound tail pre skip a aD duration ha hdur hB hpre hfull μ
    (fun z=>restFiniteState n (xD z)) ((restFiniteState_measurable n).comp hxD) d hd hds hdc
  simp only [Nat.zero_add,show 4*1=4 by norm_num] at HP
  have HAnchor:=native_two_level_weighted_anchor_integral_moment n 1 Ei Es hoi hos H e qi qs μ xi xs hxi hxs
  simp only [Nat.mul_one] at HAnchor
  have HR:=Real.sqrt_le_sqrt hraw
  rw [show sj^4=(sj^2)^2 by ring,Real.sqrt_sq (sq_nonneg sj)] at HR
  let A:=projectionLpConstant 1*(Real.log (n:ℝ))^2/(a*Real.sqrt ((n:ℝ)*duration))
  let HM:=Real.sqrt (∫z,nativeExteriorForestMean Ei Es (restWeight n) (restFeature n) qi qs
    (fun η ζ=>|H η ζ|^8) (xi z) (xs z) ∂μ)
  have hHM : 0 ≤ HM:=Real.sqrt_nonneg _
  have hAnchor : (∫z,‖V z‖^4 ∂μ) ≤ HM*sj^2 :=
    HAnchor.trans (mul_le_mul_of_nonneg_left HR hHM)
  have hcoef:=hsav a duration r W v sj ha hdur hr hW hv hsj hmass hclock hlow
  have hcoef4:=pow_le_pow_left₀ (mul_nonneg (sq_nonneg A) hsj) hcoef 2
  have hfinal : (2*A)^4*(HM*sj^2) ≤
      (2*(n:ℝ)^(-delta)*savedWeightedExteriorScale r W v sj)^4*HM := by
    have hmul:=mul_le_mul_of_nonneg_right hcoef4 (by positivity : 0 ≤ 16*HM)
    dsimp only [A] at hmul ⊢
    convert hmul using 1 <;> ring
  unfold nativeTwoLevelProjectionFourth
  rw [native_subtree_root_vector_fourth_eq_physical_resampling n hn0 hoD T s t hst qD μ xD hxD
    V hV R hR.le hVbound,hprefix]
  apply HP.trans
  apply (mul_le_mul_of_nonneg_left hAnchor (by positivity : 0 ≤ (2*A)^4)).trans
  exact hfinal

end OAI.SKFluctuations.Cavity
