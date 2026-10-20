module

public import ComparisonSignedCavityExteriorForestNative
public import CavityNativeWeightedExterior

@[expose] public section

noncomputable section
set_option maxHeartbeats 8000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal RealInnerProductSpace
namespace OAI.SKFluctuations.Cavity
open Hierarchy

def nativeTwoLevelWeightedAnchor (n : ℕ) {ias sas : List PositiveMass}
    (Ei : ClockTree (Spin n) ias) (Es : ClockTree (Spin n) sas)
    (H : Ei.Assignment → Es.Assignment → ℝ) (s : Ei.Slot)
    (qi qs : ℕ → RestCoordinate n → ℝ≥0) (xi xs : RestCoordinate n → ℝ) :
    EuclideanSpace ℝ (Fin n) :=
  nativeWeightedExteriorAnchor n Ei
    (fun η=>Es.expect (restWeight n) (restFeature n) qs (H η) xs) s qi xi

theorem native_two_level_weighted_target_difference (n : ℕ)
    {ias sas : List PositiveMass} (Ei : ClockTree (Spin n) ias)
    (Es D : ClockTree (Spin n) sas) (H : Ei.Assignment → Es.Assignment → ℝ)
    (s : Ei.Slot) (qi qs : ℕ → RestCoordinate n → ℝ≥0)
    (xi xs : RestCoordinate n → ℝ) (Z : D.Assignment → ℝ)
    (old new : D.Assignment → Spin n) :
    nativeExteriorForestConditionalTest Ei Es D (restWeight n) (restFeature n) qi qs
      (fun η ζ σ=>Z σ*H η ζ*
        (deletedOverlap n (joinSpin (old σ,false)) (joinSpin (Ei.atSlot η s,false))-
          deletedOverlap n (joinSpin (new σ,false)) (joinSpin (Ei.atSlot η s,false)))) xi xs =
    D.expect (restWeight n) (restFeature n) qs (fun σ=>Z σ*inner ℝ
      (WithLp.toLp 2 (normalizedSpin n (old σ))-
        WithLp.toLp 2 (normalizedSpin n (new σ)))
      (nativeTwoLevelWeightedAnchor n Ei Es H s qi qs xi xs)) xs := by
  simp_rw [deleted_overlap_join_eq_scaled]
  unfold nativeExteriorForestConditionalTest nativeExteriorForestMean
    nativeTwoLevelWeightedAnchor nativeWeightedExteriorAnchor ClockTree.expect
  simp only [inner_smul_right,inner_sum,inner_sub_left,normalizedSpin_inner_eq_overlap,
    Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro σ _
  apply Finset.sum_congr rfl
  intro η _
  apply Finset.sum_congr rfl
  intro ζ _
  ring

theorem native_two_level_weighted_anchor_moment (n l : ℕ)
    {ias sas : List PositiveMass} (Ei : ClockTree (Spin n) ias)
    (Es : ClockTree (Spin n) sas) {ai ast : ℝ}
    (hoi : MassOrdered ai ias) (hos : MassOrdered ast sas)
    (H : Ei.Assignment → Es.Assignment → ℝ) (s : Ei.Slot)
    (qi qs : ℕ → RestCoordinate n → ℝ≥0) (xi xs : RestCoordinate n → ℝ) :
    ‖nativeTwoLevelWeightedAnchor n Ei Es H s qi qs xi xs‖^(4*l) ≤
      nativeExteriorForestMean Ei Es (restWeight n) (restFeature n) qi qs
        (fun η ζ=>|H η ζ|^(4*l)) xi xs*
      (Ei.fork Ei).expect (restWeight n) (restFeature n) qi (fun η=>
        |deletedOverlap n (joinSpin (Ei.atSlot η.1 s,false))
          (joinSpin (Ei.atSlot η.2 s,false))|^(2*l)) xi := by
  have h := native_weighted_exterior_anchor_moment n l Ei hoi
    (fun η=>Es.expect (restWeight n) (restFeature n) qs (H η) xs) s qi xi
  apply h.trans
  apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun η _=>
    mul_nonneg (((Ei.fork Ei).weight_probability (restWeight_pos n) (restFeature n) hoi qi xi).1 η)
      (by positivity))
  unfold nativeExteriorForestMean ClockTree.expect
  apply Finset.sum_le_sum
  intro η _
  apply mul_le_mul_of_nonneg_left _
    ((Ei.weight_probability (restWeight_pos n) (restFeature n) hoi qi xi).1 η)
  exact finite_weighted_mean_abs_pow_le
    (fun ζ=>Es.weight (restWeight n) (restFeature n) qs ζ xs) (H η)
    (Es.weight_probability (restWeight_pos n) (restFeature n) hos qs xs).1
    (Es.weight_probability (restWeight_pos n) (restFeature n) hos qs xs).2 (4*l)

theorem nativeExteriorForestMean_smooth_joint
    {ι S : Type} [Fintype ι] [Fintype S] [Nonempty S]
    {ias sas : List PositiveMass} {w : S → ℝ} (hw : ∀ σ,0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (Ei : ClockTree S ias) (Es : ClockTree S sas)
    {ai ast : ℝ} (hoi : MassOrdered ai ias) (hos : MassOrdered ast sas)
    (qi qs : ℕ → ι → ℝ≥0) (H : Ei.Assignment → Es.Assignment → ℝ) (r : ℕ) :
    BddSmooth r (fun z : (ι → ℝ) × (ι → ℝ)=>
      nativeExteriorForestMean Ei Es w φ qi qs H z.1 z.2) := by
  unfold nativeExteriorForestMean ClockTree.expect
  apply BddSmooth.sum Finset.univ
  intro η _
  apply ((Ei.weight_smooth hw φ hoi qi η r).compCLM
    (ContinuousLinearMap.fst ℝ (ι → ℝ) (ι → ℝ))).mul
  apply BddSmooth.sum Finset.univ
  intro ζ _
  exact (((Es.weight_smooth hw φ hos qs ζ r).compCLM
    (ContinuousLinearMap.snd ℝ (ι → ℝ) (ι → ℝ))).mul_const (H η ζ))

theorem nativeTwoLevelWeightedAnchor_continuous (n : ℕ)
    {ias sas : List PositiveMass} (Ei : ClockTree (Spin n) ias)
    (Es : ClockTree (Spin n) sas) {ai ast : ℝ}
    (hoi : MassOrdered ai ias) (hos : MassOrdered ast sas)
    (H : Ei.Assignment → Es.Assignment → ℝ) (s : Ei.Slot)
    (qi qs : ℕ → RestCoordinate n → ℝ≥0) :
    Continuous (fun z : (RestCoordinate n → ℝ) × (RestCoordinate n → ℝ)=>
      nativeTwoLevelWeightedAnchor n Ei Es H s qi qs z.1 z.2) := by
  unfold nativeTwoLevelWeightedAnchor nativeWeightedExteriorAnchor
  apply Continuous.const_smul (c := ((n:ℝ)/(n+1 : ℕ)))
  apply continuous_finsetSum
  intro η _
  have hweight := ((Ei.weight_smooth (restWeight_pos n) (restFeature n) hoi qi η 0).continuous.comp
    continuous_fst).mul
      ((Es.nativeAnchor_expect_smooth (restWeight_pos n) (restFeature n) hos qs (H η) 0).continuous.comp
        continuous_snd)
  exact hweight.smul continuous_const

theorem nativeTwoLevelWeightedAnchor_exists_bound (n : ℕ)
    {ias sas : List PositiveMass} (Ei : ClockTree (Spin n) ias)
    (Es : ClockTree (Spin n) sas) {ai ast : ℝ}
    (hoi : MassOrdered ai ias) (hos : MassOrdered ast sas)
    (H : Ei.Assignment → Es.Assignment → ℝ) (s : Ei.Slot)
    (qi qs : ℕ → RestCoordinate n → ℝ≥0) :
    ∃ R : ℝ,0 < R ∧ ∀ xi xs,
      ‖nativeTwoLevelWeightedAnchor n Ei Es H s qi qs xi xs‖ ≤ R := by
  let A := fun z : (RestCoordinate n → ℝ) × (RestCoordinate n → ℝ)=>
    nativeExteriorForestMean Ei Es (restWeight n) (restFeature n) qi qs
      (fun η ζ=>|H η ζ|^4) z.1 z.2
  let B := fun z : (RestCoordinate n → ℝ) × (RestCoordinate n → ℝ)=>
    (Ei.fork Ei).expect (restWeight n) (restFeature n) qi (fun η=>
      |deletedOverlap n (joinSpin (Ei.atSlot η.1 s,false))
        (joinSpin (Ei.atSlot η.2 s,false))|^2) z.1
  have hAs : BddSmooth 0 A := nativeExteriorForestMean_smooth_joint
    (restWeight_pos n) (restFeature n) Ei Es hoi hos qi qs (fun η ζ=>|H η ζ|^4) 0
  have hBs : BddSmooth 0 B :=
    ((Ei.fork Ei).nativeAnchor_expect_smooth (restWeight_pos n) (restFeature n) hoi qi (fun η=>
      |deletedOverlap n (joinSpin (Ei.atSlot η.1 s,false))
        (joinSpin (Ei.atSlot η.2 s,false))|^2) 0).compCLM
      (ContinuousLinearMap.fst ℝ (RestCoordinate n → ℝ) (RestCoordinate n → ℝ))
  obtain ⟨R,_,hR⟩ := (hAs.mul hBs).bound
  refine ⟨max 1 R,lt_of_lt_of_le zero_lt_one (le_max_left _ _),?_⟩
  intro xi xs
  have hm := native_two_level_weighted_anchor_moment n 1 Ei Es hoi hos H s qi qs xi xs
  have hr : A (xi,xs)*B (xi,xs) ≤ R := (le_abs_self _).trans
    (by simpa only [Real.norm_eq_abs,Function.comp_apply] using hR (xi,xs))
  have hfour : ‖nativeTwoLevelWeightedAnchor n Ei Es H s qi qs xi xs‖^4 ≤ max 1 R :=
    (show ‖nativeTwoLevelWeightedAnchor n Ei Es H s qi qs xi xs‖^4 ≤ R by
      simpa only [Nat.mul_one,A,B] using hm.trans hr).trans (le_max_right _ _)
  by_cases hn : ‖nativeTwoLevelWeightedAnchor n Ei Es H s qi qs xi xs‖ ≤ 1
  · exact hn.trans (le_max_left _ _)
  · have hone : 1 ≤ ‖nativeTwoLevelWeightedAnchor n Ei Es H s qi qs xi xs‖ := le_of_not_ge hn
    have hpow := le_self_pow₀ hone (by norm_num : (4:ℕ) ≠ 0)
    exact hpow.trans hfour

end OAI.SKFluctuations.Cavity
