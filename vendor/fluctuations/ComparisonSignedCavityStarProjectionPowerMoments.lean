module

public import ComparisonSignedCavityActualAnchorMarginal
public import ComparisonSignedCavityRootCauchy
public import ComparisonSignedCavityActualRestStarFinalNet

@[expose] public section

noncomputable section
set_option maxHeartbeats 9000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal RealInnerProductSpace
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

def nativeStarCenteredProjection (n : ℕ) (as : List PositiveMass)
    (q : ℕ → RestCoordinate n → ℝ≥0) (center : ℝ)
    (x : RestCoordinate n → ℝ) (σ : Spin n) : ℝ :=
  singleMean (restWeight n) (restFeature n) as q
    (fun τ=>deletedOverlap n (joinSpin (σ,false)) (joinSpin (τ,false))-center) x

theorem native_star_centered_projection_eq_native (n : ℕ)
    {as : List PositiveMass} {a : ℝ} (ho : MassOrdered a as)
    (q : ℕ → RestCoordinate n → ℝ≥0) (center : ℝ)
    (x : RestCoordinate n → ℝ) (σ : Spin n) :
    nativeStarCenteredProjection n as q center x σ=
      nativeCenteredProjectedDeletedOverlap n as q x center σ := by
  unfold nativeStarCenteredProjection singleMean nativeCenteredProjectedDeletedOverlap
    nativeProjectedDeletedOverlap ClockTree.expect
  simp only [mul_sub,Finset.sum_sub_distrib,←Finset.sum_mul]
  rw [((single (S:=Spin n) as).weight_probability (restWeight_pos n) (restFeature n) ho q x).2,one_mul]

theorem native_star_centered_projection_eq_slot_expect (n : ℕ)
    {as : List PositiveMass} (T : ClockTree (Spin n) as) {a : ℝ}
    (ho : MassOrdered a as) (s : T.Slot) (q : ℕ → RestCoordinate n → ℝ≥0)
    (center : ℝ) (x : RestCoordinate n → ℝ) (σ : Spin n) :
    nativeStarCenteredProjection n as q center x σ=
      T.expect (restWeight n) (restFeature n) q
        (fun τ=>deletedOverlap n (joinSpin (σ,false)) (joinSpin (T.atSlot τ s,false))-center) x :=
  (T.expect_atSlot (restWeight_pos n) (restFeature n) ho q s _ x).symm

theorem native_star_centered_projection_smooth (n : ℕ)
    {as : List PositiveMass} {a : ℝ} (ho : MassOrdered a as)
    (q : ℕ → RestCoordinate n → ℝ≥0) (center : ℝ) (σ : Spin n) (r : ℕ) :
    BddSmooth r (fun x=>nativeStarCenteredProjection n as q center x σ) :=
  (single as).nativeAnchor_expect_smooth (restWeight_pos n) (restFeature n) ho q _ r

theorem native_star_centered_projection_bound (n : ℕ)
    {as : List PositiveMass} {a : ℝ} (ho : MassOrdered a as)
    (q : ℕ → RestCoordinate n → ℝ≥0) (center : ℝ)
    (x : RestCoordinate n → ℝ) (σ : Spin n) :
    |nativeStarCenteredProjection n as q center x σ| ≤ 1+|center| := by
  let T:=single (S:=Spin n) as
  have hw:=T.weight_probability (restWeight_pos n) (restFeature n) ho q x
  unfold nativeStarCenteredProjection singleMean ClockTree.expect
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑τ,T.weight (restWeight n) (restFeature n) q τ x*(1+|center|) := by
      apply Finset.sum_le_sum
      intro τ _
      rw [abs_mul,abs_of_nonneg (hw.1 τ)]
      exact mul_le_mul_of_nonneg_left
        ((abs_sub _ _).trans (add_le_add (abs_deletedOverlap_le_one n _ _) (le_refl |center|))) (hw.1 τ)
    _ = 1+|center| := by rw [←Finset.sum_mul,hw.2,one_mul]

theorem native_star_centered_projection_difference (n : ℕ)
    {as : List PositiveMass} (q : ℕ → RestCoordinate n → ℝ≥0) (center : ℝ)
    (x : RestCoordinate n → ℝ) (σ τ : Spin n) :
    nativeStarCenteredProjection n as q center x τ-nativeStarCenteredProjection n as q center x σ=
      inner ℝ (WithLp.toLp 2 (normalizedSpin n τ)-WithLp.toLp 2 (normalizedSpin n σ))
        (nativeWeightedExteriorAnchor n (single as) (fun _=>1) (singleSlot as) q x) := by
  unfold nativeStarCenteredProjection singleMean ClockTree.expect nativeWeightedExteriorAnchor
  simp only [inner_smul_right,inner_sum,inner_sub_left,normalizedSpin_inner_eq_overlap,
    single_atSlot,deleted_overlap_join_eq_scaled,mul_one,←Finset.sum_sub_distrib,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _
  ring

theorem native_star_projection_abs_pow_le_pair (n p : ℕ)
    {as : List PositiveMass} (T : ClockTree (Spin n) as) {a : ℝ}
    (ho : MassOrdered a as) (s : T.Slot) (q : ℕ → RestCoordinate n → ℝ≥0)
    (center : ℝ) (x : RestCoordinate n → ℝ) :
    T.expect (restWeight n) (restFeature n) q
      (fun σ=>|nativeStarCenteredProjection n as q center x (T.atSlot σ s)|^p) x ≤
      (T.fork T).expect (restWeight n) (restFeature n) q
        (fun σ=>|deletedOverlap n (joinSpin (T.atSlot σ.1 s,false))
          (joinSpin (T.atSlot σ.2 s,false))-center|^p) x := by
  rw [expect_fork]
  simp_rw [native_star_centered_projection_eq_slot_expect n T ho s]
  unfold ClockTree.expect
  apply Finset.sum_le_sum
  intro σ _
  apply mul_le_mul_of_nonneg_left _
    ((T.weight_probability (restWeight_pos n) (restFeature n) ho q x).1 σ)
  exact finite_weighted_mean_abs_pow_le _ _
    (T.weight_probability (restWeight_pos n) (restFeature n) ho q x).1
    (T.weight_probability (restWeight_pos n) (restFeature n) ho q x).2 p

theorem native_common_star_projection_power_le_original_pair (n p : ℕ)
    (pre mid tail : List PositiveMass) {a : ℝ}
    (ho : MassOrdered a (pre++(mid++tail)))
    (T : ClockTree (Spin n) tail) (s : T.Slot)
    (v : RestCoordinate n → ℝ) (q : ℕ → RestCoordinate n → ℝ)
    (center : ℝ) (x : RestCoordinate n → ℝ) :
    let qs:=fun j=>cumulativeIncrements (q 0) (fun k=>q (k+1)) (pre.length+(mid.length+j))
    (∫z,T.expect (restWeight n) (restFeature n) qs
      (fun σ=>|nativeStarCenteredProjection n tail qs center (exteriorForestStarRoot z) (T.atSlot σ s)|^p)
      (exteriorForestStarRoot z)
      ∂nativeExteriorForestDisorderRootLaw (restWeight n) (restFeature n) pre mid tail v q x) ≤
      (pairClock (pre++(mid++tail)) (pre.length+mid.length)).disorderExpect
        (restWeight n) (restFeature n) v q (fun σ=>
          |deletedOverlap n (joinSpin ((pairSpin _ _ σ).1,false))
            (joinSpin ((pairSpin _ _ σ).2,false))-center|^p) x := by
  dsimp only
  let qs:=fun j=>cumulativeIncrements (q 0) (fun k=>q (k+1)) (pre.length+(mid.length+j))
  let Q:=fun σ τ : Spin n=>|deletedOverlap n (joinSpin (σ,false)) (joinSpin (τ,false))-center|^p
  rw [←native_common_star_pair_marginal n pre mid tail ho T s v q Q x]
  let := nativeExteriorForestDisorderRootLaw_probability (restWeight_pos n) (restFeature n)
    pre mid tail ho v q x
  have HR := (T.fork T).nativeAnchor_expect_smooth (restWeight_pos n) (restFeature n)
    ho.suffix_end.suffix_end qs (fun σ=>Q (T.atSlot σ.1 s) (T.atSlot σ.2 s)) 0
  apply integral_mono_of_nonneg
  · apply Eventually.of_forall
    intro z
    unfold ClockTree.expect
    exact Finset.sum_nonneg fun σ _=>mul_nonneg
      ((T.weight_probability (restWeight_pos n) (restFeature n) ho.suffix_end.suffix_end qs
        (exteriorForestStarRoot z)).1 σ) (by positivity)
  · exact HR.integrable_comp_measurable departedAnchorExteriorRoot_measurable
  · exact Eventually.of_forall fun z=>native_star_projection_abs_pow_le_pair n p T
      ho.suffix_end.suffix_end s qs center (exteriorForestStarRoot z)

end OAI.SKFluctuations.Cavity
