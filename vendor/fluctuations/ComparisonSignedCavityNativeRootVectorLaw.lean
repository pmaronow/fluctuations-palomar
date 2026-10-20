module

public import ComparisonSignedCavitySubtreeProjectedFourth
public import ComparisonSignedCavityRootVectorResampling

@[expose] public section

noncomputable section
set_option maxHeartbeats 8000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal RealInnerProductSpace
namespace OAI.SKFluctuations.Cavity
open Hierarchy

private theorem root_vector_normalized_spin_norm_le_one (n : ℕ) (σ : Spin n) :
    ‖WithLp.toLp 2 (normalizedSpin n σ)‖ ≤ 1 := by
  have he : ‖WithLp.toLp 2 (normalizedSpin n σ)‖^2=orderedOverlap n σ σ := by
    rw [←real_inner_self_eq_norm_sq,normalizedSpin_inner_eq_overlap]
  nlinarith [norm_nonneg (WithLp.toLp 2 (normalizedSpin n σ)),
    orderedOverlap_abs_le_one n σ σ,le_abs_self (orderedOverlap n σ σ)]

private theorem root_vector_pair_inner_eq_sum (n : ℕ) (V : EuclideanSpace ℝ (Fin n))
    (σ τ : Spin n) :
    inner ℝ (WithLp.toLp 2 (normalizedSpin n τ)-WithLp.toLp 2 (normalizedSpin n σ)) V =
      -((∑ i,V i*normalizedSpin n σ i)-(∑ i,V i*normalizedSpin n τ i)) := by
  rw [inner_sub_left]
  simp only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial]
  simp_rw [mul_comm]
  ring

theorem native_subtree_root_vector_fourth_eq_physical_resampling (n : ℕ) (hn : 0 < n)
    {as : List PositiveMass} {a : ℝ} (ho : MassOrdered a as)
    (T : ClockTree (Spin n) as) (s t : T.Slot) (hst : s ≠ t)
    (q : ℕ → RestCoordinate n → ℝ≥0)
    {P : Type} [MeasurableSpace P] (μ : Measure P) [IsFiniteMeasure μ]
    (x : P → RestCoordinate n → ℝ) (hx : Measurable x)
    (V : P → EuclideanSpace ℝ (Fin n)) (hV : Measurable V)
    (R : ℝ) (_hR : 0 ≤ R) (hbound : ∀z,‖V z‖ ≤ R) :
    (∫z,T.expect (restWeight n) (restFeature n) q (fun σ=>
      (inner ℝ (WithLp.toLp 2 (normalizedSpin n (T.atSlot σ t))-
        WithLp.toLp 2 (normalizedSpin n (T.atSlot σ s))) (V z))^4) (x z) ∂μ) =
      physicalRootVectorResamplingMoment n 1 V
        ((clockSteps as (fun j=>restFiniteVariance n (q j))).drop (T.splitIndex s t))
        ((clockSteps as (fun j=>restFiniteVariance n (q j))).take (T.splitIndex s t))
        μ (fun z=>restFiniteState n (x z)) ((restFiniteState_measurable n).comp hx) := by
  let steps:=clockSteps as (fun j=>restFiniteVariance n (q j))
  let X:=fun z=>restFiniteState n (x z)
  have hX : Measurable X:=(restFiniteState_measurable n).comp hx
  let j:=T.splitIndex s t
  let Q:=fun z σ τ=>(inner ℝ (WithLp.toLp 2 (normalizedSpin n τ)-
    WithLp.toLp 2 (normalizedSpin n σ)) (V z))^4
  have hQ : Measurable (fun z : P×(Spin n×Spin n)=>Q z.1 z.2.1 z.2.2) :=
    (((measurable_of_countable (fun st : Spin n×Spin n=>
      WithLp.toLp 2 (normalizedSpin n st.2)-WithLp.toLp 2 (normalizedSpin n st.1))).comp
      measurable_snd).inner (hV.comp measurable_fst)).pow_const 4
  have hQb : ∀z σ τ,|Q z σ τ| ≤ (2*R)^4 := by
    intro z σ τ
    have hd : ‖WithLp.toLp 2 (normalizedSpin n τ)-WithLp.toLp 2 (normalizedSpin n σ)‖ ≤ 2 :=
      (norm_sub_le _ _).trans (by linarith [root_vector_normalized_spin_norm_le_one n σ,
        root_vector_normalized_spin_norm_le_one n τ])
    have hh:=norm_inner_le_norm (𝕜:=ℝ)
      (WithLp.toLp 2 (normalizedSpin n τ)-WithLp.toLp 2 (normalizedSpin n σ)) (V z)
    rw [Real.norm_eq_abs] at hh
    have hb:=hh.trans (mul_le_mul hd (hbound z) (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 2))
    simpa only [Q,abs_pow] using pow_le_pow_left₀ (abs_nonneg _) hb 4
  rw [native_subtree_root_pair_eq_physical_fork n hn ho T s t q μ x hx hst Q hQ ((2*R)^4) hQb]
  have hj : j ≤ steps.length := by
    simpa only [j,steps,length_clockSteps] using T.splitIndex_le_clockLength s t
  change (∫z,conditionalForkTest (uniformWeight n) (finiteFeature n) steps X j _ z
    ∂physicalPathLaw μ n steps X hX) =
      physicalRootVectorResamplingMoment n 1 V (steps.drop j) (steps.take j) μ X hX
  unfold physicalRootVectorResamplingMoment
  simp_rw [←physical_root_vector_cut_center_cancels]
  rw [List.take_append_drop]
  simp only [List.length_take,Nat.min_eq_left hj,show 4*1=4 by norm_num]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro z
  unfold conditionalForkTest
  have hp:=conditionalPathAverage_root_parameter (uniformWeight n) (finiteFeature n) steps j X
    (fun r t=>|(∑ i,V z.1 i*normalizedSpin n (ForwardPath.spin steps.length z.2) i)-
      (∑ i,V r i*normalizedSpin n (ForwardPath.spin steps.length t) i)|^4) z
  rw [hp]
  congr 1
  funext zz
  dsimp only [Q]
  rw [root_vector_pair_inner_eq_sum]
  simp only [neg_pow,show (-1:ℝ)^4=1 by norm_num,one_mul,(show Even 4 by decide).pow_abs]
  rfl

end OAI.SKFluctuations.Cavity
