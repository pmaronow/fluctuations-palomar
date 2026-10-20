module

public import ComparisonSignedCavityMarkedPhysicalLaw
public import CavityRootProjectedResampling
public import CavityWeightedExteriorClock

@[expose] public section

noncomputable section
set_option maxHeartbeats 2500000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal RealInnerProductSpace

namespace OAI.SKFluctuations.Cavity
open Hierarchy

theorem native_marked_root_pair_eq_physical_fork (n : ℕ) (hn : 0<n)
    {as : List PositiveMass} {a : ℝ} (ho : MassOrdered a as)
    (q : ℕ → RestCoordinate n → ℝ≥0)
    {P : Type} [MeasurableSpace P] (μ : Measure P) [IsFiniteMeasure μ]
    (x : P → RestCoordinate n → ℝ) (hx : Measurable x)
    (p : ClockTree.MarkedPlacement (ClockTree.single (S := Spin n×Bool) as))
    (hst : nativeIncomingNewSlot p ≠ nativeIncomingOldSlot p)
    (Q : P → Spin n → Spin n → ℝ)
    (hQ : Measurable (fun z : P×(Spin n×Spin n)=>Q z.1 z.2.1 z.2.2))
    (C : ℝ) (hbound : ∀ z σ τ, |Q z σ τ| ≤ C) :
    (∫ z, p.tree.cavityLeft.expect (restWeight n) (restFeature n) q
      (fun σ=>Q z (p.restSpin σ) (nativeAttachmentOld p σ)) (x z) ∂μ)=
      ∫ z, conditionalForkTest (uniformWeight n) (finiteFeature n)
        (clockSteps as (fun j=>restFiniteVariance n (q j)))
        (fun z=>restFiniteState n (x z)) (nativeIncomingPairSplit p)
        (fun zz=>Q zz.1.1
          (ForwardPath.spin (clockSteps as (fun j=>restFiniteVariance n (q j))).length zz.1.2)
          (ForwardPath.spin (clockSteps as (fun j=>restFiniteVariance n (q j))).length zz.2.2)) z
        ∂physicalPathLaw μ n (clockSteps as (fun j=>restFiniteVariance n (q j)))
          (fun z=>restFiniteState n (x z)) ((restFiniteState_measurable n).comp hx) := by
  let steps := clockSteps as (fun j=>restFiniteVariance n (q j))
  let R := fun z=>restFiniteState n (x z)
  have hR : Measurable R := (restFiniteState_measurable n).comp hx
  have hs : OrderedSteps a steps := clockSteps_ordered ho _
  let F := fun zz : (P×ForwardPath (FeatureIndex n→ℝ) (Spin n) steps.length)×
      (P×ForwardPath (FeatureIndex n→ℝ) (Spin n) steps.length)=>
    Q zz.1.1 (ForwardPath.spin steps.length zz.1.2) (ForwardPath.spin steps.length zz.2.2)
  have hF : Measurable F := hQ.comp
    ((measurable_fst.comp measurable_fst).prodMk
      (((ForwardPath.spin_measurable steps.length).comp (measurable_snd.comp measurable_fst)).prodMk
        ((ForwardPath.spin_measurable steps.length).comp (measurable_snd.comp measurable_snd))))
  have hFI := conditionalForkTest_integrable (uniformWeight_pos n) (finiteFeature n)
    steps hs μ R hR (nativeIncomingPairSplit p) hF
    (fun zz=>hbound zz.1.1 _ _)
  change _=∫ z, conditionalForkTest (uniformWeight n) (finiteFeature n) steps R
    (nativeIncomingPairSplit p) F z
    ∂μ ⊗ₘ (hierarchyPathKernel (uniformWeight n) (finiteFeature n) steps).comap R hR
  have := hierarchyPathKernel_markov (uniformWeight_pos n) (finiteFeature n) steps hs
  rw [Measure.integral_compProd hFI]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro z
  dsimp only
  rw [Kernel.comap_apply]
  rw [native_marked_rest_pair_eq_conditional_fork n hn ho q (x z) p hst (Q z)]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro c
  change conditionalForkTest (uniformWeight n) (finiteFeature n) steps
    (fun _ : Unit=>R z) (nativeIncomingPairSplit p) (terminalPairTest steps (Q z)) ((),c)=
      conditionalForkTest (uniformWeight n) (finiteFeature n) steps R
        (nativeIncomingPairSplit p) (terminalPairTest steps (Q z)) (z,c)
  exact conditional_terminal_fork_root_irrel (uniformWeight n) (finiteFeature n) steps
    (nativeIncomingPairSplit p) (fun _ : Unit=>R z) R () z rfl (Q z) c

private theorem projected_boundary_abs_le_one (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) {a : ℝ} (hs : OrderedSteps a steps)
    (σ : Spin n) (x : FeatureIndex n→ℝ) :
    |physicalProjectedBoundaryOverlap n steps σ x| ≤ 1 := by
  rw [physical_projected_overlap_eq_fresh_mean n steps hs]
  exact gaussianHierarchyMean_abs_le (uniformWeight_pos n) (finiteFeature n)
    (orderedOverlap_abs_le_one n σ) steps hs x

private theorem projected_pair_fourth_measurable (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) {a : ℝ} (hs : OrderedSteps a steps)
    {P : Type} [MeasurableSpace P] (R : P→FeatureIndex n→ℝ) (hR : Measurable R) :
    Measurable (fun z : P×(Spin n×Spin n)=>
      (physicalProjectedBoundaryOverlap n steps z.2.1 (R z.1)-
        physicalProjectedBoundaryOverlap n steps z.2.2 (R z.1))^4) := by
  have hM := (actualSpinMean_measurable n steps hs).comp hR
  apply Measurable.pow_const
  apply Measurable.sub
  all_goals
    unfold physicalProjectedBoundaryOverlap
    apply Finset.measurable_sum
    intro i _
    apply Measurable.mul
    · first
      | exact (measurable_of_countable (fun σ : Spin n=>normalizedSpin n σ i)).comp
          (measurable_fst.comp measurable_snd)
      | exact (measurable_of_countable (fun σ : Spin n=>normalizedSpin n σ i)).comp
          (measurable_snd.comp measurable_snd)
    · exact ((measurable_pi_apply i).comp hM).comp measurable_fst

theorem native_incoming_projection_fourth_integral_eq_resampling (n : ℕ) (hn : 0<n)
    {as : List PositiveMass} {a : ℝ} (ho : MassOrdered a as)
    (q : ℕ → RestCoordinate n → ℝ≥0)
    {P : Type} [MeasurableSpace P] (μ : Measure P) [IsFiniteMeasure μ]
    (x : P→RestCoordinate n→ℝ) (hx : Measurable x) (center : ℝ)
    (p : ClockTree.MarkedPlacement (ClockTree.single (S := Spin n×Bool) as))
    (hst : nativeIncomingNewSlot p ≠ nativeIncomingOldSlot p) :
    (∫ z, nativeIncomingProjectionFourth n q (x z) center p ∂μ)=
      ((n:ℝ)/(n+1 : ℕ))^4*
        physicalRootProjectedResamplingMoment n 2
          (clockSteps as (fun j=>restFiniteVariance n (q j))) μ
          (fun z=>restFiniteState n (x z)) ((restFiniteState_measurable n).comp hx)
          (nativeIncomingPairSplit p) := by
  let steps := clockSteps as (fun j=>restFiniteVariance n (q j))
  let R := fun z=>restFiniteState n (x z)
  let j := nativeIncomingPairSplit p
  let c : ℝ := (n:ℝ)/(n+1 : ℕ)
  have hR : Measurable R := (restFiniteState_measurable n).comp hx
  have hs : OrderedSteps a steps := clockSteps_ordered ho _
  let Q := fun z σ τ=>(physicalProjectedBoundaryOverlap n steps σ (R z)-
    physicalProjectedBoundaryOverlap n steps τ (R z))^4
  have hQ : Measurable (fun z : P×(Spin n×Spin n)=>Q z.1 z.2.1 z.2.2) :=
    projected_pair_fourth_measurable n steps hs R hR
  have hbound : ∀ z σ τ, |Q z σ τ| ≤ (16:ℝ) := by
    intro z σ τ
    have hdiff : |physicalProjectedBoundaryOverlap n steps σ (R z)-
        physicalProjectedBoundaryOverlap n steps τ (R z)| ≤ 2 :=
      (abs_sub _ _).trans (by linarith [projected_boundary_abs_le_one n steps hs σ (R z),
        projected_boundary_abs_le_one n steps hs τ (R z)])
    simpa only [Q,abs_pow,show (2:ℝ)^4=16 by norm_num] using
      pow_le_pow_left₀ (abs_nonneg _) hdiff 4
  have hpoint (z) : nativeIncomingProjectionFourth n q (x z) center p=
      c^4*p.tree.cavityLeft.expect (restWeight n) (restFeature n) q
        (fun σ=>Q z (p.restSpin σ) (nativeAttachmentOld p σ)) (x z) := by
    unfold nativeIncomingProjectionFourth nativeIncomingProjectionDifference
    simp_rw [native_centered_projected_difference_eq_physical n hn as ho q (x z) center]
    unfold ClockTree.expect
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro σ _
    dsimp only [Q,c,R,steps]
    ring
  simp_rw [hpoint]
  rw [integral_const_mul,
    native_marked_root_pair_eq_physical_fork n hn ho q μ x hx p hst Q hQ 16 hbound]
  have hj : j ≤ steps.length := by
    simpa only [j,nativeIncomingPairSplit,steps,length_clockSteps] using
      p.tree.cavityLeft.splitIndex_le_clockLength (nativeIncomingNewSlot p) (nativeIncomingOldSlot p)
  have he := physical_root_projected_resampling_eq_boundary n 2
    (steps.take j) (steps.drop j) μ R hR
  rw [List.take_append_drop] at he
  simp only [List.length_take,Nat.min_eq_left hj,show 2*2=4 by norm_num] at he
  change c^4*_ = c^4*physicalRootProjectedResamplingMoment n 2 steps μ R hR j
  rw [he]
  congr 1
  apply integral_congr_ae
  apply Eventually.of_forall
  intro z
  unfold conditionalForkTest
  have hp := conditionalPathAverage_root_parameter (uniformWeight n) (finiteFeature n)
    steps j R
    (fun r t=>|physicalProjectedBoundaryOverlap n steps (ForwardPath.spin steps.length z.2) (R z.1)-
      physicalProjectedBoundaryOverlap n steps (ForwardPath.spin steps.length t) (R r)|^4) z
  simpa only [Q,(show Even 4 by decide).pow_abs] using hp.symm

private theorem normalized_spin_norm_le_one (n : ℕ) (σ : Spin n) :
    ‖WithLp.toLp 2 (normalizedSpin n σ)‖ ≤ 1 := by
  have he : ‖WithLp.toLp 2 (normalizedSpin n σ)‖^2=orderedOverlap n σ σ := by
    rw [←real_inner_self_eq_norm_sq,normalizedSpin_inner_eq_overlap]
  have hh := orderedOverlap_abs_le_one n σ σ
  nlinarith [norm_nonneg (WithLp.toLp 2 (normalizedSpin n σ)),le_abs_self (orderedOverlap n σ σ)]

private theorem weighted_pair_inner_eq_sum (n : ℕ) (V : EuclideanSpace ℝ (Fin n))
    (σ τ : Spin n) :
    inner ℝ (WithLp.toLp 2 (normalizedSpin n τ)-WithLp.toLp 2 (normalizedSpin n σ)) V=
      -((∑ i, V i*normalizedSpin n σ i)-(∑ i, V i*normalizedSpin n τ i)) := by
  rw [inner_sub_left]
  simp only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial]
  simp_rw [mul_comm]
  ring

theorem native_incoming_anchor_fourth_integral_eq_resampling (n : ℕ) (hn : 0<n)
    {as : List PositiveMass} {a : ℝ} (ho : MassOrdered a as)
    (E : ClockTree (Spin n) as) (H : E.Assignment→ℝ) (s : E.Slot)
    (q : ℕ→RestCoordinate n→ℝ≥0)
    {P : Type} [MeasurableSpace P] (μ : Measure P) [IsFiniteMeasure μ]
    (x : P→RestCoordinate n→ℝ) (hx : Measurable x)
    (p : ClockTree.MarkedPlacement (ClockTree.single (S := Spin n×Bool) as))
    (hst : nativeIncomingNewSlot p ≠ nativeIncomingOldSlot p) :
    (∫ z, nativeIncomingAnchorFourth n E H s q (x z) p ∂μ)=
      ((n:ℝ)/(n+1 : ℕ))^4*
        physicalWeightedExteriorResamplingMoment n 1
          (E.realize (fun j=>restFiniteVariance n (q j)))
          (fun η=>H ((E.assignmentEquiv (fun j=>restFiniteVariance n (q j))).symm η))
          (E.slotEquiv (fun j=>restFiniteVariance n (q j)) s)
          ((clockSteps as (fun j=>restFiniteVariance n (q j))).drop (nativeIncomingPairSplit p))
          ((clockSteps as (fun j=>restFiniteVariance n (q j))).take (nativeIncomingPairSplit p))
          μ (fun z=>restFiniteState n (x z)) (fun z=>restFiniteState n (x z))
          ((restFiniteState_measurable n).comp hx) := by
  let steps := clockSteps as (fun j=>restFiniteVariance n (q j))
  let R := fun z=>restFiniteState n (x z)
  let j := nativeIncomingPairSplit p
  let c : ℝ := (n:ℝ)/(n+1 : ℕ)
  let E' := E.realize (fun j=>restFiniteVariance n (q j))
  let H' := fun η=>H ((E.assignmentEquiv (fun j=>restFiniteVariance n (q j))).symm η)
  let s' := E.slotEquiv (fun j=>restFiniteVariance n (q j)) s
  let V := fun z=>physicalWeightedExteriorAnchor n E' H' s' (R z)
  let Q := fun z σ τ=>(inner ℝ (WithLp.toLp 2 (normalizedSpin n τ)-
    WithLp.toLp 2 (normalizedSpin n σ)) (V z))^4
  let B := ∑ η, |H' η| *‖WithLp.toLp 2 (normalizedSpin n (E'.atSlot η s'))‖
  have hR : Measurable R := (restFiniteState_measurable n).comp hx
  have hs : OrderedSteps a steps := clockSteps_ordered ho _
  have hV : Measurable V := (physicalWeightedExteriorAnchor_continuous n E' hs H' s').measurable.comp hR
  have hB : 0 ≤ B := Finset.sum_nonneg fun η _=>mul_nonneg (abs_nonneg _) (norm_nonneg _)
  have hVB (z) : ‖V z‖ ≤ B := physicalWeightedExteriorAnchor_norm_le n E' hs H' s' (R z)
  have hQ : Measurable (fun z : P×(Spin n×Spin n)=>Q z.1 z.2.1 z.2.2) :=
    (((measurable_of_countable (fun st : Spin n×Spin n=>
      WithLp.toLp 2 (normalizedSpin n st.2)-WithLp.toLp 2 (normalizedSpin n st.1))).comp
      measurable_snd).inner (hV.comp measurable_fst)).pow_const 4
  have hbound : ∀ z σ τ, |Q z σ τ| ≤ (2*B)^4 := by
    intro z σ τ
    have hd : ‖WithLp.toLp 2 (normalizedSpin n τ)-WithLp.toLp 2 (normalizedSpin n σ)‖ ≤ 2 :=
      (norm_sub_le _ _).trans (by linarith [normalized_spin_norm_le_one n σ,
        normalized_spin_norm_le_one n τ])
    have hh := norm_inner_le_norm (𝕜:=ℝ)
      (WithLp.toLp 2 (normalizedSpin n τ)-WithLp.toLp 2 (normalizedSpin n σ)) (V z)
    rw [Real.norm_eq_abs] at hh
    have hb := hh.trans (mul_le_mul hd (hVB z) (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 2))
    simpa only [Q,abs_pow] using pow_le_pow_left₀ (abs_nonneg _) hb 4
  have hpoint (z) : nativeIncomingAnchorFourth n E H s q (x z) p=
      c^4*p.tree.cavityLeft.expect (restWeight n) (restFeature n) q
        (fun σ=>Q z (p.restSpin σ) (nativeAttachmentOld p σ)) (x z) := by
    unfold nativeIncomingAnchorFourth nativeIncomingAnchorDifference
    rw [native_weighted_exterior_anchor_eq_physical n hn]
    simp only [inner_smul_right]
    unfold ClockTree.expect
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro σ _
    dsimp only [Q,V,c,E',H',s',R]
    ring
  simp_rw [hpoint]
  rw [integral_const_mul,
    native_marked_root_pair_eq_physical_fork n hn ho q μ x hx p hst Q hQ ((2*B)^4) hbound]
  have hj : j ≤ steps.length := by
    simpa only [j,nativeIncomingPairSplit,steps,length_clockSteps] using
      p.tree.cavityLeft.splitIndex_le_clockLength (nativeIncomingNewSlot p) (nativeIncomingOldSlot p)
  change c^4*_ = c^4*physicalWeightedExteriorResamplingMoment n 1 E' H' s'
    (steps.drop j) (steps.take j) μ R R hR
  congr 1
  unfold physicalWeightedExteriorResamplingMoment
  simp_rw [←physical_weighted_resampling_cut_center_cancels]
  rw [List.take_append_drop]
  simp only [List.length_take,Nat.min_eq_left hj,show 4*1=4 by norm_num]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro z
  unfold conditionalForkTest
  have hp := conditionalPathAverage_root_parameter (uniformWeight n) (finiteFeature n) steps j R
    (fun r t=>|(∑ i, V z.1 i*normalizedSpin n (ForwardPath.spin steps.length z.2) i)-
      (∑ i, V r i*normalizedSpin n (ForwardPath.spin steps.length t) i)|^4) z
  rw [hp]
  congr 1
  funext zz
  dsimp only [Q]
  rw [weighted_pair_inner_eq_sum]
  simp only [neg_pow,show (-1:ℝ)^4=1 by norm_num,one_mul,(show Even 4 by decide).pow_abs]
  rfl

end OAI.SKFluctuations.Cavity
