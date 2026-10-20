module

public import ComparisonSignedCavityObservedProjectedReplacement
public import ComparisonSignedCavityActualAnchorPrimitives

@[expose] public section

noncomputable section
set_option maxHeartbeats 8000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal RealInnerProductSpace
namespace OAI.SKFluctuations.Cavity
open Hierarchy LaplaceWindowFormalization

theorem native_subtree_physical_pair_eq_fork (n : ℕ)
    {as : List PositiveMass} {a : ℝ} (ho : MassOrdered a as)
    (T : ClockTree (Spin n) as) (q : ℕ→FeatureIndex n→ℝ≥0)
    (s t : T.Slot) (hst : s≠t) (Q : Spin n→Spin n→ℝ) (x : FeatureIndex n→ℝ) :
    T.expect (uniformWeight n) (finiteFeature n) q
      (fun σ=>Q (T.atSlot σ s) (T.atSlot σ t)) x=
      ∫ z,conditionalForkTest (uniformWeight n) (finiteFeature n) (clockSteps as q)
        (fun _ : Unit=>x) (T.splitIndex s t) (terminalPairTest (clockSteps as q) Q) ((),z)
        ∂hierarchyPathKernel (uniformWeight n) (finiteFeature n) (clockSteps as q) x := by
  rw [T.expect_pairAtSlot (uniformWeight_pos n) (finiteFeature n) ho q s t hst Q x,
    ClockTree.pairMean_eq_levelPairMean (uniformWeight_pos n) (finiteFeature n) as ho]
  symm
  exact integral_terminal_fork_fixed_root (uniformWeight_pos n) (finiteFeature n)
    (clockSteps as q) (clockSteps_ordered ho q) (fun _ : Unit=>x) () _
    (by simpa only [length_clockSteps] using T.splitIndex_le_clockLength s t) Q

theorem native_subtree_pair_eq_conditional_fork (n : ℕ) (hn : 0<n)
    {as : List PositiveMass} {a : ℝ} (ho : MassOrdered a as)
    (T : ClockTree (Spin n) as) (s t : T.Slot)
    (q : ℕ→RestCoordinate n→ℝ≥0) (x : RestCoordinate n→ℝ)
    (hst : s≠t)
    (Q : Spin n→Spin n→ℝ) :
    T.expect (restWeight n) (restFeature n) q
      (fun σ=>Q (T.atSlot σ s)
        (T.atSlot σ t)) x=
      ∫ z,conditionalForkTest (uniformWeight n) (finiteFeature n)
        (clockSteps as (fun j=>restFiniteVariance n (q j)))
        (fun _ : Unit=>restFiniteState n x) (T.splitIndex s t)
        (terminalPairTest (clockSteps as (fun j=>restFiniteVariance n (q j))) Q) ((),z)
        ∂hierarchyPathKernel (uniformWeight n) (finiteFeature n)
          (clockSteps as (fun j=>restFiniteVariance n (q j))) (restFiniteState n x) := by
  rw [restFinite_clockTree_expect n hn]
  exact native_subtree_physical_pair_eq_fork n ho T _ s t hst Q _

theorem native_subtree_root_pair_eq_physical_fork (n : ℕ) (hn : 0<n)
    {as : List PositiveMass} {a : ℝ} (ho : MassOrdered a as)
    (T : ClockTree (Spin n) as) (s t : T.Slot) (q : ℕ→RestCoordinate n→ℝ≥0)
    {P : Type} [MeasurableSpace P] (μ : Measure P) [IsFiniteMeasure μ]
    (x : P→RestCoordinate n→ℝ) (hx : Measurable x)
    (hst : s≠t)
    (Q : P→Spin n→Spin n→ℝ)
    (hQ : Measurable (fun z : P×(Spin n×Spin n)=>Q z.1 z.2.1 z.2.2))
    (C : ℝ) (hbound : ∀ z σ τ,|Q z σ τ| ≤ C) :
    (∫ z,T.expect (restWeight n) (restFeature n) q
      (fun σ=>Q z (T.atSlot σ s)
        (T.atSlot σ t)) (x z) ∂μ)=
      ∫ z,conditionalForkTest (uniformWeight n) (finiteFeature n)
        (clockSteps as (fun j=>restFiniteVariance n (q j)))
        (fun z=>restFiniteState n (x z)) (T.splitIndex s t)
        (fun zz=>Q zz.1.1
          (ForwardPath.spin (clockSteps as (fun j=>restFiniteVariance n (q j))).length zz.1.2)
          (ForwardPath.spin (clockSteps as (fun j=>restFiniteVariance n (q j))).length zz.2.2)) z
        ∂physicalPathLaw μ n (clockSteps as (fun j=>restFiniteVariance n (q j)))
          (fun z=>restFiniteState n (x z)) ((restFiniteState_measurable n).comp hx) := by
  let steps:=clockSteps as (fun j=>restFiniteVariance n (q j))
  let R:=fun z=>restFiniteState n (x z)
  have hR : Measurable R:=(restFiniteState_measurable n).comp hx
  have hs : OrderedSteps a steps:=clockSteps_ordered ho _
  let F:=fun zz : (P×ForwardPath (FeatureIndex n→ℝ) (Spin n) steps.length)×
      (P×ForwardPath (FeatureIndex n→ℝ) (Spin n) steps.length)=>
    Q zz.1.1 (ForwardPath.spin steps.length zz.1.2) (ForwardPath.spin steps.length zz.2.2)
  have hF : Measurable F:=hQ.comp
    ((measurable_fst.comp measurable_fst).prodMk
      (((ForwardPath.spin_measurable steps.length).comp (measurable_snd.comp measurable_fst)).prodMk
        ((ForwardPath.spin_measurable steps.length).comp (measurable_snd.comp measurable_snd))))
  have hFI:=conditionalForkTest_integrable (uniformWeight_pos n) (finiteFeature n)
    steps hs μ R hR (T.splitIndex s t) hF (fun zz=>hbound zz.1.1 _ _)
  change _=∫ z,conditionalForkTest (uniformWeight n) (finiteFeature n) steps R
    (T.splitIndex s t) F z
    ∂μ ⊗ₘ (hierarchyPathKernel (uniformWeight n) (finiteFeature n) steps).comap R hR
  have :=hierarchyPathKernel_markov (uniformWeight_pos n) (finiteFeature n) steps hs
  rw [Measure.integral_compProd hFI]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro z
  dsimp only
  rw [Kernel.comap_apply,native_subtree_pair_eq_conditional_fork n hn ho T s t q (x z) hst (Q z)]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro d
  exact conditional_terminal_fork_root_irrel (uniformWeight n) (finiteFeature n) steps
    (T.splitIndex s t) (fun _ : Unit=>R z) R () z rfl (Q z) d

def nativeSubtreeExteriorProjectionFourth (n : ℕ)
    {as es : List PositiveMass} (T : ClockTree (Spin n) as) (s t : T.Slot)
    (E : ClockTree (Spin n) es) (H : E.Assignment→ℝ) (e : E.Slot)
    (qE q : ℕ→RestCoordinate n→ℝ≥0) (xE xD : RestCoordinate n→ℝ) : ℝ :=
  T.expect (restWeight n) (restFeature n) q
    (fun σ=>(inner ℝ (WithLp.toLp 2 (normalizedSpin n (T.atSlot σ t))-
      WithLp.toLp 2 (normalizedSpin n (T.atSlot σ s)))
      (nativeWeightedExteriorAnchor n E H e qE xE))^4) xD

private theorem subtree_normalized_spin_norm_le_one (n : ℕ) (σ : Spin n) :
    ‖WithLp.toLp 2 (normalizedSpin n σ)‖ ≤ 1 := by
  have he : ‖WithLp.toLp 2 (normalizedSpin n σ)‖^2=orderedOverlap n σ σ := by
    rw [←real_inner_self_eq_norm_sq,normalizedSpin_inner_eq_overlap]
  nlinarith [norm_nonneg (WithLp.toLp 2 (normalizedSpin n σ)),
    orderedOverlap_abs_le_one n σ σ,le_abs_self (orderedOverlap n σ σ)]

private theorem subtree_weighted_pair_inner_eq_sum (n : ℕ) (V : EuclideanSpace ℝ (Fin n))
    (σ τ : Spin n) :
    inner ℝ (WithLp.toLp 2 (normalizedSpin n τ)-WithLp.toLp 2 (normalizedSpin n σ)) V=
      -((∑ i,V i*normalizedSpin n σ i)-(∑ i,V i*normalizedSpin n τ i)) := by
  rw [inner_sub_left]
  simp only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial]
  simp_rw [mul_comm]
  ring

theorem native_subtree_exterior_fourth_eq_physical_resampling (n : ℕ) (hn : 0<n)
    {as : List PositiveMass} {a : ℝ} (ho : MassOrdered a as)
    (T : ClockTree (Spin n) as) (sD tD : T.Slot)
    {es : List PositiveMass} {aE : ℝ} (hoE : MassOrdered aE es)
    (E : ClockTree (Spin n) es) (H : E.Assignment→ℝ) (s : E.Slot)
    (qE q : ℕ→RestCoordinate n→ℝ≥0)
    {P : Type} [MeasurableSpace P] (μ : Measure P) [IsFiniteMeasure μ]
    (xE xD : P→RestCoordinate n→ℝ) (hxE : Measurable xE) (hxD : Measurable xD)
    (hst : sD≠tD) :
    (∫ z,nativeSubtreeExteriorProjectionFourth n T sD tD E H s qE q (xE z) (xD z) ∂μ)=
      ((n:ℝ)/(n+1 : ℕ))^4*physicalWeightedExteriorResamplingMoment n 1
        (E.realize (fun j=>restFiniteVariance n (qE j)))
        (fun η=>H ((E.assignmentEquiv (fun j=>restFiniteVariance n (qE j))).symm η))
        (E.slotEquiv (fun j=>restFiniteVariance n (qE j)) s)
        ((clockSteps as (fun j=>restFiniteVariance n (q j))).drop (T.splitIndex sD tD))
        ((clockSteps as (fun j=>restFiniteVariance n (q j))).take (T.splitIndex sD tD))
        μ (fun z=>restFiniteState n (xE z)) (fun z=>restFiniteState n (xD z))
        ((restFiniteState_measurable n).comp hxD) := by
  let steps:=clockSteps as (fun j=>restFiniteVariance n (q j))
  let R:=fun z=>restFiniteState n (xD z)
  let RE:=fun z=>restFiniteState n (xE z)
  let j:=T.splitIndex sD tD
  let k : ℝ:=(n:ℝ)/(n+1 : ℕ)
  let E':=E.realize (fun j=>restFiniteVariance n (qE j))
  let H':=fun η=>H ((E.assignmentEquiv (fun j=>restFiniteVariance n (qE j))).symm η)
  let s':=E.slotEquiv (fun j=>restFiniteVariance n (qE j)) s
  let V:=fun z=>physicalWeightedExteriorAnchor n E' H' s' (RE z)
  let Q:=fun z σ τ=>(inner ℝ (WithLp.toLp 2 (normalizedSpin n τ)-
    WithLp.toLp 2 (normalizedSpin n σ)) (V z))^4
  let B:=∑ η,|H' η| * ‖WithLp.toLp 2 (normalizedSpin n (E'.atSlot η s'))‖
  have hR : Measurable R:=(restFiniteState_measurable n).comp hxD
  have hRE : Measurable RE:=(restFiniteState_measurable n).comp hxE
  have hs : OrderedSteps a steps:=clockSteps_ordered ho _
  have hsE := clockSteps_ordered hoE (fun j=>restFiniteVariance n (qE j))
  have hV : Measurable V:=(physicalWeightedExteriorAnchor_continuous n E' hsE H' s').measurable.comp hRE
  have hB : 0 ≤ B:=Finset.sum_nonneg fun η _=>mul_nonneg (abs_nonneg _) (norm_nonneg _)
  have hVB z : ‖V z‖ ≤ B:=physicalWeightedExteriorAnchor_norm_le n E' hsE H' s' (RE z)
  have hQ : Measurable (fun z : P×(Spin n×Spin n)=>Q z.1 z.2.1 z.2.2):=
    (((measurable_of_countable (fun st : Spin n×Spin n=>
      WithLp.toLp 2 (normalizedSpin n st.2)-WithLp.toLp 2 (normalizedSpin n st.1))).comp
      measurable_snd).inner (hV.comp measurable_fst)).pow_const 4
  have hbound : ∀ z σ τ,|Q z σ τ| ≤ (2*B)^4 := by
    intro z σ τ
    have hd : ‖WithLp.toLp 2 (normalizedSpin n τ)-WithLp.toLp 2 (normalizedSpin n σ)‖ ≤ 2 :=
      (norm_sub_le _ _).trans (by linarith [subtree_normalized_spin_norm_le_one n σ,
        subtree_normalized_spin_norm_le_one n τ])
    have hh:=norm_inner_le_norm (𝕜:=ℝ)
      (WithLp.toLp 2 (normalizedSpin n τ)-WithLp.toLp 2 (normalizedSpin n σ)) (V z)
    rw [Real.norm_eq_abs] at hh
    have hb:=hh.trans (mul_le_mul hd (hVB z) (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 2))
    simpa only [Q,abs_pow] using pow_le_pow_left₀ (abs_nonneg _) hb 4
  have hpoint z : nativeSubtreeExteriorProjectionFourth n T sD tD E H s qE q (xE z) (xD z)=
      k^4*T.expect (restWeight n) (restFeature n) q
        (fun σ=>Q z (T.atSlot σ sD)
          (T.atSlot σ tD)) (xD z) := by
    unfold nativeSubtreeExteriorProjectionFourth
    rw [native_weighted_exterior_anchor_eq_physical n hn]
    simp only [inner_smul_right]
    unfold ClockTree.expect
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro σ _
    dsimp only [Q,V,k,E',H',s',RE]
    ring
  simp_rw [hpoint]
  rw [integral_const_mul,native_subtree_root_pair_eq_physical_fork n hn ho T sD tD q μ xD hxD
    hst Q hQ ((2*B)^4) hbound]
  have hj : j  ≤  steps.length := by
    simpa only [j,steps,length_clockSteps] using
      T.splitIndex_le_clockLength sD tD
  change k^4*_=k^4*physicalWeightedExteriorResamplingMoment n 1 E' H' s'
    (steps.drop j) (steps.take j) μ RE R hR
  congr 1
  unfold physicalWeightedExteriorResamplingMoment
  simp_rw [←physical_weighted_resampling_cut_center_cancels]
  rw [List.take_append_drop]
  simp only [List.length_take,Nat.min_eq_left hj,show 4*1=4 by norm_num]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro z
  unfold conditionalForkTest
  have hp:=conditionalPathAverage_root_parameter (uniformWeight n) (finiteFeature n) steps j R
    (fun r t=>|(∑ i,V z.1 i*normalizedSpin n (ForwardPath.spin steps.length z.2) i)-
      (∑ i,V r i*normalizedSpin n (ForwardPath.spin steps.length t) i)|^4) z
  rw [hp]
  congr 1
  funext zz
  dsimp only [Q]
  rw [subtree_weighted_pair_inner_eq_sum]
  simp only [neg_pow,show (-1:ℝ)^4=1 by norm_num,one_mul,(show Even 4 by decide).pow_abs]
  rfl

end OAI.SKFluctuations.Cavity
