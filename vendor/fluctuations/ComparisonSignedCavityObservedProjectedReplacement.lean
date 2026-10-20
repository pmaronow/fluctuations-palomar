module

public import ComparisonSignedCavityObservedGammaCollapse
public import ComparisonSignedCavityRootCauchy
public import CavityWeightedExteriorClock

@[expose] public section

noncomputable section
set_option maxHeartbeats 6000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal RealInnerProductSpace
namespace OAI.SKFluctuations.Cavity
open Hierarchy LaplaceWindowFormalization

def nativeObservedOldSlot {n : ℕ} {as : List PositiveMass}
    {T : ClockTree (Spin n×Bool) as} (c : T.Slot) (p : ClockTree.MarkedPlacement T) :
    p.tree.cavityLeft.Slot := p.tree.cavityLeftSlot (p.embed c)

def nativeObservedNewSlot {n : ℕ} {as : List PositiveMass}
    {T : ClockTree (Spin n×Bool) as} (p : ClockTree.MarkedPlacement T) :
    p.tree.cavityLeft.Slot := p.tree.cavityLeftSlot p.mark

def nativeObservedPairSplit {n : ℕ} {as : List PositiveMass}
    {T : ClockTree (Spin n×Bool) as} (c : T.Slot) (p : ClockTree.MarkedPlacement T) : ℕ :=
    p.tree.cavityLeft.splitIndex (nativeObservedNewSlot p) (nativeObservedOldSlot c p)

theorem native_observed_old_slot_at {n : ℕ} {as : List PositiveMass}
    {T : ClockTree (Spin n×Bool) as} (c : T.Slot) (p : ClockTree.MarkedPlacement T)
    (σ : p.tree.cavityLeft.Assignment) :
    p.tree.cavityLeft.atSlot σ (nativeObservedOldSlot c p)=
      T.cavityLeft.atSlot (p.restRestrict σ) (T.cavityLeftSlot c) :=
  (p.restRestrict_at σ c).symm

private theorem observed_physical_pair_eq_fork (n : ℕ)
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

theorem native_observed_pair_eq_conditional_fork (n : ℕ) (hn : 0<n)
    {as : List PositiveMass} {a : ℝ} (ho : MassOrdered a as)
    (T : ClockTree (Spin n×Bool) as) (c : T.Slot)
    (q : ℕ→RestCoordinate n→ℝ≥0) (x : RestCoordinate n→ℝ)
    (p : ClockTree.MarkedPlacement T)
    (hst : nativeObservedNewSlot p≠nativeObservedOldSlot c p)
    (Q : Spin n→Spin n→ℝ) :
    p.tree.cavityLeft.expect (restWeight n) (restFeature n) q
      (fun σ=>Q (p.restSpin σ)
        (T.cavityLeft.atSlot (p.restRestrict σ) (T.cavityLeftSlot c))) x=
      ∫ z,conditionalForkTest (uniformWeight n) (finiteFeature n)
        (clockSteps as (fun j=>restFiniteVariance n (q j)))
        (fun _ : Unit=>restFiniteState n x) (nativeObservedPairSplit c p)
        (terminalPairTest (clockSteps as (fun j=>restFiniteVariance n (q j))) Q) ((),z)
        ∂hierarchyPathKernel (uniformWeight n) (finiteFeature n)
          (clockSteps as (fun j=>restFiniteVariance n (q j))) (restFiniteState n x) := by
  simp_rw [←native_observed_old_slot_at c p]
  rw [restFinite_clockTree_expect n hn]
  exact observed_physical_pair_eq_fork n ho p.tree.cavityLeft _
    (nativeObservedNewSlot p) (nativeObservedOldSlot c p) hst Q _

theorem native_observed_root_pair_eq_physical_fork (n : ℕ) (hn : 0<n)
    {as : List PositiveMass} {a : ℝ} (ho : MassOrdered a as)
    (T : ClockTree (Spin n×Bool) as) (c : T.Slot) (q : ℕ→RestCoordinate n→ℝ≥0)
    {P : Type} [MeasurableSpace P] (μ : Measure P) [IsFiniteMeasure μ]
    (x : P→RestCoordinate n→ℝ) (hx : Measurable x)
    (p : ClockTree.MarkedPlacement T)
    (hst : nativeObservedNewSlot p≠nativeObservedOldSlot c p)
    (Q : P→Spin n→Spin n→ℝ)
    (hQ : Measurable (fun z : P×(Spin n×Spin n)=>Q z.1 z.2.1 z.2.2))
    (C : ℝ) (hbound : ∀ z σ τ,|Q z σ τ| ≤ C) :
    (∫ z,p.tree.cavityLeft.expect (restWeight n) (restFeature n) q
      (fun σ=>Q z (p.restSpin σ)
        (T.cavityLeft.atSlot (p.restRestrict σ) (T.cavityLeftSlot c))) (x z) ∂μ)=
      ∫ z,conditionalForkTest (uniformWeight n) (finiteFeature n)
        (clockSteps as (fun j=>restFiniteVariance n (q j)))
        (fun z=>restFiniteState n (x z)) (nativeObservedPairSplit c p)
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
    steps hs μ R hR (nativeObservedPairSplit c p) hF (fun zz=>hbound zz.1.1 _ _)
  change _=∫ z,conditionalForkTest (uniformWeight n) (finiteFeature n) steps R
    (nativeObservedPairSplit c p) F z
    ∂μ ⊗ₘ (hierarchyPathKernel (uniformWeight n) (finiteFeature n) steps).comap R hR
  have :=hierarchyPathKernel_markov (uniformWeight_pos n) (finiteFeature n) steps hs
  rw [Measure.integral_compProd hFI]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro z
  dsimp only
  rw [Kernel.comap_apply,native_observed_pair_eq_conditional_fork n hn ho T c q (x z) p hst (Q z)]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro d
  exact conditional_terminal_fork_root_irrel (uniformWeight n) (finiteFeature n) steps
    (nativeObservedPairSplit c p) (fun _ : Unit=>R z) R () z rfl (Q z) d

def nativeObservedExteriorProjectionDifference (n : ℕ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (c : T.Slot)
    {es : List PositiveMass} (E : ClockTree (Spin n) es) (H : E.Assignment→ℝ) (s : E.Slot)
    (q : ℕ→RestCoordinate n→ℝ≥0) (xE : RestCoordinate n→ℝ)
    (p : ClockTree.MarkedPlacement T) (σ : p.tree.cavityLeft.Assignment) : ℝ :=
  inner ℝ (WithLp.toLp 2 (normalizedSpin n
      (T.cavityLeft.atSlot (p.restRestrict σ) (T.cavityLeftSlot c)))-
    WithLp.toLp 2 (normalizedSpin n (p.restSpin σ)))
    (nativeWeightedExteriorAnchor n E H s q xE)

def nativeObservedExteriorProjectionFourth (n : ℕ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (c : T.Slot)
    {es : List PositiveMass} (E : ClockTree (Spin n) es) (H : E.Assignment→ℝ) (s : E.Slot)
    (qE q : ℕ→RestCoordinate n→ℝ≥0) (xE xD : RestCoordinate n→ℝ)
    (p : ClockTree.MarkedPlacement T) : ℝ :=
  p.tree.cavityLeft.expect (restWeight n) (restFeature n) q
    (fun σ=>nativeObservedExteriorProjectionDifference n T c E H s qE xE p σ^4) xD

private theorem observed_normalized_spin_norm_le_one (n : ℕ) (σ : Spin n) :
    ‖WithLp.toLp 2 (normalizedSpin n σ)‖ ≤ 1 := by
  have he : ‖WithLp.toLp 2 (normalizedSpin n σ)‖^2=orderedOverlap n σ σ := by
    rw [←real_inner_self_eq_norm_sq,normalizedSpin_inner_eq_overlap]
  nlinarith [norm_nonneg (WithLp.toLp 2 (normalizedSpin n σ)),
    orderedOverlap_abs_le_one n σ σ,le_abs_self (orderedOverlap n σ σ)]

private theorem observed_weighted_pair_inner_eq_sum (n : ℕ) (V : EuclideanSpace ℝ (Fin n))
    (σ τ : Spin n) :
    inner ℝ (WithLp.toLp 2 (normalizedSpin n τ)-WithLp.toLp 2 (normalizedSpin n σ)) V=
      -((∑ i,V i*normalizedSpin n σ i)-(∑ i,V i*normalizedSpin n τ i)) := by
  rw [inner_sub_left]
  simp only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial]
  simp_rw [mul_comm]
  ring

theorem native_observed_exterior_fourth_eq_physical_resampling (n : ℕ) (hn : 0<n)
    {as : List PositiveMass} {a : ℝ} (ho : MassOrdered a as)
    (T : ClockTree (Spin n×Bool) as) (c : T.Slot)
    {es : List PositiveMass} {aE : ℝ} (hoE : MassOrdered aE es)
    (E : ClockTree (Spin n) es) (H : E.Assignment→ℝ) (s : E.Slot)
    (qE q : ℕ→RestCoordinate n→ℝ≥0)
    {P : Type} [MeasurableSpace P] (μ : Measure P) [IsFiniteMeasure μ]
    (xE xD : P→RestCoordinate n→ℝ) (hxE : Measurable xE) (hxD : Measurable xD)
    (p : ClockTree.MarkedPlacement T)
    (hst : nativeObservedNewSlot p≠nativeObservedOldSlot c p) :
    (∫ z,nativeObservedExteriorProjectionFourth n T c E H s qE q (xE z) (xD z) p ∂μ)=
      ((n:ℝ)/(n+1 : ℕ))^4*physicalWeightedExteriorResamplingMoment n 1
        (E.realize (fun j=>restFiniteVariance n (qE j)))
        (fun η=>H ((E.assignmentEquiv (fun j=>restFiniteVariance n (qE j))).symm η))
        (E.slotEquiv (fun j=>restFiniteVariance n (qE j)) s)
        ((clockSteps as (fun j=>restFiniteVariance n (q j))).drop (nativeObservedPairSplit c p))
        ((clockSteps as (fun j=>restFiniteVariance n (q j))).take (nativeObservedPairSplit c p))
        μ (fun z=>restFiniteState n (xE z)) (fun z=>restFiniteState n (xD z))
        ((restFiniteState_measurable n).comp hxD) := by
  let steps:=clockSteps as (fun j=>restFiniteVariance n (q j))
  let R:=fun z=>restFiniteState n (xD z)
  let RE:=fun z=>restFiniteState n (xE z)
  let j:=nativeObservedPairSplit c p
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
      (norm_sub_le _ _).trans (by linarith [observed_normalized_spin_norm_le_one n σ,
        observed_normalized_spin_norm_le_one n τ])
    have hh:=norm_inner_le_norm (𝕜:=ℝ)
      (WithLp.toLp 2 (normalizedSpin n τ)-WithLp.toLp 2 (normalizedSpin n σ)) (V z)
    rw [Real.norm_eq_abs] at hh
    have hb:=hh.trans (mul_le_mul hd (hVB z) (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 2))
    simpa only [Q,abs_pow] using pow_le_pow_left₀ (abs_nonneg _) hb 4
  have hpoint z : nativeObservedExteriorProjectionFourth n T c E H s qE q (xE z) (xD z) p=
      k^4*p.tree.cavityLeft.expect (restWeight n) (restFeature n) q
        (fun σ=>Q z (p.restSpin σ)
          (T.cavityLeft.atSlot (p.restRestrict σ) (T.cavityLeftSlot c))) (xD z) := by
    unfold nativeObservedExteriorProjectionFourth nativeObservedExteriorProjectionDifference
    rw [native_weighted_exterior_anchor_eq_physical n hn]
    simp only [inner_smul_right]
    unfold ClockTree.expect
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro σ _
    dsimp only [Q,V,k,E',H',s',RE]
    ring
  simp_rw [hpoint]
  rw [integral_const_mul,native_observed_root_pair_eq_physical_fork n hn ho T c q μ xD hxD
    p hst Q hQ ((2*B)^4) hbound]
  have hj : j  ≤  steps.length := by
    simpa only [j,nativeObservedPairSplit,steps,length_clockSteps] using
      p.tree.cavityLeft.splitIndex_le_clockLength (nativeObservedNewSlot p) (nativeObservedOldSlot c p)
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
  rw [observed_weighted_pair_inner_eq_sum]
  simp only [neg_pow,show (-1:ℝ)^4=1 by norm_num,one_mul,(show Even 4 by decide).pow_abs]
  rfl

theorem eventually_native_observed_exterior_fourth_from_primitives
    (B ca c₀ : ℝ) (hca : 0<ca) (hc₀ : 0<c₀)
    {m delta : ℝ} (hgap : 2*delta<6*m) :
    ∀ᶠ n : ℕ in atTop,∀ (as es : List PositiveMass) (aD aE : ℝ)
      (_hoD : MassOrdered aD as) (_hoE : MassOrdered aE es)
      (T : ClockTree (Spin n×Bool) as) (c : T.Slot)
      (E : ClockTree (Spin n) es) (H : E.Assignment→ℝ) (s : E.Slot)
      (qE qD : ℕ→RestCoordinate n→ℝ≥0) (p : ClockTree.MarkedPlacement T),
      nativeObservedNewSlot p≠nativeObservedOldSlot c p→
    ∀ (pre skip : List (GaussianStep (FeatureIndex n))) (a D pH sj r W v : ℝ),
      (clockSteps as (fun j=>restFiniteVariance n (qD j))).take (nativeObservedPairSplit c p)=
        skip++pre→
      0<a→0<D→D ≤ B→0 ≤ pH→0 ≤ sj→0<r→0<W→0<v→
      ca*v ≤ a→c₀*W^3/Real.log (n:ℝ) ≤ D→(n:ℝ)^(-(1:ℝ)/6+m) ≤ r→
      OrderedSteps a
        (pre++(clockSteps as (fun j=>restFiniteVariance n (qD j))).drop (nativeObservedPairSplit c p))→
    ∀ (P : Type) [MeasurableSpace P] (μ : Measure P) [IsFiniteMeasure μ]
      (xE xD : P→RestCoordinate n→ℝ) (hxE : Measurable xE) (_hxD : Measurable xD)
      (d : Fin pre.length→ℝ),
      (∀ j,0 ≤ d j)→(∑ j,d j=D)→
      (∀ j i,(hierarchyClocks pre j (Sum.inl i):ℝ)=d j)→
      (∫ z,E.expect (restWeight n) (restFeature n) qE (fun σ=>|H σ|^8) (xE z) ∂μ) ≤ pH^8→
      physicalOverlapMoment n 2 (clockSteps es (fun j=>restFiniteVariance n (qE j))) μ
        (fun z=>restFiniteState n (xE z)) ((restFiniteState_measurable n).comp hxE) 0 ≤ sj^4→
      (∫ z,nativeObservedExteriorProjectionFourth n T c E H s qE qD (xE z) (xD z) p ∂μ) ≤
        ((n:ℝ)/(n+1 : ℕ))^4*
          (2*(n:ℝ)^(-delta)*pH*savedWeightedExteriorScale r W v sj)^4 := by
  filter_upwards [eventually_physical_weighted_exterior_resampling_from_primitives 0 B ca c₀
    hca hc₀ hgap,eventually_gt_atTop (0:ℕ)] with n hphysical hn
  intro as es aD aE hoD hoE T c E H s qE qD p hst pre skip a D pH sj r W v hprefix
    ha hD hDB hpH hsj hr hW hv hmass hclock hlow hpre P _ μ _ xE xD hxE hxD d hd hdD hdclock hH hraw
  let steps:=clockSteps as (fun j=>restFiniteVariance n (qD j))
  let ext:=clockSteps es (fun j=>restFiniteVariance n (qE j))
  let R:=fun z=>restFiniteState n (xD z)
  let RE:=fun z=>restFiniteState n (xE z)
  have hR : Measurable R:=(restFiniteState_measurable n).comp hxD
  have hRE : Measurable RE:=(restFiniteState_measurable n).comp hxE
  let E':=E.realize (fun j=>restFiniteVariance n (qE j))
  let H':=fun σ=>H ((E.assignmentEquiv (fun j=>restFiniteVariance n (qE j))).symm σ)
  let s':=E.slotEquiv (fun j=>restFiniteVariance n (qE j)) s
  let tail:=steps.drop (nativeObservedPairSplit c p)
  have hs : OrderedSteps aD ((skip++pre)++tail) := by
    rw [←hprefix]
    simpa only [tail,steps,List.take_append_drop] using clockSteps_ordered hoD
      (fun j=>restFiniteVariance n (qD j))
  have hH' : (∫ z,E'.expect (uniformWeight n) (finiteFeature n)
      (fun σ=>|H' σ|^8) (RE z) ∂μ) ≤ pH^8 := by
    simpa only [restFinite_clockTree_expect n hn,ClockTree.expect_realize] using hH
  rw [native_observed_exterior_fourth_eq_physical_resampling n hn hoD T c hoE E H s
    qE qD μ xE xD hxE hxD p hst,hprefix]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have he:=hphysical P ext E' H' s' tail pre skip a aD aE D pH sj r W v
    ha hD hDB hpH hsj hr hW hv hmass hclock hlow hpre hs (clockSteps_ordered hoE _)
    μ RE R hRE hR d hd hdD hdclock hH' hraw
  simpa only [show 0+1=1 by norm_num,show 8*1=8 by norm_num,
    show 2*1=2 by norm_num,show 4*1=4 by norm_num] using he

theorem native_observed_gamma_abs_le_clock (n : ℕ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho0 : MassOrdered 0 as)
    (U : ℕ) (hU0 : 0<U) (K : ℕ→ℝ) (hK : Monotone K) (hK0 : ∀ j,0 ≤ K j)
    (c : T.Slot) (p : ClockTree.MarkedPlacement T) (hnon : p.embed c≠p.mark)
    {C v : ℝ} (hclock : relocatedClock U 0 K (p.tree.splitIndex (p.embed c) p.mark) ≤ C*v) :
    |fullScalarCutGamma p.tree U K (p.embed c) p.mark| ≤ C*v := by
  have hm:=relocatedClock_monotone U (show (0:ℝ)∈Icc 0 1 by norm_num) hK hK0
  have hz : relocatedClock U 0 K 0=0 := by simp [relocatedClock,hU0]
  have hneq : p.tree.cavityRightSlot (p.embed c)≠p.tree.cavityRightSlot p.mark :=
    fun h=>hnon ((p.tree.cavityRightSlot).injective h)
  have hh:=actual_scalar_distinct_pair_abs_le p.tree.cavityRight ho0
    (relocatedClock U 0 K) hm hz _ _ hneq (by
      simpa only [p.tree.splitIndex_cavityRight] using hclock)
  simpa only [fullScalarCutGamma,fullScalarCutMoment,scalarCutMoment,List.map_cons,List.map_nil,
    ClockTree.slotProduct,scalarFeature_apply_spin,mul_one,one_mul,Pi.zero_def] using hh

theorem observed_weighted_scale_at_W {r W v : ℝ}
    (hr : 0 ≤ r) (hW : 0<W) (hv : 0<v) :
    savedWeightedExteriorScale r W v W=savedProjectedScale r W v := by
  have hs := savedWeightedExteriorScale_sq hW hW.le (x:=r) (v:=v)
  have ht := savedProjectedScale_sq r W v
  have he : savedWeightedExteriorScale r W v W^2=savedProjectedScale r W v^2 := by
    rw [hs,ht]
    field_simp
  have h₁ : 0 ≤ savedWeightedExteriorScale r W v W := by
    unfold savedWeightedExteriorScale
    positivity
  have h₂ : 0 ≤ savedProjectedScale r W v := by
    unfold savedProjectedScale
    positivity
  nlinarith

theorem native_observed_exterior_fourth_coincidence_zero (n : ℕ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (c : T.Slot)
    {es : List PositiveMass} (E : ClockTree (Spin n) es) (H : E.Assignment→ℝ) (s : E.Slot)
    (qE qD : ℕ→RestCoordinate n→ℝ≥0) (xE xD : RestCoordinate n→ℝ)
    (p : ClockTree.MarkedPlacement T) (hdiag : p.embed c=p.mark) :
    nativeObservedExteriorProjectionFourth n T c E H s qE qD xE xD p=0 := by
  have he σ : T.cavityLeft.atSlot (p.restRestrict σ) (T.cavityLeftSlot c)=p.restSpin σ := by
    rw [p.restRestrict_at σ c,hdiag]
    rfl
  unfold nativeObservedExteriorProjectionFourth nativeObservedExteriorProjectionDifference ClockTree.expect
  simp only [he,sub_self,inner_zero_left,zero_pow (by norm_num : (4:ℕ)≠0),
    mul_zero,Finset.sum_const_zero]

theorem native_observed_gamma_fourth_denominator_cancellation (n : ℕ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho0 : MassOrdered 0 as)
    (U : ℕ) (hU0 : 0<U) (K : ℕ→ℝ) (hK : Monotone K) (hK0 : ∀ j,0 ≤ K j)
    (c : T.Slot) (p : ClockTree.MarkedPlacement T) (hnon : p.embed c≠p.mark)
    {X C v r W sj t pH : ℝ} (hv : 0<v) (hW : 0<W)
    (hclock : relocatedClock U 0 K (p.tree.splitIndex (p.embed c) p.mark) ≤ C*v)
    (hX : X ≤ ((n:ℝ)/(n+1 : ℕ))^4*(2*t*pH*savedWeightedExteriorScale r W v sj)^4) :
    fullScalarCutGamma p.tree U K (p.embed c) p.mark^4*X ≤
      ((n:ℝ)/(n+1 : ℕ))^4*(2*t*pH*C*(r^3*Real.sqrt sj/Real.sqrt (W^3)))^4 := by
  have hg := native_observed_gamma_abs_le_clock n T ho0 U hU0 K hK hK0 c p hnon hclock
  have hg4 : fullScalarCutGamma p.tree U K (p.embed c) p.mark^4 ≤ (C*v)^4 := by
    simpa only [(show Even 4 by decide).pow_abs] using pow_le_pow_left₀ (abs_nonneg _) hg 4
  have hs : v*savedWeightedExteriorScale r W v sj=r^3*Real.sqrt sj/Real.sqrt (W^3) := by
    unfold savedWeightedExteriorScale
    field_simp [hv.ne',ne_of_gt (Real.sqrt_pos.2 (pow_pos hW 3))]
  calc
    _ ≤ fullScalarCutGamma p.tree U K (p.embed c) p.mark^4*
        (((n:ℝ)/(n+1 : ℕ))^4*(2*t*pH*savedWeightedExteriorScale r W v sj)^4) :=
      mul_le_mul_of_nonneg_left hX (by positivity)
    _ ≤ (C*v)^4*(((n:ℝ)/(n+1 : ℕ))^4*(2*t*pH*savedWeightedExteriorScale r W v sj)^4) :=
      mul_le_mul_of_nonneg_right hg4 (by positivity)
    _=((n:ℝ)/(n+1 : ℕ))^4*(2*t*pH*C*(v*savedWeightedExteriorScale r W v sj))^4 := by ring
    _=_ := by rw [hs]

end OAI.SKFluctuations.Cavity
