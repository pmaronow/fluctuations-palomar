module

public import ComparisonSignedCavityActualGroupedLayers
public import ComparisonSignedCavityActualBoundaryLayerBudget
public import ComparisonSignedCavityActualMinimumResampling
public import ComparisonSignedCavityGeneratedTestAncestry
public import ComparisonSignedCavityRetainedSubtreeClone

@[expose] public section

noncomputable section
set_option maxHeartbeats 3000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy
variable {ι S : Type} [Fintype ι] [Fintype S] [Nonempty S] [DecidableEq S]

def jointActualIndexedCutLayerFold (w : S→ℝ) (φ : S→(ι→ℝ)→L[ℝ]ℝ) :
    {steps : List (GaussianStep ι)} → (T : ReplicaTree ι S steps) →
      ℕ → ℝ → ℝ → ℝ → (T.Assignment→S→ℝ) → (ι→ℝ) → ℝ
  | _, T, 0, a, v, z, H, x =>
      jointActualCutRow T w φ a z H x-jointActualCutRow T w φ a v H x
  | _, .leaf, _+1, a, v, z, H, x =>
      jointActualCutRow (.leaf : ReplicaTree ι S []) w φ a z H x-
        jointActualCutRow (.leaf : ReplicaTree ι S []) w φ a v H x
  | _, @ReplicaTree.step _ _ st tail T, k+1, _, v, z, H, x =>
      shiftedMean (Measure.pi (fun i=>gaussianReal 0 (st.2 i))) st.1
        (gaussianHierarchy w φ tail) (jointActualIndexedCutLayerFold w φ T k st.1 v z H) x
  | _, .fork T U, k+1, a, v, z, H, x =>
      U.expect w φ (fun τ=>jointActualIndexedCutLayerFold w φ T (k+1) a v z
        (fun σ s=>H (σ,τ) s) x) x+
      T.expect w φ (fun σ=>jointActualIndexedCutLayerFold w φ U (k+1) a v z
        (fun τ s=>H (σ,τ) s) x) x

theorem jointActualIndexedCutLayerFold_eq_original {steps : List (GaussianStep ι)}
    {w : S→ℝ} (hw : ∀ σ,0<w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    (T : ReplicaTree ι S steps) (k : ℕ) {a v z : ℝ}
    (ho : OrderedSteps a steps) (hk : k ≤ steps.length)
    (hprefix : ∀ st∈steps.take k,st.1 ≤ v) (hvz : v ≤ z)
    (H : T.Assignment→S→ℝ) (x : ι→ℝ) :
    jointActualIndexedCutLayerFold w φ T k a v z H x =
      jointActualCutRow T w φ a z H x-jointActualCutRow T w φ a v H x := by
  induction T generalizing k a x with
  | leaf =>
    have hk0 : k=0 := by simpa using hk
    subst k
    rfl
  | @step st tail T ih =>
    cases k with
    | zero => rfl
    | succ k =>
      have hst : st.1 ≤ v := hprefix st (by simp)
      have hk' : k ≤ tail.length := by simpa only [List.length_cons,Nat.succ_le_succ_iff] using hk
      have hp' : ∀ r∈tail.take k,r.1 ≤ v := by
        intro r hr
        exact hprefix r (by simpa only [List.take_succ_cons,List.mem_cons] using Or.inr hr)
      change shiftedMean _ st.1 (gaussianHierarchy w φ tail)
        (jointActualIndexedCutLayerFold w φ T k st.1 v z H) x = _
      have he : jointActualIndexedCutLayerFold w φ T k st.1 v z H =
          fun y=>jointActualCutRow T w φ st.1 z H y-jointActualCutRow T w φ st.1 v H y :=
        funext fun y=>ih k ho.2.2.2 hk' hp' H y
      rw [he]
      exact (jointActualCutLayer_shared_step hw φ T st.1 st.2 ho hst hvz H x).symm
  | fork T U ihT ihU =>
    cases k with
    | zero => rfl
    | succ k =>
      change U.expect w φ (fun τ=>jointActualIndexedCutLayerFold w φ T (k+1) a v z
          (fun σ s=>H (σ,τ) s) x) x+
        T.expect w φ (fun σ=>jointActualIndexedCutLayerFold w φ U (k+1) a v z
          (fun τ s=>H (σ,τ) s) x) x = _
      simp_rw [ihT (k+1) ho hk hprefix,ihU (k+1) ho hk hprefix]
      exact (jointActualCutLayer_fork hw φ T U ho v z H x).symm

def actualIndexedCutLayerFold (w : S→ℝ) (φ : S→(ι→ℝ)→L[ℝ]ℝ) :
    {steps : List (GaussianStep ι)} → (T : ReplicaTree ι S steps) →
      ℕ → ℝ → ℝ → ℝ → (T.Assignment→ℝ) → (S→ℝ) → (ι→ℝ) → ℝ
  | _, T, 0, a, v, z, P, F, x => actualCutRow T w φ a z P F x-actualCutRow T w φ a v P F x
  | _, .leaf, _+1, a, v, z, P, F, x =>
      actualCutRow (.leaf : ReplicaTree ι S []) w φ a z P F x-
        actualCutRow (.leaf : ReplicaTree ι S []) w φ a v P F x
  | _, @ReplicaTree.step _ _ st tail T, k+1, _, v, z, P, F, x =>
      shiftedMean (Measure.pi (fun i=>gaussianReal 0 (st.2 i))) st.1
        (gaussianHierarchy w φ tail) (actualIndexedCutLayerFold w φ T k st.1 v z P F) x
  | _, .fork T U, k+1, a, v, z, P, F, x =>
      U.expect w φ (fun τ=>actualIndexedCutLayerFold w φ T (k+1) a v z
        (fun σ=>P (σ,τ)) F x) x+
      T.expect w φ (fun σ=>actualIndexedCutLayerFold w φ U (k+1) a v z
        (fun τ=>P (σ,τ)) F x) x

theorem actualIndexedCutLayerFold_eq_original {steps : List (GaussianStep ι)}
    {w : S→ℝ} (hw : ∀ σ,0<w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    (T : ReplicaTree ι S steps) (k : ℕ) {a v z : ℝ}
    (ho : OrderedSteps a steps) (hk : k ≤ steps.length)
    (hprefix : ∀ st∈steps.take k,st.1 ≤ v) (hvz : v ≤ z)
    (P : T.Assignment→ℝ) (F : S→ℝ) (x : ι→ℝ) :
    actualIndexedCutLayerFold w φ T k a v z P F x =
      actualCutRow T w φ a z P F x-actualCutRow T w φ a v P F x := by
  induction T generalizing k a x with
  | leaf =>
    have hk0 : k=0 := by simpa using hk
    subst k
    rfl
  | @step st tail T ih =>
    cases k with
    | zero => rfl
    | succ k =>
      have hst : st.1 ≤ v := hprefix st (by simp)
      have hk' : k ≤ tail.length := by simpa only [List.length_cons,Nat.succ_le_succ_iff] using hk
      have hp' : ∀ r∈tail.take k,r.1 ≤ v := by
        intro r hr
        exact hprefix r (by simpa only [List.take_succ_cons,List.mem_cons] using Or.inr hr)
      change shiftedMean _ st.1 (gaussianHierarchy w φ _)
        (actualIndexedCutLayerFold w φ T k st.1 v z P F) x = _
      have he : actualIndexedCutLayerFold w φ T k st.1 v z P F =
          fun y=>actualCutRow T w φ st.1 z P F y-actualCutRow T w φ st.1 v P F y :=
        funext fun y=>ih k ho.2.2.2 hk' hp' P y
      rw [he]
      exact (actual_cut_layer_shared_step hw φ T st.1 st.2 ho hst hvz P F x).symm
  | fork T U ihT ihU =>
    cases k with
    | zero => rfl
    | succ k =>
      change U.expect w φ (fun τ=>actualIndexedCutLayerFold w φ T (k+1) a v z
          (fun σ=>P (σ,τ)) F x) x+
        T.expect w φ (fun σ=>actualIndexedCutLayerFold w φ U (k+1) a v z
          (fun τ=>P (σ,τ)) F x) x = _
      simp_rw [ihT (k+1) ho hk hprefix,ihU (k+1) ho hk hprefix]
      exact (actual_cut_layer_fork hw φ T U ho v z P F x).symm

theorem nativeCutMarkedAttach_variation_le {as : List PositiveMass}
    (T : ClockTree S as) {a v : ℝ} (ho : MassOrdered a as) (hav : a ≤ v)
    (q : ℕ→ι→ℝ≥0) :
    ((T.nativeCutMarkedAttach a v).map (fun p=>|p.coeff|)).sum ≤
      2*(T.leaves:ℝ)*v-a := by
  have H := (T.realize q).cutMarkedAttach_variation_le (clockSteps_ordered ho q) hav
  rw [←T.nativeCutMarkedAttach_realize a v q] at H
  simpa only [List.map_map,Function.comp_def,ClockTree.MarkedPlacement.realize,
    ClockTree.realize_leaves] using H

theorem nativeCutMarkedAttach_layer_variation_le {as : List PositiveMass}
    (T : ClockTree S as) {a v z : ℝ} (ho : MassOrdered a as)
    (hav : a ≤ v) (hvz : v ≤ z) (hz : z ≤ 2*v) (q : ℕ→ι→ℝ≥0) :
    ((T.nativeCutMarkedAttach a v).map (fun p=>|p.coeff|)).sum+
      ((T.nativeCutMarkedAttach a z).map (fun p=>|p.coeff|)).sum ≤
      6*(T.leaves:ℝ)*v := by
  have H := (T.realize q).cutMarkedAttach_layer_variation_le (clockSteps_ordered ho q)
    hav hvz hz
  rw [←T.nativeCutMarkedAttach_realize a v q,←T.nativeCutMarkedAttach_realize a z q] at H
  simpa only [List.map_map,Function.comp_def,ClockTree.MarkedPlacement.realize,
    ClockTree.realize_leaves] using H

def nativeIndexedCutLayerFold {as : List PositiveMass} (T : ClockTree S as)
    (w : S→ℝ) (φ : S→(ι→ℝ)→L[ℝ]ℝ) (k : ℕ) (a v z : ℝ)
    (q : ℕ→ι→ℝ≥0) (P : T.Assignment→ℝ) (F : S→ℝ) (x : ι→ℝ) : ℝ :=
  actualIndexedCutLayerFold w φ (T.realize q) k a v z
    (fun σ=>P ((T.assignmentEquiv q).symm σ)) F x

theorem nativeIndexedCutLayerFold_eq_original {as : List PositiveMass}
    {w : S→ℝ} (hw : ∀ σ,0<w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    (T : ClockTree S as) (k : ℕ) {a v z : ℝ} (ho : MassOrdered a as)
    (q : ℕ→ι→ℝ≥0) (hk : k ≤ as.length)
    (hprefix : ∀ st∈(clockSteps as q).take k,st.1 ≤ v) (hvz : v ≤ z)
    (P : T.Assignment→ℝ) (F : S→ℝ) (x : ι→ℝ) :
    nativeIndexedCutLayerFold T w φ k a v z q P F x =
      nativeJointActualCutRow T w φ a z q (fun σ s=>P σ*F s) x-
        nativeJointActualCutRow T w φ a v q (fun σ s=>P σ*F s) x := by
  rw [nativeJointActualCutRow_eq_realized,nativeJointActualCutRow_eq_realized]
  change actualIndexedCutLayerFold w φ (T.realize q) k a v z
      (fun σ=>P ((T.assignmentEquiv q).symm σ)) F x =
    actualCutRow (T.realize q) w φ a z (fun σ=>P ((T.assignmentEquiv q).symm σ)) F x-
      actualCutRow (T.realize q) w φ a v (fun σ=>P ((T.assignmentEquiv q).symm σ)) F x
  exact actualIndexedCutLayerFold_eq_original hw φ (T.realize q) k
    (clockSteps_ordered ho q) (by simpa only [length_clockSteps] using hk)
    hprefix hvz _ F x

def nativeJointIndexedCutLayerFold {as : List PositiveMass} (T : ClockTree S as)
    (w : S→ℝ) (φ : S→(ι→ℝ)→L[ℝ]ℝ) (k : ℕ) (a v z : ℝ)
    (q : ℕ→ι→ℝ≥0) (H : T.Assignment→S→ℝ) (x : ι→ℝ) : ℝ :=
  jointActualIndexedCutLayerFold w φ (T.realize q) k a v z
    (fun σ s=>H ((T.assignmentEquiv q).symm σ) s) x

theorem nativeJointIndexedCutLayerFold_eq_original {as : List PositiveMass}
    {w : S→ℝ} (hw : ∀ σ,0<w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    (T : ClockTree S as) (k : ℕ) {a v z : ℝ} (ho : MassOrdered a as)
    (q : ℕ→ι→ℝ≥0) (hk : k ≤ as.length)
    (hprefix : ∀ st∈(clockSteps as q).take k,st.1 ≤ v) (hvz : v ≤ z)
    (H : T.Assignment→S→ℝ) (x : ι→ℝ) :
    nativeJointIndexedCutLayerFold T w φ k a v z q H x =
      nativeJointActualCutRow T w φ a z q H x-nativeJointActualCutRow T w φ a v q H x := by
  rw [nativeJointActualCutRow_eq_realized,nativeJointActualCutRow_eq_realized]
  exact jointActualIndexedCutLayerFold_eq_original hw φ (T.realize q) k
    (clockSteps_ordered ho q) (by simpa only [length_clockSteps] using hk)
    hprefix hvz _ x

theorem actual_original_retained_two_forest_response_eq (n U a d : ℕ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (b h : ℕ→ℝ) (t : ℝ) (P : ActualMixedBoundaryForest n a T b h)
    (F : ActualMixedBoundaryForest n d T b h) (target : T.Slot) (cut : ℕ)
    (houtP : ∀e,T.splitIndex target (P.i e)<cut)
    (houtF : ∀e,T.splitIndex target (F.i e)<cut) :
    zeroContinuation (Measure.pi fun i=>gaussianReal 0
      (Real.toNNReal (finitePhysicalCavityVariance n U as b h t 0 i)))
      (ClockTree.nativeRetainedCloneCutMean (fullWeight n) (fullFeature n) T target cut
        (cumulativeIncrements (finitePhysicalCavityVariance n U as b h t 0)
          (fun k=>finitePhysicalCavityVariance n U as b h t (k+1)))
        (fun σ τ=>(P.product σ-P.product τ)*(F.product σ-F.product τ))) 0 =
      (ClockTree.nativeCloneBlockAtSlot T target cut).tree.disorderExpect
        (fullWeight n) (fullFeature n) 0 (finitePhysicalCavityVariance n U as b h t)
        (fun σ=>(P.cloneAt target cut houtP).difference σ*
          (F.cloneAt target cut houtF).difference σ) 0 := by
  have H := ClockTree.nativeRetainedCloneCut_disorderLaw (fullWeight_pos n) (fullFeature n)
    T ho target cut 0 (finitePhysicalCavityVariance n U as b h t)
    (fun σ τ=>(P.product σ-P.product τ)*(F.product σ-F.product τ)) 0
  simp only [Pi.zero_apply,sub_zero] at H
  rw [H]
  congr 1
  funext σ
  rw [actual_cloned_boundary_forest_difference_eq P target cut houtP σ,
    actual_cloned_boundary_forest_difference_eq F target cut houtF σ]

theorem actual_original_retained_two_forest_response_sq_le (n U a d : ℕ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (b h : ℕ→ℝ) (t : ℝ) (P : ActualMixedBoundaryForest n a T b h)
    (F : ActualMixedBoundaryForest n d T b h) (target : T.Slot) (cut : ℕ)
    (houtP : ∀e,T.splitIndex target (P.i e)<cut)
    (houtF : ∀e,T.splitIndex target (F.i e)<cut) (sP sF : ℝ)
    (hP : zeroContinuation (Measure.pi fun i=>gaussianReal 0
      (Real.toNNReal (finitePhysicalCavityVariance n U as b h t 0 i)))
      (ClockTree.nativeRetainedCloneCutMean (fullWeight n) (fullFeature n) T target cut
        (cumulativeIncrements (finitePhysicalCavityVariance n U as b h t 0)
          (fun k=>finitePhysicalCavityVariance n U as b h t (k+1)))
        (fun σ τ=>(P.product σ-P.product τ)^2)) 0 ≤ sP^2)
    (hF : zeroContinuation (Measure.pi fun i=>gaussianReal 0
      (Real.toNNReal (finitePhysicalCavityVariance n U as b h t 0 i)))
      (ClockTree.nativeRetainedCloneCutMean (fullWeight n) (fullFeature n) T target cut
        (cumulativeIncrements (finitePhysicalCavityVariance n U as b h t 0)
          (fun k=>finitePhysicalCavityVariance n U as b h t (k+1)))
        (fun σ τ=>(F.product σ-F.product τ)^2)) 0 ≤ sF^2) :
    (zeroContinuation (Measure.pi fun i=>gaussianReal 0
      (Real.toNNReal (finitePhysicalCavityVariance n U as b h t 0 i)))
      (ClockTree.nativeRetainedCloneCutMean (fullWeight n) (fullFeature n) T target cut
        (cumulativeIncrements (finitePhysicalCavityVariance n U as b h t 0)
          (fun k=>finitePhysicalCavityVariance n U as b h t (k+1)))
        (fun σ τ=>(P.product σ-P.product τ)*(F.product σ-F.product τ))) 0)^2 ≤
          (sP*sF)^2 := by
  rw [actual_original_retained_two_forest_response_eq n U a d T ho b h t P F target cut houtP houtF]
  rw [actual_original_cloned_boundary_forest_moment_eq n U a T ho b h t P target cut houtP] at hP
  rw [actual_original_cloned_boundary_forest_moment_eq n U d T ho b h t F target cut houtF] at hF
  exact actual_full_two_forest_expectation_sq_le n U a d
    (ClockTree.nativeCloneBlockAtSlot T target cut).tree ho b h t
    (P.cloneAt target cut houtP) (F.cloneAt target cut houtF) sP sF hP hF

theorem eventually_actual_minimum_two_forest_retained_response
    (a : ℕ) (ha : 0 < a) (Bclock ce Rmacro F exponent Cb Cr Cc c BW : ℝ)
    {m delta eta cl cu Az C0 Ct D0 : ℝ}
    (hm : 0  <  m) (hdelta : 0  <  delta) (hroom : delta  <  3*m) (hgap : 2*eta  <  6*m)
    (hsitegap : eta < 1/2+3*m) (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az)
    (hC0 : 0 < C0) (hCt : 0 ≤ Ct) (hce : 0 < ce) (hmacro : 0 < Rmacro)
    (hRhalf : Rmacro ≤ 1/2) (hFmass : 1+2*cu ≤ F) (hFradius : 1+1/Rmacro ≤ F)
    (hCb : 0 ≤ Cb) (hCr : 0 ≤ Cr) (hCc : 0 ≤ Cc) (hc : 0 < c) (hBW : 0 < BW) :
    ∀ᶠ n : ℕ in atTop,
    ∀ M : LaplaceWindowFormalization.NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D0 Bclock,
    ∀ (u : PositiveMass),u.val ≤ 1  →
    ∀ (extra : List PositiveMass),(∀v∈extra,v.val ≤ 1)  →
    ∃ us : List PositiveMass,(∀v∈us,v.val ≤ 1) ∧ u∈us ∧ (∀v∈extra,v∈us) ∧
      ∀ᶠ j : ℕ in atTop,
        let as:=finiteCutMasses us j
        let steps:=sampleClockSteps (completedPathClock (n+1) M.bf M.hf) 0 as
        let Q:=stepClockValues (fun i=>(completedPathClock (n+1) M.bf M.hf 0 i:ℝ)) steps
        ∀ (b h : ℕ → ℝ),Q = physicalCompletedClock (n+1) b h  →
          Monotone b  →  Monotone h  →  (∀z,0 ≤ b z)  →  (∀z,0 ≤ h z)  →
        ∀ (U : ℕ) (T : ClockTree (Spin n×Bool) as) (t : ℝ),t∈Icc (0:ℝ) 1  →
        ∀ (P G : ActualMixedBoundaryForest n a T b h) (target : T.Slot) (cut : ℕ),
          (∀e,T.splitIndex target (P.i e) < cut) →
          (∀e,T.splitIndex target (G.i e) < cut) → cut ≤ as.length →
        ∀ (s W r scaleP scale : ℝ),0 < s → 0 < W → 0 < r →
          0 < scaleP → 0 < scale →
          W ≤ s  →  M.xs ≤ s  →  M.z ≤ s/2  →  2*s ≤ Rmacro  →  W ≤ BW  →
          ((n+1:ℕ):ℝ)^(-exponent) ≤ s  →  ((n+1:ℕ):ℝ)^(-(1:ℝ)/6+m) ≤ r  →
          ce*W^2 ≤ LaplaceWindowFormalization.laplaceComparisonStrength M.context.d M.lam W  →
          0 < partitionPoint 0 as cut  →  partitionPoint 0 as cut ≤ 1  →
          M.R (partitionPoint 0 as cut) = 4*s  →
          (∀e,cut ≤ T.splitIndex target (P.j e) →
            M.R (partitionPoint 0 as (T.splitIndex (P.i e) (P.j e))) ≤ s/2) →
          (∀e,cut ≤ T.splitIndex target (G.j e)  →
            M.R (partitionPoint 0 as (T.splitIndex (G.i e) (G.j e))) ≤ s/2)  →
          (∀e,|P.β e| ≤ Cb) → (∀e,|G.β e| ≤ Cb) →
          nativeBoundaryRowFactor n (ClockTree.nativeCloneBlockAtSlot T target cut).tree b h ≤ Cr  →
          nativeBoundaryCompletionFactor n (ClockTree.nativeCloneBlockAtSlot T target cut).tree b ≤ Cc  →
          (∀e,c*scaleP ≤ P.rho e) → (∀e,c*scale ≤ G.rho e) →
          |zeroContinuation (Measure.pi fun i=>gaussianReal 0
            (Real.toNNReal (finitePhysicalCavityVariance n U as b h t 0 i)))
            (ClockTree.nativeRetainedCloneCutMean (fullWeight n) (fullFeature n) T target cut
              (cumulativeIncrements (finitePhysicalCavityVariance n U as b h t 0)
                (fun k=>finitePhysicalCavityVariance n U as b h t (k+1)))
              (fun σ τ=>(P.product σ-P.product τ)*(G.product σ-G.product τ))) 0| ≤
            ((a:ℝ)*(actualBoundaryScalarConstant Cb Cr Cc c*
              ((n+1:ℕ):ℝ)^(-eta)*savedExteriorScale r W (partitionPoint 0 as cut)/scaleP)*
              (∏e,P.rho e))*
            ((a:ℝ)*(actualBoundaryScalarConstant Cb Cr Cc c*
              ((n+1:ℕ):ℝ)^(-eta)*savedExteriorScale r W (partitionPoint 0 as cut)/scale)*
              (∏e,G.rho e)) := by
  filter_upwards [eventually_actual_minimum_boundary_clone_from_bounded_rows
    a ha Bclock ce Rmacro F exponent Cb Cr Cc c BW
    hm hdelta hroom hgap hsitegap hcl hcu hAz hC0 hCt hce hmacro hRhalf
    hFmass hFradius hCb hCr hCc hc hBW] with n hn
  intro M u hu extra hextra
  obtain ⟨us,hus,huus,hextraus,hfinite⟩ := hn M u hu extra hextra
  refine ⟨us,hus,huus,hextraus,?_⟩
  filter_upwards [hfinite] with j hj
  dsimp only at hj ⊢
  intro b h hQ hb hh hb0 hh0 U T t ht P G target cut houtP houtG hcut
    s W r scaleP scale hs hW hr hscaleP hscale hWs hxss hzs hsR hWB hslow hcrit
    hstrength hv hv1 hhigh hlowP hlowG hβP hβG hrow hcompletion hrhoP hrhoG
  have HP := hj b h hQ hb hh hb0 hh0 U T t ht P target cut houtP hcut
    s W r scaleP hs hW hr hscaleP hWs hxss hzs hsR hWB hslow hcrit hstrength
    hv hv1 hhigh hlowP hβP hrow hcompletion hrhoP
  have HG := hj b h hQ hb hh hb0 hh0 U T t ht G target cut houtG hcut
    s W r scale hs hW hr hscale hWs hxss hzs hsR hWB hslow hcrit hstrength
    hv hv1 hhigh hlowG hβG hrow hcompletion hrhoG
  have H := actual_original_retained_two_forest_response_sq_le n U a a T
    (finiteCutMasses_ordered us hus j) b h t P G target cut houtP houtG _ _ HP HG
  have hsave : 0 ≤ ((n+1:ℕ):ℝ)^(-eta)*savedExteriorScale r W (partitionPoint 0 (finiteCutMasses us j) cut) := by
    unfold savedExteriorScale
    positivity
  have hconst : 0 ≤ actualBoundaryScalarConstant Cb Cr Cc c := by
    unfold actualBoundaryScalarConstant
    positivity
  have hP0 : 0 ≤ (a:ℝ)*(actualBoundaryScalarConstant Cb Cr Cc c*
      ((n+1:ℕ):ℝ)^(-eta)*savedExteriorScale r W (partitionPoint 0 (finiteCutMasses us j) cut)/scaleP)*
      (∏e,P.rho e) := by
    apply mul_nonneg
    · apply mul_nonneg (Nat.cast_nonneg a)
      apply div_nonneg _ hscaleP.le
      simpa only [mul_assoc] using mul_nonneg hconst hsave
    · exact Finset.prod_nonneg fun e _=>(P.rhoPos e).le
  have hG0 : 0 ≤ (a:ℝ)*(actualBoundaryScalarConstant Cb Cr Cc c*
      ((n+1:ℕ):ℝ)^(-eta)*savedExteriorScale r W (partitionPoint 0 (finiteCutMasses us j) cut)/scale)*
      (∏e,G.rho e) := by
    apply mul_nonneg
    · apply mul_nonneg (Nat.cast_nonneg a)
      apply div_nonneg _ hscale.le
      simpa only [mul_assoc] using mul_nonneg hconst hsave
    · exact Finset.prod_nonneg fun e _=>(G.rhoPos e).le
  exact (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hP0 hG0)).mp (by simpa only [sq_abs] using H)

end OAI.SKFluctuations.Cavity
