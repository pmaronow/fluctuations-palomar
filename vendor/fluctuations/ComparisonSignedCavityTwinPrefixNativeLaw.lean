module

public import ComparisonSignedCavityTwinPrefixRootLaw
public import ComparisonSignedCavityExteriorForestNativeLaw

@[expose] public section

noncomputable section
set_option maxHeartbeats 8000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree
variable {ι S : Type} [Fintype ι] [Fintype S] [Nonempty S]

def nativeTwinForestTree (pre mid : List PositiveMass) {tail : List PositiveMass}
    (A : ClockTree S (mid ++ tail)) (B D : ClockTree S tail) :
    ClockTree S (pre ++ (mid ++ tail)) :=
  exteriorPrepend pre (A.fork ((exteriorPrepend mid B).fork (exteriorPrepend mid D)))

def nativeTwinForestRead (pre mid : List PositiveMass) {tail : List PositiveMass}
    (A : ClockTree S (mid ++ tail)) (B D : ClockTree S tail)
    (Q : A.Assignment → B.Assignment → D.Assignment → ℝ) :
    (nativeTwinForestTree pre mid A B D).Assignment → ℝ :=
  fun σ =>
    let z := exteriorPrependAssignmentEquiv pre
      (A.fork ((exteriorPrepend mid B).fork (exteriorPrepend mid D))) σ
    Q z.1 (exteriorPrependAssignmentEquiv mid B z.2.1)
      (exteriorPrependAssignmentEquiv mid D z.2.2)

def nativeTwinForestConditionalTest {ias tas : List PositiveMass}
    (A : ClockTree S ias) (B D : ClockTree S tas) (w : S → ℝ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (qi qs : ℕ → ι → ℝ≥0)
    (Q : A.Assignment → B.Assignment → D.Assignment → ℝ)
    (xi xB xD : ι → ℝ) : ℝ :=
  A.expect w φ qi (fun η =>
    B.expect w φ qs (fun β => D.expect w φ qs (Q η β) xD) xB) xi

theorem nativeTwinForestConditionalTest_smooth_joint
    {ias tas : List PositiveMass} (A : ClockTree S ias) (B D : ClockTree S tas)
    {w : S → ℝ} (hw : ∀ σ, 0 < w σ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {ai ast : ℝ} (hoi : MassOrdered ai ias) (hot : MassOrdered ast tas)
    (qi qs : ℕ → ι → ℝ≥0)
    (Q : A.Assignment → B.Assignment → D.Assignment → ℝ) (r : ℕ) :
    BddSmooth r (fun z : ((ι → ℝ) × (ι → ℝ)) × (ι → ℝ) =>
      nativeTwinForestConditionalTest A B D w φ qi qs Q z.1.1 z.1.2 z.2) := by
  unfold nativeTwinForestConditionalTest ClockTree.expect
  apply BddSmooth.sum Finset.univ
  intro η _
  apply BddSmooth.mul
  · exact (A.weight_smooth hw φ hoi qi η r).compCLM
      ((ContinuousLinearMap.fst ℝ (ι → ℝ) (ι → ℝ)).comp
        (ContinuousLinearMap.fst ℝ ((ι → ℝ) × (ι → ℝ)) (ι → ℝ)))
  · apply BddSmooth.sum Finset.univ
    intro β _
    apply BddSmooth.mul
    · exact (B.weight_smooth hw φ hot qs β r).compCLM
        ((ContinuousLinearMap.snd ℝ (ι → ℝ) (ι → ℝ)).comp
          (ContinuousLinearMap.fst ℝ ((ι → ℝ) × (ι → ℝ)) (ι → ℝ)))
    · apply BddSmooth.sum Finset.univ
      intro δ _
      exact ((D.weight_smooth hw φ hot qs δ r).compCLM
        (ContinuousLinearMap.snd ℝ ((ι → ℝ) × (ι → ℝ)) (ι → ℝ))).mul_const (Q η β δ)

theorem prefixTest_native_expect_swap {as : List PositiveMass}
    (T : ClockTree S as) {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (q : ℕ → ι → ℝ≥0)
    (mid tail : List (GaussianStep ι)) {a : ℝ} (hs : OrderedSteps a (mid ++ tail))
    (R : T.Assignment → (ι → ℝ) → ℝ) (hR : ∀ σ, BddSmooth 0 (R σ))
    (x y : ι → ℝ) :
    prefixTest mid (gaussianHierarchy w φ tail)
      (fun z => T.expect w φ q (fun σ => R σ z) x) y =
      T.expect w φ q (fun σ => prefixTest mid (gaussianHierarchy w φ tail) (R σ) y) x := by
  change prefixTest mid (gaussianHierarchy w φ tail)
    (fun z => ∑ σ, T.weight w φ q σ x * R σ z) y =
      ∑ σ, T.weight w φ q σ x * prefixTest mid (gaussianHierarchy w φ tail) (R σ) y
  rw [prefixTest_fintype_sum hw φ mid tail hs _
    (fun σ => (hR σ).const_mul (T.weight w φ q σ x)) y]
  apply Finset.sum_congr rfl
  intro σ _
  exact prefixTest_scalar_mul mid _ _ _ y

theorem prefixTest_native_twin_expect_swap {as : List PositiveMass}
    (T : ClockTree S as) {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (q : ℕ → ι → ℝ≥0)
    (mid tail : List (GaussianStep ι)) {a : ℝ} (hs : OrderedSteps a (mid ++ tail))
    (R : T.Assignment → (ι → ℝ) → (ι → ℝ) → ℝ)
    (hR : ∀ σ, BddSmooth 0 (fun z : (ι → ℝ) × (ι → ℝ) => R σ z.1 z.2))
    (xi : ι → ℝ) :
    prefixTest mid (gaussianHierarchy w φ tail)
      (fun xB => prefixTest mid (gaussianHierarchy w φ tail)
        (fun xD => T.expect w φ q (fun σ => R σ xB xD) xi) xi) xi =
      T.expect w φ q (fun σ =>
        prefixTest mid (gaussianHierarchy w φ tail)
          (fun xB => prefixTest mid (gaussianHierarchy w φ tail) (R σ xB) xi) xi) xi := by
  have hL := (gaussianHierarchy_regular hw φ tail (hs.suffix mid tail) 0).1.choose_spec
  have hm := fun st hst => hs.mem_pos st (List.mem_append_left tail hst)
  have hSlice (σ : T.Assignment) (xB : ι → ℝ) : BddSmooth 0 (R σ xB) := by
    obtain ⟨K, hK, hb⟩ := (hR σ).bound
    exact ⟨(hR σ).continuous.comp
      (show Continuous (fun xD : ι → ℝ => (xB, xD)) from continuous_const.prodMk continuous_id),
      K, hK, fun xD => hb (xB, xD)⟩
  have he : (fun xB => prefixTest mid (gaussianHierarchy w φ tail)
      (fun xD => T.expect w φ q (fun σ => R σ xB xD) xi) xi) =
      fun xB => T.expect w φ q
        (fun σ => prefixTest mid (gaussianHierarchy w φ tail) (R σ xB) xi) xi := by
    funext xB
    exact prefixTest_native_expect_swap T hw φ q mid tail hs
      (fun σ => R σ xB) (fun σ => hSlice σ xB) xi xi
  rw [he]
  refine prefixTest_native_expect_swap T hw φ q mid tail hs
    (fun σ xB => prefixTest mid (gaussianHierarchy w φ tail) (R σ xB) xi) ?_ xi xi
  intro σ
  have hP := prefixTest_parameter_smooth0 (A := R σ) hL (hR σ) mid hm
  obtain ⟨K, hK, hb⟩ := hP.bound
  exact ⟨hP.continuous.comp
    (show Continuous (fun xB : ι → ℝ => (xB, xi)) from continuous_id.prodMk continuous_const),
    K, hK, fun xB => hb (xB, xi)⟩

def nativeTwinBranchTest {tail : List PositiveMass} (B D : ClockTree S tail)
    (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ) (q : ℕ → ι → ℝ≥0)
    (Q : B.Assignment → D.Assignment → ℝ) (xB xD : ι → ℝ) : ℝ :=
  B.expect w φ q (fun β => D.expect w φ q (Q β) xD) xB

theorem nativeTwinBranchTest_smooth_joint {tail : List PositiveMass}
    (B D : ClockTree S tail) {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {a : ℝ} (ho : MassOrdered a tail)
    (q : ℕ → ι → ℝ≥0) (Q : B.Assignment → D.Assignment → ℝ) (r : ℕ) :
    BddSmooth r (fun z : (ι → ℝ) × (ι → ℝ) => nativeTwinBranchTest B D w φ q Q z.1 z.2) := by
  unfold nativeTwinBranchTest ClockTree.expect
  apply BddSmooth.sum Finset.univ
  intro β _
  apply BddSmooth.mul
  · exact (B.weight_smooth hw φ ho q β r).compCLM
      (ContinuousLinearMap.fst ℝ (ι → ℝ) (ι → ℝ))
  · apply BddSmooth.sum Finset.univ
    intro δ _
    exact ((D.weight_smooth hw φ ho q δ r).compCLM
      (ContinuousLinearMap.snd ℝ (ι → ℝ) (ι → ℝ))).mul_const (Q β δ)

theorem nativeTwinOccupied_expect_eq_prefix (mid : List PositiveMass)
    {tail : List PositiveMass} (B D : ClockTree S tail)
    {w : S → ℝ} (hw : ∀ σ, 0 < w σ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {a : ℝ} (ho : MassOrdered a (mid ++ tail)) (q : ℕ → ι → ℝ≥0)
    (Q : B.Assignment → D.Assignment → ℝ) (xi : ι → ℝ) :
    ((exteriorPrepend mid B).fork (exteriorPrepend mid D)).expect w φ q
      (fun σ => Q (exteriorPrependAssignmentEquiv mid B σ.1)
        (exteriorPrependAssignmentEquiv mid D σ.2)) xi =
      twinPrefixTest w φ (clockSteps mid q)
        (clockSteps tail (fun j => q (mid.length + j)))
        (fun _ xB xD => nativeTwinBranchTest B D w φ
          (fun j => q (mid.length + j)) Q xB xD) xi := by
  rw [ClockTree.expect_fork]
  have hD (β : B.Assignment) := exteriorPrepend_expect mid hw φ D ho q (Q β) xi
  simp_rw [hD]
  have hB := exteriorPrepend_expect mid hw φ B ho q
    (fun β => prefixTest (clockSteps mid q)
      (gaussianHierarchy w φ (clockSteps tail (fun j => q (mid.length + j))))
      (D.expect w φ (fun j => q (mid.length + j)) (Q β)) xi) xi
  rw [hB]
  unfold twinPrefixTest nativeTwinBranchTest
  apply congrArg (fun R => prefixTest (clockSteps mid q)
    (gaussianHierarchy w φ (clockSteps tail (fun j => q (mid.length + j)))) R xi)
  funext xB
  have hoG : OrderedSteps a (clockSteps mid q ++ clockSteps tail (fun j => q (mid.length + j))) := by
    rw [← clockSteps_append]
    exact clockSteps_ordered ho q
  exact (prefixTest_native_expect_swap B hw φ (fun j => q (mid.length + j))
    (clockSteps mid q) _ hoG
    (fun β => D.expect w φ (fun j => q (mid.length + j)) (Q β))
    (fun β => D.nativeAnchor_expect_smooth hw φ ho.suffix_end _ (Q β) 0) xB xi).symm

theorem nativeTwinForestTail_expect_eq_prefix (mid : List PositiveMass)
    {tail : List PositiveMass} (A : ClockTree S (mid ++ tail)) (B D : ClockTree S tail)
    {w : S → ℝ} (hw : ∀ σ, 0 < w σ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {a : ℝ} (ho : MassOrdered a (mid ++ tail)) (q : ℕ → ι → ℝ≥0)
    (Q : A.Assignment → B.Assignment → D.Assignment → ℝ) (xi : ι → ℝ) :
    (A.fork ((exteriorPrepend mid B).fork (exteriorPrepend mid D))).expect w φ q
      (fun σ => Q σ.1 (exteriorPrependAssignmentEquiv mid B σ.2.1)
        (exteriorPrependAssignmentEquiv mid D σ.2.2)) xi =
      twinPrefixTest w φ (clockSteps mid q)
        (clockSteps tail (fun j => q (mid.length + j)))
        (nativeTwinForestConditionalTest A B D w φ q (fun j => q (mid.length + j)) Q) xi := by
  rw [ClockTree.expect_fork]
  have hBranch (η : A.Assignment) := nativeTwinOccupied_expect_eq_prefix
    mid B D hw φ ho q (Q η) xi
  simp_rw [hBranch]
  have hoG : OrderedSteps a (clockSteps mid q ++ clockSteps tail (fun j => q (mid.length + j))) := by
    rw [← clockSteps_append]
    exact clockSteps_ordered ho q
  exact (prefixTest_native_twin_expect_swap A hw φ q (clockSteps mid q) _ hoG
    (nativeTwinBranchTest B D w φ (fun j => q (mid.length + j)) ∘ Q)
    (fun η => nativeTwinBranchTest_smooth_joint B D hw φ ho.suffix_end _ (Q η) 0) xi).symm

theorem nativeTwinForestTree_expect_eq_prefix (pre mid : List PositiveMass)
    {tail : List PositiveMass} (A : ClockTree S (mid ++ tail)) (B D : ClockTree S tail)
    {w : S → ℝ} (hw : ∀ σ, 0 < w σ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {a : ℝ} (ho : MassOrdered a (pre ++ (mid ++ tail))) (q : ℕ → ι → ℝ≥0)
    (Q : A.Assignment → B.Assignment → D.Assignment → ℝ) (x : ι → ℝ) :
    (nativeTwinForestTree pre mid A B D).expect w φ q
      (nativeTwinForestRead pre mid A B D Q) x =
      prefixTest (clockSteps pre q)
        (gaussianHierarchy w φ (clockSteps mid (fun j => q (pre.length + j)) ++
          clockSteps tail (fun j => q (pre.length + (mid.length + j)))))
        (twinPrefixTest w φ (clockSteps mid (fun j => q (pre.length + j)))
          (clockSteps tail (fun j => q (pre.length + (mid.length + j))))
          (nativeTwinForestConditionalTest A B D w φ (fun j => q (pre.length + j))
            (fun j => q (pre.length + (mid.length + j))) Q)) x := by
  let T := A.fork ((exteriorPrepend mid B).fork (exteriorPrepend mid D))
  let Q₀ : T.Assignment → ℝ := fun σ => Q σ.1
    (exteriorPrependAssignmentEquiv mid B σ.2.1)
    (exteriorPrependAssignmentEquiv mid D σ.2.2)
  have hCore := funext fun xi => nativeTwinForestTail_expect_eq_prefix
    mid A B D hw φ ho.suffix_end (fun j => q (pre.length + j)) Q xi
  have hPre := exteriorPrepend_expect pre hw φ T ho q Q₀ x
  change (exteriorPrepend pre T).expect w φ q
    (fun σ => Q₀ (exteriorPrependAssignmentEquiv pre T σ)) x = _
  rw [hPre, hCore, clockSteps_append]

variable [MeasurableSpace S] [StandardBorelSpace S]

def nativeTwinPrefixRootLaw (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (pre mid tail : List PositiveMass) (q : ℕ → ι → ℝ≥0)
    {P : Type} [MeasurableSpace P] (μ : Measure P)
    (x : P → ι → ℝ) (hx : Measurable x) :
    Measure (((P × (ι → ℝ)) × (ι → ℝ)) × (ι → ℝ)) :=
  twinPrefixRootLaw w φ (clockSteps pre q)
    (clockSteps mid (fun j => q (pre.length + j)))
    (clockSteps tail (fun j => q (pre.length + (mid.length + j)))) μ x hx

theorem nativeTwinPrefixRootLaw_probability
    {w : S → ℝ} (hw : ∀ σ, 0 < w σ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (pre mid tail : List PositiveMass) {a : ℝ}
    (ho : MassOrdered a (pre ++ (mid ++ tail))) (q : ℕ → ι → ℝ≥0)
    {P : Type} [MeasurableSpace P] (μ : Measure P) [IsProbabilityMeasure μ]
    (x : P → ι → ℝ) (hx : Measurable x) :
    IsProbabilityMeasure (nativeTwinPrefixRootLaw w φ pre mid tail q μ x hx) := by
  have hoG : OrderedSteps a (clockSteps pre q ++
      (clockSteps mid (fun j => q (pre.length + j)) ++
        clockSteps tail (fun j => q (pre.length + (mid.length + j))))) := by
    rw [← nativeExteriorForest_clockSteps_eq]
    exact clockSteps_ordered ho q
  exact twinPrefixRootLaw_probability hw φ _ _ _ hoG μ x hx

theorem nativeTwinPrefixRootLaw_finite
    {w : S → ℝ} (hw : ∀ σ, 0 < w σ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (pre mid tail : List PositiveMass) {a : ℝ}
    (ho : MassOrdered a (pre ++ (mid ++ tail))) (q : ℕ → ι → ℝ≥0)
    {P : Type} [MeasurableSpace P] (μ : Measure P) [IsFiniteMeasure μ]
    (x : P → ι → ℝ) (hx : Measurable x) :
    IsFiniteMeasure (nativeTwinPrefixRootLaw w φ pre mid tail q μ x hx) := by
  have hoG : OrderedSteps a (clockSteps pre q ++
      (clockSteps mid (fun j => q (pre.length + j)) ++
        clockSteps tail (fun j => q (pre.length + (mid.length + j))))) := by
    rw [← nativeExteriorForest_clockSteps_eq]
    exact clockSteps_ordered ho q
  exact twinPrefixRootLaw_finite hw φ _ _ _ hoG μ x hx

theorem nativeTwinForest_original_law_eq_conditional (pre mid : List PositiveMass)
    {tail : List PositiveMass} (A : ClockTree S (mid ++ tail)) (B D : ClockTree S tail)
    {w : S → ℝ} (hw : ∀ σ, 0 < w σ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {a : ℝ} (ho : MassOrdered a (pre ++ (mid ++ tail))) (q : ℕ → ι → ℝ≥0)
    (Q : A.Assignment → B.Assignment → D.Assignment → ℝ)
    {P : Type} [MeasurableSpace P] (μ : Measure P) [IsFiniteMeasure μ]
    (x : P → ι → ℝ) (hx : Measurable x) :
    (∫ p, (nativeTwinForestTree pre mid A B D).expect w φ q
      (nativeTwinForestRead pre mid A B D Q) (x p) ∂μ) =
      ∫ z, nativeTwinForestConditionalTest A B D w φ (fun j => q (pre.length + j))
        (fun j => q (pre.length + (mid.length + j))) Q
        (twinPrefixSharedRoot z) (twinPrefixBRoot z) (twinPrefixDRoot z)
        ∂nativeTwinPrefixRootLaw w φ pre mid tail q μ x hx := by
  have hoG : OrderedSteps a (clockSteps pre q ++
      (clockSteps mid (fun j => q (pre.length + j)) ++
        clockSteps tail (fun j => q (pre.length + (mid.length + j))))) := by
    rw [← nativeExteriorForest_clockSteps_eq]
    exact clockSteps_ordered ho q
  have hC := nativeTwinForestConditionalTest_smooth_joint A B D hw φ
    ho.suffix_end ho.suffix_end.suffix_end (fun j => q (pre.length + j))
    (fun j => q (pre.length + (mid.length + j))) Q 0
  unfold nativeTwinPrefixRootLaw
  rw [integral_twinPrefixRootLaw hw φ _ _ _ hoG μ x hx hC]
  apply integral_congr_ae
  exact Eventually.of_forall fun p => nativeTwinForestTree_expect_eq_prefix pre mid A B D hw φ ho q Q (x p)

def nativeTwinPrefixDisorderRootLaw (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (pre mid tail : List PositiveMass) (v : ι → ℝ) (q : ℕ → ι → ℝ)
    (x : ι → ℝ) :
    Measure ((((ι → ℝ) × (ι → ℝ)) × (ι → ℝ)) × (ι → ℝ)) :=
  nativeTwinPrefixRootLaw w φ pre mid tail
    (cumulativeIncrements (q 0) (fun j => q (j + 1)))
    (Measure.pi fun i => gaussianReal 0 (Real.toNNReal (q 0 i - v i)))
    (fun y => x + y) (measurable_const.add measurable_id)

theorem nativeTwinPrefixDisorderRootLaw_probability
    {w : S → ℝ} (hw : ∀ σ, 0 < w σ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (pre mid tail : List PositiveMass) {a : ℝ}
    (ho : MassOrdered a (pre ++ (mid ++ tail)))
    (v : ι → ℝ) (q : ℕ → ι → ℝ) (x : ι → ℝ) :
    IsProbabilityMeasure (nativeTwinPrefixDisorderRootLaw w φ pre mid tail v q x) :=
  nativeTwinPrefixRootLaw_probability hw φ pre mid tail ho _ _ _ _

theorem nativeTwinForest_disorder_law_eq_conditional (pre mid : List PositiveMass)
    {tail : List PositiveMass} (A : ClockTree S (mid ++ tail)) (B D : ClockTree S tail)
    {w : S → ℝ} (hw : ∀ σ, 0 < w σ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {a : ℝ} (ho : MassOrdered a (pre ++ (mid ++ tail)))
    (v : ι → ℝ) (q : ℕ → ι → ℝ)
    (Q : A.Assignment → B.Assignment → D.Assignment → ℝ) (x : ι → ℝ) :
    (nativeTwinForestTree pre mid A B D).disorderExpect w φ v q
      (nativeTwinForestRead pre mid A B D Q) x =
      ∫ z, nativeTwinForestConditionalTest A B D w φ
        (fun j => cumulativeIncrements (q 0) (fun k => q (k + 1)) (pre.length + j))
        (fun j => cumulativeIncrements (q 0) (fun k => q (k + 1)) (pre.length + (mid.length + j))) Q
        (twinPrefixSharedRoot z) (twinPrefixBRoot z) (twinPrefixDRoot z)
        ∂nativeTwinPrefixDisorderRootLaw w φ pre mid tail v q x := by
  rw [(nativeTwinForestTree pre mid A B D).disorderExpect_integral hw φ ho]
  unfold zeroContinuation
  exact nativeTwinForest_original_law_eq_conditional pre mid A B D hw φ ho _ Q
    (Measure.pi fun i => gaussianReal 0 (Real.toNNReal (q 0 i - v i)))
    (fun y => x + y) (measurable_const.add measurable_id)

omit [Nonempty S] [MeasurableSpace S] [StandardBorelSpace S] in
theorem nativeTwinForestConditionalTest_eq_target_mean {ias tas : List PositiveMass}
    (A : ClockTree S ias) (B D : ClockTree S tas) (w : S → ℝ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (qi qs : ℕ → ι → ℝ≥0)
    (Q : A.Assignment → B.Assignment → D.Assignment → ℝ) (xi xB xD : ι → ℝ) :
    nativeTwinForestConditionalTest A B D w φ qi qs Q xi xB xD =
      D.expect w φ qs (fun δ => nativeExteriorForestMean A B w φ qi qs
        (fun η β => Q η β δ) xi xB) xD := by
  unfold nativeTwinForestConditionalTest nativeExteriorForestMean ClockTree.expect
  simp only [Finset.mul_sum]
  have he : (fun η : A.Assignment => ∑ β : B.Assignment, ∑ δ : D.Assignment,
      A.weight w φ qi η xi * (B.weight w φ qs β xB * (D.weight w φ qs δ xD * Q η β δ))) =
      fun η => ∑ δ : D.Assignment, ∑ β : B.Assignment,
        A.weight w φ qi η xi * (B.weight w φ qs β xB * (D.weight w φ qs δ xD * Q η β δ)) := by
    funext η
    exact Finset.sum_comm
  rw [he, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro δ _
  apply Finset.sum_congr rfl
  intro η _
  apply Finset.sum_congr rfl
  intro β _
  ring

def nativeTwinForestAveragedFourth {ias tas : List PositiveMass}
    (A : ClockTree S ias) (B D : ClockTree S tas) (w : S → ℝ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (qi qs : ℕ → ι → ℝ≥0)
    (Q : A.Assignment → B.Assignment → D.Assignment → ℝ) (xi xB xD : ι → ℝ) : ℝ :=
  D.expect w φ qs (fun δ =>
    (nativeExteriorForestMean A B w φ qi qs (fun η β => Q η β δ) xi xB)^4) xD

omit [Nonempty S] [MeasurableSpace S] [StandardBorelSpace S] in
theorem nativeTwinForestConditionalTest_quad_eq_fourth {ias tas : List PositiveMass}
    (A : ClockTree S ias) (B D : ClockTree S tas) (w : S → ℝ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (qi qs : ℕ → ι → ℝ≥0)
    (Q : A.Assignment → B.Assignment → D.Assignment → ℝ) (xi xB xD : ι → ℝ) :
    nativeTwinForestConditionalTest (exteriorQuadNative A) (exteriorQuadNative B) D w φ qi qs
      (fun η β δ => Q η.1.1 β.1.1 δ * Q η.1.2 β.1.2 δ *
        Q η.2.1 β.2.1 δ * Q η.2.2 β.2.2 δ) xi xB xD =
      nativeTwinForestAveragedFourth A B D w φ qi qs Q xi xB xD := by
  rw [nativeTwinForestConditionalTest_eq_target_mean]
  unfold nativeTwinForestAveragedFourth
  apply congrArg (fun R => D.expect w φ qs R xD)
  funext δ
  exact nativeExteriorForest_four_copy_mean A B w φ qi qs (fun η β => Q η β δ) xi xB

theorem nativeTwinForest_four_tooth_original_law (pre mid : List PositiveMass)
    {tail : List PositiveMass} (A : ClockTree S (mid ++ tail)) (B D : ClockTree S tail)
    {w : S → ℝ} (hw : ∀ σ, 0 < w σ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {a : ℝ} (ho : MassOrdered a (pre ++ (mid ++ tail))) (q : ℕ → ι → ℝ≥0)
    (Q : A.Assignment → B.Assignment → D.Assignment → ℝ)
    {P : Type} [MeasurableSpace P] (μ : Measure P) [IsFiniteMeasure μ]
    (x : P → ι → ℝ) (hx : Measurable x) :
    (∫ p, (nativeTwinForestTree pre mid (exteriorQuadNative A) (exteriorQuadNative B) D).expect w φ q
      (nativeTwinForestRead pre mid (exteriorQuadNative A) (exteriorQuadNative B) D
        (fun η β δ => Q η.1.1 β.1.1 δ * Q η.1.2 β.1.2 δ *
          Q η.2.1 β.2.1 δ * Q η.2.2 β.2.2 δ)) (x p) ∂μ) =
      ∫ z, nativeTwinForestAveragedFourth A B D w φ (fun j => q (pre.length + j))
        (fun j => q (pre.length + (mid.length + j))) Q
        (twinPrefixSharedRoot z) (twinPrefixBRoot z) (twinPrefixDRoot z)
        ∂nativeTwinPrefixRootLaw w φ pre mid tail q μ x hx := by
  rw [nativeTwinForest_original_law_eq_conditional pre mid (exteriorQuadNative A)
    (exteriorQuadNative B) D hw φ ho q _ μ x hx]
  apply integral_congr_ae
  exact Eventually.of_forall fun z => nativeTwinForestConditionalTest_quad_eq_fourth A B D w φ _ _ Q _ _ _

theorem nativeTwinForest_four_tooth_disorder_law (pre mid : List PositiveMass)
    {tail : List PositiveMass} (A : ClockTree S (mid ++ tail)) (B D : ClockTree S tail)
    {w : S → ℝ} (hw : ∀ σ, 0 < w σ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {a : ℝ} (ho : MassOrdered a (pre ++ (mid ++ tail)))
    (v : ι → ℝ) (q : ℕ → ι → ℝ)
    (Q : A.Assignment → B.Assignment → D.Assignment → ℝ) (x : ι → ℝ) :
    (nativeTwinForestTree pre mid (exteriorQuadNative A) (exteriorQuadNative B) D).disorderExpect w φ v q
      (nativeTwinForestRead pre mid (exteriorQuadNative A) (exteriorQuadNative B) D
        (fun η β δ => Q η.1.1 β.1.1 δ * Q η.1.2 β.1.2 δ *
          Q η.2.1 β.2.1 δ * Q η.2.2 β.2.2 δ)) x =
      ∫ z, nativeTwinForestAveragedFourth A B D w φ
        (fun j => cumulativeIncrements (q 0) (fun k => q (k + 1)) (pre.length + j))
        (fun j => cumulativeIncrements (q 0) (fun k => q (k + 1)) (pre.length + (mid.length + j))) Q
        (twinPrefixSharedRoot z) (twinPrefixBRoot z) (twinPrefixDRoot z)
        ∂nativeTwinPrefixDisorderRootLaw w φ pre mid tail v q x := by
  rw [nativeTwinForest_disorder_law_eq_conditional pre mid (exteriorQuadNative A)
    (exteriorQuadNative B) D hw φ ho v q _ x]
  apply integral_congr_ae
  exact Eventually.of_forall fun z => nativeTwinForestConditionalTest_quad_eq_fourth A B D w φ _ _ Q _ _ _

end OAI.SKFluctuations.Cavity
