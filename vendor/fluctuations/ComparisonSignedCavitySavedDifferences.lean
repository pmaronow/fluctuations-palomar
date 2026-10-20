module

public import CavityNativeGammaPrefixWeights
public import CavityNativeProjectedPowerMoments
public import CavityMomentAllocation

@[expose] public section

noncomputable section
set_option maxHeartbeats 1500000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal RealInnerProductSpace
namespace OAI.SKFluctuations.Cavity
open Hierarchy

private theorem nativeRest_expect_nonneg (n : ℕ) {as : List PositiveMass}
    (T : ClockTree (Spin n) as) {a : ℝ} (ho : MassOrdered a as)
    (q : ℕ → RestCoordinate n → ℝ≥0) (P : T.Assignment → ℝ)
    (hP : ∀ σ, 0 ≤ P σ) (x : RestCoordinate n → ℝ) :
    0 ≤ T.expect (restWeight n) (restFeature n) q P x := by
  unfold ClockTree.expect
  exact Finset.sum_nonneg fun σ _ => mul_nonneg
    ((T.weight_probability (restWeight_pos n) (restFeature n) ho q x).1 σ) (hP σ)

private theorem nativeRest_expect_mul_abs_le_sqrt (n : ℕ) {as : List PositiveMass}
    (T : ClockTree (Spin n) as) {a : ℝ} (ho : MassOrdered a as)
    (q : ℕ → RestCoordinate n → ℝ≥0) (P Q : T.Assignment → ℝ)
    (x : RestCoordinate n → ℝ) :
    |T.expect (restWeight n) (restFeature n) q (fun σ => P σ * Q σ) x| ≤
      Real.sqrt (T.expect (restWeight n) (restFeature n) q (fun σ => P σ ^ 2) x *
        T.expect (restWeight n) (restFeature n) q (fun σ => Q σ ^ 2) x) := by
  apply (Real.le_sqrt (abs_nonneg _) (mul_nonneg
    (nativeRest_expect_nonneg n T ho q _ (fun σ => sq_nonneg _) x)
    (nativeRest_expect_nonneg n T ho q _ (fun σ => sq_nonneg _) x))).mpr
  rw [sq_abs]
  simpa only [ClockTree.expect, mul_assoc] using finite_weighted_cauchy_schwarz
    (fun σ => T.weight (restWeight n) (restFeature n) q σ x) P Q
    (T.weight_probability (restWeight_pos n) (restFeature n) ho q x).1

def nativeIncomingProjectionDifference (n : ℕ) {as : List PositiveMass}
    (q : ℕ → RestCoordinate n → ℝ≥0) (x : RestCoordinate n → ℝ) (center : ℝ)
    (p : ClockTree.MarkedPlacement (ClockTree.single (S := Spin n × Bool) as))
    (σ : p.tree.cavityLeft.Assignment) : ℝ :=
  nativeCenteredProjectedDeletedOverlap n as q x center (p.restSpin σ) -
    nativeCenteredProjectedDeletedOverlap n as q x center (nativeAttachmentOld p σ)

def nativeIncomingAnchorDifference (n : ℕ) {as : List PositiveMass}
    (E : ClockTree (Spin n) as) (H : E.Assignment → ℝ) (s : E.Slot)
    (q : ℕ → RestCoordinate n → ℝ≥0) (x : RestCoordinate n → ℝ)
    (p : ClockTree.MarkedPlacement (ClockTree.single (S := Spin n × Bool) as))
    (σ : p.tree.cavityLeft.Assignment) : ℝ :=
  inner ℝ (WithLp.toLp 2 (normalizedSpin n (nativeAttachmentOld p σ)) -
    WithLp.toLp 2 (normalizedSpin n (p.restSpin σ)))
    (nativeWeightedExteriorAnchor n E H s q x)

def nativeIncomingAnchorPlacement (n k : ℕ) {as : List PositiveMass}
    (E : ClockTree (Spin n) as) (H : E.Assignment → ℝ) (s : E.Slot)
    (q : ℕ → RestCoordinate n → ℝ≥0) (x : RestCoordinate n → ℝ) (center : ℝ)
    (p : ClockTree.MarkedPlacement (ClockTree.single (S := Spin n × Bool) as)) : ℝ :=
  p.tree.cavityLeft.expect (restWeight n) (restFeature n) q (fun σ =>
    nativeIncomingProjectionDifference n q x center p σ *
      nativeCenteredProjectedDeletedOverlap n as q x center (p.restSpin σ)^k *
      nativeIncomingAnchorDifference n E H s q x p σ) x

def nativeIncomingProjectionFourth (n : ℕ) {as : List PositiveMass}
    (q : ℕ → RestCoordinate n → ℝ≥0) (x : RestCoordinate n → ℝ) (center : ℝ)
    (p : ClockTree.MarkedPlacement (ClockTree.single (S := Spin n × Bool) as)) : ℝ :=
  p.tree.cavityLeft.expect (restWeight n) (restFeature n) q
    (fun σ => nativeIncomingProjectionDifference n q x center p σ ^ 4) x

def nativeIncomingAnchorFourth (n : ℕ) {as : List PositiveMass}
    (E : ClockTree (Spin n) as) (H : E.Assignment → ℝ) (s : E.Slot)
    (q : ℕ → RestCoordinate n → ℝ≥0) (x : RestCoordinate n → ℝ)
    (p : ClockTree.MarkedPlacement (ClockTree.single (S := Spin n × Bool) as)) : ℝ :=
  p.tree.cavityLeft.expect (restWeight n) (restFeature n) q
    (fun σ => nativeIncomingAnchorDifference n E H s q x p σ ^ 4) x

def nativeIncomingRawTargetMoment (n k : ℕ) (as : List PositiveMass)
    (q : ℕ → RestCoordinate n → ℝ≥0) (x : RestCoordinate n → ℝ) (center : ℝ) : ℝ :=
  ClockTree.pairMean (restWeight n) (restFeature n) as q 0
    (fun σ τ => |deletedOverlap n (joinSpin (σ,false)) (joinSpin (τ,false))-center|^(2*k)) x

theorem native_incoming_anchor_placement_saved_differences (n k : ℕ)
    {as : List PositiveMass} (E : ClockTree (Spin n) as) {a : ℝ}
    (ho : MassOrdered a as) (H : E.Assignment → ℝ) (s : E.Slot)
    (q : ℕ → RestCoordinate n → ℝ≥0) (x : RestCoordinate n → ℝ) (center : ℝ)
    (p : ClockTree.MarkedPlacement (ClockTree.single (S := Spin n × Bool) as)) :
    |nativeIncomingAnchorPlacement n k E H s q x center p| ≤
      Real.sqrt (Real.sqrt (nativeIncomingProjectionFourth n q x center p *
        nativeIncomingAnchorFourth n E H s q x p) *
        nativeIncomingRawTargetMoment n k as q x center) := by
  let Y := nativeCenteredProjectedDeletedOverlap n as q x center
  let A := nativeIncomingProjectionDifference n q x center p
  let D := nativeIncomingAnchorDifference n E H s q x p
  let T := p.tree.cavityLeft
  have hfirst := nativeRest_expect_mul_abs_le_sqrt n T ho q
    (fun σ => A σ * D σ) (fun σ => Y (p.restSpin σ)^k) x
  have hsecond := nativeRest_expect_mul_abs_le_sqrt n T ho q
    (fun σ => A σ^2) (fun σ => D σ^2) x
  have hp : T.expect (restWeight n) (restFeature n) q
      (fun σ => (Y (p.restSpin σ)^k)^2) x ≤
        nativeIncomingRawTargetMoment n k as q x center := by
    convert native_projected_target_power_moment_le n (2*k) T ho
      (p.tree.cavityLeftSlot p.mark) q x center using 1
    · congr 1
      funext σ
      dsimp only [Y]
      rw [←pow_mul, Nat.mul_comm k 2]
      simp only [pow_mul, sq_abs]
      rfl
    · rfl
  have hsecond' : T.expect (restWeight n) (restFeature n) q
      (fun σ => (A σ*D σ)^2) x ≤
      Real.sqrt (nativeIncomingProjectionFourth n q x center p *
        nativeIncomingAnchorFourth n E H s q x p) := by
    have hn := nativeRest_expect_nonneg n T ho q
      (fun σ => (A σ)^2*(D σ)^2) (fun σ => mul_nonneg (sq_nonneg _) (sq_nonneg _)) x
    rw [abs_of_nonneg hn] at hsecond
    simp only [←pow_mul, show 2*2=4 by norm_num] at hsecond
    simpa only [mul_pow, nativeIncomingProjectionFourth, nativeIncomingAnchorFourth, A, D, T]
      using hsecond
  have hprod := mul_le_mul hsecond' hp
    (nativeRest_expect_nonneg n T ho q _ (fun σ => sq_nonneg _) x) (Real.sqrt_nonneg _)
  have hfinal := hfirst.trans (Real.sqrt_le_sqrt hprod)
  simpa only [nativeIncomingAnchorPlacement, A, D, Y, T,
    mul_assoc, mul_left_comm, mul_comm] using hfinal

theorem native_signed_incoming_anchor_saved_differences (n k : ℕ)
    {as : List PositiveMass} (E : ClockTree (Spin n) as) {a : ℝ}
    (ho : MassOrdered a as) (U : ℕ) (K : ℕ → ℝ)
    (H : E.Assignment → ℝ) (s : E.Slot)
    (q : ℕ → RestCoordinate n → ℝ≥0) (x : RestCoordinate n → ℝ) (center : ℝ) :
    |nativeSignedIncomingAnchorVariation n k E a U K H s q x center| ≤
      (((ClockTree.single (S := Spin n × Bool) as).markedAttach a).map fun p =>
        |p.coeff*nativeAttachmentGamma p U K| *
          Real.sqrt (Real.sqrt (nativeIncomingProjectionFourth n q x center p *
            nativeIncomingAnchorFourth n E H s q x p) *
            nativeIncomingRawTargetMoment n k as q x center)).sum := by
  change |(((ClockTree.single (S := Spin n × Bool) as).markedAttach a).map fun p =>
    (p.coeff*nativeAttachmentGamma p U K)*nativeIncomingAnchorPlacement n k E H s q x center p).sum| ≤ _
  apply ReplicaTree.list_weighted_absolute_bound
  intro p _
  exact native_incoming_anchor_placement_saved_differences n k E ho H s q x center p

theorem native_signed_incoming_replacement_saved_differences (n k : ℕ)
    {as : List PositiveMass} (E : ClockTree (Spin n) as) {a : ℝ}
    (ho : MassOrdered a as) (U : ℕ) (K : ℕ → ℝ)
    (H : E.Assignment → ℝ) (s : E.Slot)
    (q : ℕ → RestCoordinate n → ℝ≥0) (x : RestCoordinate n → ℝ)
    (center incomingCenter : ℝ) :
    |nativeSignedProjectedReplacement n E a U K q x center
      (nativeIncomingPowerTest n k E H s q x center incomingCenter)| ≤
    (1/2:ℝ) * (|nativeSignedIncomingPowerVariation n k E a U K H s q x center incomingCenter| +
      (((ClockTree.single (S := Spin n × Bool) as).markedAttach a).map fun p =>
        |p.coeff*nativeAttachmentGamma p U K| *
          Real.sqrt (Real.sqrt (nativeIncomingProjectionFourth n q x center p *
            nativeIncomingAnchorFourth n E H s q x p) *
            nativeIncomingRawTargetMoment n k as q x center)).sum) := by
  rw [native_signed_weighted_incoming_decomposition n k E ho U K H s q x center incomingCenter,
    abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact (abs_add_le _ _).trans (add_le_add le_rfl
    (native_signed_incoming_anchor_saved_differences n k E ho U K H s q x center))

def nativeSignedIncomingAnchorPrefix (n k : ℕ) (pre tail : List PositiveMass)
    (E : ClockTree (Spin n) (pre++tail)) (U : ℕ) (K : ℕ → ℝ)
    (H : E.Assignment → ℝ) (s : E.Slot)
    (q : ℕ → RestCoordinate n → ℝ≥0) (x : RestCoordinate n → ℝ) (center : ℝ) : ℝ :=
  ((ClockTree.singlePrefixAttachments (S := Spin n × Bool) pre tail 0).map fun p =>
    (p.coeff*nativeAttachmentGamma p U K)*nativeIncomingAnchorPlacement n k E H s q x center p).sum

theorem native_signed_incoming_anchor_prefix_saved_differences (n k : ℕ)
    (pre tail : List PositiveMass) (E : ClockTree (Spin n) (pre++tail))
    (ho : MassOrdered 0 (pre++tail)) (U : ℕ) (hU : 0 < U)
    (K : ℕ → ℝ) (hK : Monotone K) (hK0 : ∀ j, 0 ≤ K j)
    (H : E.Assignment → ℝ) (s : E.Slot)
    (q : ℕ → RestCoordinate n → ℝ≥0) (x : RestCoordinate n → ℝ) (center : ℝ)
    {C v A D : ℝ} (hC : 0 ≤ C) (hv : 0 ≤ v) (hA : 0 ≤ A) (_hD : 0 ≤ D)
    (hclock : relocatedClock U 0 K pre.length ≤ C*v)
    (hmass : partitionEnd 0 pre ≤ v)
    (hproj : ∀ p ∈ ClockTree.singlePrefixAttachments (S := Spin n × Bool) pre tail 0,
      nativeIncomingProjectionFourth n q x center p ≤ A)
    (hanchor : ∀ p ∈ ClockTree.singlePrefixAttachments (S := Spin n × Bool) pre tail 0,
      nativeIncomingAnchorFourth n E H s q x p ≤ D) :
    |nativeSignedIncomingAnchorPrefix n k pre tail E U K H s q x center| ≤
      C*v^2*Real.sqrt (Real.sqrt (A*D)*nativeIncomingRawTargetMoment n k (pre++tail) q x center) := by
  let M := nativeIncomingRawTargetMoment n k (pre++tail) q x center
  have hM : 0 ≤ M := by
    unfold M nativeIncomingRawTargetMoment ClockTree.pairMean
    apply nativeRest_expect_nonneg n _ ho q _ (fun _ => ?_) x
    apply nativeRest_expect_nonneg n _ ho q _ (fun _ => by positivity) x
  have hb : ∀ p ∈ ClockTree.singlePrefixAttachments (S := Spin n × Bool) pre tail 0,
      |nativeIncomingAnchorPlacement n k E H s q x center p| ≤ Real.sqrt (Real.sqrt (A*D)*M) := by
    intro p hp
    apply (native_incoming_anchor_placement_saved_differences n k E ho H s q x center p).trans
    apply Real.sqrt_le_sqrt
    apply mul_le_mul_of_nonneg_right _ hM
    apply Real.sqrt_le_sqrt
    exact mul_le_mul (hproj p hp) (hanchor p hp)
      (nativeRest_expect_nonneg n p.tree.cavityLeft ho q _ (fun _ => by positivity) x) hA
  have hsum := ReplicaTree.list_weighted_absolute_bound
    (ClockTree.singlePrefixAttachments (S := Spin n × Bool) pre tail 0)
    (fun p => p.coeff*nativeAttachmentGamma p U K)
    (nativeIncomingAnchorPlacement n k E H s q x center)
    (fun _ => Real.sqrt (Real.sqrt (A*D)*M)) hb
  change |nativeSignedIncomingAnchorPrefix n k pre tail E U K H s q x center| ≤ _ at hsum
  apply hsum.trans
  simp only [abs_mul]
  rw [List.sum_map_mul_right]
  exact mul_le_mul_of_nonneg_right
    (native_single_prefix_gamma_weight_le_square n pre tail ho U hU K hK hK0 hC hv hclock hmass)
    (Real.sqrt_nonneg _)

end OAI.SKFluctuations.Cavity
