module

public import ComparisonSignedCavityJointForestHolder

@[expose] public section

noncomputable section
set_option maxHeartbeats 6000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal RealInnerProductSpace
namespace OAI.SKFluctuations.Cavity
open Hierarchy

theorem native_unweighted_exterior_anchor_norm_le_one (n : ℕ)
    {as : List PositiveMass} (E : ClockTree (Spin n) as) {a : ℝ}
    (ho : MassOrdered a as) (s : E.Slot) (q : ℕ→RestCoordinate n→ℝ≥0)
    (x : RestCoordinate n→ℝ) :
    ‖nativeWeightedExteriorAnchor n E (fun _=>1) s q x‖ ≤ 1 := by
  have H:=(native_unweighted_exterior_anchor_eighth_le_raw_pair n E ho s q x).trans
    (native_unweighted_raw_pair_fourth_le_one n E ho s q x)
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) zero_le_one (by decide : (8:ℕ)≠0)).mp
    (by simpa only [one_pow] using H)

theorem native_fresh_pair_projection_abs_le_two (n : ℕ)
    {as : List PositiveMass} (E : ClockTree (Spin n) as) {a : ℝ}
    (ho : MassOrdered a as) (s : E.Slot) (q : ℕ→RestCoordinate n→ℝ≥0)
    (x : RestCoordinate n→ℝ) (σ τ : Spin n) :
    |inner ℝ (WithLp.toLp 2 (normalizedSpin n σ)-WithLp.toLp 2 (normalizedSpin n τ))
      (nativeWeightedExteriorAnchor n E (fun _=>1) s q x)| ≤ 2 := by
  have hnorm (ρ : Spin n) : ‖WithLp.toLp 2 (normalizedSpin n ρ)‖ ≤ 1 := by
    have he : ‖WithLp.toLp 2 (normalizedSpin n ρ)‖^2=orderedOverlap n ρ ρ := by
      rw [←real_inner_self_eq_norm_sq,normalizedSpin_inner_eq_overlap]
    nlinarith [norm_nonneg (WithLp.toLp 2 (normalizedSpin n ρ)),
      orderedOverlap_abs_le_one n ρ ρ,le_abs_self (orderedOverlap n ρ ρ)]
  have hd : ‖WithLp.toLp 2 (normalizedSpin n σ)-WithLp.toLp 2 (normalizedSpin n τ)‖ ≤ 2 :=
    (norm_sub_le _ _).trans (by linarith [hnorm σ,hnorm τ])
  have H:=norm_inner_le_norm (𝕜:=ℝ)
    (WithLp.toLp 2 (normalizedSpin n σ)-WithLp.toLp 2 (normalizedSpin n τ))
    (nativeWeightedExteriorAnchor n E (fun _=>1) s q x)
  rw [Real.norm_eq_abs] at H
  exact H.trans (by simpa only [mul_one] using (mul_le_mul hd
    (native_unweighted_exterior_anchor_norm_le_one n E ho s q x) (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 2)))

theorem native_three_root_fresh_anchor_saved_bound
    (n : ℕ) {ias tas : List PositiveMass}
    (A : ClockTree (Spin n) ias) (B D : ClockTree (Spin n) tas) (s t : D.Slot)
    {ai ast : ℝ} (hoi : MassOrdered ai ias) (hot : MassOrdered ast tas)
    (qi qs : ℕ→RestCoordinate n→ℝ≥0) {P : Type} [MeasurableSpace P]
    (μ : Measure P) [IsProbabilityMeasure μ]
    (xi xb xd : P→RestCoordinate n→ℝ) (hxi : Measurable xi) (hxb : Measurable xb)
    (hxd : Measurable xd) (Z : A.Assignment→B.Assignment→D.Assignment→ℝ)
    {p r : ℝ} (hp : 0 ≤ p) (hr : 0 ≤ r)
    (hZ2 : (∫z,A.expect (restWeight n) (restFeature n) qi (fun η=>
      B.expect (restWeight n) (restFeature n) qs (fun β=>D.expect (restWeight n) (restFeature n)
        qs (fun δ=>Z η β δ^2) (xd z)) (xb z)) (xi z) ∂μ) ≤ p^2)
    (hJ4 : (∫z,nativeSubtreeExteriorProjectionFourth n D s t (ClockTree.single tas) (fun _=>1)
      (ClockTree.singleSlot tas) qs qs (xb z) (xd z) ∂μ) ≤ r^4) :
    |∫z,A.expect (restWeight n) (restFeature n) qi (fun η=>
      B.expect (restWeight n) (restFeature n) qs (fun β=>D.expect (restWeight n) (restFeature n)
        qs (fun δ=>Z η β δ*inner ℝ
          (WithLp.toLp 2 (normalizedSpin n (D.atSlot δ t))-
            WithLp.toLp 2 (normalizedSpin n (D.atSlot δ s)))
          (nativeWeightedExteriorAnchor n (ClockTree.single tas) (fun _=>1)
            (ClockTree.singleSlot tas) qs (xb z))) (xd z)) (xb z)) (xi z) ∂μ| ≤ p*r := by
  let J:=fun z δ=>inner ℝ (WithLp.toLp 2 (normalizedSpin n (D.atSlot δ t))-
    WithLp.toLp 2 (normalizedSpin n (D.atSlot δ s)))
    (nativeWeightedExteriorAnchor n (ClockTree.single tas) (fun _=>1) (ClockTree.singleSlot tas) qs (xb z))
  have hJ : ∀δ,Measurable (fun z=>J z δ) := by
    intro δ
    exact measurable_const.inner
      ((native_unweighted_exterior_anchor_continuous n (ClockTree.single tas) hot
        (ClockTree.singleSlot tas) qs).measurable.comp hxb)
  exact native_three_root_old_second_projection_fourth n A B D hoi hot qi qs μ xi xb xd hxi hxb hxd
    Z J hJ 2 (fun z δ=>native_fresh_pair_projection_abs_le_two n (ClockTree.single tas) hot
      (ClockTree.singleSlot tas) qs (xb z) _ _) hp hr hZ2 hJ4

end OAI.SKFluctuations.Cavity
