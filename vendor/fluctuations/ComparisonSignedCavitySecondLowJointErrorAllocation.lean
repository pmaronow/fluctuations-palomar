module

public import ComparisonSignedCavitySecondLowEightGammaFactors
public import ComparisonSignedCavityWholeLawHolder

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree
open scoped BigOperators
set_option maxHeartbeats 22000000

def nativeSecondLowErrorKernel (n U : ℕ) (b h K : ℕ→ℝ)
    (j : ℕ) (σ τ : Spin n) : ℝ :=
  restLowKernel n U b h j σ τ-nativeSecondLowScalarValue U K j

def nativeSecondLowOldTest {n : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    (P : T.cavityLeft.Assignment→ℝ) (p : MarkedPlacement T) (r : MarkedPlacement p.tree)
    (s : MarkedPlacement r.tree) (t : MarkedPlacement s.tree)
    (τ : t.tree.cavityLeft.Assignment) : ℝ :=
  P (p.restRestrict (r.restRestrict (s.restRestrict (t.restRestrict τ))))

theorem native_second_low_joint_rest_test_error_decomposition (n U : ℕ)
    (b h K : ℕ→ℝ) {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    (P : T.cavityLeft.Assignment→ℝ) (p : MarkedPlacement T) (r : MarkedPlacement p.tree)
    (s : MarkedPlacement r.tree) (t : MarkedPlacement s.tree)
    (τ : t.tree.cavityLeft.Assignment) :
    nativeSecondLowJointRestTest n U b h K P p r s t τ=
      nativeSecondLowOldTest P p r s t τ*
        nativeSecondLowErrorKernel n U b h K (r.tree.splitIndex (r.embed p.mark) r.mark)
          (p.restSpin (r.restRestrict (s.restRestrict (t.restRestrict τ))))
          (r.restSpin (s.restRestrict (t.restRestrict τ)))*
        restLowKernel n U b h (t.tree.splitIndex (t.embed s.mark) t.mark)
          (s.restSpin (t.restRestrict τ)) (t.restSpin τ)+
      nativeSecondLowScalarValue U K (r.tree.splitIndex (r.embed p.mark) r.mark)*
        nativeSecondLowOldTest P p r s t τ*
        nativeSecondLowErrorKernel n U b h K (t.tree.splitIndex (t.embed s.mark) t.mark)
          (s.restSpin (t.restRestrict τ)) (t.restSpin τ) := by
  rw [native_second_low_joint_rest_test_product]
  unfold nativeSecondLowOldTest nativeSecondLowErrorKernel
  ring

theorem native_second_low_old_test_moment_preserved (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.cavityLeft.Assignment→ℝ) (order : ℕ)
    (p : MarkedPlacement T) (hp : p∈T.markedAttach 0)
    (r : MarkedPlacement p.tree) (hr : r∈p.tree.markedAttach 0)
    (s : MarkedPlacement r.tree) (hs : s∈r.tree.markedAttach 0)
    (t : MarkedPlacement s.tree) (ht : t∈s.tree.markedAttach 0) :
    t.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
      (fun τ=>|nativeSecondLowOldTest P p r s t τ|^order) 0=
      T.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q (fun τ=>|P τ|^order) 0 := by
  unfold nativeSecondLowOldTest
  rw [native_rest_marked_restrict_preserves n q U b h K s.tree ho
    (fun τ=>|P (p.restRestrict (r.restRestrict (s.restRestrict τ)))|^order) t ht,
    native_rest_marked_restrict_preserves n q U b h K r.tree ho
    (fun τ=>|P (p.restRestrict (r.restRestrict τ))|^order) s hs,
    native_rest_marked_restrict_preserves n q U b h K p.tree ho
    (fun τ=>|P (p.restRestrict τ)|^order) r hr,
    native_rest_marked_restrict_preserves n q U b h K T ho (fun τ=>|P τ|^order) p hp]

theorem native_second_low_product_difference_from_pair_moments (n : ℕ) (hn : 0<n)
    {as : List PositiveMass} (T : ClockTree (Spin n) as) (ho : MassOrdered 0 as)
    (q : ℕ→RestCoordinate n→ℝ) (P : T.Assignment→ℝ)
    (Q : ℕ→Spin n→Spin n→ℝ) (K : ℕ→ℝ) (f c e d : T.Slot)
    (hfc : f≠c) (hed : e≠d) {C E₁ E₂ R₂ : ℝ}
    (hC : 0≤C) (hE₁ : 0≤E₁) (hE₂ : 0≤E₂) (hR₂ : 0<R₂)
    (hP : T.disorderExpect (restWeight n) (restFeature n) 0 q (fun σ=>|P σ|^4) 0≤C^4)
    (hError₁ : (pairClock as (T.splitIndex f c)).disorderExpect (restWeight n) (restFeature n) 0 q
      (fun σ=>(Q (T.splitIndex f c) (pairSpin as (T.splitIndex f c) σ).1
        (pairSpin as (T.splitIndex f c) σ).2-K (T.splitIndex f c))^2) 0≤E₁^2)
    (hError₂ : (pairClock as (T.splitIndex e d)).disorderExpect (restWeight n) (restFeature n) 0 q
      (fun σ=>(Q (T.splitIndex e d) (pairSpin as (T.splitIndex e d) σ).1
        (pairSpin as (T.splitIndex e d) σ).2-K (T.splitIndex e d))^2) 0≤E₂^2)
    (hRaw₂ : (pairClock as (T.splitIndex e d)).disorderExpect (restWeight n) (restFeature n) 0 q
      (fun σ=>|Q (T.splitIndex e d) (pairSpin as (T.splitIndex e d) σ).1
        (pairSpin as (T.splitIndex e d) σ).2|^4) 0≤R₂^4) :
    |T.disorderExpect (restWeight n) (restFeature n) 0 q (fun σ=>P σ*
      (Q (T.splitIndex f c) (T.atSlot σ f) (T.atSlot σ c)*
        Q (T.splitIndex e d) (T.atSlot σ e) (T.atSlot σ d)-
        K (T.splitIndex f c)*K (T.splitIndex e d))) 0|≤
      C*(E₁*R₂+|K (T.splitIndex f c)| *E₂) := by
  let : Nonempty (RestCoordinate n):=⟨Sum.inr ⟨0,hn⟩⟩
  let A:=fun j σ τ=>Q j σ τ-K j
  have H₁:=T.disorderExpect_oneError_wholeLaw_product_scales (restWeight_pos n) (restFeature n) ho
    0 q 0 (by norm_num : 0<1) P hC hE₁ hP A f c hfc
    (fun _=>Q) (fun _=>e) (fun _=>d) (fun _=>hed) (fun _=>R₂) (fun _=>hR₂) hError₁
    (fun _=>by simpa only [Nat.mul_one] using hRaw₂)
  have H₂:=T.disorderExpect_oneError_wholeLaw_product_scales (restWeight_pos n) (restFeature n) ho
    0 q 0 (by norm_num : 0<1) P hC hE₂ hP A e d hed
    (fun _ _ _ _=>(1:ℝ)) (fun _=>f) (fun _=>c) (fun _=>hfc) (fun _=>(1:ℝ))
    (fun _=>by norm_num) hError₂ (fun _=>by
      simp only [abs_one,one_pow]
      exact ((pairClock as (T.splitIndex f c)).disorderExpect_one
        (restWeight_pos n) (restFeature n) ho 0 q 0).le)
  simp only [Fin.prod_univ_one,mul_one] at H₁ H₂
  have Hsplit : T.disorderExpect (restWeight n) (restFeature n) 0 q (fun σ=>P σ*
      (Q (T.splitIndex f c) (T.atSlot σ f) (T.atSlot σ c)*
        Q (T.splitIndex e d) (T.atSlot σ e) (T.atSlot σ d)-
        K (T.splitIndex f c)*K (T.splitIndex e d))) 0=
      T.disorderExpect (restWeight n) (restFeature n) 0 q (fun σ=>P σ*
        A (T.splitIndex f c) (T.atSlot σ f) (T.atSlot σ c)*
        Q (T.splitIndex e d) (T.atSlot σ e) (T.atSlot σ d)) 0+
      K (T.splitIndex f c)*T.disorderExpect (restWeight n) (restFeature n) 0 q (fun σ=>P σ*
        A (T.splitIndex e d) (T.atSlot σ e) (T.atSlot σ d)) 0 := by
    unfold disorderExpect
    rw [Finset.mul_sum,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro σ _
    dsimp only [A]
    ring
  rw [Hsplit]
  apply (abs_add_le _ _).trans
  rw [abs_mul]
  calc
    _≤C*E₁*R₂+|K (T.splitIndex f c)| *(C*E₂):=
      add_le_add H₁ (mul_le_mul_of_nonneg_left H₂ (abs_nonneg _))
    _= _:=by ring

end OAI.SKFluctuations.Cavity
