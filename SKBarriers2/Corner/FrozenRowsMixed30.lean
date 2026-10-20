module

public import SKBarriers2.Corner.FrozenRowsMixedSlotProfiles
public import SKBarriers2.Corner.FrozenRowsMovingTestProfiles2

@[expose] public section

noncomputable section
open scoped Topology
open Set OAI.SK.Analytic
namespace SKBarriers2.Corner
local notation "X" => (Fin 3 → ℝ)

structure MovingNoiseTestPacket (r : ℕ) (C : ℝ) (p q : ℕ) (δ : ℝ)
    (G a c A₁ B₂ : ℝ → X → ℝ) : Prop where
  value_smooth : ContDiff ℝ r (Function.uncurry G)
  first_smooth : ContDiff ℝ r (Function.uncurry a)
  centered_value_smooth : ContDiff ℝ r (Function.uncurry c)
  centered_first_smooth : ContDiff ℝ r (Function.uncurry A₁)
  second_smooth : ContDiff ℝ r (Function.uncurry B₂)
  value : ∀ t, WJets r (C*(1+|t|)^q) p (G t)
  first : ∀ t, WJets r (C*(1+|t|)^q) p (a t)
  centered : ∀ t, MovingTestProfiles r (C*(1+|t|)^q) p δ (c t) (A₁ t) (B₂ t)

theorem MovingNoiseTestPacket.mono_noise {r p q Q : ℕ} {C D δ : ℝ}
    {G a c A₁ B₂ : ℝ → X → ℝ} (H : MovingNoiseTestPacket r C p q δ G a c A₁ B₂)
    (hCD : C ≤ D) (hq : q ≤ Q) : MovingNoiseTestPacket r D p Q δ G a c A₁ B₂ := by
  have hC : 0 ≤ C := by simpa only [abs_zero,add_zero,one_pow,mul_one] using (H.value 0).nonneg
  have hcoef (t : ℝ) : C*(1+|t|)^q ≤ D*(1+|t|)^Q := by
    calc
      _ ≤ C*(1+|t|)^Q := mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ (by linarith [abs_nonneg t]) hq) hC
      _ ≤ _ := mul_le_mul_of_nonneg_right hCD (by positivity)
  exact ⟨H.value_smooth,H.first_smooth,H.centered_value_smooth,H.centered_first_smooth,H.second_smooth,
    fun t => (H.value t).mono (hcoef t) le_rfl,
    fun t => (H.first t).mono (hcoef t) le_rfl,
    fun t => (H.centered t).mono (hcoef t)⟩

theorem movingNoiseTestPacket_affine {r p : ℕ} {C δ K W : ℝ} {f a b : X → ℝ}
    (H : IntrinsicTestProfiles r C p δ f a b)
    (hp : 2 ≤ p) (hδ : |δ| ≤ 1) (hK : 1 ≤ K) (hW : 1 ≤ W)
    (A : X →L[ℝ] X) (d v : X) (V₀ W₀ : ℝ → X) (U V : X →L[ℝ] X)
    (hA : ‖A‖ ≤ K) (hd : ‖d‖ ≤ K*W) (hv : ‖v‖ ≤ K)
    (hU : ‖U‖ ≤ K) (hV : ‖V‖ ≤ K)
    (hV₀ : ContDiff ℝ r V₀) (hW₀ : ContDiff ℝ r W₀)
    (hVW : ∀ t, ‖V₀ t‖ ≤ K*(1+|t|) ∧ ‖W₀ t‖ ≤ K*(1+|t|)) :
    MovingNoiseTestPacket r (C*movingTestProfileUniformCoefficient r p K*W^p) p (p+2) δ
      (fun t x => f (A x+d+t • v))
      (affineMovingRawFirst f a A d v δ V₀ U)
      (affineMovingCenteredValue f A d v)
      (affineMovingCenteredFirst f a A d v δ V₀ U)
      (affineMovingRawSecond f a b A d v δ V₀ W₀ U V) := by
  have hK₀ : 0 ≤ K := le_trans (by norm_num) hK
  have hC : 0 ≤ C := H.value.nonneg
  have hL (t : ℝ) : 0 ≤ K*(1+|t|) := mul_nonneg hK₀ (by positivity)
  have hVt (t : ℝ) : WJets r (K*(1+|t|)) 0 (fun _ : X => V₀ t) :=
    (WJets.const r (V₀ t)).mono (hVW t).1 le_rfl
  have hWt (t : ℝ) : WJets r (K*(1+|t|)) 0 (fun _ : X => W₀ t) :=
    (WJets.const r (W₀ t)).mono (hVW t).2 le_rfl
  have hVz (t : ℝ) : WJets r (K*(1+|t|)) 0 (fun _ : X => V₀ 0) := by
    apply (WJets.const r (V₀ 0)).mono
    · have hz := (hVW 0).1
      simp only [abs_zero,add_zero,mul_one] at hz
      exact hz.trans (le_mul_of_one_le_right hK₀ (by linarith [abs_nonneg t]))
    · exact le_rfl
  have hUj (t : ℝ) : WJets r (K*(1+|t|)) 1 U := by
    have HU : WJets r ‖U‖ 1 (fun x : X => U x) := by
      simpa only [norm_zero,add_zero] using WJets.affine r U 0
    exact HU.mono (hU.trans (le_mul_of_one_le_right hK₀ (by linarith [abs_nonneg t]))) le_rfl
  have hVj (t : ℝ) : WJets r (K*(1+|t|)) 1 V := by
    have HV : WJets r ‖V‖ 1 (fun x : X => V x) := by
      simpa only [norm_zero,add_zero] using WJets.affine r V 0
    exact HV.mono (hV.trans (le_mul_of_one_le_right hK₀ (by linarith [abs_nonneg t]))) le_rfl
  have hcoef (t : ℝ) : C*movingTestProfileCoefficient r p A d v (K*(1+|t|)) t ≤
      (C*movingTestProfileUniformCoefficient r p K*W^p)*(1+|t|)^(p+2) := by
    calc
      _ ≤ C*(movingTestProfileUniformCoefficient r p K*W^p*(1+|t|)^(p+2)) :=
        mul_le_mul_of_nonneg_left (movingTestProfileCoefficient_uniform hp hK hW A d v hA hd hv t) hC
      _ = _ := by ring
  have hs := movingTestProfiles_contDiff (δ := δ) H.value H.first H.second hV₀ hW₀ U.contDiff V.contDiff A d v
  refine ⟨movingValue_affine_contDiff (H.value.of_le (by omega)) A d v,
    affineMovingRawFirst_contDiff (H.value.of_le (by omega)) (H.first.of_le (by omega)) hV₀ U.contDiff A d v,
    hs.1,hs.2.1,hs.2.2,?_,?_,?_⟩
  · intro t
    exact (movingValue_affine_profile (H.value.of_le (by omega)) (hL t) A d v).mono (hcoef t) le_rfl
  · intro t
    exact (movingRawFirst_affine_profile (by omega : 1 ≤ p)
      (H.value.of_le (by omega)) (H.first.of_le (by omega))
      (H.coarse_gradient.mono le_rfl (by omega : p-2 ≤ p-1))
      (hVt t) (hUj t) A d v).mono (hcoef t) le_rfl
  · intro t
    exact (movingTestProfiles_affine hp hδ H.value H.first H.second H.coarse_value
      H.coarse_gradient H.coarse_hessian H.coarse_first H.coarse_first_gradient
      (hVt t) (hVz t) (hUj t) (hWt t) (hVj t) A d v).mono (hcoef t)

end SKBarriers2.Corner
