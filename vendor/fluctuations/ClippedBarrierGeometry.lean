module

public import Mathlib

@[expose] public section

noncomputable section
set_option maxHeartbeats 1000000
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory Filter Set
open scoped Topology NNReal

theorem differentiable_min_selection {f g : ℝ→ℝ} {x : ℝ}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x)
    (hm : DifferentiableAt ℝ (fun u=>min (f u) (g u)) x) :
    (min (f x) (g x)=f x ∧ deriv (fun u=>min (f u) (g u)) x=deriv f x) ∨
      (min (f x) (g x)=g x ∧ deriv (fun u=>min (f u) (g u)) x=deriv g x) := by
  rcases lt_trichotomy (f x) (g x) with hlt | heq | hgt
  · have he : (fun u=>min (f u) (g u))=ᶠ[𝓝 x] f := by
      filter_upwards [(hf.continuousAt.sub hg.continuousAt).tendsto.eventually
        (gt_mem_nhds (sub_neg.mpr hlt))] with u hu
      change f u-g u<0 at hu
      exact min_eq_left (by linarith)
    exact Or.inl ⟨min_eq_left hlt.le,he.deriv_eq⟩
  · have hlocal : IsLocalMin (fun u=>f u-min (f u) (g u)) x := by
      apply Eventually.of_forall
      intro u
      simp only [heq,min_self,sub_self]
      exact sub_nonneg.mpr (min_le_left _ _)
    have hz := hlocal.hasDerivAt_eq_zero (hf.hasDerivAt.sub hm.hasDerivAt)
    exact Or.inl ⟨by rw [heq,min_self],by linarith⟩
  · have he : (fun u=>min (f u) (g u))=ᶠ[𝓝 x] g := by
      filter_upwards [(hg.continuousAt.sub hf.continuousAt).tendsto.eventually
        (gt_mem_nhds (sub_neg.mpr hgt))] with u hu
      change g u-f u<0 at hu
      exact min_eq_right (by linarith)
    exact Or.inr ⟨min_eq_right hgt.le,he.deriv_eq⟩

theorem differentiable_max_selection {f g : ℝ→ℝ} {x : ℝ}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x)
    (hm : DifferentiableAt ℝ (fun u=>max (f u) (g u)) x) :
    (max (f x) (g x)=f x ∧ deriv (fun u=>max (f u) (g u)) x=deriv f x) ∨
      (max (f x) (g x)=g x ∧ deriv (fun u=>max (f u) (g u)) x=deriv g x) := by
  rcases lt_trichotomy (f x) (g x) with hlt | heq | hgt
  · have he : (fun u=>max (f u) (g u))=ᶠ[𝓝 x] g := by
      filter_upwards [(hf.continuousAt.sub hg.continuousAt).tendsto.eventually
        (gt_mem_nhds (sub_neg.mpr hlt))] with u hu
      change f u-g u<0 at hu
      exact max_eq_right (by linarith)
    exact Or.inr ⟨max_eq_right hlt.le,he.deriv_eq⟩
  · have hlocal : IsLocalMin (fun u=>max (f u) (g u)-f u) x := by
      apply Eventually.of_forall
      intro u
      simp only [heq,max_self,sub_self]
      exact sub_nonneg.mpr (le_max_left _ _)
    have hz := hlocal.hasDerivAt_eq_zero (hm.hasDerivAt.sub hf.hasDerivAt)
    exact Or.inl ⟨by rw [heq,max_self],by linarith⟩
  · have he : (fun u=>max (f u) (g u))=ᶠ[𝓝 x] f := by
      filter_upwards [(hg.continuousAt.sub hf.continuousAt).tendsto.eventually
        (gt_mem_nhds (sub_neg.mpr hgt))] with u hu
      change g u-f u<0 at hu
      exact max_eq_left (by linarith)
    exact Or.inl ⟨max_eq_left hgt.le,he.deriv_eq⟩

theorem real_min_lipschitzOn {s : Set ℝ} {f g : ℝ→ℝ} {C D : ℝ≥0}
    (hf : LipschitzOnWith C f s) (hg : LipschitzOnWith D g s) :
    LipschitzOnWith (max C D) (fun u=>min (f u) (g u)) s := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  have hC := hf.dist_le_mul x hx y hy
  have hD := hg.dist_le_mul x hx y hy
  have hmax := abs_min_sub_min_le_max (f x) (g x) (f y) (g y)
  simp only [Real.dist_eq] at hC hD ⊢
  apply hmax.trans
  apply max_le
  · exact hC.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast le_max_left C D) (abs_nonneg (x-y)))
  · exact hD.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast le_max_right C D) (abs_nonneg (x-y)))

theorem real_max_lipschitzOn {s : Set ℝ} {f g : ℝ→ℝ} {C D : ℝ≥0}
    (hf : LipschitzOnWith C f s) (hg : LipschitzOnWith D g s) :
    LipschitzOnWith (max C D) (fun u=>max (f u) (g u)) s := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  have hC := hf.dist_le_mul x hx y hy
  have hD := hg.dist_le_mul x hx y hy
  have hmax := abs_max_sub_max_le_max (f x) (g x) (f y) (g y)
  simp only [Real.dist_eq] at hC hD ⊢
  apply hmax.trans
  apply max_le
  · exact hC.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast le_max_left C D) (abs_nonneg (x-y)))
  · exact hD.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast le_max_right C D) (abs_nonneg (x-y)))

theorem clipped_min_ae_slope {r w lower upper : ℝ→ℝ} {C D : ℝ≥0}
    (hr : LipschitzOnWith C r (Icc (0:ℝ) 1)) (hw : LipschitzOnWith D w (Icc (0:ℝ) 1))
    (hdr : ∀ᵐ u∂volume,u∈Icc (0:ℝ) 1 → lower u≤deriv r u ∧ deriv r u≤upper (r u))
    (hdw : ∀ᵐ u∂volume,u∈Icc (0:ℝ) 1 → w u≤r u →
      lower u≤deriv w u ∧ deriv w u≤upper (w u)) :
    ∀ᵐ u∂volume,u∈Icc (0:ℝ) 1 →
      lower u≤deriv (fun v=>min (r v) (w v)) u ∧
      deriv (fun v=>min (r v) (w v)) u≤upper (min (r u) (w u)) := by
  have hrv : AbsolutelyContinuousOnInterval r 0 1 := by
    apply LipschitzOnWith.absolutelyContinuousOnInterval (K := C)
    simpa only [uIcc_of_le zero_le_one] using hr
  have hwv : AbsolutelyContinuousOnInterval w 0 1 := by
    apply LipschitzOnWith.absolutelyContinuousOnInterval (K := D)
    simpa only [uIcc_of_le zero_le_one] using hw
  have hmv : AbsolutelyContinuousOnInterval (fun u=>min (r u) (w u)) 0 1 := by
    apply LipschitzOnWith.absolutelyContinuousOnInterval (K := max C D)
    simpa only [uIcc_of_le zero_le_one] using real_min_lipschitzOn hr hw
  filter_upwards [hdr,hdw,hrv.ae_differentiableAt,hwv.ae_differentiableAt,hmv.ae_differentiableAt]
    with u hdr hdw hr hw hm hu
  have hu' : u∈uIcc (0:ℝ) 1 := by simpa only [uIcc_of_le zero_le_one] using hu
  rcases differentiable_min_selection (hr hu') (hw hu') (hm hu') with h | h
  · rw [h.1,h.2]
    exact hdr hu
  · rw [h.1,h.2]
    exact hdw hu (by rw [←h.1];exact min_le_left _ _)

theorem clipped_max_ae_slope {r w lower upper : ℝ→ℝ} {C D : ℝ≥0}
    (hr : LipschitzOnWith C r (Icc (0:ℝ) 1)) (hw : LipschitzOnWith D w (Icc (0:ℝ) 1))
    (hdr : ∀ᵐ u∂volume,u∈Icc (0:ℝ) 1 → lower u≤deriv r u ∧ deriv r u≤upper (r u))
    (hdw : ∀ᵐ u∂volume,u∈Icc (0:ℝ) 1 → r u≤w u →
      lower u≤deriv w u ∧ deriv w u≤upper (w u)) :
    ∀ᵐ u∂volume,u∈Icc (0:ℝ) 1 →
      lower u≤deriv (fun v=>max (r v) (w v)) u ∧
      deriv (fun v=>max (r v) (w v)) u≤upper (max (r u) (w u)) := by
  have hrv : AbsolutelyContinuousOnInterval r 0 1 := by
    apply LipschitzOnWith.absolutelyContinuousOnInterval (K := C)
    simpa only [uIcc_of_le zero_le_one] using hr
  have hwv : AbsolutelyContinuousOnInterval w 0 1 := by
    apply LipschitzOnWith.absolutelyContinuousOnInterval (K := D)
    simpa only [uIcc_of_le zero_le_one] using hw
  have hmv : AbsolutelyContinuousOnInterval (fun u=>max (r u) (w u)) 0 1 := by
    apply LipschitzOnWith.absolutelyContinuousOnInterval (K := max C D)
    simpa only [uIcc_of_le zero_le_one] using real_max_lipschitzOn hr hw
  filter_upwards [hdr,hdw,hrv.ae_differentiableAt,hwv.ae_differentiableAt,hmv.ae_differentiableAt]
    with u hdr hdw hr hw hm hu
  have hu' : u∈uIcc (0:ℝ) 1 := by simpa only [uIcc_of_le zero_le_one] using hu
  rcases differentiable_max_selection (hr hu') (hw hu') (hm hu') with h | h
  · rw [h.1,h.2]
    exact hdr hu
  · rw [h.1,h.2]
    exact hdw hu (by rw [←h.1];exact le_max_left _ _)

theorem clipped_max_ae_slope_at_parent {r w lower upper : ℝ→ℝ} {C D : ℝ≥0}
    (hr : LipschitzOnWith C r (Icc (0:ℝ) 1)) (hw : LipschitzOnWith D w (Icc (0:ℝ) 1))
    (hdr : ∀ᵐ u∂volume,u∈Icc (0:ℝ) 1 → lower u≤deriv r u ∧ deriv r u≤upper u)
    (hdw : ∀ᵐ u∂volume,u∈Icc (0:ℝ) 1 → r u≤w u → lower u≤deriv w u ∧ deriv w u≤upper u) :
    ∀ᵐ u∂volume,u∈Icc (0:ℝ) 1 → lower u≤deriv (fun v=>max (r v) (w v)) u ∧
      deriv (fun v=>max (r v) (w v)) u≤upper u := by
  have hrv : AbsolutelyContinuousOnInterval r 0 1 := by
    apply LipschitzOnWith.absolutelyContinuousOnInterval (K := C)
    simpa only [uIcc_of_le zero_le_one] using hr
  have hwv : AbsolutelyContinuousOnInterval w 0 1 := by
    apply LipschitzOnWith.absolutelyContinuousOnInterval (K := D)
    simpa only [uIcc_of_le zero_le_one] using hw
  have hmv : AbsolutelyContinuousOnInterval (fun u=>max (r u) (w u)) 0 1 := by
    apply LipschitzOnWith.absolutelyContinuousOnInterval (K := max C D)
    simpa only [uIcc_of_le zero_le_one] using real_max_lipschitzOn hr hw
  filter_upwards [hdr,hdw,hrv.ae_differentiableAt,hwv.ae_differentiableAt,hmv.ae_differentiableAt]
    with u hdr hdw hr hw hm hu
  have hu' : u∈uIcc (0:ℝ) 1 := by simpa only [uIcc_of_le zero_le_one] using hu
  rcases differentiable_max_selection (hr hu') (hw hu') (hm hu') with h | h
  · rw [h.2]
    exact hdr hu
  · rw [h.2]
    exact hdw hu (by rw [←h.1];exact le_max_left _ _)

end OAI.SKFluctuations.LaplaceWindowFormalization
