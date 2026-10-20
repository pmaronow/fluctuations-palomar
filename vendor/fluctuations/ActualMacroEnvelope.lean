module

public import ActualMacroMinimum
public import WallEnvelope

@[expose] public section

noncomputable section

namespace OAI.SKFluctuations.LaplaceWindowFormalization

open MeasureTheory Filter Set Hierarchy
open scoped Topology NNReal

def macroInterpolationObjective (n : ℕ) (b h q : ℝ → ℝ) (t : ℝ) : ℝ :=
  massStrengthObjective n (fun u => (1-t)*b u) h (fun u => t*b u) q

theorem weighted_quantile_power_integrable (b q : ℝ → ℝ)
    (hb : MonotoneOn b (Icc (0 : ℝ) 1))
    (hq : MonotoneOn q (Icc (0 : ℝ) 1))
    (hbn : ∀ u ∈ Icc (0 : ℝ) 1, 0 ≤ b u)
    (hqn : ∀ u ∈ Icc (0 : ℝ) 1, 0 ≤ q u) (k : ℕ) :
    IntervalIntegrable (fun u => b u * q u^k) volume 0 1 := by
  have hm : MonotoneOn (fun u => b u * q u^k) (Icc (0 : ℝ) 1) := by
    intro u hu v hv huv
    exact mul_le_mul (hb hu hv huv) (pow_le_pow_left₀ (hqn u hu) (hq hu hv huv) k)
      (pow_nonneg (hqn u hu) _) (hbn v hv)
  exact (show MonotoneOn (fun u => b u * q u^k) (uIcc (0 : ℝ) 1) by simpa using hm).intervalIntegrable

theorem macro_interpolation_derivative (n : ℕ) (hn : 0 < n)
    (b h q : ℝ → ℝ) {W t : ℝ} (hW : 0 ≤ W)
    (hb : MonotoneOn b (Icc (0 : ℝ) 1))
    (hh : MonotoneOn h (Icc (0 : ℝ) 1))
    (hq : MonotoneOn q (Icc (0 : ℝ) 1))
    (hbb : ∀ u ∈ Icc (0 : ℝ) 1, b u ∈ Icc (0 : ℝ) W)
    (hqb : ∀ u ∈ Icc (0 : ℝ) 1, q u ∈ Icc (0 : ℝ) 1)
    (hhn : ∀ u ∈ Icc (0 : ℝ) 1, 0 ≤ h u)
    (ht : t ∈ Ioo (0 : ℝ) 1) :
    let bf := fun u => ((1-t)*b u).toNNReal
    let hf := fun u => (h u+t*b u*q u).toNNReal
    HasDerivAt (macroInterpolationObjective n b h q)
      ((1/4:ℝ)*(∫ u in (0:ℝ)..1,
        b u*(orderedPathB n bf hf u - 2*q u*orderedPathS n bf hf u + q u^2))) t := by
  dsimp only
  have hbm (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      MonotoneOn (fun u => b u - s*b u) (Icc (0 : ℝ) 1) := by
    intro u hu v hv huv
    have he : ∀ x, b x-s*b x=(1-s)*b x := by intro x; ring
    simpa only [he] using mul_le_mul_of_nonneg_left (hb hu hv huv) (sub_nonneg.mpr hs.2)
  have hfm (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      MonotoneOn (fun u => h u+s*b u*q u) (Icc (0 : ℝ) 1) := by
    intro u hu v hv huv
    exact add_le_add (hh hu hv huv)
      (mul_le_mul (mul_le_mul_of_nonneg_left (hb hu hv huv) hs.1)
        (hq hu hv huv) (hqb u hu).1 (mul_nonneg hs.1 (hbb v hv).1))
  have hbn (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) :
      0 ≤ b u-s*b u := by nlinarith [(hbb u hu).1, hs.2]
  have hfn (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) :
      0 ≤ h u+s*b u*q u :=
    add_nonneg (hhn u hu) (mul_nonneg (mul_nonneg hs.1 (hbb u hu).1) (hqb u hu).1)
  have hevent : ∀ᶠ τ in 𝓝 (0 : ℝ), t+τ ∈ Icc (0 : ℝ) 1 := by
    have hm : Tendsto (fun τ : ℝ => t+τ) (𝓝 0) (𝓝 (t+0)) :=
      tendsto_const_nhds.add tendsto_id
    have hm' : Tendsto (fun τ : ℝ => t+τ) (𝓝 0) (𝓝 t) := by simpa only [add_zero] using hm
    exact hm'.eventually (Icc_mem_nhds ht.1 ht.2)
  have hev : ∀ᶠ τ in 𝓝[(univ : Set ℝ) \ {0}] (0 : ℝ), t+τ ∈ Icc (0 : ℝ) 1 :=
    hevent.filter_mono nhdsWithin_le_nhds
  have hti : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2.le⟩
  have hbint : IntervalIntegrable b volume 0 1 :=
    (show MonotoneOn b (uIcc (0 : ℝ) 1) by simpa using hb).intervalIntegrable
  have hqint : IntervalIntegrable (fun u => b u*q u) volume 0 1 := by
    simpa using weighted_quantile_power_integrable b q hb hq (fun u hu => (hbb u hu).1)
      (fun u hu => (hqb u hu).1) 1
  have hkint := weighted_quantile_power_integrable b q hb hq (fun u hu => (hbb u hu).1)
    (fun u hu => (hqb u hu).1) 2
  have hprod (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) : b u*q u ≤ W := by
    calc
      b u*q u ≤ b u*1 := mul_le_mul_of_nonneg_left (hqb u hu).2 (hbb u hu).1
      _ ≤ W := by simpa using (hbb u hu).2
  have hprod2 (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) : b u*q u^2 ≤ W := by
    have hsq : q u^2 ≤ 1 := by nlinarith [(hqb u hu).1, (hqb u hu).2]
    calc
      b u*q u^2 ≤ b u*1 := mul_le_mul_of_nonneg_left hsq (hbb u hu).1
      _ ≤ W := by simpa using (hbb u hu).2
  have hd := compensated_curve_derivative n hn b h
    (fun τ u => (t+τ)*b u) (fun τ u => (t+τ)*b u*q u)
    (fun τ u => (t+τ)*(b u*q u^2)) b (fun u => b u*q u)
    (fun u => b u*q u^2) W W W univ
    (by simpa using hbm t hti) (by simpa using hfm t hti)
    (by simpa using hbn t hti) (by simpa using hfn t hti)
    (hev.mono (fun τ hτ => hbm (t+τ) hτ))
    (hev.mono (fun τ hτ => hfm (t+τ) hτ))
    (hev.mono (fun τ hτ => hbn (t+τ) hτ))
    (hev.mono (fun τ hτ => hfn (t+τ) hτ))
    (Eventually.of_forall (by
      intro τ u hu
      have he : (t+τ)*b u-(t+0)*b u=τ*b u := by ring
      rw [he, abs_mul, abs_of_nonneg (hbb u hu).1]
      exact mul_le_mul_of_nonneg_left (hbb u hu).2 (abs_nonneg _)))
    (Eventually.of_forall (by
      intro τ u hu
      have he : (t+τ)*b u*q u-(t+0)*b u*q u=τ*(b u*q u) := by ring
      rw [he, abs_mul, abs_of_nonneg (mul_nonneg (hbb u hu).1 (hqb u hu).1)]
      exact mul_le_mul_of_nonneg_left (hprod u hu) (abs_nonneg _)))
    (Eventually.of_forall (by
      intro τ u hu
      have he : (t+τ)*(b u*q u^2)-(t+0)*(b u*q u^2)=τ*(b u*q u^2) := by ring
      rw [he, abs_mul, abs_of_nonneg (mul_nonneg (hbb u hu).1 (sq_nonneg _))]
      exact mul_le_mul_of_nonneg_left (hprod2 u hu) (abs_nonneg _)))
    hbint hqint hkint (by simpa using hkint.const_mul t)
    (Eventually.of_forall (fun τ => hkint.const_mul (t+τ)))
    (Eventually.of_forall (by intro u _; simpa using
      (((hasDerivAt_id (0:ℝ)).const_add t).mul_const (b u))))
    (Eventually.of_forall (by intro u _; simpa [mul_assoc] using
      (((hasDerivAt_id (0:ℝ)).const_add t).mul_const (b u*q u))))
    (Eventually.of_forall (by intro u _; simpa using
      (((hasDerivAt_id (0:ℝ)).const_add t).mul_const (b u*q u^2))))
  have hd' := (hasDerivWithinAt_univ.mp hd).comp_of_eq t ((hasDerivAt_id t).sub_const t) (by simp)
  convert hd' using 1
  · ext s
    dsimp only [Function.comp_apply, id_eq]
    unfold macroInterpolationObjective massStrengthObjective
    have hc : t+(s-t)=s := by ring
    rw [hc]
    have he : (fun u => (1-s)*b u) = (fun u => b u-s*b u) := by funext u; ring
    rw [he]
    congr 2
    apply intervalIntegral.integral_congr
    intro u _
    ring
  · rw [mul_one]
    apply congrArg (fun x : ℝ => (1/4:ℝ)*x)
    apply intervalIntegral.integral_congr
    intro u _
    have he : (fun u => (b u-(t+0)*b u).toNNReal) = (fun u => ((1-t)*b u).toNNReal) := by
      funext u; congr 1; ring
    rw [he]
    simp only [add_zero, mul_one]
    ring

theorem macro_interpolation_lipschitz (n : ℕ) (hn : 0 < n)
    (b h q : ℝ → ℝ) {W : ℝ} (hW : 0 ≤ W)
    (hb : MonotoneOn b (Icc (0 : ℝ) 1))
    (hh : MonotoneOn h (Icc (0 : ℝ) 1))
    (hq : MonotoneOn q (Icc (0 : ℝ) 1))
    (hbb : ∀ u ∈ Icc (0 : ℝ) 1, b u ∈ Icc (0 : ℝ) W)
    (hqb : ∀ u ∈ Icc (0 : ℝ) 1, q u ∈ Icc (0 : ℝ) 1)
    (hhn : ∀ u ∈ Icc (0 : ℝ) 1, 0 ≤ h u) :
    LipschitzOnWith (NNReal.mk W hW) (macroInterpolationObjective n b h q) (Icc (0 : ℝ) 1) := by
  have hbm (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      MonotoneOn (fun u => (1-t)*b u) (Icc (0 : ℝ) 1) := by
    intro u hu v hv huv
    exact mul_le_mul_of_nonneg_left (hb hu hv huv) (sub_nonneg.mpr ht.2)
  have hfm (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      MonotoneOn (fun u => h u+t*b u*q u) (Icc (0 : ℝ) 1) := by
    intro u hu v hv huv
    exact add_le_add (hh hu hv huv)
      (mul_le_mul (mul_le_mul_of_nonneg_left (hb hu hv huv) ht.1)
        (hq hu hv huv) (hqb u hu).1 (mul_nonneg ht.1 (hbb v hv).1))
  have hfn (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) :
      0 ≤ h u+t*b u*q u :=
    add_nonneg (hhn u hu) (mul_nonneg (mul_nonneg ht.1 (hbb u hu).1) (hqb u hu).1)
  have h00 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
  have hprod (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) : b u*q u ≤ W := by
    calc
      b u*q u ≤ b u*1 := mul_le_mul_of_nonneg_left (hqb u hu).2 (hbb u hu).1
      _ ≤ W := by simpa using (hbb u hu).2
  have hprod2 (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) : b u*q u^2 ≤ W := by
    have hsq : q u^2 ≤ 1 := by nlinarith [(hqb u hu).1, (hqb u hu).2]
    calc
      b u*q u^2 ≤ b u*1 := mul_le_mul_of_nonneg_left hsq (hbb u hu).1
      _ ≤ W := by simpa using (hbb u hu).2
  have hi := intervalIntegral_abs_le_unit_bound (f := fun u => b u*q u^2) (C := W) (by
    intro u hu
    rw [abs_of_nonneg (mul_nonneg (hbb u hu).1 (sq_nonneg _))]
    exact hprod2 u hu)
  apply LipschitzOnWith.of_dist_le_mul
  intro s hs t ht
  rw [Real.dist_eq, Real.dist_eq]
  change |macroInterpolationObjective n b h q s - macroInterpolationObjective n b h q t| ≤ W * |s-t|
  have hp := realOrderedSKPathPressure_uniform_comparison n hn
    (fun u => (1-s)*b u) (fun u => h u+s*b u*q u)
    (fun u => (1-t)*b u) (fun u => h u+t*b u*q u)
    (hbm s hs) (hfm s hs) (hbm t ht) (hfm t ht)
    (mul_nonneg (sub_nonneg.mpr hs.2) (hbb 0 h00).1) (hfn s hs 0 h00)
    (mul_nonneg (sub_nonneg.mpr ht.2) (hbb 0 h00).1) (hfn t ht 0 h00)
    (B := W*|s-t|) (H := W*|s-t|) (by
      intro u hu
      have he : (1-s)*b u-(1-t)*b u=-(s-t)*b u := by ring
      rw [he, abs_mul, abs_neg, abs_of_nonneg (hbb u hu).1]
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hbb u hu).2 (abs_nonneg (s-t))) (by
      intro u hu
      have he : h u+s*b u*q u-(h u+t*b u*q u)=(s-t)*(b u*q u) := by ring
      rw [he, abs_mul, abs_of_nonneg (mul_nonneg (hbb u hu).1 (hqb u hu).1)]
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hprod u hu) (abs_nonneg (s-t))) 0
  have hid : macroInterpolationObjective n b h q s - macroInterpolationObjective n b h q t =
      (realOrderedSKPathPressure n (fun u => (1-s)*b u) (fun u => h u+s*b u*q u) 0 -
        realOrderedSKPathPressure n (fun u => (1-t)*b u) (fun u => h u+t*b u*q u) 0) +
      ((s-t)/4)*(∫ u in (0:ℝ)..1,b u*q u^2) := by
    unfold macroInterpolationObjective massStrengthObjective
    have hi' (a : ℝ) : (∫u in (0:ℝ)..1,(a*b u)*q u^2)=a*(∫u in (0:ℝ)..1,b u*q u^2) := by
      simp only [mul_assoc, intervalIntegral.integral_const_mul]
    rw [hi', hi']
    ring
  rw [hid]
  have ha := abs_add_le
    (realOrderedSKPathPressure n (fun u => (1-s)*b u) (fun u => h u+s*b u*q u) 0 -
      realOrderedSKPathPressure n (fun u => (1-t)*b u) (fun u => h u+t*b u*q u) 0)
    (((s-t)/4)*(∫ u in (0:ℝ)..1,b u*q u^2))
  rw [abs_mul, abs_div, abs_of_pos (by norm_num : 0 < (4:ℝ))] at ha
  have hpen := mul_le_mul_of_nonneg_left hi (div_nonneg (abs_nonneg (s-t)) (by norm_num : 0 ≤ (4:ℝ)))
  nlinarith

section
variable {η Q W : ℝ} (hη : 0 < η) (hη1 : η < 1) (hQ : 1 < Q)

def macroMinimumValue (n : ℕ) (b h : ℝ → ℝ) (t : ℝ) : ℝ :=
  sInf (range (fun α : MacroInverseClass η Q =>
    macroInterpolationObjective n b h (macroInverseQuantile hη hQ α) t))

include hη1 in
theorem macroMinimumValue_attained (n : ℕ) (hn : 0 < n) (b h : ℝ → ℝ) (hW : 0 ≤ W)
    (hb : MonotoneOn b (Icc (0 : ℝ) 1))
    (hh : MonotoneOn h (Icc (0 : ℝ) 1))
    (hbb : ∀ u ∈ Icc (0 : ℝ) 1, b u ∈ Icc (0 : ℝ) W)
    (hhn : ∀ u ∈ Icc (0 : ℝ) 1, 0 ≤ h u)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ∃ α : MacroInverseClass η Q,
      macroInterpolationObjective n b h (macroInverseQuantile hη hQ α) t = macroMinimumValue hη hQ n b h t ∧
      ∀ β : MacroInverseClass η Q, macroMinimumValue hη hQ n b h t ≤
        macroInterpolationObjective n b h (macroInverseQuantile hη hQ β) t := by
  have h00 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
  have hb' : MonotoneOn (fun u => (1-t)*b u) (Icc (0 : ℝ) 1) := by
    intro u hu v hv huv
    exact mul_le_mul_of_nonneg_left (hb hu hv huv) (sub_nonneg.mpr ht.2)
  have hw : MonotoneOn (fun u => t*b u) (Icc (0 : ℝ) 1) := by
    intro u hu v hv huv
    exact mul_le_mul_of_nonneg_left (hb hu hv huv) ht.1
  obtain ⟨α, hα⟩ := macroInverseObjective_minimum hη hη1 hQ n hn
    (fun u => (1-t)*b u) h (fun u => t*b u) (W := t*W) (mul_nonneg ht.1 hW) hb' hh hw
    (fun u hu => ⟨mul_nonneg ht.1 (hbb u hu).1,
      mul_le_mul_of_nonneg_left (hbb u hu).2 ht.1⟩)
    (mul_nonneg (sub_nonneg.mpr ht.2) (hbb 0 h00).1) (hhn 0 h00)
  have hleast : IsLeast (range (fun α : MacroInverseClass η Q =>
      macroInterpolationObjective n b h (macroInverseQuantile hη hQ α) t))
      (macroInterpolationObjective n b h (macroInverseQuantile hη hQ α) t) := by
    refine ⟨⟨α, rfl⟩, ?_⟩
    rintro _ ⟨β, rfl⟩
    exact hα β
  have he : macroMinimumValue hη hQ n b h t =
      macroInterpolationObjective n b h (macroInverseQuantile hη hQ α) t := hleast.csInf_eq
  exact ⟨α, he.symm, fun β => he.trans_le (hα β)⟩

include hη1 in
theorem macroMinimumValue_lipschitz (n : ℕ) (hn : 0 < n) (b h : ℝ → ℝ) (hW : 0 ≤ W)
    (hb : MonotoneOn b (Icc (0 : ℝ) 1))
    (hh : MonotoneOn h (Icc (0 : ℝ) 1))
    (hbb : ∀ u ∈ Icc (0 : ℝ) 1, b u ∈ Icc (0 : ℝ) W)
    (hhn : ∀ u ∈ Icc (0 : ℝ) 1, 0 ≤ h u) :
    LipschitzOnWith (NNReal.mk W hW) (macroMinimumValue hη hQ n b h) (Icc (0 : ℝ) 1) := by
  apply WallSweep.minimum_lipschitzOn
    (fun t α => macroInterpolationObjective n b h (macroInverseQuantile hη hQ α) t)
  · intro t ht
    exact macroMinimumValue_attained hη hη1 hQ n hn b h hW hb hh hbb hhn ht
  · intro α
    exact macro_interpolation_lipschitz n hn b h (macroInverseQuantile hη hQ α) hW hb hh
      (macroInverseQuantile_monotone hη hQ α) hbb
      (fun u _ => macroInverseQuantile_bounds hη hQ α u) hhn

end

end OAI.SKFluctuations.LaplaceWindowFormalization
