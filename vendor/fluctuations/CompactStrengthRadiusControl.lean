module

public import ActualStrengthVariationalLimit
public import RescaledProfileHelly

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory ProbabilityTheory Filter Set Hierarchy Function
open scoped Topology NNReal

theorem actualStrength_profile_geometry {d lam T : ℝ} (hd : d ≠ 0)
    (hlam : lam ∈ Ioo (0:ℝ) T) (r : boundedMassProfiles) :
    ∃ c : ℝ, 0 < c ∧
      AntitoneOn (fun u => laplaceComparisonStrength d lam (r.val u)) (Icc (0:ℝ) 1) ∧
      (∀ u ∈ Icc (0:ℝ) 1, laplaceComparisonStrength d lam (r.val u) ∈ Icc c (T-c)) ∧
      MonotoneOn (fun u => laplaceComparisonStrength d lam (r.val u)*r.val u) (Icc (0:ℝ) 1) := by
  let g1 := laplaceComparisonStrength d lam 1
  let c := min g1 (T-lam)/2
  have hg1 : 0 < g1 := laplaceComparisonStrength_pos d hlam.1 1
  have hc : 0 < c := half_pos (lt_min hg1 (sub_pos.mpr hlam.2))
  have hcg : c ≤ g1 := by
    have hh := min_le_left g1 (T-lam)
    dsimp [c]
    linarith
  have hcT : c ≤ T-lam := by
    have hh := min_le_right g1 (T-lam)
    dsimp [c]
    linarith [hlam.2]
  have hm := laplaceComparisonStrength_monotonicities_nonneg hd hlam.1.le
  refine ⟨c,hc,fun u _ v _ huv => hm.1 (r.property.1 u) (r.property.1 v)
    (r.property.2 huv),?_,fun u _ v _ huv => hm.2 (r.property.1 u) (r.property.1 v)
    (r.property.2 huv)⟩
  intro u _
  have hlo : g1 ≤ laplaceComparisonStrength d lam (r.val u) :=
    hm.1 (r.property.1 u) (by norm_num) (r.property.1 u).2
  have hhi := laplaceComparisonStrength_le d hlam.1.le (r.val u)
  exact ⟨hcg.trans hlo,by linarith⟩

theorem uniform_actualStrength_radius_lower
    {β : ℝ≥0} (hβ : 0 < β) (hT : 1 < (β:ℝ)^2)
    {dlo dhi llo lhi x : ℝ} (hdlo : 0 < dlo) (hllo : 0 < llo)
    (hlhi : lhi < (β:ℝ)^2) (hx : x ∈ Ioo (0:ℝ) 1)
    (error : ℕ → ℝ) (herror : Tendsto error atTop (𝓝 0)) :
    ∃ a : ℝ, 0 < a ∧ ∀ᶠ n : ℕ in atTop,
      ∀ d ∈ Icc dlo dhi, ∀ lam ∈ Icc llo lhi, ∀ r : boundedMassProfiles,
        pathCompensatedPressure n (fun _ => (β:ℝ)^2) (fun _ => 0)
          (fun u => laplaceComparisonStrength d lam (r.val u)) r.val 0 ≤
            normalizedScalarParisiReference β+error n → a ≤ r.val x := by
  classical
  by_contra h
  have hseq (k : ℕ) : ∃ n : ℕ, k ≤ n ∧ ∃ d ∈ Icc dlo dhi,
      ∃ lam ∈ Icc llo lhi, ∃ r : boundedMassProfiles,
        pathCompensatedPressure n (fun _ => (β:ℝ)^2) (fun _ => 0)
          (fun u => laplaceComparisonStrength d lam (r.val u)) r.val 0 ≤
            normalizedScalarParisiReference β+error n ∧ r.val x < 1/(k+1:ℕ) := by
    have he : ¬∀ᶠ n : ℕ in atTop,
        ∀ d ∈ Icc dlo dhi, ∀ lam ∈ Icc llo lhi, ∀ r : boundedMassProfiles,
          pathCompensatedPressure n (fun _ => (β:ℝ)^2) (fun _ => 0)
            (fun u => laplaceComparisonStrength d lam (r.val u)) r.val 0 ≤
              normalizedScalarParisiReference β+error n → 1/(k+1:ℕ) ≤ r.val x := by
      intro he
      exact h ⟨1/(k+1:ℕ),by positivity,he⟩
    rw [eventually_atTop] at he
    push Not at he
    obtain ⟨n,hn,d,hd,lam,hlam,r,hp,hr⟩ := he k
    exact ⟨n,hn,d,hd,lam,hlam,r,hp,hr⟩
  choose N hNk d hd lam hlam r hp hsmall using hseq
  have hN : Tendsto N atTop atTop := tendsto_atTop_mono (fun n => hNk n) tendsto_id
  obtain ⟨R,φ,hφ,hr⟩ := boundedMassProfiles_tendsto_subseq r
  obtain ⟨D,hD,ψ,hψ,hdlim⟩ := isCompact_Icc.tendsto_subseq (fun n => hd (φ n))
  obtain ⟨L,hL,χ,hχ,hlamlim⟩ := isCompact_Icc.tendsto_subseq (fun n => hlam (φ (ψ n)))
  let θ := (φ ∘ ψ) ∘ χ
  have hθ : StrictMono θ := (hφ.comp hψ).comp hχ
  have hR : Tendsto (r ∘ θ) atTop (𝓝 R) :=
    (hr.comp hψ.tendsto_atTop).comp hχ.tendsto_atTop
  have hDlim : Tendsto (d ∘ θ) atTop (𝓝 D) := hdlim.comp hχ.tendsto_atTop
  have hLlim : Tendsto (lam ∘ θ) atTop (𝓝 L) := hlamlim
  have hDz : D ≠ 0 := ne_of_gt (hdlo.trans_le hD.1)
  have hLT : L ∈ Ioo (0:ℝ) ((β:ℝ)^2) := ⟨hllo.trans_le hL.1,hL.2.trans_lt hlhi⟩
  have hval := actualStrengthComparisonPressure_tendsto_jointScalar (N ∘ θ)
    (hN.comp hθ.tendsto_atTop) hDz
    (fun n => ne_of_gt (hdlo.trans_le (hd (θ n)).1)) hDlim hLlim
    (fun n => ⟨hllo.le.trans (hlam (θ n)).1,(hlam (θ n)).2.trans hlhi.le⟩) hLT hR
  have hup : Tendsto (fun n => normalizedScalarParisiReference β+error (N (θ n)))
      atTop (𝓝 (normalizedScalarParisiReference β)) := by
    simpa only [add_zero,Function.comp_apply] using (herror.comp (hN.comp hθ.tendsto_atTop)).const_add
      (normalizedScalarParisiReference β)
  have hv : jointScalarVariationalValue ((β:ℝ)^2)
      (fun u => laplaceComparisonStrength D L (R.val u)) R.val ≤ normalizedScalarParisiReference β :=
    le_of_tendsto_of_tendsto hval hup (Eventually.of_forall fun n => hp (θ n))
  have hzero : R.val x=0 := by
    have hrx := tendsto_pi_nhds.mp (tendsto_subtype_rng.mp hR) x
    have hs : Tendsto (fun n => (r (θ n)).val x) atTop (𝓝 0) :=
      squeeze_zero (fun n => (r (θ n)).property.1 x |>.1)
        (fun n => (hsmall (θ n)).le)
        (SKCavity.tendsto_succ_reciprocal.comp hθ.tendsto_atTop)
    exact tendsto_nhds_unique hrx hs
  obtain ⟨c,hc,he,heb,her⟩ := actualStrength_profile_geometry hDz hLT R
  obtain ⟨cR,CR,ε,hcR,hCR,hε,hband⟩ :=
    jointScalarVariational_near_minimizers_fixed_band hβ hT hc hx.1
  have hbx := hband _ _ he heb her (R.property.2.monotoneOn _)
    (fun u _ => R.property.1 u) (hv.trans (by linarith)) x hx le_rfl
  rw [hzero] at hbx
  exact (not_le_of_gt (mul_pos hcR hx.1)) hbx.1

theorem uniform_actualStrength_radius_lower_near_reference
    {β : ℝ≥0} (hβ : 0 < β) (hT : 1 < (β:ℝ)^2)
    {dlo dhi llo lhi x : ℝ} (hdlo : 0 < dlo) (hllo : 0 < llo)
    (hlhi : lhi < (β:ℝ)^2) (hx : x ∈ Ioo (0:ℝ) 1)
    :
    ∃ a epsilon : ℝ, 0 < a ∧ 0 < epsilon ∧ ∀ᶠ n : ℕ in atTop,
      ∀ d ∈ Icc dlo dhi, ∀ lam ∈ Icc llo lhi, ∀ r : boundedMassProfiles,
        pathCompensatedPressure n (fun _ => (β:ℝ)^2) (fun _ => 0)
          (fun u => laplaceComparisonStrength d lam (r.val u)) r.val 0 ≤
            normalizedScalarParisiReference β+epsilon → a ≤ r.val x := by
  classical
  by_contra h
  have hseq (k : ℕ) : ∃ n : ℕ, k ≤ n ∧ ∃ d ∈ Icc dlo dhi,
      ∃ lam ∈ Icc llo lhi, ∃ r : boundedMassProfiles,
        pathCompensatedPressure n (fun _ => (β:ℝ)^2) (fun _ => 0)
          (fun u => laplaceComparisonStrength d lam (r.val u)) r.val 0 ≤
            normalizedScalarParisiReference β+1/(k+1:ℕ) ∧ r.val x < 1/(k+1:ℕ) := by
    have he : ¬∀ᶠ n : ℕ in atTop,
        ∀ d ∈ Icc dlo dhi, ∀ lam ∈ Icc llo lhi, ∀ r : boundedMassProfiles,
          pathCompensatedPressure n (fun _ => (β:ℝ)^2) (fun _ => 0)
            (fun u => laplaceComparisonStrength d lam (r.val u)) r.val 0 ≤
              normalizedScalarParisiReference β+1/(k+1:ℕ) → 1/(k+1:ℕ) ≤ r.val x := by
      intro he
      exact h ⟨1/(k+1:ℕ),1/(k+1:ℕ),by positivity,by positivity,he⟩
    rw [eventually_atTop] at he
    push Not at he
    obtain ⟨n,hn,d,hd,lam,hlam,r,hp,hr⟩ := he k
    exact ⟨n,hn,d,hd,lam,hlam,r,hp,hr⟩
  choose N hNk d hd lam hlam r hp hsmall using hseq
  have hN : Tendsto N atTop atTop := tendsto_atTop_mono (fun n => hNk n) tendsto_id
  obtain ⟨R,φ,hφ,hr⟩ := boundedMassProfiles_tendsto_subseq r
  obtain ⟨D,hD,ψ,hψ,hdlim⟩ := isCompact_Icc.tendsto_subseq (fun n => hd (φ n))
  obtain ⟨L,hL,χ,hχ,hlamlim⟩ := isCompact_Icc.tendsto_subseq (fun n => hlam (φ (ψ n)))
  let θ := (φ ∘ ψ) ∘ χ
  have hθ : StrictMono θ := (hφ.comp hψ).comp hχ
  have hR : Tendsto (r ∘ θ) atTop (𝓝 R) :=
    (hr.comp hψ.tendsto_atTop).comp hχ.tendsto_atTop
  have hDlim : Tendsto (d ∘ θ) atTop (𝓝 D) := hdlim.comp hχ.tendsto_atTop
  have hLlim : Tendsto (lam ∘ θ) atTop (𝓝 L) := hlamlim
  have hDz : D ≠ 0 := ne_of_gt (hdlo.trans_le hD.1)
  have hLT : L ∈ Ioo (0:ℝ) ((β:ℝ)^2) := ⟨hllo.trans_le hL.1,hL.2.trans_lt hlhi⟩
  have hval := actualStrengthComparisonPressure_tendsto_jointScalar (N ∘ θ)
    (hN.comp hθ.tendsto_atTop) hDz
    (fun n => ne_of_gt (hdlo.trans_le (hd (θ n)).1)) hDlim hLlim
    (fun n => ⟨hllo.le.trans (hlam (θ n)).1,(hlam (θ n)).2.trans hlhi.le⟩) hLT hR
  have hup : Tendsto (fun n => normalizedScalarParisiReference β+1/(θ n+1:ℕ))
      atTop (𝓝 (normalizedScalarParisiReference β)) := by
    simpa only [add_zero,Function.comp_apply] using (SKCavity.tendsto_succ_reciprocal.comp hθ.tendsto_atTop).const_add
      (normalizedScalarParisiReference β)
  have hv : jointScalarVariationalValue ((β:ℝ)^2)
      (fun u => laplaceComparisonStrength D L (R.val u)) R.val ≤ normalizedScalarParisiReference β :=
    le_of_tendsto_of_tendsto hval hup (Eventually.of_forall fun n => hp (θ n))
  have hzero : R.val x=0 := by
    have hrx := tendsto_pi_nhds.mp (tendsto_subtype_rng.mp hR) x
    have hs : Tendsto (fun n => (r (θ n)).val x) atTop (𝓝 0) :=
      squeeze_zero (fun n => (r (θ n)).property.1 x |>.1)
        (fun n => (hsmall (θ n)).le)
        (SKCavity.tendsto_succ_reciprocal.comp hθ.tendsto_atTop)
    exact tendsto_nhds_unique hrx hs
  obtain ⟨c,hc,he,heb,her⟩ := actualStrength_profile_geometry hDz hLT R
  obtain ⟨cR,CR,ε,hcR,hCR,hε,hband⟩ :=
    jointScalarVariational_near_minimizers_fixed_band hβ hT hc hx.1
  have hbx := hband _ _ he heb her (R.property.2.monotoneOn _)
    (fun u _ => R.property.1 u) (hv.trans (by linarith)) x hx le_rfl
  rw [hzero] at hbx
  exact (not_le_of_gt (mul_pos hcR hx.1)) hbx.1

theorem uniform_actualStrength_fixed_band
    {β : ℝ≥0} (hβ : 0 < β) (hT : 1 < (β:ℝ)^2)
    {dlo dhi llo lhi x : ℝ} (hdlo : 0 < dlo) (hllo : 0 < llo)
    (hlhi : lhi < (β:ℝ)^2) (hx : x ∈ Ioo (0:ℝ) 1)
    (error : ℕ → ℝ) (herror : Tendsto error atTop (𝓝 0)) :
    ∃ cR CR : ℝ, 0 < cR ∧ 0 < CR ∧ ∀ᶠ n : ℕ in atTop,
      ∀ d ∈ Icc dlo dhi, ∀ lam ∈ Icc llo lhi, ∀ r : boundedMassProfiles,
        pathCompensatedPressure n (fun _ => (β:ℝ)^2) (fun _ => 0)
          (fun u => laplaceComparisonStrength d lam (r.val u)) r.val 0 ≤
            normalizedScalarParisiReference β+error n →
        ∀ u ∈ Ioo (0:ℝ) 1, x ≤ u → cR*u ≤ r.val u ∧ r.val u ≤ CR*u := by
  obtain ⟨a,ha,he⟩ := uniform_actualStrength_radius_lower hβ hT hdlo hllo hlhi hx error herror
  refine ⟨a,1/x,ha,one_div_pos.mpr hx.1,?_⟩
  filter_upwards [he] with n hn
  intro d hd lam hlam r hp u hu hxu
  have hlo := hn d hd lam hlam r hp
  refine ⟨(mul_le_of_le_one_right ha.le hu.2.le).trans (hlo.trans (r.property.2 hxu)),?_⟩
  have hone : (1:ℝ) ≤ (1/x)*u := by
    rw [div_mul_eq_mul_div,one_mul,le_div_iff₀ hx.1]
    simpa only [one_mul] using hxu
  exact (r.property.1 u).2.trans hone

end OAI.SKFluctuations.LaplaceWindowFormalization
