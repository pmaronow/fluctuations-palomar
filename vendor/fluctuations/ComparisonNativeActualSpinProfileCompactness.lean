module

public import ComparisonNativeActualMeanRawUpper
public import NonnegativeMassProfileHelly

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology
set_option maxHeartbeats 5000000

namespace NativeOverlapMinimum

def actualRescaledSpinProfile {m delta cl cu Az C0 Ct D Bclock : ℝ} {n : ℕ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) :
    NonnegativeMassProfile where
  mass t := orderedPathS (n+1) M.bf M.hf (max 0 (min (M.xs*t) 1))/M.xs
  nonneg t := div_nonneg (M.mass_mean_nonneg
    ⟨le_max_left _ _,max_le zero_le_one (min_le_right _ _)⟩) M.hxs.le
  monotone := by
    intro s t hst
    apply div_le_div_of_nonneg_right _ M.hxs.le
    apply M.mass_mean_monotone
      ⟨le_max_left _ _,max_le zero_le_one (min_le_right _ _)⟩
      ⟨le_max_left _ _,max_le zero_le_one (min_le_right _ _)⟩
    exact max_le_max le_rfl (min_le_min (mul_le_mul_of_nonneg_left hst M.hxs.le) le_rfl)

end NativeOverlapMinimum

theorem exists_actual_rescaled_spin_profile_limit
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ) → NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (hx : Tendsto (fun n=>(M n).xs) atTop (𝓝 0)) :
    ∃(s : NonnegativeMassProfile) (B : ℝ) (phi : ℕ → ℕ),0 < B ∧ StrictMono phi ∧
      (∀t : ℝ,0 ≤ t → s.mass t ≤ B*(1+t)) ∧
      ∀t : ℝ,0 ≤ t → Tendsto (fun n=>
        orderedPathS (dim (phi n)+1) (M (phi n)).bf (M (phi n)).hf
          ((M (phi n)).xs*t)/(M (phi n)).xs) atTop (𝓝 (s.mass t)) := by
  obtain ⟨B,hB,HB⟩ := eventually_actual_minimum_mass_mean_upper Bclock
    hm hdelta hroom hcl hcu hAz hC0 hCt
  have Hcap : ∀t : ℝ,0 ≤ t → ∀ᶠn in atTop,
      (M n).actualRescaledSpinProfile.mass t ≤ B*(1+t) := by
    intro t ht
    filter_upwards [hdim.eventually HB] with n hn
    let u := max 0 (min ((M n).xs*t) 1)
    have hu : u∈Icc (0:ℝ) 1 :=
      ⟨le_max_left _ _,max_le zero_le_one (min_le_right _ _)⟩
    have hux : u ≤ (M n).xs*t := max_le (mul_nonneg (M n).hxs.le ht) (min_le_left _ _)
    change orderedPathS (dim n+1) (M n).bf (M n).hf u/(M n).xs ≤ _
    by_cases hu0 : u=0
    · rw [hu0]
      simp only [orderedPathS,orderedPathPair_zero,zero_div]
      positivity
    · have hup : 0 < u := lt_of_le_of_ne hu.1 (Ne.symm hu0)
      apply (div_le_iff₀ (M n).hxs).mpr
      calc
        orderedPathS (dim n+1) (M n).bf (M n).hf u  ≤  B*((M n).xs+u) :=
          hn (M n) u ⟨hup,hu.2⟩
        _  ≤  B*((M n).xs+(M n).xs*t) := by gcongr
        _ = B*(1+t)*(M n).xs := by ring
  obtain ⟨s,phi,hphi,Hs⟩ := nonnegativeMassProfile_locallyBounded_tendsto_subseq
    (fun n=>(M n).actualRescaledSpinProfile)
    (fun R hR=>⟨B*(1+R),Hcap R hR.le⟩)
  refine ⟨s,B,phi,hB,hphi,?_,?_⟩
  · intro t ht
    exact le_of_tendsto (Hs t) (hphi.tendsto_atTop.eventually (Hcap t ht))
  · intro t ht
    have Hsmall : ∀ᶠn in atTop,(M (phi n)).xs*t ≤ 1 := by
      have H := ((hx.comp hphi.tendsto_atTop).mul_const t).eventually
        (gt_mem_nhds (by simp : (0:ℝ)*t < 1))
      simpa only [zero_mul,Function.comp_apply] using H.mono fun n hn=>hn.le
    apply (Hs t).congr'
    filter_upwards [Hsmall] with n hn
    change orderedPathS _ _ _ (max 0 (min ((M (phi n)).xs*t) 1))/(M (phi n)).xs=_
    rw [min_eq_left hn,max_eq_right (mul_nonneg (M (phi n)).hxs.le ht)]

end OAI.SKFluctuations.LaplaceWindowFormalization
