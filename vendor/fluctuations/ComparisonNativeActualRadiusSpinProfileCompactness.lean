module

public import ComparisonNativeActualMeanRawUpper
public import NonnegativeMassProfileHelly

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology
set_option maxHeartbeats 6000000

namespace NativeOverlapMinimum

def actualRescaledRadiusSpinProfile {m delta cl cu Az C0 Ct D Bclock : ℝ} {n : ℕ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) :
    NonnegativeMassProfile where
  mass t := orderedPathS (n+1) M.bf M.hf (M.alpha.val.val (M.xs*t))/M.xs
  nonneg t := div_nonneg (M.mass_mean_nonneg (M.alpha.val.property.1 _)) M.hxs.le
  monotone := by
    intro s t hst
    apply div_le_div_of_nonneg_right _ M.hxs.le
    exact M.mass_mean_monotone (M.alpha.val.property.1 _) (M.alpha.val.property.1 _)
      (M.alpha.val.property.2 (mul_le_mul_of_nonneg_left hst M.hxs.le))

end NativeOverlapMinimum

theorem exists_actual_rescaled_radius_spin_profile_limit
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ) → NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (hx : Tendsto (fun n=>(M n).xs) atTop (𝓝 0)) :
    ∃(s : NonnegativeMassProfile) (B : ℝ) (phi : ℕ → ℕ),0 < B ∧ StrictMono phi ∧
      (∀t : ℝ,0 ≤ t → s.mass t ≤ B*(1+cu*(t+Az))) ∧
      ∀t : ℝ,Tendsto (fun n=>
        orderedPathS (dim (phi n)+1) (M (phi n)).bf (M (phi n)).hf
          ((M (phi n)).alpha.val.val ((M (phi n)).xs*t))/(M (phi n)).xs)
        atTop (𝓝 (s.mass t)) := by
  obtain ⟨B,hB,HB⟩ := eventually_actual_minimum_mass_mean_upper Bclock
    hm hdelta hroom hcl hcu hAz hC0 hCt
  have Hcap : ∀t : ℝ,0 ≤ t → ∀ᶠn in atTop,
      (M n).actualRescaledRadiusSpinProfile.mass t ≤ B*(1+cu*(t+Az)) := by
    intro t ht
    have Hsmall : ∀ᶠn in atTop,(M n).xs*t ≤ 1 := by
      have H := (hx.mul_const t).eventually (gt_mem_nhds (by simp : (0:ℝ)*t < 1))
      exact H.mono fun n hn=>hn.le
    filter_upwards [hdim.eventually HB,Hsmall] with n hn hnsmall
    have har : (M n).alpha.val.val ((M n).xs*t) ≤ cu*((M n).xs*(t+Az)) := by
      calc
        (M n).alpha.val.val ((M n).xs*t) ≤
            (M n).alpha.val.val (max (M n).z ((M n).xs*t)) :=
          (M n).alpha.val.property.2 (le_max_right _ _)
        _ ≤ cu*max (M n).z ((M n).xs*t) :=
          ((M n).regular _ ⟨le_max_left _ _,max_le (M n).hz.2 hnsmall⟩).2
        _ ≤ cu*((M n).xs*(t+Az)) := by
          apply mul_le_mul_of_nonneg_left _ hcu.le
          apply max_le
          · nlinarith [(M n).hzxs,mul_nonneg (M n).hxs.le ht]
          · nlinarith [mul_nonneg (M n).hxs.le hAz]
    let u := (M n).alpha.val.val ((M n).xs*t)
    have hu : u∈Icc (0:ℝ) 1 := (M n).alpha.val.property.1 _
    change orderedPathS (dim n+1) (M n).bf (M n).hf u/(M n).xs ≤ _
    by_cases hu0 : u=0
    · rw [hu0]
      simp only [orderedPathS,orderedPathPair_zero,zero_div]
      positivity
    · have hup : 0 < u := lt_of_le_of_ne hu.1 (Ne.symm hu0)
      apply (div_le_iff₀ (M n).hxs).mpr
      calc
        orderedPathS (dim n+1) (M n).bf (M n).hf u ≤ B*((M n).xs+u) :=
          hn (M n) u ⟨hup,hu.2⟩
        _ ≤ B*((M n).xs+cu*((M n).xs*(t+Az))) :=
          mul_le_mul_of_nonneg_left (by dsimp [u]; linarith [har]) hB.le
        _ = B*(1+cu*(t+Az))*(M n).xs := by ring
  obtain ⟨s,phi,hphi,Hs⟩ := nonnegativeMassProfile_locallyBounded_tendsto_subseq
    (fun n=>(M n).actualRescaledRadiusSpinProfile)
    (fun R hR=>⟨B*(1+cu*(R+Az)),Hcap R hR.le⟩)
  refine ⟨s,B,phi,hB,hphi,?_,Hs⟩
  intro t ht
  exact le_of_tendsto (Hs t) (hphi.tendsto_atTop.eventually (Hcap t ht))

end OAI.SKFluctuations.LaplaceWindowFormalization
