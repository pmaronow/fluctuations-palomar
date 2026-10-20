module

public import ActualStrengthClockConvergence
public import ActualComparisonVariationalLimit
public import StrengthParameterCalculus

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory ProbabilityTheory Filter Set Hierarchy Function
open scoped Topology NNReal

theorem actualStrengthComparisonPressure_tendsto_jointScalar
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    {dseq lamseq : ℕ → ℝ} {d lam T : ℝ}
    (hd0 : d ≠ 0) (hds : ∀ n, dseq n ≠ 0)
    (hd : Tendsto dseq atTop (𝓝 d)) (hlam : Tendsto lamseq atTop (𝓝 lam))
    (hlamb : ∀ n, lamseq n ∈ Icc (0:ℝ) T) (hlamT : lam ∈ Ioo (0:ℝ) T)
    {rseq : ℕ → boundedMassProfiles} {r : boundedMassProfiles}
    (hr : Tendsto rseq atTop (𝓝 r)) :
    let eseq := fun n u => laplaceComparisonStrength (dseq n) (lamseq n) ((rseq n).val u)
    let e := fun u => laplaceComparisonStrength d lam (r.val u)
    Tendsto (fun n => pathCompensatedPressure (N n) (fun _ => T) (fun _ => 0)
      (eseq n) (rseq n).val 0) atTop (𝓝 (jointScalarVariationalValue T e r.val)) := by
  dsimp only
  let eseq := fun n u => laplaceComparisonStrength (dseq n) (lamseq n) ((rseq n).val u)
  let e := fun u => laplaceComparisonStrength d lam (r.val u)
  let g1 := laplaceComparisonStrength d lam 1
  let c := min g1 (T-lam)/2
  have hg1 : 0 < g1 := laplaceComparisonStrength_pos d hlamT.1 1
  have hc : 0 < c := by dsimp [c]; exact half_pos (lt_min hg1 (sub_pos.mpr hlamT.2))
  have hcg : c ≤ g1 := by
    have hh := min_le_left g1 (T-lam)
    dsimp [c]
    linarith
  have hcT : c ≤ T-lam := by
    have hh := min_le_right g1 (T-lam)
    dsimp [c]
    linarith [hlamT.2]
  have hm := laplaceComparisonStrength_monotonicities_nonneg hd0 hlamT.1.le
  have hms (n : ℕ) := laplaceComparisonStrength_monotonicities_nonneg (hds n) (hlamb n).1
  have he : AntitoneOn e (Icc (0:ℝ) 1) := fun u _ v _ huv =>
    hm.1 (r.property.1 u) (r.property.1 v) (r.property.2 huv)
  have heb : ∀ u ∈ Icc (0:ℝ) 1, e u ∈ Icc c (T-c) := by
    intro u _
    have hlo : g1 ≤ e u := hm.1 (r.property.1 u) (by norm_num) (r.property.1 u).2
    have hhi : e u ≤ lam := laplaceComparisonStrength_le d hlamT.1.le _
    exact ⟨hcg.trans hlo,by linarith⟩
  have her : MonotoneOn (fun u => e u*r.val u) (Icc (0:ℝ) 1) := fun u _ v _ huv =>
    hm.2 (r.property.1 u) (r.property.1 v) (r.property.2 huv)
  have hes (n : ℕ) : AntitoneOn (eseq n) (Icc (0:ℝ) 1) := fun u _ v _ huv =>
    (hms n).1 ((rseq n).property.1 u) ((rseq n).property.1 v) ((rseq n).property.2 huv)
  have hesb : ∀ n u, u ∈ Icc (0:ℝ) 1 → eseq n u ∈ Icc (0:ℝ) T := by
    intro n u _
    exact ⟨laplaceComparisonStrength_nonneg (dseq n) _ (hlamb n).1,
      (laplaceComparisonStrength_le (dseq n) (hlamb n).1 _).trans (hlamb n).2⟩
  have hers (n : ℕ) : MonotoneOn (fun u => eseq n u*(rseq n).val u) (Icc (0:ℝ) 1) :=
    fun u _ v _ huv => (hms n).2 ((rseq n).property.1 u) ((rseq n).property.1 v)
      ((rseq n).property.2 huv)
  obtain ⟨hedist,hfielddist,hpenalty⟩ := actual_strength_clock_convergences hd0 hd hlam
    (fun n => (hlamb n).1) hlamT.1.le hr
  exact actualComparisonPressure_tendsto_jointScalar N hN (hlamT.1.trans hlamT.2) hc
    eseq (fun n => (rseq n).val) e r.val he heb her (fun u _ => (r.property.1 u).1)
    hes hesb hers (fun n u _ => ((rseq n).property.1 u).1) hedist hfielddist hpenalty

end OAI.SKFluctuations.LaplaceWindowFormalization
