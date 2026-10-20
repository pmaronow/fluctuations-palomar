module

public import SKProof.Port.ComparisonActualOriginalQSpinProfileCompactness
public import ComparisonStrengthProfileCompactness

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option linter.unusedVariables false
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology
set_option maxHeartbeats 6000000

theorem exists_actual_bounded_strength_spin_profile_limits_original_q
    {m delta cl cu Az C0 Ct D Bclock Ccal : ℝ}
    (K : ℝ) (hK : 0 ≤ K)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal)
    (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ) → ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (Hcutoff : ∀ᶠn in atTop,(M n).data.s≤1/4 ∧ (M n).data.s≤(M n).xs)
    (hx : Tendsto (fun n=>(M n).xs) atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).data.d (M n).lam (M n).xs)
    (hwork : ∀ᶠn in atTop,
      laplaceComparisonStrength (M n).data.d (M n).lam (M n).xs/(M n).xs^2 ≤ K) :
    ∃(L A B : ℝ) (s : NonnegativeMassProfile) (phi : ℕ → ℕ),StrictMono phi ∧
      L∈Icc (1/Ccal^2) (K+1) ∧ A∈Icc (0:ℝ) Ccal ∧ 0 < B ∧
      (∀t : ℝ,Tendsto (fun n=>laplaceComparisonStrength (M (phi n)).data.d
        (M (phi n)).lam ((M (phi n)).xs*t)/(M (phi n)).xs^2)
        atTop (𝓝 (L*laplaceComparisonShape (A*t)))) ∧
      (∀t : ℝ,Tendsto (fun n=>comparisonLogSlope
        (laplaceComparisonStrength (M (phi n)).data.d (M (phi n)).lam)
        ((M (phi n)).xs*t)) atTop (𝓝 (laplaceComparisonSlope (A*t)))) ∧
      (∀t : ℝ,0 < L*laplaceComparisonShape (A*t) ∧ laplaceComparisonSlope (A*t)∈Ico (0:ℝ) 1) ∧
      (∀t : ℝ,0 ≤ t → s.mass t ≤ B*(1+t)) ∧
      ∀t : ℝ,0 ≤ t → Tendsto (fun n=>orderedPathS (dim (phi n)+1)
        (M (phi n)).sweepBf (M (phi n)).sweepHf ((M (phi n)).xs*t)/(M (phi n)).xs)
        atTop (𝓝 (s.mass t)) := by
  have hCp : 0 < Ccal := lt_of_lt_of_le zero_lt_one hCcal
  have hxd n : (M n).xs ≤ Ccal*(M n).data.d := by
    apply (sq_le_sq₀ (M n).hxs.le (mul_nonneg hCp.le (M n).data.hd.le)).mp
    have H := (hcompare n).trans (mul_le_mul_of_nonneg_left
      ((laplaceComparisonStrength_le (M n).data.d (M n).hlam.le (M n).xs).trans
        (M n).hld) (sq_nonneg Ccal))
    nlinarith [H]
  have hlower n : 1/Ccal^2 ≤ 
      laplaceComparisonStrength (M n).data.d (M n).lam (M n).xs/(M n).xs^2 := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hCp) (sq_pos_of_pos (M n).hxs)).mpr
    nlinarith [hcompare n]
  obtain ⟨n0,Hwork⟩ := eventually_atTop.mp hwork
  let shift : ℕ → ℕ := fun n=>n+n0
  have hshift : StrictMono shift := by intro i j hij; dsimp [shift]; omega
  obtain ⟨L,A,eta,heta,hL,hA,HL,HA,Hpositive⟩ :=
    comparison_actual_strength_profiles_compact
      (fun n=>(M (shift n)).data.d) (fun n=>(M (shift n)).lam)
      (fun n=>(M (shift n)).xs) (by positivity : 0 < 1/Ccal^2) hK
      (fun n=>(M (shift n)).data.hd) (fun n=>(M (shift n)).hlam)
      (fun n=>(M (shift n)).hxs) (fun n=>(M (shift n)).hld)
      (fun n=>hxd (shift n)) (fun n=>⟨hlower (shift n),Hwork (shift n) (by dsimp [shift]; omega)⟩)
  let theta := shift ∘ eta
  have htheta : StrictMono theta := hshift.comp heta
  obtain ⟨s,B,psi,hB,hpsi,Hsbound,Hs⟩ := exists_actual_rescaled_spin_profile_limit_original_q
    hm hdelta hroom hcl hcu hAz hC0 hCt (fun n=>dim (theta n))
    (hdim.comp htheta.tendsto_atTop) (fun n=>M (theta n)) (htheta.tendsto_atTop.eventually Hcutoff) (hx.comp htheta.tendsto_atTop)
  refine ⟨L,A,B,s,theta ∘ psi,htheta.comp hpsi,hL,hA,hB,?_,?_,Hpositive,Hsbound,Hs⟩
  · intro t
    exact (HL t).comp hpsi.tendsto_atTop
  · intro t
    exact (HA t).comp hpsi.tendsto_atTop

end OAI.SKFluctuations.LaplaceWindowFormalization
