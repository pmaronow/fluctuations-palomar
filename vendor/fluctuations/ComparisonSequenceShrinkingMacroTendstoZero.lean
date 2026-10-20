module

public import ComparisonNativeActualGeneralHistoryCompleteStrictTest

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Filter
open scoped Topology

theorem comparison_tendsto_zero_of_shrinking_or_macro_subsequences
    (x f : ℕ → ℝ) (hx : ∀n,0 ≤ x n) (hf : ∀n,0 ≤ f n)
    (hshrinking : ∀phi : ℕ → ℕ,StrictMono phi →
      Tendsto (x ∘ phi) atTop (𝓝 0) → Tendsto (f ∘ phi) atTop (𝓝 0))
    (hmacro : ∀phi : ℕ → ℕ,StrictMono phi →
      ∀c : ℝ,0 < c → (∀n,c ≤ x (phi n)) →
      Tendsto (f ∘ phi) atTop (𝓝 0)) :
    Tendsto f atTop (𝓝 0) := by
  have Hsmall : ∀eta : ℝ,0 < eta → ∀ᶠn in atTop,f n < eta := by
    intro eta heta
    by_contra Hnone
    have Hfreq : ∃ᶠn in atTop,eta ≤ f n := by
      simpa only [Filter.Frequently,not_le] using Hnone
    obtain ⟨phi,hphi,Hphi⟩ := extraction_of_frequently_atTop Hfreq
    let y := x ∘ phi
    by_cases Hy : Tendsto y atTop (𝓝 0)
    · have Hf := hshrinking phi hphi Hy
      obtain ⟨n,hn⟩ := (Hf.eventually (gt_mem_nhds heta)).exists
      exact not_lt_of_ge (Hphi n) hn
    · obtain ⟨c,hc,psi,hpsi,Hpsi⟩ :=
        exists_positive_lower_subsequence_of_nonnegative_not_tendsto_zero
          y (fun n=>hx (phi n)) Hy
      let sigma := phi ∘ psi
      have hsigma : StrictMono sigma := hphi.comp hpsi
      have Hf := hmacro sigma hsigma c hc (fun n=>Hpsi n)
      obtain ⟨n,hn⟩ := (Hf.eventually (gt_mem_nhds heta)).exists
      exact not_lt_of_ge (Hphi (psi n)) hn
  apply Metric.tendsto_nhds.mpr
  intro eta heta
  filter_upwards [Hsmall eta heta] with n hn
  simpa only [Real.dist_eq,sub_zero,abs_of_nonneg (hf n)] using hn

end OAI.SKFluctuations.LaplaceWindowFormalization
