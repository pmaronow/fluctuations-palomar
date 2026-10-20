module

public import ComparisonNativeMacroscopicEndpointBand
public import ComparisonMacroscopicShellEndpoint
public import RescaledProfileHelly

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory ProbabilityTheory Filter Set Hierarchy Function
open scoped Topology NNReal
namespace NativeOverlapMinimum

theorem exists_macro_radius_scalar_minimizing_subseq
    {β : ℝ≥0} (hβ : 0 < β) {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (hdelta : 0 < delta) (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (a : (n:ℕ)→NativeOverlapMinimum (dim n) m delta cl cu Az C0 Ct D Bclock)
    {dlo dhi llo lhi : ℝ} (hdlo : 0 < dlo) (hllo : 0 < llo)
    (hlhi : lhi < (β:ℝ)^2)
    (hd : ∀n,(a n).context.d∈Icc dlo dhi) (hlam : ∀n,(a n).lam∈Icc llo lhi)
    (hcost : Tendsto (fun n=>comparisonEndpointL1Cost ((β:ℝ)^2) (a n).b (a n).h)
      atTop (𝓝 0)) :
    ∃r : boundedMassProfiles,∃phi : ℕ→ℕ,StrictMono phi ∧
      Tendsto (fun n=>comparisonSweepRadiusProfile (a (phi n)).context.hc (a (phi n)).context.hk
        (a (phi n)).context.hkc (a (phi n)).context.hm (a (phi n)).context.hM
        (a (phi n)).alpha) atTop (𝓝 r) ∧
      quantileMassProfile r.val (fun u _=>r.property.1 u) ∈ scalarReferenceMinimizers β hβ := by
  let R : ℕ→boundedMassProfiles := fun n=>comparisonSweepRadiusProfile (a n).context.hc
    (a n).context.hk (a n).context.hkc (a n).context.hm (a n).context.hM (a n).alpha
  obtain ⟨r,phi,hphi,hR⟩ := boundedMassProfiles_tendsto_subseq R
  obtain ⟨d,hD,psi,hpsi,hdlim⟩ := isCompact_Icc.tendsto_subseq (fun n=>hd (phi n))
  obtain ⟨lam,hL,chi,hchi,hllim⟩ := isCompact_Icc.tendsto_subseq
    (fun n=>hlam (phi (psi n)))
  let theta := (phi ∘ psi) ∘ chi
  have htheta : StrictMono theta := (hphi.comp hpsi).comp hchi
  have hdimtheta : Tendsto (dim ∘ theta) atTop atTop := hdim.comp htheta.tendsto_atTop
  have hRtheta : Tendsto (R ∘ theta) atTop (𝓝 r) :=
    (hR.comp hpsi.tendsto_atTop).comp hchi.tendsto_atTop
  have hdtheta : Tendsto (fun n=>(a (theta n)).context.d) atTop (𝓝 d) :=
    hdlim.comp hchi.tendsto_atTop
  have hltheta : Tendsto (fun n=>(a (theta n)).lam) atTop (𝓝 lam) := hllim
  refine ⟨r,theta,htheta,hRtheta,?_⟩
  exact macro_radius_limit_scalar_minimizer hβ hdelta (dim ∘ theta) hdimtheta
    (fun n=>a (theta n)) (ne_of_gt (hdlo.trans_le hD.1)) hdtheta hltheta
    (fun n=>(hlam (theta n)).2.trans hlhi.le) ⟨hllo.trans_le hL.1,hL.2.trans_lt hlhi⟩
    hRtheta (hcost.comp htheta.tendsto_atTop)

theorem eventually_macro_radius_fixed_band
    {β : ℝ≥0} (hβ : 0 < β) (hT : 1 < (β:ℝ)^2)
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (hdelta : 0 < delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (a : (n:ℕ)→NativeOverlapMinimum (dim n) m delta cl cu Az C0 Ct D Bclock)
    {dlo dhi llo lhi x : ℝ} (hdlo : 0 < dlo) (hllo : 0 < llo)
    (hlhi : lhi < (β:ℝ)^2) (hx : x∈Ioo (0:ℝ) 1)
    (hd : ∀n,(a n).context.d∈Icc dlo dhi) (hlam : ∀n,(a n).lam∈Icc llo lhi)
    (hcost : Tendsto (fun n=>comparisonEndpointL1Cost ((β:ℝ)^2) (a n).b (a n).h)
      atTop (𝓝 0)) :
    ∃cR CR : ℝ,0 < cR ∧ 0 < CR ∧ ∀ᶠn in atTop,
      ∀u∈Ioo (0:ℝ) 1,x ≤ u → cR*u ≤ (a n).R u ∧ (a n).R u ≤ CR*u := by
  obtain ⟨rho,cR,CR,hrho,hcR,hCR,hevent⟩ := eventually_macro_minimizers_fixed_band
    (dhi := dhi) hβ hT hdelta hdlo hllo hlhi hx m cl cu Az C0 Ct D Bclock
  refine ⟨cR,CR,hcR,hCR,?_⟩
  filter_upwards [hdim.eventually hevent,hcost.eventually (eventually_le_nhds hrho)]
    with n hn hc
  exact hn (a n) (hd n) (hlam n) hc

theorem exists_shell_macro_radius_scalar_minimizing_subseq
    {β : ℝ≥0} (hβ : 0 < β) {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (hdelta : 0 < delta) (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (a : (n:ℕ)→NativeOverlapMinimum (dim n) m delta cl cu Az C0 Ct D Bclock)
    {dlo dhi llo lhi : ℝ} (hdlo : 0 < dlo) (hllo : 0 < llo)
    (hlhi : lhi < (β:ℝ)^2)
    (hd : ∀n,(a n).context.d∈Icc dlo dhi) (hlam : ∀n,(a n).lam∈Icc llo lhi)
    (epsilon shell : ℕ→ℝ) (hepsilon : ∀n,epsilon n∈Icc (0:ℝ) ((β:ℝ)^2))
    (hshell : ∀n,shell n∈Icc (0:ℝ) 1) (hlim : Tendsto shell atTop (𝓝 0))
    (hb : ∀n,(a n).b=initialShellMatrixClock ((β:ℝ)^2) (epsilon n) (shell n))
    (hh : ∀n,(a n).h=(fun _=>0)) :
    ∃r : boundedMassProfiles,∃phi : ℕ→ℕ,StrictMono phi ∧
      Tendsto (fun n=>comparisonSweepRadiusProfile (a (phi n)).context.hc (a (phi n)).context.hk
        (a (phi n)).context.hkc (a (phi n)).context.hm (a (phi n)).context.hM
        (a (phi n)).alpha) atTop (𝓝 r) ∧
      quantileMassProfile r.val (fun u _=>r.property.1 u) ∈ scalarReferenceMinimizers β hβ := by
  apply exists_macro_radius_scalar_minimizing_subseq hβ hdelta dim hdim a hdlo hllo hlhi hd hlam
  have hcost := shell_endpoint_cost_tendsto_zero (T := (β:ℝ)^2) hepsilon hshell hlim
  simpa only [hb,hh] using hcost

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
