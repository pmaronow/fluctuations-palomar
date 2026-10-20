module

public import ComparisonActualHighOnlyMacroscopicScalarLimit
public import RescaledProfileHelly

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Function
open scoped Topology NNReal
set_option maxHeartbeats 10000000

theorem exists_actual_high_only_macro_radius_scalar_minimizing_subseq
    {beta : ℝ≥0} (hbeta : 0<beta) {delta : ℝ} (hdelta : 0<delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (a : (n:ℕ)→ActualHighOnlyComparisonData (dim n) delta)
    (lam : ℕ→ℝ) (hlam : ∀n,lam n∈Icc (0:ℝ) ((a n).d^2))
    (M : (n:ℕ)→ActualHighOnlyComparisonMinimum (a n) (lam n))
    {dlo dhi llo lhi : ℝ} (hdlo : 0<dlo) (hllo : 0<llo) (hlhi : lhi<(beta:ℝ)^2)
    (hd : ∀n,(a n).d∈Icc dlo dhi) (hl : ∀n,lam n∈Icc llo lhi)
    (hs : Tendsto (fun n=>(a n).s) atTop (𝓝 0))
    (hcost : Tendsto (fun n=>comparisonEndpointL1Cost ((beta:ℝ)^2) (a n).b (a n).h)
      atTop (𝓝 0)) :
    ∃r : boundedMassProfiles,∃phi : ℕ→ℕ,StrictMono phi ∧
      Tendsto (fun n=>(a (phi n)).radiusProfile (M (phi n)).alpha) atTop (𝓝 r) ∧
      quantileMassProfile r.val (fun u _=>r.property.1 u)∈scalarReferenceMinimizers beta hbeta := by
  let R:ℕ→boundedMassProfiles:=fun n=>(a n).radiusProfile (M n).alpha
  obtain ⟨r,phi,hphi,hR⟩:=boundedMassProfiles_tendsto_subseq R
  obtain ⟨d,hD,psi,hpsi,hdlim⟩:=isCompact_Icc.tendsto_subseq (fun n=>hd (phi n))
  obtain ⟨l,hL,chi,hchi,hllim⟩:=isCompact_Icc.tendsto_subseq (fun n=>hl (phi (psi n)))
  let theta:=(phi∘psi)∘chi
  have htheta:StrictMono theta:=(hphi.comp hpsi).comp hchi
  have HR:Tendsto (R∘theta) atTop (𝓝 r):=(hR.comp hpsi.tendsto_atTop).comp hchi.tendsto_atTop
  have HD:Tendsto (fun n=>(a (theta n)).d) atTop (𝓝 d):=hdlim.comp hchi.tendsto_atTop
  have HL:Tendsto (fun n=>lam (theta n)) atTop (𝓝 l):=hllim
  refine ⟨r,theta,htheta,HR,?_⟩
  exact actual_high_only_radius_limit_scalar_minimizer hbeta hdelta
    (dim∘theta) (hdim.comp htheta.tendsto_atTop) (fun n=>a (theta n))
    (fun n=>lam (theta n)) (fun n=>hlam (theta n)) (fun n=>M (theta n))
    (ne_of_gt (hdlo.trans_le hD.1)) HD HL
    (fun n=>(hl (theta n)).2.trans hlhi.le) ⟨hllo.trans_le hL.1,hL.2.trans_lt hlhi⟩
    HR (hs.comp htheta.tendsto_atTop) (hcost.comp htheta.tendsto_atTop)

end OAI.SKFluctuations.LaplaceWindowFormalization
