module

public import ComparisonActualHighOnlySuccessfulChildDirectProfile
public import ComparisonActualHighOnlySuccessfulChildProfileTransfer

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy Cavity
open scoped Topology NNReal
set_option autoImplicit false
set_option maxHeartbeats 18000000
namespace ActualHighOnlyOverlapMinimum

theorem successful_child_parent_direct_profile_of_context
    {m delta cl cu Az C0 Ct D Bclock T c0 C : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0)
    (hc0 : 0 < c0) (hc01 : c0 ≤ 1) (hC : 1 ≤ C)
    (hmargin : delta/4 < 3*m-99*delta)
    (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (hclmargin : cl < 2*T*Real.exp (-12*T))
    (hcumargin : T*(ReplicaTree.attachmentCount 1 3 : ℝ)^2/
      (2*Real.exp (-12*T)) < cu)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1)
      m delta cl cu Az C0 Ct D Bclock)
    (a : (n:ℕ)→ActualHighOnlyChildBarrierCall (dim n+1) delta)
    (Q : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1)
      m delta (cl/4) (4*cu) (4*C/cl) C0 (max Ct 1)
      (max D 1) (max Bclock T))
    (G : HighOnlyActualComparableBandContext Q T)
    (x : ℕ→ℝ) (hxs : ∀n,(M n).xs≤x n)
    (hxlim : Tendsto x atTop (𝓝 0))
    (hparent : ∀n,(a n).context.E=(M n).context.E ∧
      (a n).context.d=(M n).context.d ∧ (a n).lam=(M n).lam ∧
      (a n).R=(M n).R ∧ (a n).context.s=(M n).context.s)
    (hchild : ∀ᶠn in atTop,(a n).childRadius=c0*x n ∧
      (a n).childLam=(c0*x n)^2 ∧
      (a n).err≤((dim n+1:ℕ):ℝ)^(20*delta)*
        actualChildErrorBudget (dim n+1) delta c0
          (M n).context.d (M n).lam (x n))
    (homission : Tendsto (fun n=>(M n).data.s/x n) atTop (𝓝 0))
    (hweak : Tendsto (fun n=>laplaceComparisonStrength (M n).context.d
      (M n).lam (x n)/(x n)^2) atTop (𝓝 0))
    (hQ : ∀n,(Q n).R=(a n).Z ∧ (Q n).xs=x n ∧
      (Q n).context.d=c0*x n ∧ (Q n).lam=(c0*x n)^2) :
    ∃phi : ℕ→ℕ,StrictMono phi ∧ ∃kappa : ℝ,
      2*T*Real.exp (-12*T)≤kappa ∧
      kappa≤T*(ReplicaTree.attachmentCount 1 3 : ℝ)^2/
        (2*Real.exp (-12*T)) ∧
      TendstoLocallyUniformlyOn
        (fun n v=>(M (phi n)).R (x (phi n)*v)/x (phi n))
        (fun v=>v/kappa) atTop (Ioi (0:ℝ)) ∧
      ∀ᶠn in atTop,
        cl*x (phi n)<(M (phi n)).alpha.val.val (x (phi n)) ∧
        (M (phi n)).alpha.val.val (x (phi n))<cu*x (phi n) := by
  have hcl' : 0<cl/4 := by positivity
  have hcu' : 0<4*cu := by positivity
  have hAz' : 0≤4*C/cl := by positivity
  have hCt' : 0≤ max Ct 1 := zero_le_one.trans (le_max_right _ _)
  have hx (n:ℕ) : 0<x n := (M n).hxs.trans_le (hxs n)
  obtain ⟨phi,hphi,kappa,hklo,hkup,HQ⟩ :=
    exists_full_strength_successful_child_linear_profile
      hm hdelta hroom hcl' hcu' hAz' hC0 hCt' hc0 hc01
      hmargin hcapmargin hgapmargin dim hdim Q G x hx hxlim
      (fun n=>(hQ n).2.1) (fun n=>(hQ n).2.2.1)
      (fun n=>(hQ n).2.2.2)
  have HZ : TendstoLocallyUniformlyOn
      (fun n v=>(a (phi n)).Z (x (phi n)*v)/x (phi n))
      (fun v=>v/kappa) atTop (Ioi (0:ℝ)) := by
    have heq (n:ℕ) : (Q n).R=(a n).Z := (hQ n).1
    simpa only [heq] using HQ
  have hN : Tendsto (fun n=>dim (phi n)+1) atTop atTop :=
    (tendsto_add_atTop_nat 1).comp (hdim.comp hphi.tendsto_atTop)
  have hxlim' : Tendsto (fun n=>x (phi n)) atTop (𝓝 0) :=
    hxlim.comp hphi.tendsto_atTop
  have homission' : Tendsto
      (fun n=>(M (phi n)).data.s/x (phi n)) atTop (𝓝 0) :=
    homission.comp hphi.tendsto_atTop
  have hweak' : Tendsto
      (fun n=>laplaceComparisonStrength (M (phi n)).context.d
        (M (phi n)).lam (x (phi n))/(x (phi n))^2)
      atTop (𝓝 0) := hweak.comp hphi.tendsto_atTop
  have hchild' : ∀ᶠn in atTop,
      (a (phi n)).childRadius=c0*x (phi n) ∧
      (a (phi n)).childLam=(c0*x (phi n))^2 ∧
      (a (phi n)).err≤((dim (phi n)+1:ℕ):ℝ)^(20*delta)*
        actualChildErrorBudget (dim (phi n)+1) delta c0
          (M (phi n)).context.d (M (phi n)).lam (x (phi n)) :=
    hphi.tendsto_atTop.eventually hchild
  have hkmlo : cl<kappa := hclmargin.trans_le hklo
  have hkmup : kappa<cu := hkup.trans_lt hcumargin
  have Hparent := actual_high_only_successful_child_parent_profile_transfer
    hm hdelta hcl hcu hAz hC0 hc0
    (fun n=>dim (phi n)+1) hN (fun n=>M (phi n))
    (fun n=>a (phi n)) (fun n=>x (phi n))
    (fun n=>hxs (phi n)) hxlim' (fun n=>hparent (phi n))
    hchild' homission' hweak' hkmlo hkmup HZ
  exact ⟨phi,hphi,kappa,hklo,hkup,Hparent.1,Hparent.2⟩

end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
