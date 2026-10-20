module

public import ComparisonActualHighWallCriticalBroadMassSource
public import ComparisonActualHighWallCriticalWholeCapSampler

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal
set_option maxHeartbeats 16000000
namespace ActualHighWallOverlapMinimum
variable {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem eventually_actual_critical_broad_slice_thermal
    (ell : ℕ) (hell : 2< ell)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta< 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0≤ Az) (hC0 : 0 < C0) (hCt : 0≤ Ct) :
    ∃Q : ℝ,1≤ Q ∧ ∀ᶠn in atTop,
      ∀(a : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
        (P : a.Potential) (cap : ShiftedCapInterval a P)
        (f : CriticalWholeCapBroadSampler cap) (i : Fin f.count) (Lside cut : ℝ),
      (P.H cap.left=0 ∨ cap.left=a.data.rmin) ∧ (P.H cap.right=0 ∨ cap.right=1) →
      0≤ Lside → 0< cut → 2*cut< comparisonSmallMass a.data.N a.data.E →
      Real.log (1/cut)≤ Lside →
      (∫u in 0..1,(f.slice i).indicator (fun _=>1) (a.shiftedNativeModel.R u)*
        a.shiftedNativeModel.thermal u) ≤
      a.criticalBroadMassBudget ell Q Lside cut (f.scale i)
        (∫r in f.slice i,deriv a.alpha.val.val r) := by
  obtain ⟨Q,hQ,Hphysical⟩:=eventually_actual_high_wall_critical_broad_mass_budget ell hell Bclock
    (D:=D) hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Q,hQ,?_⟩
  filter_upwards [Hphysical] with n hn
  intro a P cap f i Lside cut hcontacts hL hcut hcutU hlog
  let model:=a.shiftedNativeModel
  let l:=model.R (f.node i.val)
  let z:=model.R (f.node (i.val+1))
  let v:=f.scale i
  have HG:=f.geometry i
  have HN:=f.nodes_mem i
  have hαl:a.alpha.val.val l=f.node i.val:=model.R_spec HN.1
  have hαz:a.alpha.val.val z=f.node (i.val+1):=model.R_spec HN.2
  have hlz:l< z:=model.R_strictMonoOn HN.1 HN.2 HG.2.2.2.2.2.2
  have hnode : a.data.s< f.node i.val := by
    have Hbase : 8*a.data.s≤ a.criticalMassCoverBase:=le_max_right _ _
    have H := Hbase.trans ((le_max_right _ _).trans HG.2.2.2.2.1)
    linarith only [H,a.data.hs.1]
  have hl0:a.data.rmin< l:=by
    simpa only [model.R_left] using model.R_strictMonoOn ⟨le_rfl,model.hu.2⟩ HN.1 hnode
  have hzcap:z≤ cap.right:=by
    calc z≤ model.R (a.alpha.val.val cap.right):=model.R_monotone HG.2.2.2.2.2.1
         _=cap.right:=model.R_inverse ⟨cap.hleft.trans cap.hlt.le,cap.hright⟩
  have hcapL:cap.left≤ l:=by
    calc cap.left=model.R (a.alpha.val.val cap.left):=
           (model.R_inverse ⟨cap.hleft,cap.hlt.le.trans cap.hright⟩).symm
         _≤ l:=model.R_monotone ((le_max_left _ _).trans HG.2.2.2.2.1)
  have hw:=f.width_bounds i
  have hv:0< v:=(criticalMassCoverBase_pos (a:=a)).trans_le HG.1
  have hv1:v≤ 1:=hw.1.trans hw.2.2
  have hUv:comparisonSmallMass a.data.N a.data.E≤ v:=(le_max_left _ _).trans HG.1
  have HH:=hn a P cap l z v Lside cut hcontacts hl0 hlz hcapL hzcap hv hv1 hUv
    (by rw [hαl];exact HG.2.2.1)
    (by rw [hαz];exact le_min HG.2.2.2.1 HN.2.2)
    hw.1 hL hcut hcutU hlog
  have HI:=model.mass_radius_cell_substitution model.thermal HN.1 HN.2 HG.2.2.2.2.2.2.le
  rw [integral_Icc_eq_integral_Ioo] at HI
  dsimp only [CriticalWholeCapBroadSampler.slice]
  rw [model.massSlice_thermal_integral HN.1 HN.2 HG.2.2.2.2.2.2.le,HI]
  exact HH

end ActualHighWallOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
