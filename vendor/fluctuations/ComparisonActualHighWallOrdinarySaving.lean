module

public import ComparisonActualHighWallOrdinaryPhysicalBudget
public import ComparisonActualHighWallOrdinaryNumerics
public import ComparisonActualHighWallOrdinaryGroupData

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 24000000
namespace ActualHighWallOverlapMinimum
variable {n : ℕ} {margin delta cl cu Az C0 Ct D Bclock : ℝ}

theorem localCapDiameter_eq_highMassDiameter
    (a : ActualHighWallOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock) (v K : ℝ) :
    a.localCapDiameter v K=a.highMassDiameter (9*K) v:=by
  unfold localCapDiameter highMassDiameter
  ring_nf

theorem ordinaryOptimizedBudget_eq_highMassOrdinaryBudget
    (a : ActualHighWallOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock)
    (ell : ℕ) (Q K cut v : ℝ) :
    a.ordinaryOptimizedBudget ell Q (2*K) (10*Real.log a.data.N) cut (K*v) (v/4)
      (a.highMassHeight K v) v K (a.shiftedNativeModel.R (min (K*v) 1))=
      a.highMassOrdinaryBudgetAtDiameter ell Q 10 K cut v (a.highMassDiameter (9*K) v):=by
  unfold ordinaryOptimizedBudget highMassOrdinaryBudgetAtDiameter
  rw [a.localCapDiameter_eq_highMassDiameter v K]
  rfl

end ActualHighWallOverlapMinimum

theorem eventually_actual_high_wall_ordinary_group_polynomial_bound
    (K c : ℝ) (hK : 16 ≤ K) (hc : 0< c) {margin delta cl cu Az C0 Ct D Bclock : ℝ}
    (hm : 0< margin) (hdelta : 0< delta) (hroom : delta<3*margin)
    (hcl : 0< cl) (hcu : 0< cu) (hAz : 0 ≤ Az) (hC0 : 0< C0) (hCt : 0 ≤ Ct) (hD : 0< D) :
    ∃ell : ℕ,2< ell ∧ ∃Q : ℝ,1 ≤ Q ∧ ∀ᶠn : ℕ in atTop,
      ∀a : ActualHighWallOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock,
        a.xs ≤ a.data.d → ∀(P : a.Potential) (F : Finset (ordConnectedSection P.negativeSet))
          (A : Set ℝ) (j : comparisonMassDyadicIndices (comparisonSmallMass a.data.N a.data.E)),
          let v:=comparisonSmallMass a.data.N a.data.E*(2:ℝ)^(j:ℕ)
          v ≤ 1 → c*a.data.d ≤ v → a.data.s< v/2 →
            (∫u in 0..1,(P.ordinaryGroup (P.capFamily F) A K j).indicator (fun _=>1)
              (a.shiftedNativeModel.R u)*a.shiftedNativeModel.thermal u)/(a.xs^4*v/a.data.d^2) ≤
                a.data.N^(-actualMassSavingExponent margin delta) := by
  have hK0 : 0< K:=by linarith
  obtain ⟨ell,hell,Hnumeric⟩:=ActualHighWallOverlapMinimum.exists_high_mass_ordinary_polynomial_order
    (width:=K) (c:=c) (Cdiam:=9*K) (cl:=cl) (cu:=cu) (Az:=Az) (C0:=C0) (Ct:=Ct) (D:=D) (Bclock:=Bclock)
    hm hdelta hcl hAz hCt hC0 hD hK hc (by positivity)
  obtain ⟨Q,hQ,Hphysical⟩:=eventually_actual_high_wall_ordinary_optimized_budget ell hell Bclock
    (D:=D) hm hdelta hroom hcl hcu hAz hC0 hCt
  have Hlog:=(tendsto_add_atTop_nat 1).eventually
    ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop (1:ℝ))
  refine ⟨ell,hell,Q,hQ,?_⟩
  filter_upwards [Hnumeric Q hQ,Hphysical,Hlog] with n hnNum hnPhys hnLog
  intro a hxsD P F A j
  dsimp only
  let v:=comparisonSmallMass a.data.N a.data.E*(2:ℝ)^(j:ℕ)
  intro hv1 hvlo hs
  let m:=a.shiftedNativeModel
  let c0:=P.capFamily F
  let caps:=P.ordinaryCapFamily c0 A K v
  let ag:=m.R (v/2)
  let zg:=m.R (min (K*v) 1)
  let lo:=v/2
  let hi:=min (K*v) 1
  let cut:=a.data.N^(-(10:ℝ))
  let Lside:=10*Real.log a.data.N
  let y:=a.highMassHeight K v
  have hv : 0< v:=(comparison_mass_dyadic_scale a.data.hU j).1
  obtain ⟨hag,hzg,hagz,haMass,hzMass,hcap⟩:=P.ordinary_group_geometry (K:=K) (v:=v) c0 A (by linarith) hv hv1 hs
  have hwhole : ∀t,∀r∈Ioo (caps t).left (caps t).right,
      wholeUnit P.negativeSet r=Ioo (caps t).left (caps t).right:=by
    intro t r hr
    exact P.capFamily_wholeUnit F t.val hr
  have hcontacts : ∀t,P.H (caps t).left=0 ∧ (P.H (caps t).right=0 ∨ (caps t).right=1):=
    P.ordinary_group_contacts (K:=K) (v:=v) c0 A (by linarith) (P.capFamily_contacts F)
  have hdisjoint : Pairwise (fun t u=> Disjoint (Ioo (caps t).left (caps t).right)
      (Ioo (caps u).left (caps u).right)):=by
    intro t u htu
    exact P.capFamily_disjoint F (fun HH=> htu (Subtype.ext HH))
  have hleft : ∀t,ag ≤ (caps t).left:=fun t=>(hcap t).1
  have hright : ∀t,(caps t).right ≤ zg:=fun t=>(hcap t).2.1
  have hlo : 0 ≤ lo:=by dsimp [lo];positivity
  have hband : hi+comparisonSmallMass a.data.N a.data.E ≤
      (2*K)*(lo+comparisonSmallMass a.data.N a.data.E):=by
    have HU:=mul_le_mul_of_nonneg_right (show 1 ≤ 2*K by linarith) a.data.hU.le
    dsimp [hi,lo]
    nlinarith [min_le_left (K*v) (1:ℝ)]
  have hamass : ∀t,lo ≤ a.alpha.val.val (caps t).left:=by
    intro t
    have HT:=t.property.2.1
    change v/2 ≤ a.alpha.val.val (c0 t.val).left
    linarith
  have hzmass : ∀t,a.alpha.val.val (caps t).right ≤ hi:=fun t=> t.property.2.2
  have hMassSpan : a.alpha.val.val zg-a.alpha.val.val ag ≤ K*v:=by
    rw [hzMass,haMass]
    linarith [min_le_left (K*v) (1:ℝ)]
  have hRho : 0< v/4:=by positivity
  have hRhoFloor : v/4 ≤ a.alpha.val.val ag:=by rw [haMass];linarith
  have hy : 0< y:=by
    have Hmin : 0 ≤ min (K*v) 1:=le_min (by positivity) zero_le_one
    dsimp [y,ActualHighWallOverlapMinimum.highMassHeight]
    exact add_pos_of_pos_of_nonneg a.hxs Hmin
  have hY : a.xs+a.alpha.val.val zg ≤ y:=by rw [hzMass];exact le_rfl
  have hsourceLeft : ∀t,v ≤ a.alpha.val.val (caps t).left+comparisonSmallMass a.data.N a.data.E:=
    fun t=>(hcap t).2.2.1
  have hsourceSpan : ∀t,a.alpha.val.val (caps t).right-a.alpha.val.val (caps t).left ≤ K*v:=
    fun t=>(hcap t).2.2.2
  have hnLogN : 1 ≤ Real.log a.data.N:=hnLog
  have hLside : 0 ≤ Lside:=by dsimp [Lside];linarith
  have hcut : 0< cut:=Real.rpow_pos_of_pos a.data.hN _
  have hlogcut : Real.log (1/cut) ≤ Lside:=by
    dsimp [cut,Lside]
    rw [one_div,Real.log_inv,Real.log_rpow a.data.hN]
    ring_nf
    exact le_rfl
  have HP:=hnPhys a P (P.OrdinaryCapIndex c0 A K v) caps ag zg lo hi (2*K) (K*v) (v/4) y v K Lside cut
    hwhole hcontacts hdisjoint hag hagz hzg hleft hright hlo (by linarith) hband hamass hzmass
    (mul_pos hK0 hv) hMassSpan hRho hRhoFloor hy hY hv hK0 hsourceLeft hsourceSpan hLside hcut hlogcut
  have HE:=P.ordinaryGroup_eq_retainedSupport c0 A (by linarith : 1 ≤ K) j hv1 hs
  rw [←HE] at HP
  have HB : a.ordinaryOptimizedBudget ell Q (2*K) Lside cut (K*v) (v/4) y v K zg=
      a.highMassOrdinaryBudgetAtDiameter ell Q 10 K cut v (a.highMassDiameter (9*K) v):=
    a.ordinaryOptimizedBudget_eq_highMassOrdinaryBudget ell Q K cut v
  rw [HB] at HP
  have HN:=hnNum a hxsD v hv hv1 hvlo
  exact (div_le_div_of_nonneg_right HP (by positivity : 0 ≤ a.xs^4*v/a.data.d^2)).trans HN

end OAI.SKFluctuations.LaplaceWindowFormalization
