module

public import ComparisonActualHighWallThetaZeroOrdinaryGroupPhysicalBudget

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option autoImplicit false
set_option maxHeartbeats 32000000
attribute [local instance] Classical.propDecidable

namespace ActualThetaZeroOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem terminal_arbitrary_bin_right_radius_eq_one_import_first_draft
    (Q : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (K : ℝ)
    (j : comparisonMassDyadicIndices
      (comparisonSmallMass Q.data.N Q.data.E))
    (hterminal : 1 ≤ K *
      (comparisonSmallMass Q.data.N Q.data.E * (2:ℝ)^(j.val:ℕ))) :
    Q.shiftedNativeModel.R
      (min (K * (comparisonSmallMass Q.data.N Q.data.E *
        (2:ℝ)^(j.val:ℕ))) 1) = 1 := by
  rw [min_eq_right hterminal]
  exact Q.shiftedNativeModel.R_one

theorem eventually_original_q_terminal_arbitrary_group_import_first_draft
    (ell : ℕ) (hell : 2 < ell) (Bclock : ℝ)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az)
    (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃ Qraw : ℝ, 1 ≤ Qraw ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (Q : ActualThetaZeroOverlapMinimum
          (n+1) m delta cl cu Az C0 Ct D Bclock)
        (P : Q.Potential) (F : Finset (ordConnectedSection P.negativeSet))
        (A : Set ℝ) (K : ℝ)
        (j : comparisonMassDyadicIndices
          (comparisonSmallMass Q.data.N Q.data.E))
        (Lside cut : ℝ),
      4 ≤ K →
      Q.data.s <
        (comparisonSmallMass Q.data.N Q.data.E*(2:ℝ)^(j.val:ℕ))/2 →
      0 ≤ Lside → 0 < cut → Real.log (1/cut) ≤ Lside →
      let v := comparisonSmallMass Q.data.N Q.data.E*(2:ℝ)^(j.val:ℕ)
      let z := min (K*v) 1
      (∫u in 0..1,
        (P.ordinaryGroup (P.capFamily F) A K j).indicator
          (fun _ => (1:ℝ)) (Q.shiftedNativeModel.R u)*
            Q.shiftedNativeModel.thermal u) ≤
        Q.ordinaryOptimizedBudget ell Qraw K Lside cut (K*v) (v/2)
          (Q.xs+z) v K (Q.shiftedNativeModel.R z) := by
  obtain ⟨Qraw,hQraw,Hphysical⟩ :=
    eventually_actual_theta_zero_ordinary_optimized_budget ell hell
      Bclock (D:=D) hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Qraw,hQraw,?_⟩
  filter_upwards [Hphysical] with n hn
  intro Q P F A K j Lside cut hK hstart hLside hcut hlogcut
  let v := comparisonSmallMass Q.data.N Q.data.E*(2:ℝ)^(j.val:ℕ)
  let z := min (K*v) 1
  let ag := Q.shiftedNativeModel.R (v/2)
  let zg := Q.shiftedNativeModel.R z
  let c := P.ordinaryCapSubfamily (P.capFamily F) A K j
  have hv := comparison_mass_dyadic_scale Q.data.hU j
  have hKpos : 0 < K := by linarith
  have hK1 : 1 ≤ K := by linarith
  have hz1 : z ≤ 1 := min_le_right _ _
  have hzKv : z ≤ K*v := min_le_left _ _
  have hvhalfz : v/2 ≤ z := le_min (by nlinarith [hv.1])
    (by linarith [hv.2.2])
  have hlow : v/2 ∈ Icc Q.data.s 1 :=
    ⟨hstart.le,by linarith [hv.2.2]⟩
  have hhigh : z ∈ Icc Q.data.s 1 :=
    ⟨hlow.1.trans hvhalfz,hz1⟩
  have Hlow := Q.shiftedNativeModel.R_spec hlow
  have Hhigh := Q.shiftedNativeModel.R_spec hhigh
  have hag : Q.data.rmin < ag := by
    have H := Q.shiftedNativeModel.R_strictMonoOn
      ⟨le_rfl,Q.data.hs1⟩ hlow hstart
    rw [Q.shiftedNativeModel.R_left] at H
    exact H
  have hagz : ag ≤ zg := Q.shiftedNativeModel.R_monotone hvhalfz
  have hzg : zg ≤ 1 := (Q.shiftedNativeModel.R_bounds z).2
  have Hleft (t : P.ordinaryCapIndex (P.capFamily F) A K j) :
      ag ≤ (c t).left := by
    have Hmass : v/2 ≤ Q.alpha.val.val (c t).left := by
      have H := t.property.2.1
      change v ≤ Q.alpha.val.val (c t).left at H
      linarith
    have H := Q.shiftedNativeModel.R_monotone Hmass
    rw [Q.shiftedNativeModel.R_inverse
      ⟨(c t).hleft,(c t).hlt.le.trans (c t).hright⟩] at H
    exact H
  have Hright (t : P.ordinaryCapIndex (P.capFamily F) A K j) :
      (c t).right ≤ zg := by
    have H := Q.shiftedNativeModel.R_monotone t.property.2.2
    rw [Q.shiftedNativeModel.R_inverse
      ⟨(c t).hleft.trans (c t).hlt.le,(c t).hright⟩] at H
    exact H
  have Hcontacts (t : P.ordinaryCapIndex (P.capFamily F) A K j) :
      P.H (c t).left = 0 ∧
        (P.H (c t).right = 0 ∨ (c t).right = 1) := by
    have H := P.capFamily_contacts F t.val
    refine ⟨?_,H.2⟩
    rcases H.1 with H | H
    · exact H
    · have Hmass := t.property.2.1
      change v ≤ Q.alpha.val.val (P.capFamily F t.val).left at Hmass
      rw [H,Q.alpha.property.1] at Hmass
      linarith [hstart]
  have Hdisjoint : Pairwise (fun s t :
      P.ordinaryCapIndex (P.capFamily F) A K j =>
        Disjoint (Ioo (c s).left (c s).right)
          (Ioo (c t).left (c t).right)) := by
    intro s t hst
    exact P.capFamily_disjoint F (fun H => hst (Subtype.ext H))
  have Hbudget := hn Q P _ c ag zg v z K (K*v) (v/2) (Q.xs+z)
    v K Lside cut
    (fun t r hr => P.capFamily_wholeUnit F t.val hr)
    Hcontacts Hdisjoint hag hagz hzg Hleft Hright hv.1.le hK1
    (by nlinarith [hzKv,Q.data.hU] :
      z+comparisonSmallMass Q.data.N Q.data.E ≤
        K*(v+comparisonSmallMass Q.data.N Q.data.E))
    (fun t => t.property.2.1) (fun t => t.property.2.2)
    (mul_pos hKpos hv.1)
    (by dsimp only [ag,zg]; rw [Hlow,Hhigh]; linarith)
    (by exact div_pos hv.1 (by norm_num : (0:ℝ) < 2)) Hlow.ge
    (by
      have hzpos : 0 < z := (div_pos hv.1 (by norm_num : (0:ℝ) < 2)).trans_le hvhalfz
      exact add_pos Q.hxs hzpos)
    (by dsimp only [zg]; rw [Hhigh]) hv.1 hKpos
    (fun t => by
      have H := t.property.2.1
      change v ≤ Q.alpha.val.val (c t).left at H
      linarith [Q.data.hU])
    (fun t => by
      have Hl := t.property.2.1
      have Hr := t.property.2.2.trans hzKv
      change v ≤ Q.alpha.val.val (c t).left at Hl
      change Q.alpha.val.val (c t).right ≤ K*v at Hr
      linarith)
    hLside hcut hlogcut
  rw [P.ordinaryGroup_eq_retainedSupport (P.capFamily F) A K j]
  exact Hbudget

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
