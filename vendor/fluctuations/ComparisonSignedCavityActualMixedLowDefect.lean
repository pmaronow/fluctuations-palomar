module

public import ComparisonSignedCavityActualGAllocation
public import CavityMarginalProfileJets

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy LaplaceWindowFormalization
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 9000000

theorem native_retained_high_marked_preserves (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.cavityLeft.Assignment→ℝ)
    (p : ClockTree.MarkedPlacement T) (hp : p∈T.markedAttach 0)
    (hq0 : ∀ j i,0 ≤ q j i) (hq : ∀ i,Monotone (fun j=>q j i))
    (hb : ∀ j,0 ≤ b j) (hh : ∀ j,0 ≤ h j) (hK : ∀ j,0 ≤ K j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K) :
    retainedSignedJets n q U b h K [restHighKernel n U b h K] p.tree
      (fun σ=>P (p.restRestrict σ)) []=
    retainedSignedJets n q U b h K [restHighKernel n U b h K] T P [] := by
  classical
  let D:=cutTSlope n U 0 b h K
  let B : ℝ:=∑ j : Fin (as.length+1),∑ i : FullCoordinate n,|D j.val i|
  have hB : 0 ≤ B := Finset.sum_nonneg fun _ _=>Finset.sum_nonneg fun _ _=>abs_nonneg _
  have hD : ∀ A∈[D],∀ j,j ≤ as.length → ∀ i,|A j i| ≤ B := by
    intro A hA j hj i
    simp only [List.mem_singleton] at hA
    subst A
    let r : Fin (as.length+1):=⟨j,by omega⟩
    have H₁ : |D j i| ≤ ∑ z : FullCoordinate n,|D j z| :=
      Finset.single_le_sum (s:=Finset.univ) (f:=fun z : FullCoordinate n=>|D j z|)
        (fun _ _=>abs_nonneg _) (Finset.mem_univ i)
    have H₂ : (∑ z : FullCoordinate n,|D j z|) ≤ B := by
      simpa only [B,r] using (Finset.single_le_sum
        (s:=Finset.univ) (f:=fun t : Fin (as.length+1)=>∑ z : FullCoordinate n,|D t.val z|)
        (fun _ _=>Finset.sum_nonneg fun _ _=>abs_nonneg _) (Finset.mem_univ r))
    exact H₁.trans H₂
  have HQ : ∀ i,Monotone (fun j=>cutFullVariance n q U 0 0 b h K j i) :=
    cutFullVariance_monotone n q U (by norm_num) (by norm_num) hq hb hh hK hbm hhm hKm
  have HQ0 : ∀ i,(0 : FullCoordinate n→ℝ) i ≤ cutFullVariance n q U 0 0 b h K 0 i :=
    fun i=>cutFullVariance_nonneg n q U (by norm_num) (by norm_num) hq0 hb hh hK 0 i
  have H : ClockTree.disorderProfileJets (fullWeight n) (fullFeature n) 0
      (cutFullVariance n q U 0 0 b h K) 0 ([D].map (ReplicaTree.coordinateProfile (fullFeature n)))
      p.tree (fun σ=>P (T.cavityAssignment (p.restrict σ)).1)=
    ClockTree.disorderProfileJets (fullWeight n) (fullFeature n) 0
      (cutFullVariance n q U 0 0 b h K) 0 ([D].map (ReplicaTree.coordinateProfile (fullFeature n)))
      T (fun σ=>P (T.cavityAssignment σ).1) := by
    rw [ClockTree.disorderProfileJets_eq_clipDirections (fullWeight n) (fullFeature n) 0
        (cutFullVariance n q U 0 0 b h K) 0 [D] p.tree _,
      ClockTree.disorderProfileJets_eq_clipDirections (fullWeight n) (fullFeature n) 0
        (cutFullVariance n q U 0 0 b h K) 0 [D] T _]
    exact T.markedAttach_profileJets_preserves_actual (fullWeight_pos n) (fullFeature n) ho p hp
      0 (cutFullVariance n q U 0 0 b h K) HQ HQ0 ([D].map (ClockTree.clipDirection as.length))
      hB (ClockTree.clipDirection_bounded as.length [D] hB hD) (fun σ=>P (T.cavityAssignment σ).1) 0
  rw [←actual_site_rest_jets_eq_retained n q U b h K [restHighKernel n U b h K]
      p.tree ho (fun σ=>P (p.restRestrict σ)) [],
    ←actual_site_rest_jets_eq_retained n q U b h K [restHighKernel n U b h K] T ho P []]
  simpa only [List.map_cons,List.map_nil,siteRestKernel_eq_cut_high,siteMonomial,mul_one,
    p.restRestrict_actual,D] using H

theorem native_retained_high_double_marked_preserves (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.cavityLeft.Assignment→ℝ)
    (p : ClockTree.MarkedPlacement T) (hp : p∈T.markedAttach 0)
    (r : ClockTree.MarkedPlacement p.tree) (hr : r∈p.tree.markedAttach 0)
    (hq0 : ∀ j i,0 ≤ q j i) (hq : ∀ i,Monotone (fun j=>q j i))
    (hb : ∀ j,0 ≤ b j) (hh : ∀ j,0 ≤ h j) (hK : ∀ j,0 ≤ K j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K) :
    retainedSignedJets n q U b h K [restHighKernel n U b h K] r.tree
      (fun σ=>P (p.restRestrict (r.restRestrict σ))) []=
    retainedSignedJets n q U b h K [restHighKernel n U b h K] T P [] := by
  rw [native_retained_high_marked_preserves n q U b h K p.tree ho (fun σ=>P (p.restRestrict σ))
      r hr hq0 hq hb hh hK hbm hhm hKm,
    native_retained_high_marked_preserves n q U b h K T ho P p hp hq0 hq hb hh hK hbm hhm hKm]

theorem retained_signed_jets_add_test
    (n : ℕ) (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    (As : List (ℕ→Spin n→Spin n→ℝ)) {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (P Q : T.cavityLeft.Assignment→ℝ) (es : List T.Slot) :
    retainedSignedJets n q U b h K As T (fun σ=>P σ+Q σ) es=
      retainedSignedJets n q U b h K As T P es+retainedSignedJets n q U b h K As T Q es := by
  simpa only [neg_one_mul,sub_neg_eq_add] using
    retained_signed_jets_sub_smul n q U b h K As T P Q (-1) es

theorem retained_signed_jets_const_mul_test
    (n : ℕ) (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    (As : List (ℕ→Spin n→Spin n→ℝ)) {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (P : T.cavityLeft.Assignment→ℝ) (c : ℝ) (es : List T.Slot) :
    retainedSignedJets n q U b h K As T (fun σ=>c*P σ) es=
      c*retainedSignedJets n q U b h K As T P es := by
  have H : (fun σ=>c*P σ)=(fun σ=>0-(-c)*P σ) := by funext σ;ring
  rw [H,retained_signed_jets_sub_smul,retained_signed_jets_zero_test]
  ring

theorem native_inserted_low_centering_high_jet (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K S : ℕ→ℝ)
    (hKS : ∀ j,K j=h j+b j*S j) {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.cavityLeft.Assignment→ℝ)
    (p : ClockTree.MarkedPlacement T) (hp : p∈T.markedAttach 0)
    (r : ClockTree.MarkedPlacement p.tree) (hr : r∈p.tree.markedAttach 0)
    (hq0 : ∀ j i,0 ≤ q j i) (hq : ∀ i,Monotone (fun j=>q j i))
    (hb : ∀ j,0 ≤ b j) (hh : ∀ j,0 ≤ h j) (hK : ∀ j,0 ≤ K j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K) :
    retainedSignedJets n q U b h K [restHighKernel n U b h K] r.tree
      (insertedRestTest P (restLowKernel n U b h) p r) []=
    retainedSignedJets n q U b h K [restHighKernel n U b h K] r.tree
      (insertedRestTest P (restCenteredLowKernel n U b S) p r) []+
    retainedSignedJets n q U b h K [restHighKernel n U b h K] T P []*
      r.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
        (insertedRestTest (fun _=>1) (restLowKernel n U 0 K) p r) 0 := by
  rw [native_inserted_scalar_low_mean n q U K T ho p r]
  let j:=r.tree.splitIndex (r.embed p.mark) r.mark
  by_cases hj : j < U
  · have H : insertedRestTest P (restLowKernel n U b h) p r=
        fun σ=>insertedRestTest P (restCenteredLowKernel n U b S) p r σ+
          K j*P (p.restRestrict (r.restRestrict σ)) := by
      funext σ
      simp only [insertedRestTest,restLowKernel,restCenteredLowKernel,
        show r.tree.splitIndex (r.embed p.mark) r.mark < U from hj,ite_true]
      rw [hKS]
      dsimp only [j]
      ring
    rw [H,retained_signed_jets_add_test,retained_signed_jets_const_mul_test,
      native_retained_high_double_marked_preserves n q U b h K T ho P p hp r hr
        hq0 hq hb hh hK hbm hhm hKm]
    simp only [show r.tree.splitIndex (r.embed p.mark) r.mark < U from hj,ite_true]
    ring
  · have H₁ : insertedRestTest P (restLowKernel n U b h) p r=fun _=>0 := by
      funext σ
      simp only [insertedRestTest,restLowKernel,
        show ¬r.tree.splitIndex (r.embed p.mark) r.mark < U from hj,ite_false,mul_zero]
    have H₂ : insertedRestTest P (restCenteredLowKernel n U b S) p r=fun _=>0 := by
      funext σ
      simp only [insertedRestTest,restCenteredLowKernel,
        show ¬r.tree.splitIndex (r.embed p.mark) r.mark < U from hj,ite_false,mul_zero]
    rw [H₁,H₂,retained_signed_jets_zero_test]
    simp only [show ¬r.tree.splitIndex (r.embed p.mark) r.mark < U from hj,ite_false,mul_zero,add_zero]

def nativeCenteredLowGammaHighLedger (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K S : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (P : T.cavityLeft.Assignment→ℝ) (a z : T.Slot) : ℝ :=
  ((T.markedAttach 0).map (fun p=>p.coeff*
    ((p.tree.markedAttach 0).map (fun r=>r.coeff*
      (nativeLowScalarPairing r.tree U K (r.embed (p.embed a)) (r.embed (p.embed z))
        (r.embed p.mark) r.mark*
      retainedSignedJets n q U b h K [restHighKernel n U b h K] r.tree
        (insertedRestTest P (restCenteredLowKernel n U b S) p r) []))).sum)).sum/2

theorem native_low_gamma_high_baseline_centering (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K S : ℕ→ℝ)
    (hKS : ∀ j,K j=h j+b j*S j) {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.cavityLeft.Assignment→ℝ) (a z : T.Slot)
    (hq0 : ∀ j i,0 ≤ q j i) (hq : ∀ i,Monotone (fun j=>q j i))
    (hb : ∀ j,0 ≤ b j) (hh : ∀ j,0 ≤ h j) (hK : ∀ j,0 ≤ K j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K)
    (hU : U ≤ as.length) (haz : T.splitIndex a z < U) :
    nativeLowGammaHighBaseline n q U b h K T P a z-
      retainedSignedJets n q U b h K [restHighKernel n U b h K] T P []*
        retainedSignedJets n q U b h K [restLowKernel n U 0 K] T (fun _=>1) [a,z]=
      nativeCenteredLowGammaHighLedger n q U b h K S T P a z := by
  let J:=retainedSignedJets n q U b h K [restHighKernel n U b h K] T P []
  let F:=fun (p : ClockTree.MarkedPlacement T) (r : ClockTree.MarkedPlacement p.tree)=>
    nativeLowScalarPairing r.tree U K (r.embed (p.embed a)) (r.embed (p.embed z))
      (r.embed p.mark) r.mark*
      retainedSignedJets n q U b h K [restHighKernel n U b h K] r.tree
        (insertedRestTest P (restLowKernel n U b h) p r) []
  let G:=fun (p : ClockTree.MarkedPlacement T) (r : ClockTree.MarkedPlacement p.tree)=>
    r.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
      (insertedRestTest (fun _=>1) (restLowKernel n U 0 K) p r) 0*
    nativeLowScalarPairing r.tree U K (r.embed (p.embed a)) (r.embed (p.embed z))
      (r.embed p.mark) r.mark
  let F₀:=fun (p : ClockTree.MarkedPlacement T) (r : ClockTree.MarkedPlacement p.tree)=>
    nativeLowScalarPairing r.tree U K (r.embed (p.embed a)) (r.embed (p.embed z))
      (r.embed p.mark) r.mark*
      retainedSignedJets n q U b h K [restHighKernel n U b h K] r.tree
        (insertedRestTest P (restCenteredLowKernel n U b S) p r) []
  have HS:=retained_one_low_eq_gamma_allocations n q U b h K T ho (fun _=>1)
    (restLowKernel n U 0 K) (by intro j hj σ τ;simp [restLowKernel,not_lt.mpr hj]) a z hU haz
  simp only [mul_assoc] at HS
  change retainedSignedJets n q U b h K [restLowKernel n U 0 K] T (fun _=>1) [a,z]=
    ((T.markedAttach 0).map (fun p=>p.coeff*
      ((p.tree.markedAttach 0).map (fun r=>r.coeff*G p r)).sum)).sum/2 at HS
  have HE : (T.markedAttach 0).map (fun p=>p.coeff*
      ((p.tree.markedAttach 0).map (fun r=>r.coeff*(F p r-J*G p r))).sum)=
    (T.markedAttach 0).map (fun p=>p.coeff*
      ((p.tree.markedAttach 0).map (fun r=>r.coeff*F₀ p r)).sum) := by
    apply List.map_congr_left
    intro p hp
    congr 1
    apply congrArg List.sum
    apply List.map_congr_left
    intro r hr
    dsimp only [F,G,F₀,J]
    rw [native_inserted_low_centering_high_jet n q U b h K S hKS T ho P p hp r hr
      hq0 hq hb hh hK hbm hhm hKm]
    ring
  have H:=native_signed_double_sum_sub T F G J
  rw [HE] at H
  rw [HS]
  unfold nativeLowGammaHighBaseline nativeCenteredLowGammaHighLedger
  change ((T.markedAttach 0).map (fun p=>p.coeff*
      ((p.tree.markedAttach 0).map (fun r=>r.coeff*F p r)).sum)).sum/2-
    J*(((T.markedAttach 0).map (fun p=>p.coeff*
      ((p.tree.markedAttach 0).map (fun r=>r.coeff*G p r)).sum)).sum/2)=
    ((T.markedAttach 0).map (fun p=>p.coeff*
      ((p.tree.markedAttach 0).map (fun r=>r.coeff*F₀ p r)).sum)).sum/2
  linear_combination (-1/2:ℝ)*H

theorem native_actual_mixed_scalar_baseline_eq_centered_low (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K S : ℕ→ℝ)
    (hKS : ∀ j,K j=h j+b j*S j) {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.cavityLeft.Assignment→ℝ) (a z : T.Slot)
    (hq0 : ∀ j i,0 ≤ q j i) (hq : ∀ i,Monotone (fun j=>q j i))
    (hb : ∀ j,0 ≤ b j) (hh : ∀ j,0 ≤ h j) (hK : ∀ j,0 ≤ K j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K)
    (hU : U ≤ as.length) (haz : T.splitIndex a z < U) :
    nativeActualMixedScalarBaseline n q U b h K T P a z=
      nativeCenteredLowGammaHighLedger n q U b h K S T P a z := by
  have H:=native_low_gamma_high_baseline_centering n q U b h K S hKS T ho P a z
    hq0 hq hb hh hK hbm hhm hKm hU haz
  rw [native_scalar_first_retained_eq_K_hessian_sq n q U b h K T ho a z hU haz] at H
  unfold nativeActualMixedScalarBaseline
  convert H using 1
  ring

theorem actual_first_low_high_centered_eq_G_and_centered_low (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K S : ℕ→ℝ)
    (hKS : ∀ j,K j=h j+b j*S j) {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.cavityLeft.Assignment→ℝ) (a z : T.Slot)
    (hq0 : ∀ j i,0 ≤ q j i) (hq : ∀ i,Monotone (fun j=>q j i))
    (hb : ∀ j,0 ≤ b j) (hh : ∀ j,0 ≤ h j) (hK : ∀ j,0 ≤ K j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K)
    (hU : U ≤ as.length) (haz : T.splitIndex a z < U) :
    cutFrozenCenteredJet n q U b h K T P (sitePair T a z) 0 1 1 0=
      nativeGPairLowAllocation n q U b h K T P a z+
      nativeCenteredLowGammaHighLedger n q U b h K S T P a z := by
  rw [actual_first_low_high_centered_eq_G_and_baseline n q U b h K T ho P a z
      hq0 hq hb hh hK hbm hhm hKm hU haz,
    native_actual_mixed_scalar_baseline_eq_centered_low n q U b h K S hKS T ho P a z
      hq0 hq hb hh hK hbm hhm hKm hU haz]

end OAI.SKFluctuations.Cavity
