module

public import ComparisonSignedCavityCanonicalSecondLowRestoration

@[expose] public section

noncomputable section
set_option maxHeartbeats 16000000
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy LaplaceWindowFormalization
open scoped Topology NNReal ENNReal BigOperators

private theorem scalarGamma_abs_le_one {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as) (U : ℕ) (K : ℕ→ℝ)
    (a c : T.Slot) : |fullScalarCutGamma T U K a c|≤1 := by
  let V:=T.cavityRight
  let q:=fun j (_ : Fin 1)=>relocatedClock U 0 K j
  have hw:=V.disorderWeight_probability (by intro σ;norm_num : ∀σ : Bool,(0:ℝ)<1/2)
    scalarFeature ho 0 q 0
  unfold fullScalarCutGamma fullScalarCutMoment scalarCutMoment ClockTree.disorderExpect
  calc
    _≤∑σ : V.Assignment,|V.disorderWeight (fun _=>(1/2:ℝ)) scalarFeature 0 q σ 0*
      V.slotProduct spinValue σ [T.cavityRightSlot a,T.cavityRightSlot c]| :=
        Finset.abs_sum_le_sum_abs _ _
    _=∑σ : V.Assignment,V.disorderWeight (fun _=>(1/2:ℝ)) scalarFeature 0 q σ 0 := by
      apply Finset.sum_congr rfl
      intro σ _
      simp only [abs_mul,abs_of_nonneg (hw.1 σ),ClockTree.slotProduct,abs_spinValue,
        mul_one]
    _=1:=hw.2

theorem native_low_scalar_pairing_abs_le_two {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as) (U : ℕ) (K : ℕ→ℝ)
    (a z c d : T.Slot) : |nativeLowScalarPairing T U K a z c d|≤2 := by
  have H1:=mul_le_mul (scalarGamma_abs_le_one T ho U K a c)
    (scalarGamma_abs_le_one T ho U K z d) (abs_nonneg _) zero_le_one
  have H2:=mul_le_mul (scalarGamma_abs_le_one T ho U K a d)
    (scalarGamma_abs_le_one T ho U K z c) (abs_nonneg _) zero_le_one
  unfold nativeLowScalarPairing
  apply (abs_add_le _ _).trans
  rw [abs_mul,abs_mul]
  linarith only [H1,H2]

theorem native_centered_low_gamma_low_restoration_wholeLaw_bound (n U : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (b h S : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    {rBound : ℕ} (hT : T.leaves≤rBound) (P : T.cavityLeft.Assignment→ℝ)
    (a z : T.Slot) (hU : U≤as.length) (haz : T.splitIndex a z<U)
    {C rho B d : ℝ} (hC : 0≤C) (hrho : 0<rho) (hB : 0≤B) (hd : 0≤d)
    (hq0 : ∀j i,0≤q j i) (hq : ∀i,Monotone (fun j=>q j i))
    (hb : ∀j,0≤b j) (hh : ∀j,0≤h j) (hK : ∀j,0≤h j+b j*S j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone (fun j=>h j+b j*S j))
    (hP : ∀l∈Icc (0:ℝ) 1,T.disorderExpect (fullWeight n) (fullFeature n) 0
      (cutFullVariance n q U l 1 b h (fun j=>h j+b j*S j))
      (fun σ=>|P (T.cavityAssignment σ).1|^4) 0≤C^4)
    (hclock : ∀j,j≤as.length→|b j|≤B∧|h j|≤B∧|h j+b j*S j|≤B)
    (hR : ∀l∈Icc (0:ℝ) 1,nativeWholeLawErrorRadius n as
      (cutFullVariance n q U l 1 b h (fun j=>h j+b j*S j))
      (cutLowError n U b h (fun j=>h j+b j*S j)) (T.splitIndex a z)≤d)
    (hmoment : ∀l∈Icc (0:ℝ) 1,∀j,j≤as.length→(ClockTree.pairClock as j).disorderExpect
      (fullWeight n) (fullFeature n) 0
      (cutFullVariance n q U l 1 b h (fun j=>h j+b j*S j))
      (fun σ=>|ReplicaTree.coordinateProfile (fullFeature n)
        (cutLSlope n U 1 b h (fun j=>h j+b j*S j)) j
        (ClockTree.pairSpin as j σ).1 (ClockTree.pairSpin as j σ).2|^8) 0≤rho^8) :
    |nativeCenteredLowGammaLowRestoration n q U b h (fun j=>h j+b j*S j) S T P a z|≤
      4*(rBound:ℝ)*(rBound+1)*ClockTree.absJetVariation (rBound+2) 2*C*d*rho^2 := by
  let K:=fun j=>h j+b j*S j
  let V:=ClockTree.absJetVariation (rBound+2) 2*C*d*rho^2
  have hV : 0≤V:=by
    have H:=ClockTree.absJetVariation_nonneg (rBound+2) 2
    dsimp [V]
    positivity
  let F:=fun (p : ClockTree.MarkedPlacement T) (r : ClockTree.MarkedPlacement p.tree)=>
    nativeLowScalarPairing r.tree U K (r.embed (p.embed a)) (r.embed (p.embed z))
      (r.embed p.mark) r.mark*
    (∫l in (0:ℝ)..1,(1-l)*cutLowJet n q U b h K r.tree
      (fun σ=>insertedRestTest P (restCenteredLowKernel n U b S) p r
        (r.tree.cavityAssignment σ).1) 0 2 l 1)
  have HF (p : ClockTree.MarkedPlacement T) (hp : p∈T.markedAttach 0)
      (r : ClockTree.MarkedPlacement p.tree) (hr : r∈p.tree.markedAttach 0) : |F p r|≤2*V := by
    let Pi:=nativeLowScalarPairing r.tree U K (r.embed (p.embed a)) (r.embed (p.embed z))
      (r.embed p.mark) r.mark
    by_cases hPi : Pi=0
    · change |Pi*_|≤_
      simp only [hPi,zero_mul,abs_zero]
      positivity
    · have hold : r.tree.splitIndex (r.embed (p.embed a)) (r.embed (p.embed z))=T.splitIndex a z :=
        ((p.tree.markedAttach_embed_preserves 0 r hr).2 _ _).trans
          ((T.markedAttach_embed_preserves 0 p hp).2 _ _)
      have hsplit : r.tree.splitIndex (r.embed p.mark) r.mark=T.splitIndex a z := by
        have H:=native_low_scalar_pairing_split_weight r.tree ho U K
          (fun j=>if j=T.splitIndex a z then (1:ℝ) else 0)
          (r.embed (p.embed a)) (r.embed (p.embed z)) (r.embed p.mark) r.mark hU
          (by rwa [hold])
        rw [hold,ite_eq_left rfl,one_mul] at H
        by_contra hne
        rw [ite_eq_right hne,zero_mul] at H
        exact hPi H.symm
      have hne : r.embed p.mark≠r.mark := by
        intro H
        rw [H,r.tree.splitIndex_self] at hsplit
        omega
      have hleaf : r.tree.leaves≤rBound+2 := by
        have H1:=T.markedAttach_leaves 0 p hp
        have H2:=p.tree.markedAttach_leaves 0 r hr
        omega
      let Pn:=fun σ=>P (p.restRestrict (r.restRestrict (r.tree.cavityAssignment σ).1))
      have Htest : (fun σ=>insertedRestTest P (restCenteredLowKernel n U b S) p r
          (r.tree.cavityAssignment σ).1)=
          fun σ=>Pn σ*restCenteredFixedForkKernel n b S (r.tree.splitIndex (r.embed p.mark) r.mark) 0
            (r.tree.atSlot σ (r.embed p.mark)).1 (r.tree.atSlot σ r.mark).1 := by
        funext σ
        simp only [insertedRestTest,restCenteredLowKernel,hsplit,haz,ite_true,Pn,
          restCenteredFixedForkKernel,ClockTree.MarkedPlacement.restSpin,
          r.restRestrict_at,r.tree.atSlot_cavityLeft]
      have Hjet l (hl : l∈Icc (0:ℝ) 1) :
          |cutLowJet n q U b h K r.tree
            (fun σ=>insertedRestTest P (restCenteredLowKernel n U b S) p r
              (r.tree.cavityAssignment σ).1) 0 2 l 1|≤V := by
        have HPn : r.tree.disorderExpect (fullWeight n) (fullFeature n) 0
            (cutFullVariance n q U l 1 b h K) (fun σ=>|Pn σ|^4) 0≤C^4 := by
          have HE:=ClockTree.wholeLaw_double_marked_nat_moment_eq (fullWeight_pos n) (fullFeature n)
            T ho 0 (cutFullVariance n q U l 1 b h K) 0 (fun σ=>P (T.cavityAssignment σ).1) 4 p hp r hr
          simpa only [Pn,r.restRestrict_actual,p.restRestrict_actual] using HE.trans_le (hP l hl)
        rw [Htest,hsplit]
        have H:=native_fixed_low_second_restoration_wholeLaw_bound n U q b h S r.tree ho hleaf
          Pn (r.embed p.mark) r.mark hne (by rwa [hsplit]) hl hC hrho hB hq0 hq hb hh hK hbm hhm hKm
          HPn hclock (hmoment l hl)
        rw [hsplit] at H
        exact H.trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hR l hl) (mul_nonneg (ClockTree.absJetVariation_nonneg _ _) hC))
          (sq_nonneg rho))
      have HI:=weighted_unit_integral_abs_le hV Hjet 1
      have HPi:=native_low_scalar_pairing_abs_le_two r.tree ho U K
        (r.embed (p.embed a)) (r.embed (p.embed z)) (r.embed p.mark) r.mark
      change |Pi*_|≤_
      rw [abs_mul]
      exact mul_le_mul HPi (by simpa only [pow_one] using HI) (abs_nonneg _) (by norm_num)
  have H:=T.signedPair_abs_le_pairAbsSum F
  have Htotal:=(H.trans (T.pairAbsSum_mono HF)).trans (T.pairAbsSum_constant_le ho hT
    (show 0≤2*V by positivity))
  change |_/2|≤_
  rw [abs_div,show |(2:ℝ)|=2 by norm_num]
  dsimp only [F,V,K] at Htotal ⊢
  nlinarith only [Htotal]

end OAI.SKFluctuations.Cavity
