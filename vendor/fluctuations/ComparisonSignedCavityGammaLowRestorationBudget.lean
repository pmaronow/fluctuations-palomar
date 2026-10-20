module

public import ComparisonSignedCavityOriginalGammaLawAdapter
public import ComparisonSignedCavityFixedLowRestorationBudget
public import ComparisonSignedCavityProfileTestCalculus
public import ComparisonSignedCavityActualGeneratedPairedSource
public import ComparisonSignedCavityActualTerminalGAtom

@[expose] public section

noncomputable section
set_option maxHeartbeats 18000000
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators

theorem native_low_two_fixed_star_difference_bound (n U star : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (b h S : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    {r : ℕ} (hT : T.leaves≤r) (P : T.Assignment→ℝ)
    (a c z : T.Slot) (haz : T.splitIndex a z=star) (hcz : T.splitIndex c z=star)
    (hs : star<U) (hU : U≤as.length)
    {l C rho B : ℝ} (hl : l∈Icc (0:ℝ) 1)
    (hC : 0≤C) (hrho : 0<rho) (hB : 0≤B)
    (hq0 : ∀j i,0≤q j i) (hq : ∀i,Monotone (fun j=>q j i))
    (hb : ∀j,0≤b j) (hh : ∀j,0≤h j) (hK : ∀j,0≤h j+b j*S j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone (fun j=>h j+b j*S j))
    (hP : T.disorderExpect (fullWeight n) (fullFeature n) 0
      (cutFullVariance n q U l 1 b h (fun j=>h j+b j*S j))
      (fun σ=>|P σ|^4) 0≤C^4)
    (hclock : ∀j,j≤as.length→|b j|≤B∧|h j|≤B∧|h j+b j*S j|≤B)
    (hmoment : ∀j,j≤as.length→(ClockTree.pairClock as j).disorderExpect
      (fullWeight n) (fullFeature n) 0
      (cutFullVariance n q U l 1 b h (fun j=>h j+b j*S j))
      (fun σ=>|ReplicaTree.coordinateProfile (fullFeature n)
        (cutLSlope n U 1 b h (fun j=>h j+b j*S j)) j
        (ClockTree.pairSpin as j σ).1 (ClockTree.pairSpin as j σ).2|^8) 0≤rho^8) :
    |cutLowJet n q U b h (fun j=>h j+b j*S j) T
      (fun σ=>(restCenteredFixedForkKernel n b S star 0 (T.atSlot σ c).1 (T.atSlot σ z).1-
        restCenteredFixedForkKernel n b S star 0 (T.atSlot σ a).1 (T.atSlot σ z).1)*P σ)
      0 2 l 1|≤
      2*ClockTree.absJetVariation r 2*C*
        nativeWholeLawErrorRadius n as
          (cutFullVariance n q U l 1 b h (fun j=>h j+b j*S j))
          (cutLowError n U b h (fun j=>h j+b j*S j)) star*rho^2 := by
  have hane : a≠z := by
    intro he
    rw [he,T.splitIndex_self] at haz
    omega
  have hcne : c≠z := by
    intro he
    rw [he,T.splitIndex_self] at hcz
    omega
  have HA:=native_fixed_low_second_restoration_wholeLaw_bound n U q b h S T ho hT P a z
    hane (by omega) hl hC hrho hB hq0 hq hb hh hK hbm hhm hKm hP hclock hmoment
  have HC:=native_fixed_low_second_restoration_wholeLaw_bound n U q b h S T ho hT P c z
    hcne (by omega) hl hC hrho hB hq0 hq hb hh hK hbm hhm hKm hP hclock hmoment
  rw [haz] at HA
  rw [hcz] at HC
  let A:=fun σ : T.Assignment=>P σ*restCenteredFixedForkKernel n b S star 0
    (T.atSlot σ a).1 (T.atSlot σ z).1
  let Q:=fun σ : T.Assignment=>P σ*restCenteredFixedForkKernel n b S star 0
    (T.atSlot σ c).1 (T.atSlot σ z).1
  have HE : (fun σ : T.Assignment=>
      (restCenteredFixedForkKernel n b S star 0 (T.atSlot σ c).1 (T.atSlot σ z).1-
        restCenteredFixedForkKernel n b S star 0 (T.atSlot σ a).1 (T.atSlot σ z).1)*P σ)=
      fun σ=>Q σ+(-1:ℝ)*A σ := by
    funext σ
    dsimp only [A,Q]
    ring
  rw [HE]
  have HL : cutLowJet n q U b h (fun j=>h j+b j*S j) T
      (fun σ=>Q σ+(-1:ℝ)*A σ) 0 2 l 1=
      cutLowJet n q U b h (fun j=>h j+b j*S j) T Q 0 2 l 1-
        cutLowJet n q U b h (fun j=>h j+b j*S j) T A 0 2 l 1 := by
    rw [cutLowJet_eq_profileJets n q U b h _ T ho _ 0 hq0 hq hb hh hK hbm hhm hKm 2 hl (by norm_num),
      cutLowJet_eq_profileJets n q U b h _ T ho Q 0 hq0 hq hb hh hK hbm hhm hKm 2 hl (by norm_num),
      cutLowJet_eq_profileJets n q U b h _ T ho A 0 hq0 hq hb hh hK hbm hhm hKm 2 hl (by norm_num),
      disorderProfileJets_add,disorderProfileJets_const_mul]
    ring
  rw [HL]
  exact (abs_sub _ _).trans ((add_le_add HC HA).trans_eq (by ring))

theorem native_gamma_projected_low_second_restoration_wholeLaw_bound (n U star : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (b h S : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    {rBound : ℕ} (hT : T.leaves≤rBound) (P : T.cavityLeft.Assignment→ℝ)
    (a : T.Slot) (hs : star<U) (hU : U≤as.length)
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
      (cutLowError n U b h (fun j=>h j+b j*S j)) star≤d)
    (hmoment : ∀l∈Icc (0:ℝ) 1,∀j,j≤as.length→(ClockTree.pairClock as j).disorderExpect
      (fullWeight n) (fullFeature n) 0
      (cutFullVariance n q U l 1 b h (fun j=>h j+b j*S j))
      (fun σ=>|ReplicaTree.coordinateProfile (fullFeature n)
        (cutLSlope n U 1 b h (fun j=>h j+b j*S j)) j
        (ClockTree.pairSpin as j σ).1 (ClockTree.pairSpin as j σ).2|^8) 0≤rho^8) :
    |nativeGammaProjectedLowSecondRestoration T a star U q b h (fun j=>h j+b j*S j)
      (restCenteredFixedForkKernel n b S star 0) P|≤
      4*((rBound:ℝ)+1)*ClockTree.absJetVariation (rBound+2) 2*C*d*rho^2 := by
  let K:=fun j=>h j+b j*S j
  let g:=nativeFreshAtSlot T 0 a star
  let V:=2*ClockTree.absJetVariation (rBound+2) 2*C*d*rho^2
  have hV : 0≤V := by
    have H:=ClockTree.absJetVariation_nonneg (rBound+2) 2
    dsimp only [V]
    positivity
  let F:=fun p : MarkedPlacement g.tree=>
    fullScalarCutGamma p.tree U K (p.embed (g.embed a)) p.mark*
      (∫l in (0:ℝ)..1,(1-l)*cutLowJet n q U b h K p.tree
        (fun σ=>nativeRestProjectedDisplacementTest T a star
          (restCenteredFixedForkKernel n b S star 0) P p (p.tree.cavityAssignment σ).1) 0 2 l 1)
  have HF (p : MarkedPlacement g.tree) (hp : p∈g.tree.markedAttach 0) : |F p|≤V := by
    by_cases hhigh : U≤p.tree.splitIndex (p.embed (g.embed a)) p.mark
    · have Hsplit:=native_fresh_observed_endpoint_splits T a hs hU p hp hhigh
      have Hleaf : p.tree.leaves≤rBound+2 := by
        have H1:=T.markedAttach_leaves 0 g (nativeFreshAtSlot_mem T 0 a star)
        have H2:=g.tree.markedAttach_leaves 0 p hp
        omega
      have Hjet l (hl : l∈Icc (0:ℝ) 1) :
          |cutLowJet n q U b h K p.tree
            (fun σ=>nativeRestProjectedDisplacementTest T a star
              (restCenteredFixedForkKernel n b S star 0) P p (p.tree.cavityAssignment σ).1)
            0 2 l 1|≤V := by
        let Q:=fun σ : p.tree.Assignment=>P (T.cavityAssignment (g.restrict (p.restrict σ))).1
        have HQ : p.tree.disorderExpect (fullWeight n) (fullFeature n) 0
            (cutFullVariance n q U l 1 b h K) (fun σ=>|Q σ|^4) 0≤C^4 := by
          have HE:=wholeLaw_double_marked_nat_moment_eq (fullWeight_pos n) (fullFeature n)
            T ho 0 (cutFullVariance n q U l 1 b h K) 0
            (fun σ=>P (T.cavityAssignment σ).1) 4 g (nativeFreshAtSlot_mem T 0 a star) p hp
          exact HE.trans_le (hP l hl)
        have HE : (fun σ : p.tree.Assignment=>nativeRestProjectedDisplacementTest T a star
            (restCenteredFixedForkKernel n b S star 0) P p (p.tree.cavityAssignment σ).1)=
            fun σ=>(restCenteredFixedForkKernel n b S star 0
                (p.tree.atSlot σ p.mark).1 (p.tree.atSlot σ (p.embed g.mark)).1-
              restCenteredFixedForkKernel n b S star 0
                (p.tree.atSlot σ (p.embed (g.embed a))).1 (p.tree.atSlot σ (p.embed g.mark)).1)*Q σ := by
          funext σ
          rw [native_rest_projected_displacement_test_actual]
          simp only [←p.spin_at,←p.restrict_at,←g.spin_at,←g.restrict_at,Q]
          rfl
        rw [HE]
        have H:=native_low_two_fixed_star_difference_bound n U star q b h S p.tree ho Hleaf Q
          (p.embed (g.embed a)) p.mark (p.embed g.mark)
          (by simpa only [ClockTree.splitIndex_symm] using Hsplit.2)
          (by simpa only [ClockTree.splitIndex_symm] using Hsplit.1)
          hs hU hl hC hrho hB hq0 hq hb hh hK hbm hhm hKm HQ hclock (hmoment l hl)
        exact H.trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hR l hl)
            (mul_nonneg (mul_nonneg (by norm_num) (ClockTree.absJetVariation_nonneg _ _)) hC))
          (sq_nonneg rho))
      have HI:=weighted_unit_integral_abs_le hV Hjet 1
      have HG:=native_full_scalar_cut_moment_abs_le_one p.tree ho U K [p.embed (g.embed a),p.mark]
      change |fullScalarCutGamma p.tree U K (p.embed (g.embed a)) p.mark * _|≤V
      rw [abs_mul]
      exact (mul_le_mul HG (by simpa only [pow_one] using HI) (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
    · dsimp only [F]
      rw [fullScalarCutGamma_cross_zero p.tree ho U K _ _ hU (by omega),zero_mul,abs_zero]
      exact hV
  have H:=marked_list_weight_abs_le (g.tree.markedAttach 0) F HF
  rw [g.tree.markedAttach_variation ho,sub_zero] at H
  have Hleaf : (g.tree.leaves:ℝ)≤(rBound:ℝ)+1 := by
    exact_mod_cast (T.markedAttach_leaves 0 g (nativeFreshAtSlot_mem T 0 a star)).trans
      (by omega : T.leaves+1≤rBound+1)
  have Hbound:=H.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left Hleaf (by norm_num : (0:ℝ)≤2)) hV)
  unfold nativeGammaProjectedLowSecondRestoration
  simp only [mul_assoc]
  change |((g.tree.markedAttach 0).map (fun p=>p.coeff*F p)).sum|≤_
  exact Hbound.trans_eq (by dsimp only [V];ring)

end OAI.SKFluctuations.Cavity
