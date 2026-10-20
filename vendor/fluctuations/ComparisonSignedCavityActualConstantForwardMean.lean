module

public import ComparisonSignedCavityActualConstantForwardSource

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped BigOperators NNReal
set_option maxHeartbeats 18000000

theorem fullEndpoint_deleted_centered_mean_eq_exact_physical
    (n U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (a z : T.Slot) (haz : a≠z) (S : ℝ) :
    T.disorderExpect (fullWeight n) (fullFeature n) 0
      (cavityPath n U 1 1 (fun j=>Sum.elim (fun _=>b j) (fun _=>h j)) b h K)
      (fun σ=>deletedOverlap n (joinSpin (T.atSlot σ a)) (joinSpin (T.atSlot σ z))-S) 0=
      finitePhysicalMean (n+1) as b h (T.splitIndex a z)-
        finitePhysicalMean (n+1) as b h (T.splitIndex a z)/(n+1:ℕ)-S := by
  let q:=cavityPath n U 1 1 (fun j=>Sum.elim (fun _=>b j) (fun _=>h j)) b h K
  have Hfull:=fullEndpoint_overlap_mean_eq_physical n U b h K T ho a z haz
  have Hsite:=native_actual_full_site_pair_eq_overlap T ho U b h K (fun _=>1)
    (by intro π σ;rfl) a z (Fin.last n)
  simp only [joinSpin_last,mul_one] at Hsite
  have Hone:=T.disorderExpect_one (fullWeight_pos n) (fullFeature n) ho 0 q 0
  have HE : T.disorderExpect (fullWeight n) (fullFeature n) 0 q
      (fun σ=>deletedOverlap n (joinSpin (T.atSlot σ a)) (joinSpin (T.atSlot σ z))-S) 0=
      T.disorderExpect (fullWeight n) (fullFeature n) 0 q
        (fun σ=>orderedOverlap (n+1) (joinSpin (T.atSlot σ a)) (joinSpin (T.atSlot σ z))) 0-
      T.disorderExpect (fullWeight n) (fullFeature n) 0 q
        (fun σ=>spinValue (T.atSlot σ a).2*spinValue (T.atSlot σ z).2) 0/(n+1:ℕ)-
      S*T.disorderExpect (fullWeight n) (fullFeature n) 0 q (fun _=>1) 0:=by
    simp_rw [deletedOverlap_eq,joinSpin_last]
    unfold ClockTree.disorderExpect
    rw [Finset.sum_div,Finset.mul_sum,←Finset.sum_sub_distrib,←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro σ hσ
    ring
  rw [Hone] at HE
  dsimp only [q] at HE
  rw [Hsite,Hfull] at HE
  simpa only [mul_one] using HE

theorem native_original_constant_fresh_pair_moment_eq_exact_physical
    (n U : ℕ) (b h K S : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (s : T.Slot) (star : ℕ) (hstar : star≤as.length) :
    nativeActualOriginalFreshPairMoment n
      (fun j=>Sum.elim (fun _=>b j) (fun _=>h j)) U b h K S T (fun _=>1) s star=
      finitePhysicalMean (n+1) as b h star-finitePhysicalMean (n+1) as b h star/(n+1:ℕ)-S star := by
  let g:=nativeFreshAtSlot T 0 s star
  have hdistinct : g.embed s≠g.mark:=(nativeFreshAtSlot_distinct T 0 s star s).symm
  have HE:=fullEndpoint_deleted_centered_mean_eq_exact_physical n U b h K g.tree ho
    (g.embed s) g.mark hdistinct (S star)
  have hsplit : g.tree.splitIndex (g.embed s) g.mark=star:=by
    rw [g.tree.splitIndex_symm,nativeFreshAtSlot_split,T.splitIndex_self,Nat.min_eq_left hstar]
  rw [hsplit] at HE
  unfold nativeActualOriginalFreshPairMoment
  simp only [one_mul]
  simp_rw [MarkedPlacement.restrict_at,MarkedPlacement.spin_at]
  exact HE

theorem actual_generated_original_constant_gap_eq_star_responses_and_mean_corrections
    {n : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    {i star U k : ℕ} {seed : List NativeResourceMark} {P₀ : NativeResourceTerm i star T}
    (hP : NativeActualResourceGenerated i star U seed k T P₀) (hi : i ≤ star)
    (hs : star < U) (ho : MassOrdered 0 as) (b h K S : ℕ→ℝ)
    (hKS : ∀j,K j=h j+b j*S j)
    (hb : ∀j,0 ≤ b j) (hh : ∀j,0 ≤ h j) (hK : ∀j,0 ≤ K j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K) :
    let q:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
    let s:=P₀.live.test.target
    let g:=nativeFreshAtSlot T 0 s star
    let qfull:=cutFullVariance n q U 1 1 b h K
    let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
    let A:=fun σ τ : Spin n×Bool=>deletedOverlap n (joinSpin σ) (joinSpin τ)-S star
    finitePhysicalMean (n+1) as b h star-nativeOriginalScalarPairMean as K star=
      chi*K star*
        (nativeOriginalLongitudinalPairing n 0 qfull 0 U K b S g.tree (fun _=>1) (g.embed s)+
         nativeOriginalLongitudinalPairing n 0 qfull 0 U K b S g.tree (fun _=>1) g.mark)+
      chi^2*b star*(finitePhysicalMean (n+1) as b h star-
        finitePhysicalMean (n+1) as b h star/(n+1:ℕ)-S star)+
      b star*(chi*nativeOriginalLongitudinalPairing n 0 qfull 0 U K b S g.tree
        (fun σ=>A (T.atSlot (g.restrict σ) s) (g.spin σ)) (g.embed s)+
        nativeOriginalFreshPartnerLResponse n 0 qfull 0 U K b S T s star
          (fun _ c d=>A c d))+
      nativeActualOriginalForwardTaylorError n q U b h K S g.tree (fun _=>1) (g.embed s) g.mark := by
  dsimp only
  have HE:=actual_generated_original_constant_physical_scalar_gap_eq_star_responses
    hP hi hs ho b h K S hKS hb hh hK hbm hhm hKm
  dsimp only at HE
  rw [native_original_constant_fresh_pair_moment_eq_exact_physical n U b h K S T ho
    P₀.live.test.target star (hs.le.trans hP.highCut_le_length)] at HE
  exact HE

theorem actual_original_constant_gap_eq_single_star_responses
    (n : ℕ) (as : List PositiveMass) (star U : ℕ)
    (hs : star < U) (hU : U≤as.length) (ho : MassOrdered 0 as) (b h K S : ℕ→ℝ)
    (hKS : ∀j,K j=h j+b j*S j)
    (hb : ∀j,0 ≤ b j) (hh : ∀j,0 ≤ h j) (hK : ∀j,0 ≤ K j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K) :
    let T:=ClockTree.single (S:=Spin n×Bool) as
    let q:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
    let s:=singleSlot as
    let g:=nativeFreshAtSlot T 0 s star
    let qfull:=cutFullVariance n q U 1 1 b h K
    let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
    let A:=fun σ τ : Spin n×Bool=>deletedOverlap n (joinSpin σ) (joinSpin τ)-S star
    finitePhysicalMean (n+1) as b h star-nativeOriginalScalarPairMean as K star=
      chi*K star*
        (nativeOriginalLongitudinalPairing n 0 qfull 0 U K b S g.tree (fun _=>1) (g.embed s)+
         nativeOriginalLongitudinalPairing n 0 qfull 0 U K b S g.tree (fun _=>1) g.mark)+
      chi^2*b star*(finitePhysicalMean (n+1) as b h star-
        finitePhysicalMean (n+1) as b h star/(n+1:ℕ)-S star)+
      b star*(chi*nativeOriginalLongitudinalPairing n 0 qfull 0 U K b S g.tree
        (fun σ=>A (T.atSlot (g.restrict σ) s) (g.spin σ)) (g.embed s)+
        nativeOriginalFreshPartnerLResponse n 0 qfull 0 U K b S T s star
          (fun _ c d=>A c d))+
      nativeActualOriginalForwardTaylorError n q U b h K S g.tree (fun _=>1) (g.embed s) g.mark := by
  dsimp only
  let st:=nativeActualConstantState (S:=Spin n×Bool) as star star
  have hst : NativeActualResourceGenerated star star U [] st.generation st.tree st.term:=
    .physical (.constant as hU)
  exact actual_generated_original_constant_gap_eq_star_responses_and_mean_corrections
    hst le_rfl hs ho b h K S hKS hb hh hK hbm hhm hKm

end OAI.SKFluctuations.Cavity
