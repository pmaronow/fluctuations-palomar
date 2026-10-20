module

public import ComparisonSignedCavityActualUncenteredFreshForwardSource
public import ComparisonSignedCavityActualOriginalOneStep
public import ComparisonSignedCavityOriginalConstantEndpoints

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped BigOperators NNReal
set_option maxHeartbeats 28000000
set_option backward.isDefEq.respectTransparency false

theorem native_original_connected_high_response_zero_test
    (n : ℕ) (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ)
    (x : FullCoordinate n→ℝ) (U : ℕ) (K b S : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (a c : T.Slot) :
    nativeOriginalConnectedHighResponse n v q x U K b S T (fun _=>0) a c=0 := by
  simp [nativeOriginalConnectedHighResponse,nativeOriginalSignedJets,
    ClockTree.profilePairTest,ClockTree.disorderExpect]

theorem native_original_G_projected_resampling_constant_test
    {n : ℕ} {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (s : T.Slot) (star U : ℕ) (K b S : ℕ→ℝ)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (x : FullCoordinate n→ℝ)
    (A : (Spin n×Bool)→(Spin n×Bool)→ℝ) :
    nativeActualOriginalGProjectedResampling T s star U K b S v q x A (fun _=>1)=0 := by
  simp [nativeActualOriginalGProjectedResampling,
    native_original_connected_high_response_zero_test]

theorem native_original_Gamma_pair_resampling_constant_test
    {n : ℕ} {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (s : T.Slot) (star U : ℕ) (K : ℕ→ℝ)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (x : FullCoordinate n→ℝ)
    (A : (Spin n×Bool)→(Spin n×Bool)→ℝ) :
    nativeActualOriginalGammaPairResampling T s star U K v q x A (fun _=>1)=0 := by
  simp [nativeActualOriginalGammaPairResampling,ClockTree.disorderExpect]

theorem actual_generated_original_constant_physical_scalar_gap_eq_star_responses
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
      chi^2*b star*nativeActualOriginalFreshPairMoment n q U b h K S T (fun _=>1) s star+
      b star*(chi*nativeOriginalLongitudinalPairing n 0 qfull 0 U K b S g.tree
        (fun σ=>A (T.atSlot (g.restrict σ) s) (g.spin σ)) (g.embed s)+
        nativeOriginalFreshPartnerLResponse n 0 qfull 0 U K b S T s star
          (fun _ c d=>A c d))+
      nativeActualOriginalForwardTaylorError n q U b h K S g.tree (fun _=>1) (g.embed s) g.mark := by
  dsimp only
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let s:=P₀.live.test.target
  let g:=nativeFreshAtSlot T 0 s star
  let qfull:=cutFullVariance n q U 1 1 b h K
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  let A:=fun σ τ : Spin n×Bool=>deletedOverlap n (joinSpin σ) (joinSpin τ)-S star
  let B:=fun σ τ : Spin n×Bool=>restCenteredFixedForkKernel n b S star 0 σ.1 τ.1
  have hq0 : ∀j c,0 ≤ q j c:=by
    intro j c
    cases c with
    | inl c=>exact hb j
    | inr c=>exact hh j
  have hq : ∀c,Monotone (fun j=>q j c):=by
    intro c
    cases c with
    | inl c=>exact hbm
    | inr c=>exact hhm
  have HE:=actual_generated_original_uncentered_pair_gap_eq_fresh_sources hP hi hs ho q b h K S
    hKS (fun _=>1) hq0 hq hb hh hK hbm hhm hKm
  dsimp only at HE
  simp only [one_mul] at HE
  have HL:=native_actual_generated_original_leading_response_eq_baseline_add_resampling
    hP hi hs ho K 0 qfull 0 B (fun _=>1)
  dsimp only at HL
  simp only [one_mul,native_original_Gamma_pair_resampling_constant_test,mul_zero,add_zero] at HL
  rw [HL,native_original_G_projected_resampling_constant_test] at HE
  have hB : ∀σ τ,B σ τ=b star*A σ τ:=by
    intro σ τ
    simp only [B,A,restCenteredFixedForkKernel,deletedOverlap,joinSpin,Fin.lastCases_castSucc]
  have HP : (fun σ : g.tree.Assignment=>B (T.atSlot (g.restrict σ) s) (g.spin σ))=
      fun σ=>b star*A (T.atSlot (g.restrict σ) s) (g.spin σ):=by
    funext σ
    rw [hB]
  have HF : (fun _ : T.Assignment=>fun c d=>B c d)=
      (fun _ : T.Assignment=>fun c d=>b star*A c d):=by
    funext σ c d
    rw [hB]
  rw [HP,g.tree.disorderExpect_const_mul (fullWeight_pos n) (fullFeature n) ho,
    native_original_longitudinal_const_mul_test n 0 qfull 0 U K b S g.tree ho,
    HF,native_original_fresh_partner_L_response_const_mul n 0 qfull 0 U K b S T ho] at HE
  have Hmoment : g.tree.disorderExpect (fullWeight n) (fullFeature n) 0 qfull
      (fun σ=>A (T.atSlot (g.restrict σ) s) (g.spin σ)) 0=
      nativeActualOriginalFreshPairMoment n q U b h K S T (fun _=>1) s star:=by
    unfold nativeActualOriginalFreshPairMoment
    simp only [one_mul]
    rfl
  have hsplit : g.tree.splitIndex (g.embed s) g.mark=star:=by
    rw [g.tree.splitIndex_symm,nativeFreshAtSlot_split,T.splitIndex_self,
      Nat.min_eq_left (hs.le.trans hP.highCut_le_length)]
  have hdistinct : g.embed s≠g.mark:=(nativeFreshAtSlot_distinct T 0 s star s).symm
  rw [Hmoment,native_original_rest_test_one n q U b h K g.tree ho,
    native_original_site_pair_one_eq_physical n U b h K g.tree ho (g.embed s) g.mark hdistinct,
    native_pure_scalar_endpoint_pair_eq_original n q U b h K g.tree ho (g.embed s) g.mark hdistinct,
    hsplit] at HE
  dsimp only [s,g,qfull,chi,A,B] at HE ⊢
  linear_combination HE

end OAI.SKFluctuations.Cavity
