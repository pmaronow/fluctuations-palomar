module

public import ComparisonSignedCavityActualFreshCentering
public import ComparisonSignedCavityActualOriginalProjectionResampling
public import ComparisonSignedCavityActualOriginalForwardSourceAdapters

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped BigOperators NNReal
set_option maxHeartbeats 24000000
set_option backward.isDefEq.respectTransparency false

def nativeActualOriginalForwardTaylorError (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K S : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (P : T.cavityLeft.Assignment→ℝ) (a z : T.Slot) : ℝ :=
  nativeActualHigherAllocatedRemainder n q U b h K T P a z-
    nativeCenteredLowGammaHighSecondRemainder n q U b h K S T P a z-
    nativeCenteredLowGammaLowRestoration n q U b h K S T P a z-
    (scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0*
      K (T.splitIndex a z)*
      (nativeOriginalLongitudinalRestoration n q U b h K S T
        (fun σ=>P (T.cavityAssignment σ).1) a+
       nativeOriginalLongitudinalRestoration n q U b h K S T
        (fun σ=>P (T.cavityAssignment σ).1) z)-
    nativeOriginalGKernelLowRestoration n q U b h K S T P a z
      (restCenteredLowKernel n U b S)

theorem actual_generated_original_centered_pair_eq_fresh_sources
    {n : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    {i star U k : ℕ} {seed : List NativeResourceMark} {P₀ : NativeResourceTerm i star T}
    (hP : NativeActualResourceGenerated i star U seed k T P₀) (hi : i ≤ star)
    (hs : star < U) (ho : MassOrdered 0 as)
    (q : ℕ→RestCoordinate n→ℝ) (b h K S : ℕ→ℝ)
    (hKS : ∀j,K j=h j+b j*S j) (P : T.cavityLeft.Assignment→ℝ)
    (hq0 : ∀j j₀,0 ≤ q j j₀) (hq : ∀j₀,Monotone (fun j=>q j j₀))
    (hb : ∀j,0 ≤ b j) (hh : ∀j,0 ≤ h j) (hK : ∀j,0 ≤ K j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K) :
    let s:=P₀.live.test.target
    let g:=nativeFreshAtSlot T 0 s star
    let Pc:=nativeOriginalCenteredRestTest n q U b h K T P
    let Pg:=fun σ=>Pc (g.restRestrict σ)
    let Q:=fun σ=>Pc (T.cavityAssignment σ).1
    let qfull:=cutFullVariance n q U 1 1 b h K
    let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
    let A:=fun σ τ : Spin n×Bool=>restCenteredFixedForkKernel n b S star 0 σ.1 τ.1
    nativeOriginalSitePairExpectation n q U b h K g.tree Pg (g.embed s) g.mark=
      chi*K star*
        (nativeOriginalLongitudinalPairing n 0 qfull 0 U K b S g.tree
          (fun σ=>Pg (g.tree.cavityAssignment σ).1) (g.embed s)+
         nativeOriginalLongitudinalPairing n 0 qfull 0 U K b S g.tree
          (fun σ=>Pg (g.tree.cavityAssignment σ).1) g.mark)+
      chi*nativeOriginalFreshPartnerLeadingResponse n 0 qfull 0 U K T s star
        (fun σ c d=>Q σ*A c d)+
      chi*nativeOriginalLongitudinalPairing n 0 qfull 0 U K b S g.tree
        (fun σ=>Q (g.restrict σ)*A (T.atSlot (g.restrict σ) s) (g.spin σ)) (g.embed s)+
      nativeOriginalFreshPartnerLResponse n 0 qfull 0 U K b S T s star
        (fun σ c d=>Q σ*A c d)+
      (chi/2)*nativeActualOriginalGProjectedResampling T s star U K b S 0 qfull 0 A Q+
      nativeActualOriginalForwardTaylorError n q U b h K S g.tree Pg (g.embed s) g.mark := by
  dsimp only
  let s:=P₀.live.test.target
  let g:=nativeFreshAtSlot T 0 s star
  let Pc:=nativeOriginalCenteredRestTest n q U b h K T P
  let Pg:=fun σ=>Pc (g.restRestrict σ)
  let Q:=fun σ=>Pc (T.cavityAssignment σ).1
  let qfull:=cutFullVariance n q U 1 1 b h K
  let A:=fun σ τ : Spin n×Bool=>restCenteredFixedForkKernel n b S star 0 σ.1 τ.1
  have hU:=hP.highCut_le_length
  have hstar : star ≤ as.length:=hs.le.trans hU
  have hsplit : g.tree.splitIndex (g.embed s) g.mark=star := by
    rw [g.tree.splitIndex_symm,nativeFreshAtSlot_split,T.splitIndex_self,Nat.min_eq_left hstar]
  have hcenter : nativeOriginalCenteredRestTest n q U b h K g.tree
      (fun σ=>P (g.restRestrict σ))=Pg :=
    native_original_centered_rest_test_fresh n q U b h K T ho P s star
  have hQ : (fun σ=>Pg (g.tree.cavityAssignment σ).1)=fun σ=>Q (g.restrict σ) := by
    funext σ
    dsimp only [Pg,Q]
    rw [←g.restRestrict_actual]
  have hA : ∀σ τ,A σ τ=A τ σ := by
    intro σ τ
    have HE : (∑j,spinValue (σ.1 j)*spinValue (τ.1 j))=
        ∑j,spinValue (τ.1 j)*spinValue (σ.1 j) := by
      apply Finset.sum_congr rfl
      intro j _
      ring
    simp only [A,restCenteredFixedForkKernel,HE]
  have hqfull : ∀j₀,Monotone (fun j=>qfull j j₀):=
    cutFullVariance_monotone n q U (by norm_num) (by norm_num) hq hb hh hK hbm hhm hKm
  have hqfull0 : ∀j₀,(0:ℝ) ≤ qfull 0 j₀:=
    cutFullVariance_nonneg n q U (by norm_num) (by norm_num) hq0 hb hh hK 0
  have HE:=actual_original_centered_site_pair_eq_forward_sources n q U b h K S hKS g.tree ho
    (fun σ=>P (g.restRestrict σ)) (g.embed s) g.mark
    hq0 hq hb hh hK hbm hhm hKm (by omega) hU (by rw [hsplit];exact hs)
  dsimp only at HE
  rw [hcenter,hsplit,hQ] at HE
  have HL:=native_original_fresh_gamma_forward_eq_chi_response n 0 qfull 0 U K T ho
    s star hs hU Q A
  have HA:=native_actual_generated_original_forward_G_eq_projection_add_resampling
    hP hi hs ho 0 qfull 0 K b S hqfull hqfull0 hK hKm A Q
  have HB:=native_original_fresh_forward_G_eq_partner_L_response n 0 qfull 0 U K b S T ho
    s star hs hU hqfull hqfull0 hK hKm Q A hA
  dsimp only at HL HA HB
  rw [HL,HA,HB] at HE
  change _= _ at HE
  unfold nativeActualOriginalForwardTaylorError
  rw [hsplit,hQ]
  dsimp only [s,g,Pc,Pg,Q,qfull,A] at HE ⊢
  linear_combination HE

end OAI.SKFluctuations.Cavity
