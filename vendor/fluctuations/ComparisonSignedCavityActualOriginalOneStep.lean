module

public import ComparisonSignedCavityActualFreshForwardSource
public import ComparisonSignedCavityActualOriginalGammaPairRow
public import ComparisonSignedCavityActualResourceResponseOperations

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped BigOperators NNReal
set_option maxHeartbeats 28000000
set_option backward.isDefEq.respectTransparency false

theorem native_original_fresh_partner_L_response_const_mul (n : ℕ)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (x : FullCoordinate n→ℝ)
    (U : ℕ) (K b C : ℕ→ℝ) {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as) (s : T.Slot) (star : ℕ)
    (Q : T.Assignment→(Spin n×Bool)→(Spin n×Bool)→ℝ) (c : ℝ) :
    nativeOriginalFreshPartnerLResponse n v q x U K b C T s star (fun σ a d=>c*Q σ a d)=
      c*nativeOriginalFreshPartnerLResponse n v q x U K b C T s star Q := by
  unfold nativeOriginalFreshPartnerLResponse
  dsimp only
  simp_rw [native_original_longitudinal_const_mul_test n v q x U K b C _ ho]
  simp only [mul_left_comm,List.sum_map_mul_left]

def nativeActualOriginalFreshPairMoment (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K S : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (P : T.cavityLeft.Assignment→ℝ) (s : T.Slot) (star : ℕ) : ℝ :=
  let g:=nativeFreshAtSlot T 0 s star
  g.tree.disorderExpect (fullWeight n) (fullFeature n) 0 (cutFullVariance n q U 1 1 b h K)
    (fun σ=>P (g.restRestrict (g.tree.cavityAssignment σ).1)*
      (deletedOverlap n (joinSpin (T.atSlot (g.restrict σ) s)) (joinSpin (g.spin σ))-S star)) 0

def nativeActualOriginalOneStepError (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K S : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (P : T.cavityLeft.Assignment→ℝ) (s : T.Slot) (star : ℕ) : ℝ :=
  let g:=nativeFreshAtSlot T 0 s star
  let Pg:=fun σ=>P (g.restRestrict σ)
  let Q:=fun σ=>P (T.cavityAssignment σ).1
  let qfull:=cutFullVariance n q U 1 1 b h K
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  let A:=fun σ τ : Spin n×Bool=>restCenteredFixedForkKernel n b S star 0 σ.1 τ.1
  (chi/2)*nativeActualOriginalGammaPairResampling T s star U K 0 qfull 0 A Q+
  (chi/2)*nativeActualOriginalGProjectedResampling T s star U K b S 0 qfull 0 A Q+
  nativeActualOriginalForwardTaylorError n q U b h K S g.tree Pg (g.embed s) g.mark-
  (nativeOriginalSitePairExpectation n q U b h K g.tree Pg (g.embed s) g.mark-
    nativeActualOriginalFreshPairMoment n q U b h K S T P s star)

theorem actual_generated_original_pair_eq_longitudinal_step
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
    let A:=fun σ τ : Spin n×Bool=>deletedOverlap n (joinSpin σ) (joinSpin τ)-S star
    (1-b star*chi^2)*nativeActualOriginalFreshPairMoment n q U b h K S T Pc s star=
      chi*K star*
        (nativeOriginalLongitudinalPairing n 0 qfull 0 U K b S g.tree
          (fun σ=>Pg (g.tree.cavityAssignment σ).1) (g.embed s)+
         nativeOriginalLongitudinalPairing n 0 qfull 0 U K b S g.tree
          (fun σ=>Pg (g.tree.cavityAssignment σ).1) g.mark)+
      b star*(chi*nativeOriginalLongitudinalPairing n 0 qfull 0 U K b S g.tree
        (fun σ=>Q (g.restrict σ)*A (T.atSlot (g.restrict σ) s) (g.spin σ)) (g.embed s)+
        nativeOriginalFreshPartnerLResponse n 0 qfull 0 U K b S T s star
          (fun σ c d=>Q σ*A c d))+
      nativeActualOriginalOneStepError n q U b h K S T Pc s star := by
  dsimp only
  let s:=P₀.live.test.target
  let g:=nativeFreshAtSlot T 0 s star
  let Pc:=nativeOriginalCenteredRestTest n q U b h K T P
  let Pg:=fun σ=>Pc (g.restRestrict σ)
  let Q:=fun σ=>Pc (T.cavityAssignment σ).1
  let qfull:=cutFullVariance n q U 1 1 b h K
  let A:=fun σ τ : Spin n×Bool=>deletedOverlap n (joinSpin σ) (joinSpin τ)-S star
  let B:=fun σ τ : Spin n×Bool=>restCenteredFixedForkKernel n b S star 0 σ.1 τ.1
  have hB : ∀σ τ,B σ τ=b star*A σ τ := by
    intro σ τ
    simp only [B,A,restCenteredFixedForkKernel,deletedOverlap,joinSpin,Fin.lastCases_castSucc]
  have HE:=actual_generated_original_centered_pair_eq_fresh_sources hP hi hs ho q b h K S
    hKS P hq0 hq hb hh hK hbm hhm hKm
  dsimp only at HE
  have HL:=native_actual_generated_original_leading_response_eq_baseline_add_resampling
    hP hi hs ho K 0 qfull 0 B Q
  rw [HL] at HE
  have HP : (fun σ : g.tree.Assignment=>Q (g.restrict σ)*B (T.atSlot (g.restrict σ) s) (g.spin σ))=
      fun σ=>b star*(Q (g.restrict σ)*A (T.atSlot (g.restrict σ) s) (g.spin σ)) := by
    funext σ
    rw [hB]
    ring
  have HF : (fun σ c d=>Q σ*B c d)=fun σ c d=>b star*(Q σ*A c d) := by
    funext σ c d
    rw [hB]
    ring
  rw [HP,g.tree.disorderExpect_const_mul (fullWeight_pos n) (fullFeature n) ho,
    native_original_longitudinal_const_mul_test n 0 qfull 0 U K b S g.tree ho,
    HF,native_original_fresh_partner_L_response_const_mul n 0 qfull 0 U K b S T ho] at HE
  have Hmoment : g.tree.disorderExpect (fullWeight n) (fullFeature n) 0 qfull
      (fun σ=>Q (g.restrict σ)*A (T.atSlot (g.restrict σ) s) (g.spin σ)) 0=
      nativeActualOriginalFreshPairMoment n q U b h K S T Pc s star := by
    have HT : (fun σ : g.tree.Assignment=>Q (g.restrict σ)*A (T.atSlot (g.restrict σ) s) (g.spin σ))=
        fun σ=>Pc (g.restRestrict (g.tree.cavityAssignment σ).1)*
          (deletedOverlap n (joinSpin (T.atSlot (g.restrict σ) s)) (joinSpin (g.spin σ))-S star) := by
      funext σ
      dsimp only [Q,A]
      rw [g.restRestrict_actual]
    exact congrArg (fun F=>g.tree.disorderExpect (fullWeight n) (fullFeature n) 0 qfull F 0) HT
  rw [Hmoment] at HE
  unfold nativeActualOriginalOneStepError
  dsimp only [s,g,Pc,Pg,Q,qfull,A,B] at HE ⊢
  linear_combination HE

end OAI.SKFluctuations.Cavity
