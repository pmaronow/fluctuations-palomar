module

public import ComparisonSignedCavityActualOriginalOneStep
public import ComparisonSignedCavityTwoFreshLongitudinal

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped BigOperators NNReal
set_option maxHeartbeats 24000000
set_option backward.isDefEq.respectTransparency false

def nativeOriginalPairRecursionChildren (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K S : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (P : T.cavityLeft.Assignment→ℝ) (s : T.Slot) (star : ℕ) : ℝ :=
  let g:=nativeFreshAtSlot T 0 s star
  let Q:=fun σ=>P (T.cavityAssignment σ).1
  let qfull:=cutFullVariance n q U 1 1 b h K
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  let A:=fun σ τ : Spin n×Bool=>deletedOverlap n (joinSpin σ) (joinSpin τ)-S star
  b star*(chi*nativeOriginalLongitudinalPairing n 0 qfull 0 U K b S g.tree
    (fun σ=>Q (g.restrict σ)*A (T.atSlot (g.restrict σ) s) (g.spin σ)) (g.embed s)+
    nativeOriginalFreshPartnerLResponse n 0 qfull 0 U K b S T s star (fun σ c d=>Q σ*A c d))

def nativeOriginalPairRecursionDefect (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K S : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (P : T.cavityLeft.Assignment→ℝ) (s : T.Slot) (star : ℕ) : ℝ :=
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  (1-b star*chi^2)*nativeActualOriginalFreshPairMoment n q U b h K S T P s star-
    nativeActualOriginalOneStepError n q U b h K S T P s star

theorem actual_original_pair_step_eq_parent_add_fresh
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
    let Q:=fun σ=>Pc (T.cavityAssignment σ).1
    let qfull:=cutFullVariance n q U 1 1 b h K
    let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
    nativeOriginalPairRecursionDefect n q U b h K S T Pc s star=
      chi*K star*(nativeOriginalLongitudinalPairing n 0 qfull 0 U K b S T Q s+
        nativeOriginalLongitudinalPairing n 0 qfull 0 U K b S g.tree
          (fun σ=>Q (g.restrict σ)) g.mark)+
      nativeOriginalPairRecursionChildren n q U b h K S T Pc s star := by
  dsimp only
  let s:=P₀.live.test.target
  let g:=nativeFreshAtSlot T 0 s star
  let Pc:=nativeOriginalCenteredRestTest n q U b h K T P
  let Q:=fun σ=>Pc (T.cavityAssignment σ).1
  let qfull:=cutFullVariance n q U 1 1 b h K
  have hqfull : ∀j₀,Monotone (fun j=>qfull j j₀):=
    cutFullVariance_monotone n q U (by norm_num) (by norm_num) hq hb hh hK hbm hhm hKm
  have hqfull0 : ∀j₀,(0:ℝ) ≤ qfull 0 j₀:=
    cutFullVariance_nonneg n q U (by norm_num) (by norm_num) hq0 hb hh hK 0
  have HE:=actual_generated_original_pair_eq_longitudinal_step hP hi hs ho q b h K S hKS P
    hq0 hq hb hh hK hbm hhm hKm
  dsimp only at HE
  have HR : (fun σ : g.tree.Assignment=>Pc (g.restRestrict (g.tree.cavityAssignment σ).1))=
      fun σ=>Q (g.restrict σ) := by
    funext σ
    dsimp only [Q]
    rw [g.restRestrict_actual]
  rw [HR,native_original_longitudinal_fresh_star_preserves n 0 qfull 0 U K b S T ho Q s s star
    hqfull hqfull0 hK hKm (by omega) hP.highCut_le_length] at HE
  unfold nativeOriginalPairRecursionDefect nativeOriginalPairRecursionChildren
  dsimp only [s,g,Pc,Q,qfull] at HE ⊢
  linear_combination HE

theorem actual_original_longitudinal_eq_two_fresh_subtraction
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
    chi*K star*nativeOriginalLongitudinalPairing n 0 qfull 0 U K b S T Q s=
      nativeOriginalPairRecursionDefect n q U b h K S T Pc s star-
      (1/2:ℝ)*nativeOriginalPairRecursionDefect n q U b h K S g.tree Pg g.mark star-
      nativeOriginalPairRecursionChildren n q U b h K S T Pc s star+
      (1/2:ℝ)*nativeOriginalPairRecursionChildren n q U b h K S g.tree Pg g.mark star := by
  dsimp only
  let s:=P₀.live.test.target
  let g:=nativeFreshAtSlot T 0 s star
  let f:=nativeFreshAtSlot g.tree 0 g.mark star
  let Pc:=nativeOriginalCenteredRestTest n q U b h K T P
  let Pg:=fun σ=>Pc (g.restRestrict σ)
  let Q:=fun σ=>Pc (T.cavityAssignment σ).1
  let qfull:=cutFullVariance n q U 1 1 b h K
  have hqfull : ∀j₀,Monotone (fun j=>qfull j j₀):=
    cutFullVariance_monotone n q U (by norm_num) (by norm_num) hq hb hh hK hbm hhm hKm
  have hqfull0 : ∀j₀,(0:ℝ) ≤ qfull 0 j₀:=
    cutFullVariance_nonneg n q U (by norm_num) (by norm_num) hq0 hb hh hK 0
  have H0:=actual_original_pair_step_eq_parent_add_fresh hP hi hs ho q b h K S hKS P
    hq0 hq hb hh hK hbm hhm hKm
  have H1:=actual_original_pair_step_eq_parent_add_fresh hP.retarget hi hs ho q b h K S hKS
    (fun σ=>P (g.restRestrict σ)) hq0 hq hb hh hK hbm hhm hKm
  dsimp only at H0 H1
  have HC : nativeOriginalCenteredRestTest n q U b h K g.tree (fun σ=>P (g.restRestrict σ))=Pg:=
    native_original_centered_rest_test_fresh n q U b h K T ho P s star
  have HR : (fun σ : g.tree.Assignment=>Pg (g.tree.cavityAssignment σ).1)=
      fun σ=>Q (g.restrict σ) := by
    funext σ
    dsimp only [Pg,Q]
    rw [g.restRestrict_actual]
  rw [HC,HR] at H1
  have HE:=native_original_two_fresh_longitudinal_sum n 0 qfull 0 U K b S T ho Q s star
    (hs.le.trans hP.highCut_le_length) hqfull hqfull0 hK hKm (by omega) hP.highCut_le_length
  dsimp only at HE
  have HG:=native_original_longitudinal_fresh_star_preserves n 0 qfull 0 U K b S g.tree ho
    (fun σ=>Q (g.restrict σ)) g.mark g.mark star hqfull hqfull0 hK hKm
    (by omega) hP.highCut_le_length
  have HF : nativeOriginalLongitudinalPairing n 0 qfull 0 U K b S f.tree
      (fun σ=>Q (g.restrict (f.restrict σ))) f.mark=
      nativeOriginalLongitudinalPairing n 0 qfull 0 U K b S g.tree
        (fun σ=>Q (g.restrict σ)) g.mark := by
    rw [HG] at HE
    linarith
  have HRf : (fun σ : f.tree.Assignment=>Pg (g.tree.cavityAssignment (f.restrict σ)).1)=
      fun σ=>Q (g.restrict (f.restrict σ)) := by
    funext σ
    exact congrFun HR (f.restrict σ)
  change nativeOriginalPairRecursionDefect n q U b h K S g.tree Pg g.mark star=
    (scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0*K star*
      (nativeOriginalLongitudinalPairing n 0 qfull 0 U K b S g.tree
        (fun σ=>Q (g.restrict σ)) g.mark+
       nativeOriginalLongitudinalPairing n 0 qfull 0 U K b S f.tree
        (fun σ=>Pg (g.tree.cavityAssignment (f.restrict σ)).1) f.mark)+
      nativeOriginalPairRecursionChildren n q U b h K S g.tree Pg g.mark star at H1
  rw [HRf,HF] at H1
  dsimp only [s,g,Pc,Pg,Q,qfull] at H0 H1 ⊢
  linear_combination -H0+(1/2:ℝ)*H1

end OAI.SKFluctuations.Cavity
