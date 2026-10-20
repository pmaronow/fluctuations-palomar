module

public import ComparisonSignedCavityActualProjectionFactorization
public import ComparisonSignedCavityHighFreshInterchange
public import ComparisonSignedCavityStarFieldFreshTestFold
public import ComparisonSignedCavityProjectionRestrictionReplacement
public import ComparisonSignedCavityStarFieldMarkedExchange

@[expose] public section

noncomputable section
set_option maxHeartbeats 24000000
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {ι S B : Type} [Fintype ι] [Fintype S] [Nonempty S] [Fintype B] [Nonempty B]
variable {as : List PositiveMass}

theorem NativeProjectionSpine.observed_rest_factorization
    {A T : ClockTree (S×B) as} {base : NativeGeneratedTest A} {P : NativeGeneratedTest T}
    {star : ℕ} (h : NativeProjectionSpine base star P)
    {w : S→ℝ} (hw : ∀σ,0<w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    {a₀ : ℝ} (ho : MassOrdered a₀ as) (aRow : ℝ)
    (p : MarkedPlacement T) (hp : p∈T.markedAttach aRow)
    (hh : star<p.tree.splitIndex (p.embed P.target) p.mark)
    (R : S→S→ℝ) (C : ℕ→ℝ) :
    ∃r : MarkedPlacement A,r∈A.markedAttach aRow ∧ p.coeff=r.coeff ∧
      p.tree.splitIndex (p.embed P.target) p.mark=r.tree.splitIndex (r.embed base.target) r.mark ∧
      ∀(q : ℕ→ι→ℝ≥0) (J : (ι→ℝ)→A.cavityLeft.Assignment→S→ℝ) (x : ι→ℝ),
      nativeStarFieldTestMean w φ p.tree.cavityLeft (p.tree.cavityLeftSlot (p.embed P.target)) star q
        (fun y σ=>J y (h.restRead (p.restRestrict σ)) (p.restSpin σ)*
          nativeRestGeneratedTestValue T P R C (p.restRestrict σ)) x=
      nativeStarFieldTestMean w φ r.tree.cavityLeft (r.tree.cavityLeftSlot (r.embed base.target)) star q
        (fun y σ=>J y (r.restRestrict σ) (r.restSpin σ)*
          nativeRestGeneratedTestValue A base R C (r.restRestrict σ)*
          (nativeStarPairFactor w φ as star q (fun u v=>R u v-C star) y
            (A.cavityLeft.atSlot (r.restRestrict σ) (A.cavityLeftSlot base.target)))^h.toothCount) x := by
  induction h generalizing aRow with
  | base=>
    refine ⟨p,hp,rfl,rfl,?_⟩
    intro q J x
    simp only [NativeProjectionSpine.restRead,NativeProjectionSpine.toothCount,id_eq,pow_zero,mul_one]
  | @projection T P h a hl ih=>
    obtain ⟨r₀,hr₀,hcoeff₀,hsplit₀,Hlaw⟩:=
      native_high_fresh_interchange T P.target star hl a aRow p hp hh hw φ ho
    have hh₀ : star<r₀.tree.splitIndex (r₀.embed P.target) r₀.mark := by
      rw [←hsplit₀]
      exact hh
    obtain ⟨r,hr,hcoeff,hsplit,IH⟩:=ih aRow r₀ hr₀ hh₀
    refine ⟨r,hr,hcoeff₀.trans hcoeff,hsplit₀.trans hsplit,?_⟩
    intro q J x
    let F:=fun u v=>R u v-C star
    let Q:=fun (y:ι→ℝ) (σ:T.cavityLeft.Assignment) (u v:S)=>
      J y (h.restRead σ) u*nativeRestGeneratedTestValue T P R C σ*
        F (T.cavityLeft.atSlot σ (T.cavityLeftSlot P.target)) v
    have Hleft : nativeStarFieldTestMean w φ p.tree.cavityLeft
        (p.tree.cavityLeftSlot (p.embed (P.addProjection a star).target)) star q
        (fun y σ=>J y ((NativeProjectionSpine.projection h a hl).restRead (p.restRestrict σ))
          (p.restSpin σ)*nativeRestGeneratedTestValue _ (P.addProjection a star) R C
          (p.restRestrict σ)) x=
      nativeStarFieldTestMean w φ p.tree.cavityLeft
        (p.tree.cavityLeftSlot (p.embed ((nativeFreshAtSlot T a P.target star).embed P.target))) star q
        (fun y σ=>Q y ((nativeFreshAtSlot T a P.target star).restRestrict (p.restRestrict σ))
          (p.restSpin σ) ((nativeFreshAtSlot T a P.target star).restSpin (p.restRestrict σ))) x := by
      apply congrArg (fun L=>nativeStarFieldTestMean w φ p.tree.cavityLeft
        (p.tree.cavityLeftSlot (p.embed ((nativeFreshAtSlot T a P.target star).embed P.target))) star q L x)
      funext y σ
      dsimp only [NativeProjectionSpine.restRead]
      rw [native_rest_add_projection_value P a hl R C]
      dsimp only [Q,F]
      ring
    rw [Hleft,Hlaw q Q x]
    have Hfresh:=native_star_field_fresh_selector_factor r₀.tree (r₀.embed P.target) star hl a
      hw φ ho q
      (fun y σ=>J y (h.restRead (r₀.restRestrict σ)) (r₀.restSpin σ)*
        nativeRestGeneratedTestValue T P R C (r₀.restRestrict σ))
      (fun _ σ=>T.cavityLeft.atSlot (r₀.restRestrict σ) (T.cavityLeftSlot P.target)) F x
    dsimp only at Hfresh
    rw [Hfresh]
    have Hpayload : (fun y σ=>
        (J y (h.restRead (r₀.restRestrict σ)) (r₀.restSpin σ)*
          nativeRestGeneratedTestValue T P R C (r₀.restRestrict σ))*
          nativeStarPairFactor w φ as star q F y
            (T.cavityLeft.atSlot (r₀.restRestrict σ) (T.cavityLeftSlot P.target)))=
      (fun y σ=>(J y (h.restRead (r₀.restRestrict σ)) (r₀.restSpin σ)*
          nativeStarPairFactor w φ as star q F y
            (A.cavityLeft.atSlot (h.restRead (r₀.restRestrict σ)) (A.cavityLeftSlot base.target)))*
          nativeRestGeneratedTestValue T P R C (r₀.restRestrict σ)) := by
      funext y σ
      rw [h.restTargetRead]
      ring
    rw [Hpayload,IH q (fun y σ u=>J y σ u*nativeStarPairFactor w φ as star q F y
      (A.cavityLeft.atSlot σ (A.cavityLeftSlot base.target))) x]
    apply congrArg (fun L=>nativeStarFieldTestMean w φ r.tree.cavityLeft
      (r.tree.cavityLeftSlot (r.embed base.target)) star q L x)
    funext y σ
    dsimp only [NativeProjectionSpine.toothCount,F]
    rw [pow_succ]
    ring

theorem NativeProjectionSpine.observed_paired_rest_factorization
    {A T : ClockTree (S×B) as} {base : NativeGeneratedTest A} {P : NativeGeneratedTest T}
    {star : ℕ} (h : NativeProjectionSpine base star P)
    (hA : NativeTargetStarSingleton A base.target star)
    (hT : NativeTargetStarSingleton T P.target star)
    {w : S→ℝ} (hw : ∀σ,0<w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    (aRow : ℝ) (ho : MassOrdered aRow as)
    (p : MarkedPlacement T) (hp : p∈T.markedAttach aRow)
    (hh : star<p.tree.splitIndex (p.embed P.target) p.mark)
    (R : S→S→ℝ) (C : ℕ→ℝ) :
    ∃r : MarkedPlacement A,r∈A.markedAttach aRow ∧ p.coeff=r.coeff ∧
      p.tree.splitIndex (p.embed P.target) p.mark=r.tree.splitIndex (r.embed base.target) r.mark ∧
      (∀(q : ℕ→ι→ℝ≥0) (J : (ι→ℝ)→A.cavityLeft.Assignment→S→ℝ) (x : ι→ℝ),
        nativeStarFieldTestMean w φ p.tree.cavityLeft (p.tree.cavityLeftSlot (p.embed P.target)) star q
          (fun y σ=>J y (h.restRead (p.restRestrict σ)) (p.restSpin σ)*
            nativeRestGeneratedTestValue T P R C (p.restRestrict σ)) x=
        nativeStarFieldTestMean w φ r.tree.cavityLeft (r.tree.cavityLeftSlot (r.embed base.target)) star q
          (fun y σ=>J y (r.restRestrict σ) (r.restSpin σ)*
            nativeRestGeneratedTestValue A base R C (r.restRestrict σ)*
            (nativeStarPairFactor w φ as star q (fun u v=>R u v-C star) y
              (A.cavityLeft.atSlot (r.restRestrict σ) (A.cavityLeftSlot base.target)))^h.toothCount) x) ∧
      (∀(q : ℕ→ι→ℝ≥0) (J : (ι→ℝ)→A.cavityLeft.Assignment→S→ℝ) (x : ι→ℝ),
        nativeStarFieldTestMean w φ p.tree.cavityLeft (p.tree.cavityLeftSlot (p.embed P.target)) star q
          (fun y σ=>J y (h.restRead (p.restRestrict σ)) (p.restSpin σ)*
            nativeRestGeneratedTestValue T P R C
              (nativeReplaceAtSlot T.cavityLeft (T.cavityLeftSlot P.target)
                (p.restRestrict σ) (p.restSpin σ))) x=
        nativeStarFieldTestMean w φ r.tree.cavityLeft (r.tree.cavityLeftSlot (r.embed base.target)) star q
          (fun y σ=>J y (r.restRestrict σ) (r.restSpin σ)*
            nativeRestGeneratedTestValue A base R C
              (nativeReplaceAtSlot A.cavityLeft (A.cavityLeftSlot base.target)
                (r.restRestrict σ) (r.restSpin σ))*
            (nativeStarPairFactor w φ as star q (fun u v=>R u v-C star) y (r.restSpin σ))^h.toothCount) x) := by
  obtain ⟨r,hr,hcoeff,hsplit,HO⟩:=h.observed_rest_factorization hw φ ho aRow p hp hh R C
  refine ⟨r,hr,hcoeff,hsplit,HO,?_⟩
  intro q J x
  let F:=fun u v=>R u v-C star
  let Jswap:=fun (y:ι→ℝ) (σ:A.cavityLeft.Assignment) (u:S)=>
    J y (nativeReplaceAtSlot A.cavityLeft (A.cavityLeftSlot base.target) σ u)
      (A.cavityLeft.atSlot σ (A.cavityLeftSlot base.target))
  have HX:=native_target_singleton_full_rest_star_field_exchange T P.target star hT hw φ ho
    p hp hh q (fun y σ u=>J y (h.restRead σ) u*nativeRestGeneratedTestValue T P R C
      (nativeReplaceAtSlot T.cavityLeft (T.cavityLeftSlot P.target) σ u)) x
  have Hsource : nativeStarFieldTestMean w φ p.tree.cavityLeft
      (p.tree.cavityLeftSlot (p.embed P.target)) star q
      (fun y σ=>J y (h.restRead (p.restRestrict σ)) (p.restSpin σ)*
        nativeRestGeneratedTestValue T P R C
          (nativeReplaceAtSlot T.cavityLeft (T.cavityLeftSlot P.target)
            (p.restRestrict σ) (p.restSpin σ))) x=
    nativeStarFieldTestMean w φ p.tree.cavityLeft
      (p.tree.cavityLeftSlot (p.embed P.target)) star q
      (fun y σ=>Jswap y (h.restRead (p.restRestrict σ)) (p.restSpin σ)*
        nativeRestGeneratedTestValue T P R C (p.restRestrict σ)) x := by
    rw [HX]
    apply congrArg (fun L=>nativeStarFieldTestMean w φ p.tree.cavityLeft
      (p.tree.cavityLeftSlot (p.embed P.target)) star q L x)
    funext y σ
    rw [nativeReplaceAtSlot_restore,h.restRead_replace_target]
    dsimp only [Jswap]
    rw [h.restTargetRead]
  rw [Hsource,HO q Jswap x]
  have hhA : star<r.tree.splitIndex (r.embed base.target) r.mark := by
    rw [←hsplit]
    exact hh
  have HR:=native_target_singleton_full_rest_star_field_exchange A base.target star hA hw φ ho
    r hr hhA q (fun y σ u=>Jswap y σ u*nativeRestGeneratedTestValue A base R C σ*
      (nativeStarPairFactor w φ as star q F y
        (A.cavityLeft.atSlot σ (A.cavityLeftSlot base.target)))^h.toothCount) x
  convert HR using 1
  apply congrArg (fun L=>nativeStarFieldTestMean w φ r.tree.cavityLeft
    (r.tree.cavityLeftSlot (r.embed base.target)) star q L x)
  funext y σ
  dsimp only [Jswap,F]
  rw [nativeReplaceAtSlot_restore,nativeReplaceAtSlot_self]

end OAI.SKFluctuations.Hierarchy.ClockTree
