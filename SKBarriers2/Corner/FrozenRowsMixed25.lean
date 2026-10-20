module

public import SKBarriers2.Corner.FrozenRowsNoise5
public import SKBarriers2.Corner.FrozenRowsMixedValue4

@[expose] public section

noncomputable section
open scoped Topology
open OAI.SK.Analytic
namespace SKBarriers2.Corner
variable {P X : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup X] [NormedSpace ℝ X]

structure AffineGaussianCoordinate.AgreeAt (c : AffineGaussianCoordinate P X) (p q : P) : Prop where
  logMass : c.logMass p = c.logMass q
  mean : c.mean p = c.mean q
  shift : c.shift p = c.shift q
  noise : c.noise p = c.noise q

theorem affinePotentialChain_parameter_congr (cs : List (AffineGaussianCoordinate P X))
    (F : P × X → ℝ) (p q : P)
    (hcs : ∀ c ∈ cs, c.AgreeAt p q) (hF : ∀ x, F (p,x) = F (q,x)) :
    ∀ x, affinePotentialChain cs F (p,x) = affinePotentialChain cs F (q,x) := by
  induction cs with
  | nil => exact hF
  | cons c cs ih =>
    have hc := hcs c List.mem_cons_self
    have ht := ih (fun b hb => hcs b (List.mem_cons_of_mem c hb))
    have he : (fun x => affinePotentialChain cs F (p,x)) =
        fun x => affinePotentialChain cs F (q,x) := funext ht
    intro x
    simp only [affinePotentialChain,hc.logMass,hc.mean,hc.shift,hc.noise,he]

theorem affineCoordinateAverage_parameter_congr (c : AffineGaussianCoordinate P X)
    (F G : P × X → ℝ) (p q : P) (hc : c.AgreeAt p q)
    (hF : ∀ x, F (p,x) = F (q,x)) (hG : ∀ x, G (p,x) = G (q,x)) (x : X) :
    affineCoordinateAverage c F G (p,x) = affineCoordinateAverage c F G (q,x) := by
  have hF' : (fun x => F (p,x)) = fun x => F (q,x) := funext hF
  have hG' : (fun x => G (p,x)) = fun x => G (q,x) := funext hG
  simp only [affineCoordinateAverage,hc.logMass,hc.mean,hc.shift,hc.noise,hF',hG']

theorem affineCoordinateAverage_parameter_shift (c : AffineGaussianCoordinate P X)
    (F G : P × X → ℝ) (p q : P) (u x : X)
    (hm : c.logMass q = c.logMass p) (hA : c.mean q = c.mean p)
    (hv : c.noise q = c.noise p) (hb : c.shift q = c.shift p+c.mean p u)
    (hF : ∀ y, F (q,y) = F (p,y)) (hG : ∀ y, G (q,y) = G (p,y)) :
    affineCoordinateAverage c F G (q,x) = affineCoordinateAverage c F G (p,x+u) := by
  have hF' : (fun y => F (q,y)) = fun y => F (p,y) := funext hF
  have hG' : (fun y => G (q,y)) = fun y => G (p,y) := funext hG
  simp only [affineCoordinateAverage,hm,hA,hv,hb,hF',hG']
  congr 1
  rw [map_add]
  abel

theorem affineEpsilonJetChain_parameter_congr (cs : List (AffineGaussianCoordinate P X))
    (F K : P × X → ℝ) (p q : P)
    (hcs : ∀ c ∈ cs, c.AgreeAt p q)
    (hF : ∀ x, F (p,x) = F (q,x)) (hK : ∀ x, K (p,x) = K (q,x)) :
    ∀ i x, affineEpsilonJetChain cs F K i (p,x) = affineEpsilonJetChain cs F K i (q,x) := by
  induction cs with
  | nil =>
    intro i x
    fin_cases i
    · exact hK x
    · rfl
    · rfl
  | cons c cs ih =>
    have hc := hcs c List.mem_cons_self
    have htail := fun b hb => hcs b (List.mem_cons_of_mem c hb)
    have ht := ih htail
    have hpot := affinePotentialChain_parameter_congr cs F p q htail hF
    let m := fun z : P × X => Real.exp (c.logMass z.1)
    let R := affineEpsilonJetChain cs F K
    have hbell (i : Fin 3) (x : X) :
        epsilonBellFamilies m R i (p,x) = epsilonBellFamilies m R i (q,x) := by
      fin_cases i <;> simp only [epsilonBellFamilies,Matrix.cons_val_zero',Matrix.cons_val_succ',
        m,R,ht,hc.logMass]
    have havg (i : Fin 3) (x : X) :
        affineCoordinateAverage c (affinePotentialChain cs F) (epsilonBellFamilies m R i) (p,x) =
          affineCoordinateAverage c (affinePotentialChain cs F) (epsilonBellFamilies m R i) (q,x) :=
      affineCoordinateAverage_parameter_congr c _ _ p q hc hpot (hbell i) x
    intro i x
    change epsilonCumulantFamilies m
      (fun i => affineCoordinateAverage c (affinePotentialChain cs F) (epsilonBellFamilies m R i)) i (p,x) =
      epsilonCumulantFamilies m
      (fun i => affineCoordinateAverage c (affinePotentialChain cs F) (epsilonBellFamilies m R i)) i (q,x)
    fin_cases i <;> simp only [epsilonCumulantFamilies,Matrix.cons_val_zero',Matrix.cons_val_succ',
      havg,m,hc.logMass]

section RowCoordinate
open SKOptimized.Overshoot

def AffineRowParameters.addHeadShift (p : AffineRowParameters) (i : Fin 12) (v : Vec3) :
    AffineRowParameters :=
  Function.update p i ((p i).1,((p i).2.1,((p i).2.2.1+v,(p i).2.2.2)))

theorem AffineRowParameters.addHeadShift_contDiffAt
    {r : WithTop ℕ∞} {p : ℝ → AffineRowParameters} {v : ℝ → Vec3} {k : ℝ}
    (hp : ContDiffAt ℝ r p k) (hv : ContDiffAt ℝ r v k) (i : Fin 12) :
    ContDiffAt ℝ r (fun t => (p t).addHeadShift i (v t)) k := by
  apply contDiffAt_pi.mpr
  intro j
  have hj : ContDiffAt ℝ r (fun t => p t j) k :=
    (ContinuousLinearMap.proj j : AffineRowParameters →L[ℝ] AffineRowParameter).contDiff.contDiffAt.comp k hp
  by_cases hji : j = i
  · subst j
    simp only [AffineRowParameters.addHeadShift,Function.update_self]
    exact hj.fst.prodMk (hj.snd.fst.prodMk ((hj.snd.snd.fst.add hv).prodMk hj.snd.snd.snd))
  · simpa only [AffineRowParameters.addHeadShift,Function.update_of_ne hji] using hj

theorem affineRowCoordinate_addHeadShift_agree (p : AffineRowParameters)
    (i j : Fin 12) (v : Vec3) (hij : i ≠ j) :
    (affineRowCoordinate i).AgreeAt (p.addHeadShift j v) p := by
  have H : p.addHeadShift j v i = p i := by
    simp only [AffineRowParameters.addHeadShift,Function.update_of_ne hij]
  exact ⟨congrArg Prod.fst H,congrArg (fun z : AffineRowParameter => z.2.1) H,
    congrArg (fun z : AffineRowParameter => z.2.2.1) H,
    congrArg (fun z : AffineRowParameter => z.2.2.2) H⟩

theorem AffineGaussianCoordinate.AgreeAt.centeredRescale
    {c : AffineGaussianCoordinate P Vec3} {p q : P} (H : c.AgreeAt p q)
    (ρ : ℝ) (center : Vec3) (a : ℝ) :
    (c.centeredRescale ρ center).AgreeAt (a,p) (a,q) := by
  refine ⟨H.logMass,H.mean,?_,?_⟩
  · change ρ⁻¹ • (c.mean p center+c.shift p-a • center) =
      ρ⁻¹ • (c.mean q center+c.shift q-a • center)
    rw [H.mean,H.shift]
  · change ρ⁻¹ • c.noise p = ρ⁻¹ • c.noise q
    rw [H.noise]

theorem affineRowCoordinate_centered_addHeadShift (p : AffineRowParameters)
    (i : Fin 12) (v center : Vec3) (ρ a : ℝ) :
    let c := (affineRowCoordinate i).centeredRescale ρ center
    c.logMass (a,p.addHeadShift i v) = c.logMass (a,p) ∧
      c.mean (a,p.addHeadShift i v) = c.mean (a,p) ∧
      c.noise (a,p.addHeadShift i v) = c.noise (a,p) ∧
      c.shift (a,p.addHeadShift i v) = c.shift (a,p)+ρ⁻¹ • v := by
  dsimp only
  have H : p.addHeadShift i v i = ((p i).1,((p i).2.1,((p i).2.2.1+v,(p i).2.2.2))) := by
    simp only [AffineRowParameters.addHeadShift,Function.update_self]
  change (p.addHeadShift i v i).1 = (p i).1 ∧
    (p.addHeadShift i v i).2.1 = (p i).2.1 ∧
    ρ⁻¹ • (p.addHeadShift i v i).2.2.2 = ρ⁻¹ • (p i).2.2.2 ∧
    ρ⁻¹ • ((p.addHeadShift i v i).2.1 center+(p.addHeadShift i v i).2.2.1-a • center) =
      ρ⁻¹ • ((p i).2.1 center+(p i).2.2.1-a • center)+ρ⁻¹ • v
  rw [H]
  refine ⟨rfl,rfl,rfl,?_⟩
  module

theorem affineRowCoordinates_mem_label {n : ℕ} {hn : n ≤ 12}
    {c : AffineGaussianCoordinate AffineRowParameters Vec3}
    (hc : c ∈ affineRowCoordinates n hn) :
    ∃ i : Fin 12, i.val < n ∧ c = affineRowCoordinate i := by
  induction n with
  | zero => simp only [affineRowCoordinates,List.not_mem_nil] at hc
  | succ n ih =>
    change c ∈ affineRowCoordinate ⟨n,by omega⟩ :: affineRowCoordinates n (by omega) at hc
    rcases List.mem_cons.mp hc with hhead | htail
    · exact ⟨⟨n,by omega⟩,by simp,hhead⟩
    · obtain ⟨i,hi,he⟩ := ih htail
      exact ⟨i,by omega,he⟩

theorem affineRowCoordinates_drop_eq_lower (n : ℕ) (hn : n ≤ 12) (m : ℕ) :
    (affineRowCoordinates n hn).drop m =
      affineRowCoordinates (n-m) ((Nat.sub_le n m).trans hn) := by
  induction n generalizing m with
  | zero => simp only [affineRowCoordinates,List.drop_nil,Nat.zero_sub]
  | succ n ih =>
    cases m with
    | zero => rfl
    | succ m =>
      change (affineRowCoordinates n (by omega)).drop m =
        affineRowCoordinates ((n+1)-(m+1)) ((Nat.sub_le (n+1) (m+1)).trans hn)
      simpa only [Nat.add_sub_add_right] using ih (by omega) m

theorem affineRowCoordinates_centered_addHeadShift_agree
    (p : AffineRowParameters) (i : Fin 12) (v center : Vec3) (ρ a : ℝ)
    {n : ℕ} (hn : n ≤ 12) (hni : n ≤ i.val) :
    ∀ c ∈ (affineRowCoordinates n hn).map (fun c => c.centeredRescale ρ center),
      c.AgreeAt (a,p.addHeadShift i v) (a,p) := by
  intro c hc
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hc
  obtain ⟨j,hj,rfl⟩ := affineRowCoordinates_mem_label hb
  have hji : j ≠ i := by intro he; subst j; omega
  exact (affineRowCoordinate_addHeadShift_agree p j i v hji).centeredRescale ρ center a

end RowCoordinate

end SKBarriers2.Corner
