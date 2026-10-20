module

public import SKBarriers2.Corner.PathEnergyPrefix2

@[expose] public section

noncomputable section
open scoped BigOperators Topology
open Set Filter MeasureTheory ProbabilityTheory OAI.SK.Analytic
namespace SKBarriers2.ParamChain
open StepCalculus
local notation "E" => (Fin 3 → ℝ)
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem exponentialPrefixSource_twoJet {F G : P × E → ℝ}
    (hF : ParamRegular F) (hG : ParamSmooth G)
    (z : (P →L[ℝ] ℝ) × (P →L[ℝ] E))
    (ps : List ((P →L[ℝ] ℝ) × (P →L[ℝ] E)))
    (hJ : ParamSmooth (fun u : P × E => pathGeneratorSum (fun y => F (u.1,y))
      (fun y => G (u.1,y)) (exponentialSteps ps u.1) u.2))
    (hK : ParamSmooth (fun u : P × E => pathGenerator (Real.exp (z.1 u.1))
      (z.2 u.1) (fun y => F (u.1,y)) (fun y => G (u.1,y)) u.2))
    {p : ℝ → P} {k B A C D CJ DJ : ℝ} (hp : ContDiffAt ℝ 2 p k)
    (hbase : QPotential 4 B (fun y => exponentialChain ps F (p k,y)))
    (hbase₁ : QBoundedJets 3 A (fun y => deriv (fun t => exponentialChain ps F (p t,y)) k))
    (hg : QBoundedJets 3 C (fun y => G (p k,y)))
    (hg₁ : QBoundedJets 1 D (fun y => deriv (fun t => G (p t,y)) k))
    (hj : QBoundedJets 3 CJ (fun y => pathGeneratorSum (fun x => F (p k,x))
      (fun x => G (p k,x)) (exponentialSteps ps (p k)) y))
    (hj₁ : QBoundedJets 1 DJ (fun y => deriv (fun t => pathGeneratorSum (fun x => F (p t,x))
      (fun x => G (p t,x)) (exponentialSteps ps (p t)) y) k))
    (hm : Real.exp (z.1 (p k)) ≤ 1) {K₁ K₂ : E → ℝ}
    (hK₁ : ∀ x, deriv (fun t => pathGenerator (Real.exp (z.1 (p t))) (z.2 (p t))
      (fun y => F (p t,y)) (fun y => G (p t,y)) x) k = K₁ x)
    (hK₂ : ∀ x, deriv (deriv (fun t => pathGenerator (Real.exp (z.1 (p t))) (z.2 (p t))
      (fun y => F (p t,y)) (fun y => G (p t,y)) x)) k = K₂ x) (x : E) :
    let H := fun t y => exponentialChain ps F (p t,y)
    let H₁ := fun y => deriv (fun t => H t y) k
    let H₂ := fun y => deriv (deriv (fun t => H t y)) k
    let g := fun t y => G (p t,y)
    let a := fun y => deriv (fun t => g t y) k
    let q := fun y => deriv (deriv (fun t => g t y)) k
    let J := fun t y => pathGeneratorSum (fun w => F (p t,w))
      (g t) (exponentialSteps ps (p t)) y
    let J₁ := fun y => deriv (fun t => J t y) k
    let J₂ := fun y => deriv (deriv (fun t => J t y)) k
    let m := fun t => Real.exp (z.1 (p t))
    let v := fun t => z.2 (p t)
    let S := fun t => tiltedPathTaylorDefect (exponentialSteps (z::ps) (p t))
      (fun y => F (p t,y)) (g t) x-
      tiltedAverage (m t) (v t) (H t)
        (tiltedPathTaylorDefect (exponentialSteps ps (p t)) (fun y => F (p t,y)) (g t)) x
    ContDiffAt ℝ 2 S k ∧
    deriv S k = firstTiltedAverageSource (m k) (v k) (H k) H₁ (g k) a
      (deriv m k) (deriv v k) x-a x-K₁ x+
      (firstTiltedAverageSource (m k) (v k) (H k) H₁ (J k) J₁
        (deriv m k) (deriv v k) x-J₁ x) ∧
    deriv (deriv S) k = secondMovingAverageSource (m k) (deriv m k)
      (deriv (deriv m) k) (v k) (deriv v k) (deriv (deriv v) k)
      (H k) H₁ H₂ (g k) a q x-q x-K₂ x+
      (secondMovingAverageSource (m k) (deriv m k) (deriv (deriv m) k)
        (v k) (deriv v k) (deriv (deriv v) k) (H k) H₁ H₂ (J k) J₁ J₂ x-J₂ x) := by
  dsimp only
  let J := fun u : P × E => pathGeneratorSum (fun y => F (u.1,y))
    (fun y => G (u.1,y)) (exponentialSteps ps u.1) u.2
  let K := fun u : P × E => pathGenerator (Real.exp (z.1 u.1)) (z.2 u.1)
    (fun y => F (u.1,y)) (fun y => G (u.1,y)) u.2
  let H := exponentialChain ps F
  let T := fun t => tiltedAverage (Real.exp (z.1 (p t))) (z.2 (p t))
    (fun y => H (p t,y)) (fun y => G (p t,y)) x
  let U := fun t => tiltedAverage (Real.exp (z.1 (p t))) (z.2 (p t))
    (fun y => H (p t,y)) (fun y => J (p t,y)) x
  have HT := chartAverage_twoJet (regular_exponentialChain ps hF) hG z.1 z.2
    hp hbase hbase₁ hg hg₁ hm x
  have HU := chartAverage_twoJet (regular_exponentialChain ps hF) hJ z.1 z.2
    hp hbase hbase₁ hj hj₁ hm x
  dsimp only at HT HU
  have hcG : ContDiffAt ℝ 2 (fun t => G (p t,x)) k :=
    (hG.1.contDiffAt (x := (p k,x))).comp (f := fun t : ℝ => (p t,x)) k
      (hp.prodMk (contDiffAt_const (c := x)))
  have hcJ : ContDiffAt ℝ 2 (fun t => J (p t,x)) k :=
    (hJ.1.contDiffAt (x := (p k,x))).comp (f := fun t : ℝ => (p t,x)) k
      (hp.prodMk (contDiffAt_const (c := x)))
  have hcK : ContDiffAt ℝ 2 (fun t => K (p t,x)) k :=
    (hK.1.contDiffAt (x := (p k,x))).comp (f := fun t : ℝ => (p t,x)) k
      (hp.prodMk (contDiffAt_const (c := x)))
  have heq : (fun t => tiltedPathTaylorDefect (exponentialSteps (z::ps) (p t))
      (fun y => F (p t,y)) (fun y => G (p t,y)) x-
      tiltedAverage (Real.exp (z.1 (p t))) (z.2 (p t)) (fun y => H (p t,y))
        (tiltedPathTaylorDefect (exponentialSteps ps (p t))
          (fun y => F (p t,y)) (fun y => G (p t,y))) x) =
      fun t => (T t-G (p t,x)-K (p t,x))+(U t-J (p t,x)) := by
    funext t
    exact exponentialPrefixSource_eq hF hG z ps hJ (p t) x
  rw [heq]
  have hcT : ContDiffAt ℝ 2 T k := HT.1
  have hcU : ContDiffAt ℝ 2 U k := HU.1
  refine ⟨((hcT.sub hcG).sub hcK).add (hcU.sub hcJ),?_,?_⟩
  · rw [deriv_fun_add (((hcT.sub hcG).sub hcK).differentiableAt (by norm_num))
      ((hcU.sub hcJ).differentiableAt (by norm_num)),
      deriv_fun_sub ((hcT.sub hcG).differentiableAt (by norm_num)) (hcK.differentiableAt (by norm_num)),
      deriv_fun_sub (hcT.differentiableAt (by norm_num)) (hcG.differentiableAt (by norm_num)),
      deriv_fun_sub (hcU.differentiableAt (by norm_num)) (hcJ.differentiableAt (by norm_num))]
    rw [HT.2.1,HU.2.1,hK₁ x]
  · have HH := iteratedDeriv_fun_add ((hcT.sub hcG).sub hcK) (hcU.sub hcJ)
    rw [iteratedDeriv_fun_sub (hcT.sub hcG) hcK,iteratedDeriv_fun_sub hcT hcG,
      iteratedDeriv_fun_sub hcU hcJ] at HH
    simp only [iteratedDeriv_succ,iteratedDeriv_zero] at HH
    rw [HH,HT.2.2,HU.2.2,hK₂ x]

end SKBarriers2.ParamChain
