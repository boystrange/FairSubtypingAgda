open import Data.Nat
open import Data.Vec
open import Data.Fin
open import Data.Product
open import Data.Unit
open import Data.Empty
open import Relation.Nullary
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
open import Size
open import Codata.Thunk
open import Relation.Binary.PropositionalEquality as ≡


open import is-lib.SInfSys as IS
open import Examples.Lambda.Lambda

module Examples.Lambda.SmallStep where

  U : Set
  U = Term 0 × Term 0

  data SmallStepRN : Set where
    β L-APP R-APP : SmallStepRN

  β-r : FinMetaRule U
  β-r .Ctx = Term 1 × Value
  β-r .comp (t , v) =
    [] ,
    -------------------------
    (app (lambda t) (term v) , subst-0 t (term v))

  l-app-r : FinMetaRule U
  l-app-r .Ctx = Term 0 × Term 0 × Term 0
  l-app-r .comp (t1 , t1' , t2) =
    (t1 , t1') ∷ [] ,
    -------------------------
    ((app t1 t2) , (app t1' t2))

  r-app-r : FinMetaRule U
  r-app-r .Ctx = Value × Term 0 × Term 0
  r-app-r .comp (v , t2 , t2') =
    (t2 , t2') ∷ [] ,
    -------------------------
    ((app (term v) t2) , app (term v) t2')

  SmallStepIS : IS U
  SmallStepIS .Names = SmallStepRN
  SmallStepIS .rules β = from β-r
  SmallStepIS .rules L-APP = from l-app-r
  SmallStepIS .rules R-APP = from r-app-r

  _⇒_ : Term 0 → Term 0 → Set
  t ⇒ t' = Ind⟦ SmallStepIS ⟧ (t , t')

  _⇒*_ : Term 0 → Term 0 → Set
  _⇒*_ = Star _⇒_

  _ConvergesSS : Term 0 → Set
  t ConvergesSS = Σ[ v ∈ Value ] (t ⇒* term v)

  data ⇒∞ : Term 0 → Size → Set where
    step : ∀{t t' i} → t ⇒ t' → Thunk (⇒∞ t') i → ⇒∞ t i

  {- Properties -}
  inj-l-app : ∀{t1 t1'} t2 → t1 ⇒* t1' → (app t1 t2) ⇒* (app t1' t2)
  inj-l-app _ ε = ε
  inj-l-app {t1} t2 (fold x ◅ red) =
    apply-ind L-APP _ (λ {zero → IS.fold x}) ◅ inj-l-app t2 red
  
  inj-r-app : ∀{t2 t2'} v → t2 ⇒* t2' → (app (term v) t2) ⇒* (app (term v) t2')
  inj-r-app _ ε = ε
  inj-r-app {t2} v (fold x ◅ red) =
    apply-ind R-APP _ (λ {zero → IS.fold x}) ◅ inj-r-app v red
    
  val-not-reduce⇒ : ∀{v e'} → ¬ (term v ⇒ e')
  val-not-reduce⇒ {lambda _} (fold (β , c , () , pr))
  val-not-reduce⇒ {lambda _} (fold (L-APP , c , () , pr))
  val-not-reduce⇒ {lambda _} (fold (R-APP , c , () , pr))

  ⇒-deterministic : ∀{e e' e''} → e ⇒ e' → e ⇒ e'' → e' ≡ e''
  ⇒-deterministic (fold (β , (_ , lambda _) , refl , _)) (fold (β , (_ , lambda _) , refl , _)) = refl
  ⇒-deterministic (fold (β , (_ , lambda _) , refl , _)) (fold (L-APP , _ , refl , pr)) = ⊥-elim (val-not-reduce⇒ (pr zero))
  ⇒-deterministic (fold (β , (_ , lambda _) , refl , _)) (fold (R-APP , (lambda _ , _) , refl , pr)) = ⊥-elim (val-not-reduce⇒ (pr zero))
  ⇒-deterministic (fold (L-APP , _ , refl , pr)) (fold (β , _ , refl , _)) = ⊥-elim (val-not-reduce⇒ (pr zero))
  ⇒-deterministic (fold (L-APP , _ , refl , pr)) (fold (L-APP , _ , refl , pr')) = cong (λ x → app x _) (⇒-deterministic (pr zero) (pr' zero))
  ⇒-deterministic (fold (L-APP , _ , refl , pr)) (fold (R-APP , _ , refl , _)) = ⊥-elim (val-not-reduce⇒ (pr zero))
  ⇒-deterministic (fold (R-APP , (lambda _ , _) , refl , pr)) (fold (β , _ , refl , _)) = ⊥-elim (val-not-reduce⇒ (pr zero))
  ⇒-deterministic (fold (R-APP , (lambda _ , _) , refl , _)) (fold (L-APP , _ , refl , pr)) = ⊥-elim (val-not-reduce⇒ (pr zero))
  ⇒-deterministic (fold (R-APP , (lambda _ , _) , refl , pr)) (fold (R-APP , (lambda _ , _) , refl , pr')) = cong (λ x → app _ x) (⇒-deterministic (pr zero) (pr' zero))

  ⇒*-preserves-⇒∞ : ∀{e e'} → (∀{i} → ⇒∞ e i) → e ⇒* e' → (∀{i} → ⇒∞ e' i)
  ⇒*-preserves-⇒∞ ss ε = ss
  ⇒*-preserves-⇒∞ ss (x ◅ red-e) with ss
  ⇒*-preserves-⇒∞ ss (x ◅ red-e) | step x₁ x₂ =
    let e'-eq = ⇒-deterministic x₁ x in
    ⇒*-preserves-⇒∞ (≡.subst (λ x → (∀{i} → ⇒∞ x i)) e'-eq (x₂ .force)) red-e

  app-subst-⇒∞ : ∀{e v} → (∀{i} → ⇒∞ (app (lambda e) (term v)) i) → (∀{i} → ⇒∞ (subst-0 e (term v)) i)
  app-subst-⇒∞ ss with ss
  app-subst-⇒∞ {_} {lambda _} ss | step (fold (β , (_ , lambda _) , refl , _)) rec = rec .force
  app-subst-⇒∞ {_} {lambda _} ss | step (fold (L-APP , _ , refl , pr)) _ = ⊥-elim (val-not-reduce⇒ (pr zero))
  app-subst-⇒∞ {_} {lambda _} ss | step (fold (R-APP , (lambda _ , _) , refl , pr)) rec = ⊥-elim (val-not-reduce⇒ (pr zero))

  app-subst-⇒∞₁ : ∀{e1 e1' e2 v} → e1 ⇒* lambda e1' → e2 ⇒* term v → (∀{i} → ⇒∞ (app e1 e2) i) → (∀{i} → ⇒∞ (subst-0 e1' (term v)) i)
  app-subst-⇒∞₁ red-e1 red-e2 ss =
    let red-left = ⇒*-preserves-⇒∞ ss (inj-l-app _ red-e1) in
    let red-right = ⇒*-preserves-⇒∞ red-left (inj-r-app _ red-e2) in
    app-subst-⇒∞ red-right

  not-conv-next : ∀{e e'} → ¬ (Σ[ v ∈ Value ] e ⇒* term v) → e ⇒ e' → ¬ (Σ[ v ∈ Value ] e' ⇒* term v)
  not-conv-next {e} {e'} n ss-e (v , ss-e') = ⊥-elim (n (v , ss-e ◅ ss-e'))
  
  div-app-l-not-conv : ∀{e1 e2} → (∀{i} → ⇒∞ (app e1 e2) i) → ¬ (e1 ConvergesSS) → (∀{i} → ⇒∞ e1 i)
  div-app-l-not-conv ss n-conv with ss
  div-app-l-not-conv ss n-conv | step (fold (β , _ , refl , _)) _ = ⊥-elim (n-conv (_ , ε))
  div-app-l-not-conv ss n-conv | step (fold (L-APP , _ , refl , pr)) x₁ =
    step (pr zero) λ where .force → div-app-l-not-conv (x₁ .force) (not-conv-next n-conv (pr zero))
  div-app-l-not-conv ss n-conv | step (fold (R-APP , _ , refl , _)) _ = ⊥-elim (n-conv (_ , ε))

  div-app-r-not-conv : ∀{e1 e2 v} → (∀{i} → ⇒∞ (app e1 e2) i) → e1 ⇒* term v → ¬ (e2 ConvergesSS) → (∀{i} → ⇒∞ e2 i)
  div-app-r-not-conv ss red-e1 ¬e2-conv with ss
  div-app-r-not-conv ss red-e1 ¬e2-conv | step (fold (β , _ , refl , _)) _ = ⊥-elim (¬e2-conv (_ , ε))
  div-app-r-not-conv ss ε ¬e2-conv | step (fold (L-APP , _ , refl , pr)) _ = ⊥-elim (val-not-reduce⇒ (pr zero))
  div-app-r-not-conv ss (x ◅ red-e1) ¬e2-conv | step (fold (L-APP , _ , refl , pr)) x₁ =
    div-app-r-not-conv (λ {i} → ≡.subst (λ x → ⇒∞ (app x _) i) (⇒-deterministic (pr zero) x) (x₁ .force)) red-e1 ¬e2-conv
  div-app-r-not-conv ss red-e1 ¬e2-conv | step (fold (R-APP , (lambda _ , _) , refl , pr)) x₁ =
    step (pr zero) λ where .force → div-app-r-not-conv (x₁ .force) red-e1 (not-conv-next ¬e2-conv (pr zero))

  ⇒∞-reduce-⇒ : ∀{e} → (∀{i} → ⇒∞ e i) → Σ[ e' ∈ Term 0 ] e ⇒ e' × (∀{i} → ⇒∞ e' i)
  ⇒∞-reduce-⇒ ss with ss
  ⇒∞-reduce-⇒ ss | step s s' = _ , s , s' .force
  
  val-not-⇒∞ : ∀{e v} → e ⇒ term v → ¬ (∀{i} → ⇒∞ e i)
  val-not-⇒∞ {e} {v} ss ss' with ss'
  val-not-⇒∞ {.(app (lambda (var zero)) (lambda _))} {lambda _} (fold (β , (var zero , lambda _) , refl , _)) ss' | step (fold (β , (.(var zero) , lambda _) , refl , _)) rec =
    ⊥-elim (val-not-reduce⇒ (proj₁ (proj₂ (⇒∞-reduce-⇒ (rec .force)))))
  val-not-⇒∞ {.(app (lambda (lambda _)) (lambda _))} {lambda _} (fold (β , (lambda _ , lambda _) , refl , _)) ss' | step (fold (β , (.(lambda _) , lambda _) , refl , _)) rec =
    ⊥-elim (val-not-reduce⇒ (proj₁ (proj₂ (⇒∞-reduce-⇒ (rec .force)))))
  val-not-⇒∞ {.(app (lambda e1) e2)} {lambda _} (fold (β , (_ , lambda _) , _)) ss' | step (fold (L-APP , (lambda e1 , e1' , e2) , refl , pr)) rec =
    ⊥-elim (val-not-reduce⇒ (pr zero))
  val-not-⇒∞ {.(app e1 e2)} {lambda _} (fold (L-APP , _ , () , _)) ss' | step (fold (L-APP , (e1 , e1' , e2) , refl , _)) _
  val-not-⇒∞ {.(app e1 e2)} {lambda _} (fold (R-APP , (lambda _ , _) , () , _)) ss' | step (fold (L-APP , (e1 , e1' , e2) , refl , pr)) _
  val-not-⇒∞ {.(app (lambda _) (lambda e2))} {lambda _} (fold (β , (_ , lambda _) , _)) ss' | step (fold (R-APP , (lambda _ , lambda e2 , e2') , refl , pr)) rec =
    ⊥-elim (val-not-reduce⇒ (pr zero))