open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Data.Nat
open import Data.Vec
open import Data.Fin
open import Data.Product
open import Data.Sum
open import Data.Bool
open import Data.Unit
open import Data.Empty
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
open import Size
open import Codata.Thunk
open import Axiom.ExcludedMiddle
open import Level renaming (zero to ∅ ; suc to ++)

open import is-lib.SInfSys as IS
open import Examples.Lambda.Lambda
open import Examples.Lambda.BigStep renaming (U to BigStepU)
open import Examples.Lambda.SmallStep

module Examples.Lambda.Proofs where

  Spec : BigStepU → Set
  Spec (e , res x) = e ⇒* term x
  Spec (e , div) = ∀{i} → ⇒∞ e i

  {- Soundness -}
  Spec-val : BigStepU → Set
  Spec-val (e , v) = ∀{v'} → v ≡ res v' → Spec (e , v)

  Spec-closed : ISClosed (BigStepIS ∪ BigStepCOIS) Spec-val
  Spec-closed (inj₁ VAL) _ _ refl = ε
  Spec-closed (inj₁ APP) _ prem refl =
    let s-e1 = prem zero refl in
    let s-e2 = prem (suc zero) refl in
    let s-subst = prem (suc (suc zero)) refl in
    let subst = IS.fold (β , _ , refl , λ ()) in
    inj-l-app _ (prem zero refl) ◅◅ inj-r-app _ (prem (suc zero) refl) ◅◅ subst ◅ prem (suc (suc zero)) refl
  Spec-closed (inj₂ COA) s_ _ ()

  ⇓ᵢ-to-⇒* : ∀{e v} → e ⇓ᵢ v → Spec-val (e , v)
  ⇓ᵢ-to-⇒* = ind[ BigStepIS ∪ BigStepCOIS ] Spec-val Spec-closed

  bs-sound-v : ∀{e v} → (∀{i} → (e ⇓ (res v)) i) → e ⇒* (term v)
  bs-sound-v r = ⇓ᵢ-to-⇒* (sfcoind-to-ind r) refl

  subject-red-⇓ : ∀{e e' v} → (∀{i} → (e ⇓ v) i) → e ⇒ e' → (∀{i} → (e' ⇓ v) i)
  subject-red-⇓ bs (fold (β , (e , v) , eq , _)) with bs
  subject-red-⇓ bs (fold (β , (e , v) , () , _)) | sfold (VAL , (lambda x , _) , refl , prem)
  subject-red-⇓ bs (fold (β , (e , lambda x) , refl , _)) | sfold (APP , ((.(lambda e) , _ , .(lambda x) , v , _) , _) , refl , prem)
    with val-⇓-≡ (prem zero .force) | val-⇓-≡ (prem (suc zero) .force)
  subject-red-⇓ bs (fold (β , (e , lambda x) , refl , _)) | sfold (APP , ((.(lambda e) , .e , .(lambda x) , .(lambda x) , _) , _) , refl , prem) | refl | refl = prem (suc (suc zero)) .force
  subject-red-⇓ bs (fold (β , (e , v) , refl , _)) | sfold (L-DIV , _ , refl , prem) = ⊥-elim (val-not-reduce⇓ (prem zero .force))
  subject-red-⇓ bs (fold (β , (e , v) , refl , _)) | sfold (R-DIV , _ , refl , prem) = ⊥-elim (val-not-reduce⇓ (prem (suc zero) .force))
  subject-red-⇓ bs (fold (L-APP , c , eq , _)) with bs
  subject-red-⇓ bs (fold (L-APP , _ , () , _)) | sfold (VAL , (lambda _ , _) , refl , _)
  subject-red-⇓ bs (fold (L-APP , (e1 , e1' , e2) , refl , pr)) | sfold (APP , ((.e1 , e1'' , .e2 , lambda _ , _) , ind) , refl , prem) =
    let rec = subject-red-⇓ (prem zero .force) (pr zero) in
    let prems = λ{zero → rec ; (suc zero) → prem (suc zero) .force ; (suc (suc zero)) → prem (suc (suc zero)) .force} in
    apply-sfcoind APP _ prems
  subject-red-⇓ bs (fold (L-APP , (e1 , e1' , e2) , refl , pr)) | sfold (L-DIV , ((.e1 , .e2) , ind) , refl , prem) =
    let rec = subject-red-⇓ (prem zero .force) (pr zero) in
    apply-sfcoind L-DIV _ λ{zero → rec}
  subject-red-⇓ bs (fold (L-APP , (e1 , e1' , e2) , refl , pr)) | sfold (R-DIV , ((.e1 , .e2 , lambda v) , ind) , refl , prem) =
    let rec = subject-red-⇓ (prem zero .force) (pr zero) in
    let prems = λ{zero → rec ; (suc zero) → prem (suc zero) .force} in
    apply-sfcoind R-DIV _ prems
  subject-red-⇓ bs (fold (R-APP , (lambda _ , e2 , e2') , eq , pr)) with bs
  subject-red-⇓ bs (fold (R-APP , (lambda _ , _ , _) , refl , _)) | sfold (VAL , (lambda _ , _) , () , _)
  subject-red-⇓ bs (fold (R-APP , (lambda e1 , e2 , e2') , refl , pr)) | sfold (APP , ((.(lambda _) , e1' , .e2 , lambda _ , _) , ind) , refl , prem)
    with val-⇓-≡ (prem zero .force)
  subject-red-⇓ bs (fold (R-APP , (lambda e1 , e2 , e2') , refl , pr)) | sfold (APP , ((.(lambda e1) , .e1 , .e2 , lambda _ , _) , ind) , refl , prem) | refl =
    let rec = subject-red-⇓ (prem (suc zero) .force) (pr zero) in
    let prems = λ{zero → prem zero .force ; (suc zero) → rec ; (suc (suc zero)) → prem (suc (suc zero)) .force} in
    apply-sfcoind APP _ prems
  subject-red-⇓ bs (fold (R-APP , (lambda _ , e2 , e2') , refl , _)) | sfold (L-DIV , ((.(lambda _) , .e2) , _) , refl , prem) = ⊥-elim (val-not-reduce⇓ (prem zero .force))
  subject-red-⇓ bs (fold (R-APP , (lambda e , e2 , e2') , refl , pr)) | sfold (R-DIV , ((.(lambda e) , .e2 , v) , ind) , refl , prem) with val-⇓-≡ (prem zero .force)
  subject-red-⇓ bs (fold (R-APP , (lambda e , e2 , e2') , refl , pr)) | sfold (R-DIV , ((.(lambda e) , .e2 , .(lambda e)) , ind) , refl , prem) | refl =
    let rec = subject-red-⇓ (prem (suc zero) .force) (pr zero) in
    let prems = λ{zero → prem zero .force ; (suc zero) → rec} in
    apply-sfcoind R-DIV _ prems

  progress : ∀{e} →(∀{i} → (e ⇓ div) i) → Σ[ e' ∈ Term 0 ] (e ⇒ e')
  progress {e} bs with bs
  progress  bs | sfold (APP , _ , refl , prem) with bs-sound-v (prem zero .force)
  progress  bs | sfold (APP , ((_ , e1' , _ , _ , .div) , _) , refl , prem) | ε with bs-sound-v (prem (suc zero) .force)
  progress  bs | sfold (APP , ((.(lambda e1') , e1' , _ , v , .div) , _) , refl , prem) | ε | ε =
    _ , apply-ind β _ λ ()
  progress  bs | sfold (APP , ((.(lambda e1') , e1' , e2 , _ , .div) , _) , refl , prem) | ε | x ◅ _ =
    app (lambda e1') _ , apply-ind R-APP _ λ{zero → x}
  progress  bs | sfold (APP , ((e1 , _ , e2 , _ , .div) , _) , refl , prem) | x ◅ _ =
    app _ e2 , apply-ind L-APP _ λ{zero → x}
  progress  bs | sfold (L-DIV , ((e1 , e2) , _) , refl , prem) =
    let e1' , e1⇒e1' = progress (prem zero .force) in
    app e1' e2 , apply-ind L-APP _ λ{zero → e1⇒e1'}
  progress  bs | sfold (R-DIV , ((e1 , e2 , v) , _) , refl , prem) with bs-sound-v (prem zero .force)
  progress  bs | sfold (R-DIV , ((.(term _) , e2 , (lambda e)) , _) , refl , prem) | ε =
    let e2' , e2⇒e2' = progress (prem (suc zero) .force) in
    app (lambda e) e2' , apply-ind R-APP _ λ{zero → e2⇒e2'}
  progress  bs | sfold (R-DIV , ((e1 , e2 , (lambda e)) , _) , refl , prem) | x ◅ _ =
    app _ e2 , apply-ind L-APP _ λ{zero → x}

  bs-sound-∞ : ∀{e} → (∀{i} → (e ⇓ div) i) → (∀{i} → ⇒∞ e i)
  bs-sound-∞ bs with progress bs
  ... | e' , ss = step ss λ where .force → bs-sound-∞ (subject-red-⇓ bs ss)

  bs-sound : ∀{e v} → (∀{i} → (e ⇓ v) i) → Spec (e , v)
  bs-sound {_} {res _} = bs-sound-v
  bs-sound {_} {div} = bs-sound-∞


  {- Completeness -}
  inv-app : ∀{e1 e2 v} → (app e1 e2) ⇓ᵢ (res v) →
    Σ[ e1' ∈ Term 1 ] Σ[ e2' ∈ Value ]
      (e1 ⇓ᵢ res (lambda e1')) ×
      (e2 ⇓ᵢ (res e2')) ×
      (subst-0 e1' (term e2') ⇓ᵢ res v)
  -- Using consistency of inductive interpretation
  inv-app bs with ind-postfix bs
  inv-app bs | inj₁ VAL , lambda _ , () , _
  inv-app bs | inj₁ APP , _ , refl , pr = _ , _ , pr zero , pr (suc zero) , pr (suc (suc zero))
  inv-app bs | inj₂ COA , _ , () , _

  subject-exp : ∀{e e' v} → e ⇒ e' → e' ⇓ᵢ v → e ⇓ᵢ v
  subject-exp {.(app (lambda e1) (term v))} {_} {v'} (fold (β , (e1 , v) , refl , _)) bs =
    let prem-e1 = IS.fold (inj₁ VAL , lambda e1 , refl , λ ()) in
    let prem-e2 = IS.fold (inj₁ VAL , v , refl , λ ()) in
    let prems = λ{zero → prem-e1 ; (suc zero) → prem-e2 ; (suc (suc zero)) → bs} in
    apply-ind (inj₁ APP) _ prems
  subject-exp {.(app e1 e2)} {.(app e1' e2)} {res x} (fold (L-APP , (e1 , e1' , e2) , refl , pr)) bs =
    let e1'' , e2' , bs-e1' , bs-e2 , bs-subst = inv-app bs in
    let prems = λ{zero → subject-exp (pr zero) bs-e1' ; (suc zero) → bs-e2 ; (suc (suc zero)) → bs-subst} in
    apply-ind (inj₁ APP) _ prems
  subject-exp {.(app e1 e2)} {.(app e1' e2)} {div} (fold (L-APP , (e1 , e1' , e2) , refl , pr)) bs =
    apply-ind (inj₂ COA) _ λ ()
  subject-exp {.(app (term v) e2)} {.(app (term v) e2')} {res x} (fold (R-APP , (v , e2 , e2') , refl , pr)) bs =
    let e1' , e2'' , bs-e1 , bs-e2' , bs-subst = inv-app bs in
    let prems = λ{zero → bs-e1 ; (suc zero) → subject-exp (pr zero) bs-e2' ; (suc (suc zero)) → bs-subst} in
    apply-ind (inj₁ APP) _ prems
  subject-exp {.(app (term v) e2)} {.(app (term v) e2')} {div} (fold (R-APP , (v , e2 , e2') , refl , _)) bs =
    apply-ind (inj₂ COA) _ λ ()

  bounded-v : ∀{e v} → e ⇒* term v → e ⇓ᵢ res v
  bounded-v ε = apply-ind (inj₁ VAL) _ λ ()
  bounded-v (x ◅ ss) = subject-exp x (bounded-v ss)

  bounded-∞ : ∀{e} → (∀{i} → ⇒∞ e i) → e ⇓ᵢ div
  bounded-∞ {e} ss = apply-ind (inj₂ COA) _ λ ()
  
  bounded : ∀{e v} → Spec (e , v) → e ⇓ᵢ v
  bounded {_} {res _} = bounded-v
  bounded {_} {div} = bounded-∞

  get-prem-cons : ∀{e1 e2 v} → app e1 e2 ⇒* (term v) →
    Σ[ e1' ∈ Term 1 ] Σ[ e2' ∈ Value ]
      (e1 ⇒* lambda e1') ×
      (e2 ⇒* term e2') ×
      (subst-0 e1' (term e2') ⇒* (term v))
  get-prem-cons {.(lambda e1)} {.(term v)} {lambda _} (fold (β , (e1 , v) , refl , _) ◅ ss) =
    e1 , v , ε , ε , ss
  get-prem-cons {.e1} {.e2} {lambda _} (fold (L-APP , (e1 , e1' , e2) , refl , pr) ◅ ss) =
    let e1'' , e2' , rec-e1' , rec-e2 , rec-subst = get-prem-cons ss in
    e1'' , e2' , pr zero ◅ rec-e1' , rec-e2 , rec-subst
  get-prem-cons {.(term v)} {.e2} {lambda _} (fold (R-APP , (v , e2 , e2') , refl , pr) ◅ ss) =
    let e1' , e2'' , rec-e1 , rec-e2' , rec-subst = get-prem-cons ss in
    e1' , e2'' , rec-e1 , pr zero ◅ rec-e2' , rec-subst

  consistent-v : ∀{e v} → e ⇒* term v → IS.ISF[ BigStepIS ] Spec (e , res v)
  consistent-v {.(lambda _)} {lambda _} ε = VAL , _ , refl , λ ()
  consistent-v {lambda _} {lambda _} (x ◅ ss) = ⊥-elim (val-not-reduce⇒ x)
  consistent-v {app e1 e2} {lambda _} (x ◅ ss) =
    let e1' , e2' , e1⇒* , e2⇒* , subst⇒* = get-prem-cons (x ◅ ss) in
    let prems = λ{zero → e1⇒* ; (suc zero) → e2⇒* ; (suc (suc zero)) → subst⇒*} in
    APP , (e1 , e1' , e2 , e2' , _) , refl , prems
    
  postulate
    excluded-middle : ExcludedMiddle ∅
  
  lemma-divergence : ∀{e1 e2} → (∀{i} → ⇒∞ (app e1 e2) i) →
    (∀{i} → ⇒∞ e1 i) ⊎
    e1 ConvergesSS × (∀{i} → ⇒∞ e2 i) ⊎
    Σ[ t1 ∈ Term 1 ] Σ[ v ∈ Value ] (e1 ⇒* lambda t1) × (e2 ⇒* term v) × (∀{i} → ⇒∞ (subst-0 t1 (term v)) i)
  lemma-divergence {e1} {e2} ss with excluded-middle {e1 ConvergesSS}
  lemma-divergence {e1} {e2} ss | no ¬e1-conv = inj₁ (div-app-l-not-conv ss ¬e1-conv)
  lemma-divergence {e1} {e2} ss | yes e1-conv with excluded-middle {e2 ConvergesSS}
  lemma-divergence {e1} {e2} ss | yes e1-conv | no ¬e2-conv =
    inj₂ (inj₁ (e1-conv , div-app-r-not-conv ss (proj₂ e1-conv) ¬e2-conv))
  lemma-divergence {e1} {e2} ss | yes (lambda _ , red-e1) | yes (_ , red-e2) =
    inj₂ (inj₂ (_ , _ , ( red-e1 , red-e2 , app-subst-⇒∞₁ red-e1 red-e2 ss)))

  consistent-∞ : ∀{e} → (∀{i} → ⇒∞ e i) → IS.ISF[ BigStepIS ] Spec (e , div)
  consistent-∞ {e} ss with ss
  consistent-∞ {lambda e} ss | step x _ = ⊥-elim (val-not-reduce⇒ x)
  consistent-∞ {app e₁ e₂} ss | step x x₁ with lemma-divergence (step x x₁)
  consistent-∞ {app e₁ e₂} ss | step x x₁ | inj₁ e1-div =
    L-DIV , _ , refl , λ{zero → e1-div}
  consistent-∞ {app e₁ e₂} ss | step x x₁ | inj₂ (inj₁ (e1-conv , e2-div)) =
    R-DIV , _ , refl , λ{zero → proj₂ e1-conv ; (suc zero) → e2-div}
  consistent-∞ {app e₁ e₂} ss | step x x₁ | inj₂ (inj₂ (_ , _ , red-e1 , red-e2 , subst-div)) =
    APP , _ , refl , λ{zero → red-e1 ; (suc zero) → red-e2 ; (suc (suc zero)) → subst-div}

  consistent : ∀{e v} → Spec (e , v) → IS.ISF[ BigStepIS ] Spec (e , v)
  consistent {_} {res _} = consistent-v
  consistent {_} {div} = consistent-∞

  complete : ∀{e v} → Spec (e , v) → (∀{i} → (e ⇓ v) i)
  complete = bounded-scoind[ BigStepIS , BigStepCOIS ] Spec bounded consistent