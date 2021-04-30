open import Data.Nat
open import Data.Vec
open import Data.Fin
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Size

open import is-lib.SInfSys
open import Examples.Lambda.Lambda

module Examples.Lambda.BigStep where

  data Value∞ : Set where
    res : Value → Value∞
    div : Value∞

  U : Set
  U = Term 0 × Value∞

  data BigStepRN : Set where
    VAL APP L-DIV R-DIV : BigStepRN

  data BigStepCoRN : Set where
    COA : BigStepCoRN

  coa-r : FinMetaRule U
  coa-r .Ctx = Term 0
  coa-r .comp t =
    [] ,
    -------------------------
    (t , div)

  val-r : FinMetaRule U
  val-r .Ctx = Value
  val-r .comp v =
    [] ,
    -------------------------
    (term v , res v)

  app-r : FinMetaRule U
  app-r .Ctx = Term 0 × Term 1 × Term 0 × Value × Value∞
  app-r .comp (t1 , t , t2 , v , v∞) =
    (t1 , res (lambda t))  ∷ (t2 , res v) ∷ (subst-0 t (term v) , v∞) ∷ [] ,
    -------------------------
    (app t1 t2 , v∞)
  
  l-div-r : FinMetaRule U
  l-div-r .Ctx = Term 0 × Term 0
  l-div-r .comp (t1 , t2) =
    (t1 , div) ∷ [] ,
    -------------------------
    (app t1 t2 , div)
  
  r-div-r : FinMetaRule U
  r-div-r .Ctx = Term 0 × Term 0 × Value
  r-div-r .comp (t1 , t2 , v) =
    (t1 , res v) ∷ (t2 , div) ∷ [] ,
    -------------------------
    (app t1 t2 , div)
  
  BigStepIS : IS U
  BigStepIS .Names = BigStepRN
  BigStepIS .rules VAL = from val-r
  BigStepIS .rules APP = from app-r
  BigStepIS .rules L-DIV = from l-div-r
  BigStepIS .rules R-DIV = from r-div-r
  
  BigStepCOIS : IS U
  BigStepCOIS .Names = BigStepCoRN
  BigStepCOIS .rules COA = from coa-r
  
  _⇓_ : Term 0 → Value∞ → Size → Set
  (t ⇓ v∞) i = SFCoInd⟦ BigStepIS , BigStepCOIS ⟧ (t , v∞) i
  
  _⇓ᵢ_ : Term 0 → Value∞ → Set
  t ⇓ᵢ v∞ = Ind⟦ BigStepIS ∪ BigStepCOIS ⟧ (t , v∞)
  
  {- Properties -}
  
  val-not-reduce⇓ : ∀{v} → ¬ (∀{i} → ((term v) ⇓ div) i)
  val-not-reduce⇓ {lambda _} bs with bs
  val-not-reduce⇓ {lambda _} bs | (sfold (VAL , _ , () , _))
  
  val-⇓ᵢ-≡ : ∀{v v'} → term v ⇓ᵢ res v' → v ≡ v'
  val-⇓ᵢ-≡ {lambda x} {lambda .x} (fold (inj₁ VAL , .(lambda x) , refl , _)) = refl
  val-⇓ᵢ-≡ {lambda x} {lambda x₁} (fold (inj₁ APP , _ , () , _))
  val-⇓ᵢ-≡ {v} {v'} (fold (inj₂ COA , _ , () , _))
  
  val-⇓-≡ : ∀{v v'} → (∀{i} → (term v ⇓ res v') i) → v ≡ v'
  val-⇓-≡ bs = val-⇓ᵢ-≡ (sfcoind-to-ind bs)