open import Codata.Colist
open import Codata.Thunk
open import Size
open import Data.Empty
open import Relation.Binary.PropositionalEquality

module Examples.Colists.Auxiliary.Colist_member {A : Set} where

  data _∈_ : A → Colist A ∞ → Set where
    here : ∀ {x xs} → x ∈ (x ∷ xs)
    there : ∀{x y xs} → x ∈ xs .force → x ∈ (y ∷ xs)

  mem-abs : ∀{x xs} → x ∈ xs → xs ≡ [] → ⊥
  mem-abs {_} {.[]} () refl