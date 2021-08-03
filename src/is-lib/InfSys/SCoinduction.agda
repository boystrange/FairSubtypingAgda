--------------------------------------------------------------------------------
-- This is part of Agda Inference Systems 

{-# OPTIONS --sized-types #-}

open import Agda.Builtin.Equality
open import Data.Product
open import Size
open import Codata.Thunk
open import Level
open import Relation.Unary using (_⊆_)

module is-lib.InfSys.SCoinduction {𝓁} where

  private
    variable
      U : Set 𝓁
  
  open import is-lib.InfSys.Base {𝓁}
  open import is-lib.InfSys.Induction {𝓁}
  open MetaRule
  open IS

  {- Coinductive interpretation -}

  data SCoInd⟦_⟧ {𝓁c 𝓁p 𝓁n : Level} (is : IS {𝓁c} {𝓁p} {𝓁n} U) : U → Size → Set (𝓁 ⊔ 𝓁c ⊔ 𝓁p ⊔ 𝓁n) where
    sfold : ∀{u i} → ISF[ is ] (λ u → Thunk (SCoInd⟦ is ⟧ u) i) u → SCoInd⟦ is ⟧ u i

  {- Coinduction Principle -}

  scoind[_] : ∀{𝓁c 𝓁p 𝓁n 𝓁'}
      → (is : IS {𝓁c} {𝓁p} {𝓁n} U) 
      → (S : U → Set 𝓁')         
      → S ⊆ ISF[ is ] S     -- S is consistent
      → S ⊆ λ u → ∀{i} → SCoInd⟦ is ⟧ u i
  scoind[ is ] S cn Su with cn Su
  ... | rn , c , refl , pr = sfold (rn , c , refl , λ i → λ where .force → scoind[ is ] S cn (pr i))

  {- Apply Rule -}

  apply-scoind : ∀{𝓁c 𝓁p 𝓁n}{is : IS {𝓁c} {𝓁p} {𝓁n} U} → (rn : is .Names) → RClosed (is .rules rn) (λ u → ∀{i} → SCoInd⟦ is ⟧ u i) 
  apply-scoind {is = is} rn =
    prefix⇒closed (is .rules rn) {P = λ u → ∀{i} → SCoInd⟦ is ⟧ u i } λ{(c , refl , pr) → sfold (rn , c , refl , λ i → λ where .force → pr i)}

  {- Postfix - Prefix -}

  scoind-postfix : ∀{𝓁c 𝓁p 𝓁n}{is : IS {𝓁c} {𝓁p} {𝓁n} U} → (λ u → ∀{i} → SCoInd⟦ is ⟧ u i) ⊆ ISF[ is ] (λ u → ∀{i} → SCoInd⟦ is ⟧ u i)
  scoind-postfix p-scoind with p-scoind
  ... | sfold (rn , c , refl , pr) = rn , c , refl , λ i → (pr i) .force

  scoind-prefix : ∀{𝓁c 𝓁p 𝓁n}{is : IS {𝓁c} {𝓁p} {𝓁n} U} → ISF[ is ] (λ u → ∀{i} → SCoInd⟦ is ⟧ u i) ⊆ λ u → ∀{i} → SCoInd⟦ is ⟧ u i
  scoind-prefix (rn , c , refl , pr) = apply-scoind rn c pr