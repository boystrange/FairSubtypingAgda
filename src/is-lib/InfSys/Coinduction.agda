--------------------------------------------------------------------------------
-- This is part of Agda Inference Systems 

open import Agda.Builtin.Equality
open import Data.Product
open import Level
open import Relation.Unary using (_⊆_)

module is-lib.InfSys.Coinduction {𝓁} where

  private
    variable
      U : Set 𝓁
  
  open import is-lib.InfSys.Base {𝓁}
  open import is-lib.InfSys.Induction {𝓁}
  open MetaRule
  open IS
  
  {- Coinductive interpretation -}

  record CoInd⟦_⟧ {𝓁c 𝓁p 𝓁n : Level} (is : IS {𝓁c} {𝓁p} {𝓁n} U) (u : U) : Set (𝓁 ⊔ 𝓁c ⊔ 𝓁p ⊔ 𝓁n) where
    coinductive
    constructor cofold_
    field
      unfold : ISF[ is ] CoInd⟦ is ⟧ u

  {- Coinduction Principle -}

  coind[_] : ∀{𝓁c 𝓁p 𝓁n 𝓁'}
      → (is : IS {𝓁c} {𝓁p} {𝓁n} U) 
      → (S : U → Set 𝓁')
      → (S ⊆ ISF[ is ] S)   -- S is consistent
      → S ⊆ CoInd⟦ is ⟧
  CoInd⟦_⟧.unfold (coind[ is ] S cn Su) with cn Su
  ... | rn , c , refl , pr = rn , c , refl , λ i → coind[ is ] S cn (pr i)

  {- Apply Rule -}

  apply-coind : ∀{𝓁c 𝓁p 𝓁n}{is : IS {𝓁c} {𝓁p} {𝓁n} U} → (rn : is .Names) → RClosed (is .rules rn) CoInd⟦ is ⟧
  apply-coind {is = is} rn = prefix⇒closed (is .rules rn) {P = CoInd⟦ _ ⟧} λ{(c , refl , pr) → cofold (rn , c , refl , pr)}

  {- Postfix - Prefix -}

  coind-postfix : ∀{𝓁c 𝓁p 𝓁n}{is : IS {𝓁c} {𝓁p} {𝓁n} U} → CoInd⟦ is ⟧ ⊆ ISF[ is ] CoInd⟦ is ⟧
  coind-postfix x = x .CoInd⟦_⟧.unfold
  
  coind-prefix : ∀{𝓁c 𝓁p 𝓁n}{is : IS {𝓁c} {𝓁p} {𝓁n} U} → ISF[ is ] CoInd⟦ is ⟧ ⊆ CoInd⟦ is ⟧
  coind-prefix x = cofold x