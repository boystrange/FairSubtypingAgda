open import Agda.Builtin.Equality
open import Data.Product

module is-lib.InfSys.Coinduction {l} where

  private
    variable
      U : Set l
  
  open import is-lib.InfSys.Base {l}
  open import is-lib.InfSys.Induction {l}
  open MetaRule
  open IS
  
-- Coinductive interpretation

  record CoInd⟦_⟧ (is : IS U) (u : U) : Set l where
    coinductive
    constructor cofold_
    field
      unfold : ISF[ is ] CoInd⟦ is ⟧ u

-- Coinduction Principle

  coind[_] : (is : IS U) →
            (S : U → Set l) →              -- specification
            (∀ {u} → S u → ISF[ is ] S u) →   -- S is consistent
            ∀ {u}  → S u → CoInd⟦ is ⟧ u
  CoInd⟦_⟧.unfold (coind[ is ] S cn Su) with cn Su
  ... | rn , c , refl , sd , pr = rn , c , refl , sd , λ i → coind[ is ] S cn (pr i)

  {- Apply Rule -}

  apply-coind : ∀{is : IS U} → (rn : is .Names) → RClosed (is .rules rn) CoInd⟦ is ⟧
  apply-coind {_} {is} rn = prefix⇒closed (is .rules rn) {CoInd⟦ _ ⟧} λ{(c , refl , sd , prems) → cofold (rn , c , refl , sd , prems)}

  {- Postfix -}

  coind-postfix : ∀{is : IS U}{u} → CoInd⟦ is ⟧ u → ISF[ is ] CoInd⟦ is ⟧ u
  coind-postfix coind = coind .CoInd⟦_⟧.unfold

  {- Prefix -}
  
  coind-prefix : ∀{is : IS U}{u} → ISF[ is ] CoInd⟦ is ⟧ u → CoInd⟦ is ⟧ u
  coind-prefix x = cofold x