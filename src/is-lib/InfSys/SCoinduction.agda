open import Agda.Builtin.Equality
open import Data.Product
open import Size
open import Codata.Thunk

module is-lib.InfSys.SCoinduction {l} where
  private
    variable
      U : Set l
  
  open import is-lib.InfSys.Base {l}
  open import is-lib.InfSys.Induction {l}
  open MetaRule
  open IS

-- Coinductive interpretation

  data SCoInd⟦_⟧ (is : IS U) : U → Size → Set l where
    sfold : ∀ {u i} → ISF[ is ] (λ u → Thunk (SCoInd⟦ is ⟧ u) i) u → SCoInd⟦ is ⟧ u i

-- Coinduction Principle

  scoind[_] : (is : IS U) →
            (S : U → Set l) →              -- specification
            (∀ {u} → S u → ISF[ is ] S u) →   -- S is consistent
            ∀ {u}  → S u → (∀{i} → SCoInd⟦ is ⟧ u i)
  scoind[ is ] S cn Su with cn Su
  ... | rn , c , refl , sd , pr = sfold (rn , c , refl , sd , λ i → λ where .force → scoind[ is ] S cn (pr i))

  {- Apply Rule -}

  apply-scoind : ∀{is : IS U} → (rn : is .Names) → RClosed (is .rules rn) (λ u → ∀{i} → SCoInd⟦ is ⟧ u i) 
  apply-scoind {_} {is} rn =
    prefix⇒closed (is .rules rn) {λ u → ∀{i} → SCoInd⟦ _ ⟧ u i} λ{(c , refl , sd , prems) → sfold (rn , c , refl , sd , λ i → λ where .force → prems i)}

  {- Postfix -}

  scoind-postfix : {is : IS U} → ∀ {u} → (∀{i} → SCoInd⟦ is ⟧ u i) → ISF[ is ] (λ u → ∀{j} → SCoInd⟦ is ⟧ u j) u
  scoind-postfix p-scoind with p-scoind
  ... | sfold (rn , c , refl , sd , pr) = rn , c , refl , sd , λ i → (pr i) .force

  {- Prefix -}

  scoind-prefix : ∀{is : IS U}{u} → ISF[ is ] (λ u → ∀{i} → SCoInd⟦ is ⟧ u i) u → ∀{i} → SCoInd⟦ is ⟧ u i
  scoind-prefix (rn , _ , refl , sd , pr) = apply-scoind rn sd pr