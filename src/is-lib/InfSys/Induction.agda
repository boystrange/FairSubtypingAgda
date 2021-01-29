open import Agda.Builtin.Equality
open import Data.Product
open import Size
open import Codata.Thunk

module is-lib.InfSys.Induction {l} where
  private
    variable
      U : Set l

  open import is-lib.InfSys.Base {l}
  open MetaRule
  open IS

  -- Inductive Interpretation

  data Ind⟦_⟧ (is : IS U) : U →  Set l where
    fold : ∀ {u} →  ISF[ is ] Ind⟦ is ⟧ u → Ind⟦ is ⟧ u

  -- Induction Principle

  ind[_] : (is : IS U) →
           (S : U → Set l) →        -- specification
           ISClosed is S →          -- S is closed
           ∀ {u} → Ind⟦ is ⟧ u → S u
  ind[ is ] S cl (fold (rn , c , refl , sd , pr)) = cl rn sd λ i → ind[ is ] S cl (pr i)

  {- Apply Rule -}
  
  apply-ind : ∀{is : IS U} → (rn : is .Names) → RClosed (is .rules rn) Ind⟦ is ⟧
  apply-ind {_} {is} rn = prefix⇒closed (is .rules rn) {Ind⟦ _ ⟧} λ{(c , refl , sd , prems) → fold (rn , c , refl , sd , prems)}

  {- Postfix -}

  ind-postfix : ∀{is : IS U}{u} → Ind⟦ is ⟧ u → ISF[ is ] Ind⟦ is ⟧ u
  ind-postfix (fold x) = x

  {- Prefix -}
  ind-prefix : ∀{is : IS U}{u} → ISF[ is ] Ind⟦ is ⟧ u → Ind⟦ is ⟧ u
  ind-prefix x = fold x