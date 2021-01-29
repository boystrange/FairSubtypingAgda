open import Agda.Builtin.Equality
open import Data.Product
open import Data.Sum

module is-lib.InfSys.FlexCoinduction {l} where

  private
    variable
      U : Set l
  
  open import is-lib.InfSys.Base {l}
  open import is-lib.InfSys.Induction {l}
  open import is-lib.InfSys.Coinduction {l}
  open MetaRule
  open IS

-- Generalized inference systems

  FCoInd⟦_,_⟧ : (I C : IS U) → U → Set l
  FCoInd⟦ I , C ⟧ = CoInd⟦ I ⊓ Ind⟦ I ∪ C ⟧ ⟧

-- Bounded Coinduction Principle

  bdc-lem : (I : IS U) → (S Q : U → Set l) →
            (∀ {u} → S u → Q u) →
            (∀ {u} → S u → ISF[ I ] S u) →
            ∀ {u} → S u → ISF[ I ⊓ Q ] S u
  bdc-lem I S Q bd cn Su with cn Su
  ... | rn , c , refl , sd , pr = rn , c , refl , (sd , bd Su) , pr

  bounded-coind[_,_] : (I C : IS U) →
                       (S : U → Set l) →                    -- specification
                       (∀ {u} → S u → Ind⟦ I ∪ C ⟧ u) →  -- S is bounded w.r.t. I ∪ C
                       (∀ {u} → S u → ISF[ I ] S u) →  -- S is consistent w.r.t. I
                       ∀ {u} → S u → FCoInd⟦ I , C ⟧ u
  bounded-coind[ I , C ] S bd cn Su = coind[ I ⊓ Ind⟦ I ∪ C ⟧ ] S (bdc-lem I S Ind⟦ I ∪ C ⟧ bd cn) Su

  {- Get Ind from FCoInd -}

  fcoind-to-ind : ∀{is cois}{u : U} → FCoInd⟦ is , cois ⟧ u → Ind⟦ is ∪ cois ⟧ u
  fcoind-to-ind co with CoInd⟦_⟧.unfold co
  ... | _ , _ , refl , sd , _ = proj₂ sd

  {- Apply Rule -}

  apply-fcoind : ∀{is cois : IS U} → (rn : is .Names) → RClosed (is .rules rn) FCoInd⟦ is , cois ⟧
  apply-fcoind rn sd prems = apply-coind rn (sd , apply-ind (inj₁ rn) sd λ i → fcoind-to-ind (prems i)) prems

  {- Postfix -}
  
  fcoind-postfix : ∀{is cois : IS U}{u} → FCoInd⟦ is , cois ⟧ u
    → ISF[ is ] FCoInd⟦ is , cois ⟧ u
  fcoind-postfix FCoInd with FCoInd .CoInd⟦_⟧.unfold
  ... | rn , _ , refl , (sd , _) , pr = rn , _ , refl , sd , pr

  {- Prefix -}

  fcoind-prefix : ∀{is cois : IS U}{u}
    → ISF[ is ] FCoInd⟦ is , cois ⟧ u
    → FCoInd⟦ is , cois ⟧ u
  fcoind-prefix (rn , _ , refl , sd , pr) = apply-fcoind rn sd pr