open import Agda.Builtin.Equality
open import Data.Product
open import Data.Sum
open import Size
open import Codata.Thunk

module is-lib.InfSys.FlexSCoinduction {l} where
  private
    variable
      U : Set l
  
  open import is-lib.InfSys.Base {l}
  open import is-lib.InfSys.Induction {l}
  open import is-lib.InfSys.SCoinduction {l}
  open MetaRule
  open IS

-- Generalized inference systems

  SFCoInd⟦_,_⟧ : (I C : IS U) → U → Size → Set l
  SFCoInd⟦ I , C ⟧ = SCoInd⟦ I ⊓ Ind⟦ I ∪ C ⟧ ⟧

-- Bounded Coinduction Principle

  bdc-lem : (I : IS U) → (S Q : U → Set l) →
            (∀ {u} → S u → Q u) →
            (∀ {u} → S u → ISF[ I ] S u) →
            ∀ {u} → S u → ISF[ I ⊓ Q ] S u
  bdc-lem I S Q bd cn Su with cn Su
  ... | rn , c , refl , sd , pr = rn , c , refl , (sd , bd Su) , pr

  bounded-scoind[_,_] : (I C : IS U) →
                       (S : U → Set l) →                    -- specification
                       (∀ {u} → S u → Ind⟦ I ∪ C ⟧ u) →  -- S is bounded w.r.t. I ∪ C
                       (∀ {u} → S u → ISF[ I ] S u) →  -- S is consistent w.r.t. I
                       ∀ {u} → S u → (∀{i} → SFCoInd⟦ I , C ⟧ u i)
  bounded-scoind[ I , C ] S bd cn Su = scoind[ I ⊓ Ind⟦ I ∪ C ⟧ ] S (bdc-lem I S Ind⟦ I ∪ C ⟧ bd cn) Su

  {- Get Ind from SFCoInd -}
  
  sfcoind-to-ind : ∀{is cois}{u : U} → (∀{i} → SFCoInd⟦ is , cois ⟧ u i) → Ind⟦ is ∪ cois ⟧ u
  sfcoind-to-ind co with co
  sfcoind-to-ind co | sfold (rn , _ , refl , sd , _) = proj₂ sd

  {- Apply Rule -}

  apply-sfcoind : ∀{is cois : IS U} → (rn : is .Names) → RClosed (is .rules rn) (λ u → ∀{i} → SFCoInd⟦ is , cois ⟧ u i)  
  apply-sfcoind rn sd prems = apply-scoind rn (sd , apply-ind (inj₁ rn) sd λ i → sfcoind-to-ind (prems i)) prems

  {- Postfix -}

  sfcoind-postfix : ∀{is cois : IS U}{u} → (∀{i} → SFCoInd⟦ is , cois ⟧ u i)
    → ISF[ is ] (λ u → ∀{i} → SFCoInd⟦ is , cois ⟧ u i) u
  sfcoind-postfix SFCoInd with SFCoInd
  ... | sfold (rn , _ , refl , (sd , _) , pr) = rn , _ , refl , sd , λ i → (pr i) .force

  {- Prefix -}

  sfcoind-prefix : ∀{is cois : IS U}{u}
    → ISF[ is ] (λ u → ∀{i} → SFCoInd⟦ is , cois ⟧ u i) u
    → ∀{i} → SFCoInd⟦ is , cois ⟧ u i
  sfcoind-prefix (rn , _ , refl , sd , pr) = apply-sfcoind rn sd pr