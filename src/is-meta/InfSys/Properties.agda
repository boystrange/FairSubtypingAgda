open import Agda.Builtin.Equality
open import Data.Product
open import Data.Sum
open import Codata.Thunk
open import Size

module is-meta.InfSys.Properties {l} where
  open import is-meta.InfSys.Base
  open import is-meta.InfSys.Principles
  open IS
  open MetaRule

  private
    variable
      U : Set l

-------------------------------------------------------------------------------------------------------
  {- Postfix -}
  ind-postfix : ∀{is : IS U}{u} → Ind⟦ is ⟧ u → ISF[ is ] (λ u → Ind⟦ is ⟧ u) u
  ind-postfix (fold x) = x

  coind-postfix : ∀{is : IS U}{u} → CoInd⟦ is ⟧ u → ISF[ is ] (λ u → CoInd⟦ is ⟧ u) u
  coind-postfix coind = coind .CoInd⟦_⟧.unfold
  
  scoind-postfix : {is : IS U} → ∀ {u} → (∀{i} → SCoInd⟦ is ⟧ u i) → ISF[ is ] (λ u → ∀{j} → SCoInd⟦ is ⟧ u j) u
  scoind-postfix p-scoind with p-scoind
  ... | sfold (rn , c , refl , sd , pr) = rn , c , refl , sd , λ i → Thunk.force (pr i)

  gen-postfix : ∀{is cois : IS U}{u} → Gen⟦ is , cois ⟧ u
    → ISF[ is ⊓ Ind⟦ is ∪ cois ⟧ ] (λ u → Gen⟦ is , cois ⟧ u) u
  gen-postfix = coind-postfix

  sgen-postfix : ∀{is cois : IS U}{u} → (∀{i} → SGen⟦ is , cois ⟧ u i)
    → ISF[ is ⊓ Ind⟦ is ∪ cois ⟧ ] (λ u → ∀{i} → SGen⟦ is , cois ⟧ u i) u
  sgen-postfix = scoind-postfix

  {- Prefix -}
  ind-prefix : ∀{is : IS U}{u} → ISF[ is ] (λ u → Ind⟦ is ⟧ u) u → Ind⟦ is ⟧ u
  ind-prefix x = fold x

  coind-prefix : ∀{is : IS U}{u} → ISF[ is ] (λ u → CoInd⟦ is ⟧ u) u → CoInd⟦ is ⟧ u
  coind-prefix x = cofold x

  scoind-prefix : ∀{is : IS U}{u} → ISF[ is ] (λ u → ∀{i} → SCoInd⟦ is ⟧ u i) u → ∀{i} → SCoInd⟦ is ⟧ u i
  scoind-prefix (rn , c , refl , sd , pr) = sfold (rn , c , refl , sd , λ i → λ where .force → pr i)

  gen-prefix : ∀{is cois : IS U}{u}
    → ISF[ is ⊓ Ind⟦ is ∪ cois ⟧ ] (λ u → Gen⟦ is , cois ⟧ u) u
    → Gen⟦ is , cois ⟧ u
  gen-prefix = coind-prefix

  sgen-prefix : ∀{is cois : IS U}{u}
    → ISF[ is ⊓ Ind⟦ is ∪ cois ⟧ ] (λ u → ∀{i} → SGen⟦ is , cois ⟧ u i) u
    → ∀{i} → SGen⟦ is , cois ⟧ u i
  sgen-prefix = scoind-prefix
  
  -- Equivalence CoInd and SCoInd
  coind-size : {is : IS U} →  ∀ {u} → CoInd⟦ is ⟧ u → ∀ {i} → SCoInd⟦ is ⟧ u i
  coind-size p-coind with CoInd⟦_⟧.unfold p-coind
  ... | rn , c , refl , sd , pr = sfold (rn , c , refl , sd , λ i → λ where .force → coind-size (pr i) )

  size-coind : {is : IS U} → ∀ {u} → (∀ {i} → SCoInd⟦ is ⟧ u i) → CoInd⟦ is ⟧ u
  size-coind {is = is} p-scoind = coind[ is ] (λ u → ∀ {j} → SCoInd⟦ is ⟧ u j) scoind-postfix p-scoind

  {- Get Ind from Gen -}
  gen-to-ind : ∀{is cois}{u : U} → Gen⟦ is , cois ⟧ u → Ind⟦ is ∪ cois ⟧ u
  gen-to-ind co with CoInd⟦_⟧.unfold co
  ... | _ , _ , refl , sd , _ = proj₂ sd
  
  sgen-to-ind : ∀{is cois}{u : U} → (∀{i} → SGen⟦ is , cois ⟧ u i) → Ind⟦ is ∪ cois ⟧ u
  sgen-to-ind co with co
  sgen-to-ind co | sfold (rn , _ , refl , sd , _) = proj₂ sd

  {- Apply Rule -}
  --{is : IS U} -> (rn : is .Names) -> RClosed (is .rules rn) Ind[[ is ]] 
  apply-ind : ∀{r : MetaRule U}{is} → Σ[ rn ∈ is .Names ] is .rules rn ≡ r → RClosed r (Ind⟦ is ⟧) 
  apply-ind {r = r} (rn , refl) = app r {Ind⟦ _ ⟧} λ{(c , refl , sd , prems) → fold (rn , c , refl , sd , prems)}

  apply-coind : ∀{r : MetaRule U}{is} → Σ[ rn ∈ is .Names ] is .rules rn ≡ r → RClosed r (CoInd⟦ is ⟧)
  apply-coind {r = r} (rn , refl) = app r {CoInd⟦ _ ⟧} λ{(c , refl , sd , prems) → cofold (rn , c , refl , sd , prems)}

  apply-scoind : ∀{r : MetaRule U}{is} → Σ[ rn ∈ is .Names ] is .rules rn ≡ r → RClosed r (λ u → ∀{i} → SCoInd⟦ is ⟧ u i) 
  apply-scoind {r = r} (rn , refl) =
    app r {λ u → ∀{i} → SCoInd⟦ _ ⟧ u i} λ{(c , refl , sd , prems) → sfold (rn , c , refl , sd , λ i → λ where .force → prems i)}

  apply-gen : ∀{r : MetaRule U}{is cois} → Σ[ rn ∈ is .Names ] is .rules rn ≡ r → RClosed r (Gen⟦ is , cois ⟧) 
  apply-gen {r = r} (rn , refl) sd prems = apply-coind (rn , refl) (sd , apply-ind (inj₁ rn , refl) sd λ i → gen-to-ind (prems i)) prems

  apply-sgen : ∀{r : MetaRule U}{is cois} → Σ[ rn ∈ is .Names ] is .rules rn ≡ r → RClosed r (λ u → ∀{i} → SGen⟦ is , cois ⟧ u i)  
  apply-sgen {r = r} (rn , refl) sd prems = apply-scoind (rn , refl) (sd , apply-ind (inj₁ rn , refl) sd λ i → sgen-to-ind (prems i)) prems
