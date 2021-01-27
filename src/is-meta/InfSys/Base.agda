open import Agda.Builtin.Equality
open import Data.Product
open import Data.Sum
open import Data.Empty
open import Data.Fin using (Fin)
open import Data.Vec using (Vec; fromList) renaming (lookup to get)
open import Data.List using (List ; length ; lookup)
open import Data.Unit
open import Level using (Lift) renaming (suc to _++)
open import Size
open import Codata.Thunk

module is-meta.InfSys.Base {l} where

  record MetaRule (U : Set l) : Set (l ++) where
    constructor rule
    field
      C : Set l
      comp : C → List U × U × Set l

    prems : C → List U
    prems c = proj₁ (comp c)

    conclu : C → U
    conclu c = proj₁ (proj₂ (comp c))

    side : C → Set l
    side c = proj₂ (proj₂ (comp c))

    addSideCond : (U → Set l) → MetaRule U
    (addSideCond P) .C = C
    (addSideCond P) .comp c = prems c , conclu c , ((side c) × P (conclu c))

    get-prem : (c : C) → (i : Fin (length (prems c))) → U
    get-prem c i = lookup (prems c) i

    RF[_] : (U → Set l) → (U → Set l)
    RF[_] J u = Σ[ c ∈ C ] (u ≡ conclu c) × (side c) × (∀ i → J (get-prem c i))

    RClosed : (U → Set l) → Set l
    RClosed J = ∀ {c} → side c → (∀ i → J (get-prem c i)) → J (conclu c)

    -- closed implies prefix
    --apply[_] : ∀{J u} → RClosed J → RF[_] J u → J u
    --apply[_] cl (c , refl , sd , pr) = cl sd pr

    -- prefix implies closed
    app : ∀{J} → (∀{u} → RF[_] J u → J u) → RClosed J
    app f = λ sd prems → f (_ , refl , sd , prems)
    
  open MetaRule

  record NoSide : Set l where
    constructor <>

  record IS (U : Set l) : Set (l ++) where
    field
      Names : Set            -- rule names
      rules : Names → MetaRule U   -- rules

    ISF[_] : (U → Set l) → (U → Set l)
    ISF[_] J u = Σ[ rn ∈ Names ] RF[ rules rn ] J u

    ISClosed : (U → Set l) → Set l
    ISClosed J = ∀ rn → RClosed (rules rn) J
    --to do: ISClosed is S  equivalente ∀ u → ⟦ is ⟧ S u → S u
  open IS

  ISfromPred : {U : Set l} → (U → Set l) → IS U
  ISfromPred {U} P .Names = ⊤
  ISfromPred {U} P .rules rn .C = U
  ISfromPred {U} P .rules rn .comp u = List.[] , u , P u

  private
    variable
      U : Set l

  -- union
  _∪_ : IS U → IS U → IS U
  (is1 ∪ is2) .Names = (is1 .Names) ⊎ (is2 .Names)
  (is1 ∪ is2) .rules = [ is1 .rules , is2 .rules ]

  -- restriction
  _⊓_ : IS U → (U → Set l) → IS U
  (is ⊓ P) .Names = is .Names
  (is ⊓ P) .rules rn = addSideCond (is .rules rn) P

------------------------------------------
-- Inductive interpretation

  data Ind⟦_⟧ (is : IS U) : U →  Set l where
    fold : ∀ {u} →  ISF[ is ] Ind⟦ is ⟧ u → Ind⟦ is ⟧ u

---------------------------------------------
-- Coinductive interpretation

  record CoInd⟦_⟧ (is : IS U) (u : U) : Set l where
    coinductive
    constructor cofold_
    field
      unfold : ISF[ is ] CoInd⟦ is ⟧ u

  data SCoInd⟦_⟧ (is : IS U) : U → Size → Set l where
    sfold : ∀ {u i} → ISF[ is ] (λ u → Thunk (SCoInd⟦ is ⟧ u) i) u → SCoInd⟦ is ⟧ u i

-------------------------------------------------------------------------------------------------------
-- Generalized inference systems
  SGen⟦_,_⟧ : (I C : IS U) → U → Size → Set l
  SGen⟦ I , C ⟧ = SCoInd⟦ I ⊓ Ind⟦ I ∪ C ⟧ ⟧

  Gen⟦_,_⟧ : (I C : IS U) → U → Set l
  Gen⟦ I , C ⟧ = CoInd⟦ I ⊓ Ind⟦ I ∪ C ⟧ ⟧

  CoGen⟦_,_⟧ : (I C : IS U) → U → Set l
  CoGen⟦ I , C ⟧ = Ind⟦ (I ∪ C) ∪ (ISfromPred CoInd⟦ C ⟧) ⟧
