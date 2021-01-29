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

module is-lib.InfSys.Base {l} where

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

  {- Properties -}
  
  -- closed implies prefix
  closed⇒prefix : (m : MetaRule U) → ∀{J u} → RClosed m J → RF[ m ] J u → J u
  closed⇒prefix _ cl (c , refl , sd , pr) = cl sd pr

  -- prefix implies closed
  prefix⇒closed : (m : MetaRule U) → ∀{J} → (∀{u} → RF[ m ] J u → J u) → RClosed m J
  prefix⇒closed _ f = λ sd prems → f (_ , refl , sd , prems)