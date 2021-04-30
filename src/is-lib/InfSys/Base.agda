--------------------------------------------------------------------------------
-- This is part of Agda Inference Systems 

open import Agda.Builtin.Equality
open import Data.Product
open import Data.Sum
open import Data.Vec using (Vec; fromList; length) renaming (lookup to get)
open import Data.Fin using (Fin)
open import Level
open import Relation.Unary using (_⊆_)

module is-lib.InfSys.Base {𝓁} where

  record MetaRule {𝓁c 𝓁p : Level} (U : Set 𝓁) : Set (𝓁 ⊔ suc 𝓁c ⊔ suc 𝓁p) where 
    field 
      Ctx : Set 𝓁c
      Pos : Set 𝓁p 
      prems : Ctx → Pos → U
      conclu : Ctx → U 

    addSideCond : ∀{𝓁'} → (U → Set 𝓁') → MetaRule {𝓁c ⊔ 𝓁'} U
    (addSideCond P) .Ctx = Σ[ c ∈ Ctx ] P (conclu c)
    (addSideCond P) .Pos = Pos
    (addSideCond P) .prems (c , _) p = prems c p
    (addSideCond P) .conclu (c , _) = conclu c

    RF[_] : ∀{𝓁'} → (U → Set 𝓁') → (U → Set _)
    RF[_] P u = Σ[ c ∈ Ctx ] (u ≡ conclu c × (∀ p → P (prems c p)))

    RClosed : ∀{𝓁'} → (U → Set 𝓁') → Set _
    RClosed P = ∀ c → (∀ p → P (prems c p)) → P (conclu c)

  {- Finitary Rule -}

  record FinMetaRule {𝓁c n} (U : Set 𝓁) : Set (𝓁 ⊔ suc 𝓁c) where
    field
      Ctx : Set 𝓁c
      comp : Ctx → Vec U n × U

    from : MetaRule {𝓁c} {zero} U
    from .MetaRule.Ctx = Ctx
    from .MetaRule.Pos = Fin n
    from .MetaRule.prems c n = get (proj₁ (comp c)) n
    from .MetaRule.conclu c = proj₂ (comp c)

  open MetaRule

  record IS {𝓁c 𝓁p 𝓁n : Level} (U : Set 𝓁) : Set (𝓁 ⊔ suc 𝓁c ⊔ suc 𝓁p ⊔ suc 𝓁n) where
    field
      Names : Set 𝓁n            
      rules : Names → MetaRule {𝓁c} {𝓁p} U 

    ISF[_] : ∀{𝓁'} → (U → Set 𝓁') → (U → Set _)
    ISF[_] P u = Σ[ rn ∈ Names ] RF[ rules rn ] P u

    ISClosed : ∀{𝓁'} → (U → Set 𝓁') → Set _
    ISClosed P = ∀ rn → RClosed (rules rn) P

  open IS

  _∪_ : ∀{𝓁c 𝓁p 𝓁n 𝓁n'}{U : Set 𝓁} → IS {𝓁c} {𝓁p} {𝓁n} U → IS {_} {_} {𝓁n'} U → IS {_} {_} {𝓁n ⊔ 𝓁n'} U
  (is1 ∪ is2) .Names = (is1 .Names) ⊎ (is2 .Names)
  (is1 ∪ is2) .rules = [ is1 .rules , is2 .rules ]

  _⊓_ : ∀{𝓁c 𝓁p 𝓁n 𝓁'}{U : Set 𝓁} → IS {𝓁c} {𝓁p} {𝓁n} U → (U → Set 𝓁') → IS {𝓁c ⊔ 𝓁'} {_} {_} U
  (is ⊓ P) .Names = is .Names
  (is ⊓ P) .rules rn = addSideCond (is .rules rn) P

  {- Properties -}

  -- closed implies prefix
  closed⇒prefix : ∀{𝓁c 𝓁p}{U : Set 𝓁} → (m : MetaRule {𝓁c} {𝓁p} U) → ∀{𝓁'}{P : U → Set 𝓁'} → RClosed m {𝓁'} P → RF[ m ] P ⊆ P
  closed⇒prefix _ cl (_ , refl , pr) = cl _ pr

  -- prefix implies closed
  prefix⇒closed : ∀{𝓁c 𝓁p}{U : Set 𝓁} → (m : MetaRule {𝓁c} {𝓁p} U) → ∀{𝓁'}{P : U → Set 𝓁'} → (RF[ m ] P ⊆ P) → RClosed m {𝓁'} P
  prefix⇒closed _ prf c pr = prf (c , refl , pr)