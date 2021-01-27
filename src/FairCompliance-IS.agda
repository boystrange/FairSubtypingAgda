-- MIT License

-- Copyright (c) 2021 Luca Ciccone and Luca Padovani

-- Permission is hereby granted, free of charge, to any person
-- obtaining a copy of this software and associated documentation
-- files (the "Software"), to deal in the Software without
-- restriction, including without limitation the rights to use,
-- copy, modify, merge, publish, distribute, sublicense, and/or sell
-- copies of the Software, and to permit persons to whom the
-- Software is furnished to do so, subject to the following
-- conditions:

-- The above copyright notice and this permission notice shall be
-- included in all copies or substantial portions of the Software.

-- THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
-- EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES
-- OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
-- NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT
-- HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
-- WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
-- FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR
-- OTHER DEALINGS IN THE SOFTWARE.

open import Data.Product
open import Data.Empty
open import Data.Sum
open import Data.List
open import Data.Fin
open import Data.Bool renaming (Bool to 𝔹)
open import Relation.Unary using (_∈_; _⊆_)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

open import Common

open import is-meta.InfSys as IS
open MetaRule
open IS.IS
open import is-meta.InfSys.Properties
open import is-meta.InfSys.Principles

module FairCompliance-IS where

  message : Message 𝔹
  message = record{_?=_ = Data.Bool._≟_}

  open import SessionType message
  open import Session message
  open import Transitions message
  
  U : Set
  U = SessionType × SessionType

  data FCompIS-RN : Set where
    client-end : FCompIS-RN
    oi-true oi-false oi-both : FCompIS-RN
    io-true io-false io-both : FCompIS-RN

  data FCompCOIS-RN : Set where
    co-oi co-io : FCompCOIS-RN

  client-end-r : MetaRule U
  client-end-r .C = SessionType × SessionType
  client-end-r .comp (S , T) =
    [] ,
    --------------------
    (S , T) , (Win S × Defined T)

  OI-true-r : MetaRule U
  OI-true-r .C = Continuation × Continuation
  OI-true-r .comp (f , g) =
    (f true .force , g true .force) ∷ [] ,
    --------------------
    (out f , inp g) , (dom f true × ¬ dom f false)

  OI-false-r : MetaRule U
  OI-false-r .C = Continuation × Continuation
  OI-false-r .comp (f , g) =
    (f false .force , g false .force) ∷ [] ,
    --------------------
    (out f , inp g) , (dom f false × ¬ dom f true)

  OI-both-r : MetaRule U
  OI-both-r .C = Continuation × Continuation
  OI-both-r .comp (f , g) =
    (f true .force , g true .force) ∷ (f false .force , g false .force) ∷ [] ,
    --------------------
    (out f , inp g) , (dom f true × dom f false)

  IO-true-r : MetaRule U
  IO-true-r .C = Continuation × Continuation
  IO-true-r .comp (f , g) =
    (f true .force , g true .force) ∷ [] ,
    --------------------
    (inp f , out g) , (dom g true × ¬ dom g false)

  IO-false-r : MetaRule U
  IO-false-r .C = Continuation × Continuation
  IO-false-r .comp (f , g) =
    (f false .force , g false .force) ∷ [] ,
    --------------------
    (inp f , out g) , (dom g false × ¬ dom g true)

  IO-both-r : MetaRule U
  IO-both-r .C = Continuation × Continuation
  IO-both-r .comp (f , g) =
    (f true .force , g true .force) ∷ (f false .force , g false .force) ∷ [] ,
    --------------------
    (inp f , out g) , (dom g true × dom g false)

  co-IO-r : MetaRule U
  co-IO-r .C = Continuation × Continuation × 𝔹
  co-IO-r .comp (f , g , x) =
    (f x .force , g x .force) ∷ [] ,
    --------------------
    (inp f , out g) , dom g x

  co-OI-r : MetaRule U
  co-OI-r .C = Continuation × Continuation × 𝔹
  co-OI-r .comp (f , g , x) =
    (f x .force , g x .force) ∷ [] ,
    --------------------
    (out f , inp g) , dom f x

  FCompIS : IS U
  FCompIS .Names = FCompIS-RN
  FCompIS .rules client-end = client-end-r
  FCompIS .rules oi-true = OI-true-r
  FCompIS .rules oi-false = OI-false-r
  FCompIS .rules oi-both = OI-both-r
  FCompIS .rules io-true = IO-true-r
  FCompIS .rules io-false = IO-false-r
  FCompIS .rules io-both = IO-both-r

  FCompCOIS : IS U
  FCompCOIS .Names = FCompCOIS-RN
  FCompCOIS .rules co-oi = co-OI-r
  FCompCOIS .rules co-io = co-IO-r

  _⊢_ : SessionType → SessionType → Set
  S ⊢ T = Gen⟦ FCompIS , FCompCOIS ⟧ (S , T)

  _⊢ᵢ_ : SessionType → SessionType → Set
  S ⊢ᵢ T = Ind⟦ FCompIS ∪ FCompCOIS ⟧ (S , T)


  {- Soundness -}
  ⊢ᵢ-implies-succeed : ∀{S T} → S ⊢ᵢ T → MaySucceed (S # T)
  ⊢ᵢ-implies-succeed (fold (inj₁ client-end , (S , T) , refl , (win , def) , _)) = (S # T) , ε , win#def win def
  ⊢ᵢ-implies-succeed (fold (inj₁ oi-true , (f , g) , refl , (ok-t , _) , pr)) =
    let Sys' , red-Sys' , Succ = ⊢ᵢ-implies-succeed (pr zero) in
    Sys' , sync (out ok-t) inp ◅ red-Sys' , Succ
  ⊢ᵢ-implies-succeed (fold (inj₁ oi-false , (f , g) , refl , (ok-f , _) , pr)) =
    let Sys' , red-Sys' , Succ = ⊢ᵢ-implies-succeed (pr zero) in
    Sys' , sync (out ok-f) inp ◅ red-Sys' , Succ
  ⊢ᵢ-implies-succeed (fold (inj₁ oi-both , (f , g) , refl , (ok-t , _) , pr)) =
    let Sys' , red-Sys' , Succ = ⊢ᵢ-implies-succeed (pr zero) in
    Sys' , sync (out ok-t) inp ◅ red-Sys' , Succ
  ⊢ᵢ-implies-succeed (fold (inj₁ io-true , (f , g) , refl , (ok-t , _) , pr)) =
    let Sys' , red-Sys' , Succ = ⊢ᵢ-implies-succeed (pr zero) in
    Sys' , sync inp (out ok-t) ◅ red-Sys' , Succ
  ⊢ᵢ-implies-succeed (fold (inj₁ io-false , (f , g) , refl , (ok-f , _) , pr)) =
    let Sys' , red-Sys' , Succ = ⊢ᵢ-implies-succeed (pr zero) in
    Sys' , sync inp (out ok-f) ◅ red-Sys' , Succ
  ⊢ᵢ-implies-succeed (fold (inj₁ io-both , (f , g) , refl , (ok-t , _) , pr)) =
    let Sys' , red-Sys' , Succ = ⊢ᵢ-implies-succeed (pr zero) in
    Sys' , sync inp (out ok-t) ◅ red-Sys' , Succ
  ⊢ᵢ-implies-succeed (fold (inj₂ co-oi , (f , g , b) , refl , ok-b , pr)) =
    let Sys' , red-Sys' , Succ = ⊢ᵢ-implies-succeed (pr zero) in
    Sys' , sync (out ok-b) inp ◅ red-Sys' , Succ
  ⊢ᵢ-implies-succeed (fold (inj₂ co-io , (f , g , b) , refl , ok-b , pr)) =
    let Sys' , red-Sys' , Succ = ⊢ᵢ-implies-succeed (pr zero) in
    Sys' , sync inp (out ok-b) ◅ red-Sys' , Succ

  win-reduces-⊥ : ∀{S S' α} → Win S → Transition S α S' → ⊥
  win-reduces-⊥ (out e) (out !x) = e _ !x
  
  success-reduces-⊥ : ∀{S S'} → Success S → Reduction S S' → ⊥
  success-reduces-⊥ (win#def win _) (sync r _) = win-reduces-⊥ win r

  fc-sound : ∀{S T} → S ⊢ T → FairComplianceS (S # T)
  fc-sound fc ε = ⊢ᵢ-implies-succeed (gen-to-ind fc) 
  fc-sound fc (x ◅ red) with fc .CoInd⟦_⟧.unfold
  fc-sound fc (x ◅ red) | client-end , _ , refl , ((win , def) , _) , _ = ⊥-elim (success-reduces-⊥ (win#def win def) x)
  fc-sound fc (sync (out ok-f) (inp {x = false}) ◅ red) | oi-true , _ , refl , ((_ , no-f) , _) , _ = ⊥-elim (no-f ok-f)
  fc-sound fc (sync (out _) (inp {x = true}) ◅ red) | oi-true , _ , refl , ((_ , _) , _) , pr = fc-sound (pr zero) red
  fc-sound fc (sync (out _) (inp {x = false}) ◅ red) | oi-false , _ , refl , ((_ , _) , _) , pr = fc-sound (pr zero) red
  fc-sound fc (sync (out ok-t) (inp {x = true}) ◅ red) | oi-false , _ , refl , ((_ , no-t) , _) , _ = ⊥-elim (no-t ok-t)
  fc-sound fc (sync (out _) (inp {x = false}) ◅ red) | oi-both , _ , refl , _ , pr = fc-sound (pr (suc zero)) red
  fc-sound fc (sync (out _) (inp {x = true}) ◅ red) | oi-both , _ , refl , _ , pr = fc-sound (pr zero) red
  fc-sound fc (sync (inp {x = false}) (out ok-f) ◅ red) | io-true , _ , refl , ((_ , no-f) , _) , _ = ⊥-elim (no-f ok-f)
  fc-sound fc (sync (inp {x = true}) (out _) ◅ red) | io-true , _ , refl , ((_ , _) , _) , pr = fc-sound (pr zero) red
  fc-sound fc (sync (inp {x = false}) (out _) ◅ red) | io-false , _ , refl , ((_ , _) , _) , pr = fc-sound (pr zero) red
  fc-sound fc (sync (inp {x = true}) (out ok-t) ◅ red) | io-false , _ , refl , ((_ , no-t) , _) , _ = ⊥-elim (no-t ok-t)
  fc-sound fc (sync (inp {x = false}) (out _) ◅ red) | io-both , _ , refl , _ , pr = fc-sound (pr (suc zero)) red
  fc-sound fc (sync (inp {x = true}) (out _) ◅ red) | io-both , _ , refl , _ , pr = fc-sound (pr zero) red

  {- Boundedness -}
  maysucceed-implies-⊢ᵢ : ∀{S T Sys} → Reductions (S # T) Sys → Success Sys → S ⊢ᵢ T
  maysucceed-implies-⊢ᵢ ε (win#def win def) = IS.fold (inj₁ client-end , _ , refl , (win , def) , λ ())
  maysucceed-implies-⊢ᵢ (sync (out ok) inp ◅ red) Succ =
    let rec = maysucceed-implies-⊢ᵢ red Succ in
    IS.fold (inj₂ co-oi , _ , refl , ok , λ{zero → rec})
  maysucceed-implies-⊢ᵢ (sync inp (out ok) ◅ red) Succ =
    let rec = maysucceed-implies-⊢ᵢ red Succ in
    IS.fold (inj₂ co-io , _ , refl , ok , λ{zero → rec})

  fc-bounded : ∀{S T} → FairComplianceS (S # T) → S ⊢ᵢ T
  fc-bounded fc =
    let _ , red-Sys , Succ = fc ε in
    maysucceed-implies-⊢ᵢ red-Sys Succ

  {- Consistency -}
  fc-consistent : ∀{S T} → FairComplianceS (S # T) → ISF[ FCompIS ] (λ{(S , T) → FairComplianceS (S # T)}) (S , T)
  fc-consistent fc with fc ε
  fc-consistent fc | .(_ # _) , ε , win#def win def = client-end , _ , refl , (win , def) , λ ()
  fc-consistent {out f} fc | _ , sync (out ok-f) (inp {x = false}) ◅ _ , _ with true ∈? f
  fc-consistent {out f} fc | _ , sync (out ok-f) (inp {_} {false}) ◅ _ , _ | no no-t =
    oi-false , _ , refl , (ok-f , no-t) , λ{zero → λ red → fc (sync (out ok-f) inp ◅ red)}
  fc-consistent {out f} fc | _ , sync (out ok-f) (inp {_} {false}) ◅ _ , _ | yes ok-t =
    let prems = λ{
              zero → λ red → fc (sync (out ok-t) inp ◅ red) ;
              (suc zero) → λ red → fc (sync (out ok-f) inp ◅ red)} in
    oi-both , _ , refl , (ok-t , ok-f) , prems
  fc-consistent {out f} fc | _ , sync (out ok-t) (inp {x = true}) ◅ _ , _ with false ∈? f
  fc-consistent {out f} fc | _ , sync (out ok-t) (inp {_} {true}) ◅ _ , _ | no no-f =
    oi-true , _ , refl , (ok-t , no-f) , λ{zero → λ red → fc (sync (out ok-t) inp ◅ red)}
  fc-consistent {out f} fc | _ , sync (out ok-t) (inp {_} {true}) ◅ _ , _ | yes ok-f =
    let prems = λ{
              zero → λ red → fc (sync (out ok-t) inp ◅ red) ;
              (suc zero) → λ red → fc (sync (out ok-f) inp ◅ red)} in
    oi-both , _ , refl , (ok-t , ok-f) , prems
  fc-consistent {_} {out g} fc | _ , sync (inp {x = false}) (out ok-f) ◅ _ , _ with true ∈? g
  fc-consistent {_} {out g} fc | _ , sync (inp {x = false}) (out ok-f) ◅ _ , _ | no no-t =
    io-false , _ , refl , (ok-f , no-t) , λ{zero → λ red → fc (sync inp (out ok-f) ◅ red)}
  fc-consistent {_} {out g} fc | _ , sync (inp {x = false}) (out ok-f) ◅ _ , _ | yes ok-t =
    let prems = λ{
              zero → λ red → fc (sync inp (out ok-t) ◅ red) ;
              (suc zero) → λ red → fc (sync inp (out ok-f) ◅ red)} in
    io-both , _ , refl , (ok-t , ok-f) , prems
  fc-consistent {_} {out g} fc | _ , sync (inp {x = true}) (out ok-t) ◅ _ , _ with false ∈? g
  fc-consistent {_} {out g} fc | _ , sync (inp {x = true}) (out ok-t) ◅ _ , _ | no no-f =
    io-true , _ , refl , (ok-t , no-f) , λ{zero → λ red → fc (sync inp (out ok-t) ◅ red)}
  fc-consistent {_} {out g} fc | _ , sync (inp {x = true}) (out ok-t) ◅ _ , _ | yes ok-f =
    let prems = λ{
              zero → λ red → fc (sync inp (out ok-t) ◅ red) ;
              (suc zero) → λ red → fc (sync inp (out ok-f) ◅ red)} in
    io-both , _ , refl , (ok-t , ok-f) , prems

  {- Completeness -}
  fc-complete : ∀{S T} → FairComplianceS (S # T) → S ⊢ T
  fc-complete =
    let S = λ{(S , T) → FairComplianceS (S # T)} in
    bounded-coind[ FCompIS , FCompCOIS ] S fc-bounded fc-consistent
