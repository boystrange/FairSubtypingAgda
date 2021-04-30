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
open import Data.Vec
open import Data.Fin
open import Data.Bool renaming (Bool to 𝔹)
open import Relation.Unary using (_∈_; _⊆_; _∉_)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

open import Common

open import is-lib.InfSys

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

  client-end-r : FinMetaRule U
  client-end-r .Ctx = Σ[ (S , T) ∈ SessionType × SessionType ] Win S × Defined T
  client-end-r .comp ((S , T) , _) =
    [] ,
    --------------------
    (S , T)

  OI-true-r : FinMetaRule U
  OI-true-r .Ctx = Σ[ (f , _) ∈ Continuation × Continuation ] true ∈ dom f × false ∉ dom f
  OI-true-r .comp ((f , g) , _) =
    (f true .force , g true .force) ∷ [] ,
    --------------------
    (out f , inp g)

  OI-false-r : FinMetaRule U
  OI-false-r .Ctx = Σ[ (f , _) ∈ Continuation × Continuation ] false ∈ dom f × true ∉ dom f
  OI-false-r .comp ((f , g) , _) =
    (f false .force , g false .force) ∷ [] ,
    --------------------
    (out f , inp g)

  OI-both-r : FinMetaRule U
  OI-both-r .Ctx = Σ[ (f , _) ∈ Continuation × Continuation ] true ∈ dom f × false ∈ dom f
  OI-both-r .comp ((f , g) , _) =
    (f true .force , g true .force) ∷ (f false .force , g false .force) ∷ [] ,
    --------------------
    (out f , inp g)

  IO-true-r : FinMetaRule U
  IO-true-r .Ctx = Σ[ (_ , g) ∈ Continuation × Continuation ] true ∈ dom g × false ∉ dom g
  IO-true-r .comp ((f , g) , _) =
    (f true .force , g true .force) ∷ [] ,
    --------------------
    (inp f , out g)

  IO-false-r : FinMetaRule U
  IO-false-r .Ctx = Σ[ (_ , g) ∈ Continuation × Continuation ] false ∈ dom g × true ∉ dom g
  IO-false-r .comp ((f , g) , _) =
    (f false .force , g false .force) ∷ [] ,
    --------------------
    (inp f , out g)

  IO-both-r : FinMetaRule U
  IO-both-r .Ctx = Σ[ (_ , g) ∈ Continuation × Continuation ] true ∈ dom g × false ∈ dom g
  IO-both-r .comp ((f , g) , _) =
    (f true .force , g true .force) ∷ (f false .force , g false .force) ∷ [] ,
    --------------------
    (inp f , out g)

  co-IO-r : FinMetaRule U
  co-IO-r .Ctx = Σ[ (_ , g , x) ∈ Continuation × Continuation × 𝔹 ] dom g x
  co-IO-r .comp ((f , g , x) , _) =
    (f x .force , g x .force) ∷ [] ,
    --------------------
    (inp f , out g)

  co-OI-r : FinMetaRule U
  co-OI-r .Ctx = Σ[ (f , _ , x) ∈ Continuation × Continuation × 𝔹 ] dom f x
  co-OI-r .comp ((f , g , x) , _) =
    (f x .force , g x .force) ∷ [] ,
    --------------------
    (out f , inp g)

  FCompIS : IS U
  FCompIS .Names = FCompIS-RN
  FCompIS .rules client-end = from client-end-r
  FCompIS .rules oi-true = from OI-true-r
  FCompIS .rules oi-false = from OI-false-r
  FCompIS .rules oi-both = from OI-both-r
  FCompIS .rules io-true = from IO-true-r
  FCompIS .rules io-false = from IO-false-r
  FCompIS .rules io-both = from IO-both-r

  FCompCOIS : IS U
  FCompCOIS .Names = FCompCOIS-RN
  FCompCOIS .rules co-oi = from co-OI-r
  FCompCOIS .rules co-io = from co-IO-r

  _⊢_ : SessionType → SessionType → Set
  S ⊢ T = FCoInd⟦ FCompIS , FCompCOIS ⟧ (S , T)

  _⊢ᵢ_ : SessionType → SessionType → Set
  S ⊢ᵢ T = Ind⟦ FCompIS ∪ FCompCOIS ⟧ (S , T)

  {- Properties -}

  ¬nil-⊢ : ∀{S} → ¬ (nil ⊢ S)
  ¬nil-⊢ fc with fc .CoInd⟦_⟧.unfold
  ... | client-end , ((C , (() , _)) , _) , refl , _

  ⊢ᵢ-implies-succeed : ∀{S T} → S ⊢ᵢ T → MaySucceed (S # T)
  ⊢ᵢ-implies-succeed (fold (inj₁ client-end , ((S , T) , (win , def)) , refl , _)) = (S # T) , ε , win#def win def
  ⊢ᵢ-implies-succeed (fold (inj₁ oi-true , (_ , (ok-t , _)) , refl , pr)) =
    let Sys' , red-Sys' , Succ = ⊢ᵢ-implies-succeed (pr zero) in
    Sys' , sync (out ok-t) inp ◅ red-Sys' , Succ
  ⊢ᵢ-implies-succeed (fold (inj₁ oi-false , (_ , (ok-f , _)) , refl , pr)) =
    let Sys' , red-Sys' , Succ = ⊢ᵢ-implies-succeed (pr zero) in
    Sys' , sync (out ok-f) inp ◅ red-Sys' , Succ
  ⊢ᵢ-implies-succeed (fold (inj₁ oi-both , (_ , (ok-t , _)) , refl , pr)) =
    let Sys' , red-Sys' , Succ = ⊢ᵢ-implies-succeed (pr zero) in
    Sys' , sync (out ok-t) inp ◅ red-Sys' , Succ
  ⊢ᵢ-implies-succeed (fold (inj₁ io-true , (_ , (ok-t , _)) , refl , pr)) =
    let Sys' , red-Sys' , Succ = ⊢ᵢ-implies-succeed (pr zero) in
    Sys' , sync inp (out ok-t) ◅ red-Sys' , Succ
  ⊢ᵢ-implies-succeed (fold (inj₁ io-false , (_ , (ok-f , _)) , refl , pr)) =
    let Sys' , red-Sys' , Succ = ⊢ᵢ-implies-succeed (pr zero) in
    Sys' , sync inp (out ok-f) ◅ red-Sys' , Succ
  ⊢ᵢ-implies-succeed (fold (inj₁ io-both , (_ , (ok-t , _)) , refl , pr)) =
    let Sys' , red-Sys' , Succ = ⊢ᵢ-implies-succeed (pr zero) in
    Sys' , sync inp (out ok-t) ◅ red-Sys' , Succ
  ⊢ᵢ-implies-succeed (fold (inj₂ co-oi , (_ , ok-b) , refl , pr)) =
    let Sys' , red-Sys' , Succ = ⊢ᵢ-implies-succeed (pr zero) in
    Sys' , sync (out ok-b) inp ◅ red-Sys' , Succ
  ⊢ᵢ-implies-succeed (fold (inj₂ co-io , (_ , ok-b) , refl , pr)) =
    let Sys' , red-Sys' , Succ = ⊢ᵢ-implies-succeed (pr zero) in
    Sys' , sync inp (out ok-b) ◅ red-Sys' , Succ

  {- Soundness -}

  fc-sound : ∀{S T} → S ⊢ T → FairComplianceS (S # T)
  fc-sound fc ε = ⊢ᵢ-implies-succeed (fcoind-to-ind fc) 
  fc-sound fc (x ◅ red) with fc .CoInd⟦_⟧.unfold
  fc-sound fc (x ◅ red) | client-end , ((_ , (win , def)) , _) , refl , _ = ⊥-elim (success-not-reduce (win#def win def) x)
  fc-sound fc (sync (out ok-f) (inp {x = false}) ◅ red) | oi-true , ((_ , (_ , no-f)) , _) , refl , _ = ⊥-elim (no-f ok-f)
  fc-sound fc (sync (out _) (inp {x = true}) ◅ red) | oi-true , _ , refl , pr = fc-sound (pr zero) red
  fc-sound fc (sync (out _) (inp {x = false}) ◅ red) | oi-false , _ , refl , pr = fc-sound (pr zero) red
  fc-sound fc (sync (out ok-t) (inp {x = true}) ◅ red) | oi-false , ((_ , (_ , no-t)) , _) , refl , _ = ⊥-elim (no-t ok-t)
  fc-sound fc (sync (out _) (inp {x = false}) ◅ red) | oi-both , _ , refl , pr = fc-sound (pr (suc zero)) red
  fc-sound fc (sync (out _) (inp {x = true}) ◅ red) | oi-both , _ , refl , pr = fc-sound (pr zero) red
  fc-sound fc (sync (inp {x = false}) (out ok-f) ◅ red) | io-true , ((_ , (_ , no-f)) , _) , refl , _ = ⊥-elim (no-f ok-f)
  fc-sound fc (sync (inp {x = true}) (out _) ◅ red) | io-true , _ , refl , pr = fc-sound (pr zero) red
  fc-sound fc (sync (inp {x = false}) (out _) ◅ red) | io-false , _ , refl , pr = fc-sound (pr zero) red
  fc-sound fc (sync (inp {x = true}) (out ok-t) ◅ red) | io-false , ((_ , (_ , no-t)) , _) , refl , _ = ⊥-elim (no-t ok-t)
  fc-sound fc (sync (inp {x = false}) (out _) ◅ red) | io-both , _ , refl , pr = fc-sound (pr (suc zero)) red
  fc-sound fc (sync (inp {x = true}) (out _) ◅ red) | io-both , _ , refl , pr = fc-sound (pr zero) red

  {- Boundedness -}

  maysucceed-implies-⊢ᵢ : ∀{S T Sys} → Reductions (S # T) Sys → Success Sys → S ⊢ᵢ T
  maysucceed-implies-⊢ᵢ ε (win#def win def) = apply-ind (inj₁ client-end) (_ , (win , def)) λ ()
  maysucceed-implies-⊢ᵢ (sync (out ok) inp ◅ red) Succ =
    let rec = maysucceed-implies-⊢ᵢ red Succ in
    apply-ind (inj₂ co-oi) (_ , ok) λ{zero → rec}
  maysucceed-implies-⊢ᵢ (sync inp (out ok) ◅ red) Succ =
    let rec = maysucceed-implies-⊢ᵢ red Succ in
    apply-ind (inj₂ co-io) (_ , ok) λ{zero → rec}

  fc-bounded : ∀{S T} → FairComplianceS (S # T) → S ⊢ᵢ T
  fc-bounded fc =
    let _ , red-Sys , Succ = fc ε in
    maysucceed-implies-⊢ᵢ red-Sys Succ

  {- Consistency -}

  fc-consistent : ∀{S T} → FairComplianceS (S # T) → ISF[ FCompIS ] (λ{(S , T) → FairComplianceS (S # T)}) (S , T)
  fc-consistent fc with fc ε
  fc-consistent fc | .(_ # _) , ε , win#def win def = client-end , (_ , (win , def)) , refl , λ ()
  fc-consistent {out f} fc | _ , sync (out ok-f) (inp {x = false}) ◅ _ , _ with true ∈? f
  fc-consistent {out f} fc | _ , sync (out ok-f) (inp {_} {false}) ◅ _ , _ | no no-t =
    oi-false , (_ , (ok-f , no-t)) , refl , λ{zero → λ red → fc (sync (out ok-f) inp ◅ red)}
  fc-consistent {out f} fc | _ , sync (out ok-f) (inp {_} {false}) ◅ _ , _ | yes ok-t =
    let prems = λ{
              zero → λ red → fc (sync (out ok-t) inp ◅ red) ;
              (suc zero) → λ red → fc (sync (out ok-f) inp ◅ red)} in
    oi-both , (_ , (ok-t , ok-f)) , refl , prems
  fc-consistent {out f} fc | _ , sync (out ok-t) (inp {x = true}) ◅ _ , _ with false ∈? f
  fc-consistent {out f} fc | _ , sync (out ok-t) (inp {_} {true}) ◅ _ , _ | no no-f =
    oi-true , (_ , (ok-t , no-f)) , refl , λ{zero → λ red → fc (sync (out ok-t) inp ◅ red)}
  fc-consistent {out f} fc | _ , sync (out ok-t) (inp {_} {true}) ◅ _ , _ | yes ok-f =
    let prems = λ{
              zero → λ red → fc (sync (out ok-t) inp ◅ red) ;
              (suc zero) → λ red → fc (sync (out ok-f) inp ◅ red)} in
    oi-both , (_ , (ok-t , ok-f)) , refl , prems
  fc-consistent {_} {out g} fc | _ , sync (inp {x = false}) (out ok-f) ◅ _ , _ with true ∈? g
  fc-consistent {_} {out g} fc | _ , sync (inp {x = false}) (out ok-f) ◅ _ , _ | no no-t =
    io-false , (_ , (ok-f , no-t)) , refl , λ{zero → λ red → fc (sync inp (out ok-f) ◅ red)}
  fc-consistent {_} {out g} fc | _ , sync (inp {x = false}) (out ok-f) ◅ _ , _ | yes ok-t =
    let prems = λ{
              zero → λ red → fc (sync inp (out ok-t) ◅ red) ;
              (suc zero) → λ red → fc (sync inp (out ok-f) ◅ red)} in
    io-both , (_ , (ok-t , ok-f)) , refl , prems
  fc-consistent {_} {out g} fc | _ , sync (inp {x = true}) (out ok-t) ◅ _ , _ with false ∈? g
  fc-consistent {_} {out g} fc | _ , sync (inp {x = true}) (out ok-t) ◅ _ , _ | no no-f =
    io-true , (_ , (ok-t , no-f)) , refl , λ{zero → λ red → fc (sync inp (out ok-t) ◅ red)}
  fc-consistent {_} {out g} fc | _ , sync (inp {x = true}) (out ok-t) ◅ _ , _ | yes ok-f =
    let prems = λ{
              zero → λ red → fc (sync inp (out ok-t) ◅ red) ;
              (suc zero) → λ red → fc (sync inp (out ok-f) ◅ red)} in
    io-both , (_ , (ok-t , ok-f)) , refl , prems

  {- Completeness -}
  
  fc-complete : ∀{S T} → FairComplianceS (S # T) → S ⊢ T
  fc-complete =
    let S = λ{(S , T) → FairComplianceS (S # T)} in
    bounded-coind[ FCompIS , FCompCOIS ] S fc-bounded fc-consistent