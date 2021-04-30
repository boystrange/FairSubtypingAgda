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
open import Data.List as List
open import Data.Unit
open import Data.Fin
open import Data.Bool renaming (Bool to 𝔹)
open import Relation.Unary using (_∈_; _⊆_;_∉_)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Size
open import Codata.Thunk

open import is-lib.InfSys

module FairSubtyping-IS where
  open import Common

  message : Message 𝔹
  message = record{_?=_ = Data.Bool._≟_}

  
  open import SessionType message
  open import Session message
  open import Transitions message
  open import Convergence message
  open import Divergence message
  open import Discriminator message
  open import Action message using (Action)
  open import Subtyping message
  open import FairSubtyping message as FS
  open import HasTrace message
  open import Compliance message
  open import FairCompliance message
  open import Trace message
  open import FairCompliance-IS

  data FSubIS-RN : Set where
    nil-any end-def inp-inp : FSubIS-RN
    out-out-true out-out-false out-out-both : FSubIS-RN

  data FSubCOIS-RN : Set where
    co-conv : FSubCOIS-RN

  nil-any-r : FinMetaRule U
  nil-any-r .Ctx = SessionType
  nil-any-r .comp T =
    [] ,
    ------------------
    (nil , T)

  end-def-r : FinMetaRule U
  end-def-r .Ctx = Σ[ (T , S) ∈ SessionType × SessionType ] End T × Defined S
  end-def-r .comp ((T , S) , _) =
    [] ,
    ------------------
    (T , S)

  inp-inp-r : FinMetaRule U
  inp-inp-r .Ctx = Σ[ (f , g) ∈ Continuation × Continuation ] dom f ⊆ dom g
  inp-inp-r .comp ((f , g) , _) =
    (f true .force , g true .force) ∷ (f false .force , g false .force) ∷ [] ,
    ------------------
    (inp f , inp g)

  out-out-true-r : FinMetaRule U
  out-out-true-r .Ctx = Σ[ (f , g) ∈ Continuation × Continuation ] Witness g × dom g ⊆ dom f × true ∈ dom g × ¬ false ∈ dom g
  out-out-true-r .comp ((f , g) , _) =
    (f true .force , g true .force) ∷ [] ,
    ------------------
    (out f , out g)

  out-out-false-r : FinMetaRule U
  out-out-false-r .Ctx = Σ[ (f , g) ∈ Continuation × Continuation ] Witness g × dom g ⊆ dom f × false ∈ dom g × ¬ true ∈ dom g
  out-out-false-r .comp ((f , g) , _) =
    (f false .force , g false .force) ∷ [] ,
    ------------------
    (out f , out g)

  out-out-both-r : FinMetaRule U
  out-out-both-r .Ctx = Σ[ (f , g) ∈ Continuation × Continuation ] Witness g × dom g ⊆ dom f × true ∈ dom g × false ∈ dom g
  out-out-both-r .comp ((f , g) , _) =
    (f true .force , g true .force) ∷ (f false .force , g false .force) ∷ [] ,
    ------------------
    (out f , out g)

  co-conv-r : FinMetaRule U
  co-conv-r .Ctx = Σ[ (T , S) ∈ SessionType × SessionType ] T ↓ S
  co-conv-r .comp ((T , S) , _) =
    [] ,
    ------------------
    (T , S)

  FSubIS : IS U
  FSubIS .Names = FSubIS-RN
  FSubIS .rules nil-any = from nil-any-r
  FSubIS .rules end-def = from end-def-r
  FSubIS .rules inp-inp = from inp-inp-r
  FSubIS .rules out-out-true = from out-out-true-r
  FSubIS .rules out-out-false = from out-out-false-r
  FSubIS .rules out-out-both = from out-out-both-r

  FSubCOIS : IS U
  FSubCOIS .Names = FSubCOIS-RN
  FSubCOIS .rules co-conv = from co-conv-r

  _≤F_ : SessionType → SessionType → Set
  T ≤F S = FCoInd⟦ FSubIS , FSubCOIS ⟧ (T , S)

  _≤Fᵢ_ : SessionType → SessionType → Set
  T ≤Fᵢ S = Ind⟦ FSubIS ∪ FSubCOIS ⟧ (T , S)

  {- Specification using _⊢_ is correct wrt FairSubtypingS -}

  FSSpec-⊢ : U → Set
  FSSpec-⊢ (T , S) = ∀{R} → R ⊢ T → R ⊢ S
  
  spec-sound : ∀{T S} → FairSubtypingS T S → FSSpec-⊢ (T , S)
  spec-sound fs fc = fc-complete (fs (fc-sound fc))

  spec-complete : ∀{T S} → FSSpec-⊢ (T , S) → FairSubtypingS T S
  spec-complete fs fc = fc-sound (fs (fc-complete fc))

  ------------------------------------------------------

  {- Domain inclusion for Booleans -}

  dom-incl-single : ∀{f g} x → not x ∉ dom f → x ∈ dom f → x ∈ dom g → dom f ⊆ dom g
  dom-incl-single false _ _ ok {false} _ = ok
  dom-incl-single false no-x _ _ {true} ok = ⊥-elim (no-x ok)
  dom-incl-single true no-x _ _ {false} ok = ⊥-elim (no-x ok)
  dom-incl-single true _ _ ok {true} _ = ok

  dom-incl-empty : ∀{f g} → true ∉ dom f → false ∉ dom f → dom f ⊆ dom g
  dom-incl-empty no-x _ {true} ok = ⊥-elim (no-x ok)
  dom-incl-empty _ no-x {false} ok = ⊥-elim (no-x ok)

  dom-incl-full : ∀{f g} → true ∈ dom g → false ∈ dom g → dom f ⊆ dom g
  dom-incl-full {f} {g} ok-t ok-f {false} _ = ok-f
  dom-incl-full {f} {g} ok-t ok-f {true} _ = ok-t

  ¬dom-incl : ∀{f g} x → x ∈ dom f → x ∉ dom g → ¬ (dom f ⊆ dom g)
  ¬dom-incl b ok no-x incl = no-x (incl ok)
  
  -------------------------------------------------------

  {- Sample SessionType -}

  cont cont-true cont-false : SessionType → Continuation
  
  cont S false = box S
  cont S true = box S

  cont-true S false = box nil
  cont-true S true = box S

  cont-false S false = box S
  cont-false S true = box nil

  cont-ch : 𝔹 → SessionType → Continuation
  cont-ch false S = cont-false S
  cont-ch true S = cont-true S

  R-out-t R-out-f R-in-t R-in-f R-in-both : SessionType
  R-out-t = out (cont-true win)
  R-out-f = out (cont-false win)
  R-in-t = inp (cont-true win)
  R-in-f = inp (cont-false win)
  R-in-both = inp (cont win)

  send-R : 𝔹 → SessionType → SessionType
  send-R b S = out (cont-ch b S)

  rec-R : SessionType → SessionType
  rec-R S = inp (cont S) 

  rec-R' : 𝔹 → SessionType → SessionType
  rec-R' false S = inp λ{true → box win ; false → box S}
  rec-R' true S = inp λ{true → box S ; false → box win}

  win-not-reduce : ∀{S S' α} → Win S → ¬ (Transition S α S')
  win-not-reduce (out e) (out ok) = ⊥-elim (e _ ok)

  R-out-t-comp : ∀{f} → true ∈ dom f → FairComplianceS (R-out-t # inp f)
  R-out-t-comp {f} ok-t ε = (win # f true .force) , sync (out out) inp ◅ ε , win#def Win-win ok-t
  R-out-t-comp {f} ok-t (sync (out _) (inp {x = true}) ◅ ε) = (win # f true .force) , ε , win#def Win-win ok-t
  R-out-t-comp {f} ok-t (sync (out _) (inp {x = true}) ◅ sync red-win _ ◅ _) = ⊥-elim (win-not-reduce Win-win red-win)

  R-out-t-⊢-inp : ∀{f} → true ∈ dom f → R-out-t ⊢ inp f
  R-out-t-⊢-inp ok-t = fc-complete (R-out-t-comp ok-t)

  R-out-f-comp : ∀{f} → false ∈ dom f → FairComplianceS (R-out-f # inp f)
  R-out-f-comp {f} ok-f ε = (win # f false .force) , sync (out out) inp ◅ ε , win#def Win-win ok-f
  R-out-f-comp {f} ok-f (sync (out _) (inp {x = false}) ◅ ε) = (win # f false .force) , ε , win#def Win-win ok-f
  R-out-f-comp {f} ok-f (sync (out _) (inp {x = false}) ◅ sync red-win _ ◅ _) = ⊥-elim (win-not-reduce Win-win red-win)

  R-out-f-⊢-inp : ∀{f} → false ∈ dom f → R-out-f ⊢ inp f
  R-out-f-⊢-inp ok-f = fc-complete (R-out-f-comp ok-f)

  R-in-both-comp : ∀{f x} → x ∈ dom f → FairComplianceS (R-in-both # out f)
  R-in-both-comp {f} {false} ok ε = (win # f false .force) , sync inp (out ok) ◅ ε , win#def Win-win ok
  R-in-both-comp {f} {true} ok ε = (win # f true .force) , sync inp (out ok) ◅ ε , win#def Win-win ok
  R-in-both-comp {f} {false} ok (sync (inp {x = .false}) (out {x = false} _) ◅ ε) = win # f false .force , ε  , win#def Win-win ok
  R-in-both-comp {f} {false} ok (sync (inp {x = .false}) (out {x = false} _) ◅ sync red-win _ ◅ red) = ⊥-elim (win-not-reduce Win-win red-win)
  R-in-both-comp {f} {false} ok (sync (inp {x = .true}) (out {x = true} ok-t) ◅ ε) = win # f true .force , ε , win#def Win-win ok-t
  R-in-both-comp {f} {false} ok (sync (inp {x = .true}) (out {x = true} ok-t) ◅ sync red-win _ ◅ red) = ⊥-elim (win-not-reduce Win-win red-win)
  R-in-both-comp {f} {true} ok (sync (inp {x = .false}) (out {x = false} ok-f) ◅ ε) = win # f false .force , ε  , win#def Win-win ok-f
  R-in-both-comp {f} {true} ok (sync (inp {x = .false}) (out {x = false} ok-f) ◅ sync red-win _ ◅ red) = ⊥-elim (win-not-reduce Win-win red-win)
  R-in-both-comp {f} {true} ok (sync (inp {x = .true}) (out {x = true} _) ◅ ε) = win # f true .force , ε , win#def Win-win ok
  R-in-both-comp {f} {true} ok (sync (inp {x = .true}) (out {x = true} _) ◅ sync red-win _ ◅ red) = ⊥-elim (win-not-reduce Win-win red-win)

  R-in-both-⊢-out : ∀{f x} → x ∈ dom f → R-in-both ⊢ out f
  R-in-both-⊢-out ok = fc-complete (R-in-both-comp ok)

  R-in-t-comp : ∀{f} → true ∈ dom f → false ∉ dom f → FairComplianceS (R-in-t # out f)
  R-in-t-comp {f} ok no-f ε = (win # f true .force) , sync inp (out ok) ◅ ε , win#def Win-win ok
  R-in-t-comp {f} ok no-f (sync (inp {x = .false}) (out {x = false} ok-f) ◅ red) = ⊥-elim (no-f ok-f)
  R-in-t-comp {f} ok no-f (sync (inp {x = .true}) (out {x = true} _) ◅ ε) = (win # f true .force) , ε , win#def Win-win ok
  R-in-t-comp {f} ok no-f (sync (inp {x = .true}) (out {x = true} _) ◅ sync red-win _ ◅ red) = ⊥-elim (win-not-reduce Win-win red-win)

  R-in-t-⊢-out : ∀{f} → true ∈ dom f → false ∉ dom f → R-in-t ⊢ out f
  R-in-t-⊢-out ok no-f = fc-complete (R-in-t-comp ok no-f)

  R-in-f-comp : ∀{f} → false ∈ dom f → true ∉ dom f → FairComplianceS (R-in-f # out f)
  R-in-f-comp {f} ok no-t ε = (win # f false .force) , sync inp (out ok) ◅ ε , win#def Win-win ok
  R-in-f-comp {f} ok no-t (sync (inp {x = .true}) (out {x = true} ok-t) ◅ red) = ⊥-elim (no-t ok-t)
  R-in-f-comp {f} ok no-t (sync (inp {x = .false}) (out {x = false} _) ◅ ε) = (win # f false .force) , ε , win#def Win-win ok
  R-in-f-comp {f} ok no-t (sync (inp {x = .false}) (out {x = false} _) ◅ sync red-win _ ◅ red) = ⊥-elim (win-not-reduce Win-win red-win)

  R-in-f-⊢-out : ∀{f} → false ∈ dom f → true ∉ dom f → R-in-f ⊢ out f
  R-in-f-⊢-out ok no-t = fc-complete (R-in-f-comp ok no-t)

  end-def-fcomp : ∀{S} → Defined S → FairComplianceS (win # S)
  end-def-fcomp def ε = _ , ε , win#def Win-win def
  end-def-fcomp _ (sync red-win _ ◅ _) = ⊥-elim (win-not-reduce Win-win red-win)

  send-R-⊢-inp : ∀{R f} x → Defined R → R ⊢ f x .force → send-R x R ⊢ inp f
  send-R-⊢-inp false def prem = apply-fcoind oi-false (_ , (def , λ ())) λ{zero → prem}
  send-R-⊢-inp true def prem = apply-fcoind oi-true (_ , (def , λ ())) λ{zero → prem}

  rec-R-⊢-out : ∀{R f} x → x ∈ dom f → ¬ (not x ∈ dom f) → R ⊢ f x .force → rec-R R ⊢ out f
  rec-R-⊢-out false ok-x no-x prem = apply-fcoind io-false (_ , (ok-x , no-x)) λ{zero → prem}
  rec-R-⊢-out true ok-x no-x prem = apply-fcoind io-true (_ , (ok-x , no-x)) λ{zero → prem}

  rec-R'-⊢-out : ∀{R f} x → x ∈ dom f → not x ∈ dom f → R ⊢ f x .force → rec-R' x R ⊢ out f
  rec-R'-⊢-out false ok ok' prem = 
    apply-fcoind io-both (_ , (ok' , ok)) λ{zero → apply-fcoind client-end (_ , (Win-win , ok')) λ () ; (suc zero) → prem}
  rec-R'-⊢-out true ok ok' prem = 
    apply-fcoind io-both (_ , (ok , ok')) λ{zero → prem ; (suc zero) → apply-fcoind client-end (_ , (Win-win , ok')) λ ()}

  send-R-reduces : ∀{S} b → Defined S → Transition (send-R b S) (O b) S
  send-R-reduces false def = out def
  send-R-reduces true def = out def

  rec-R-reduces : ∀{S} b → Transition (rec-R S) (I b) S
  rec-R-reduces false = inp
  rec-R-reduces true = inp

  rec-R'-reduces : ∀{S} b → Transition (rec-R' b S) (I b) S
  rec-R'-reduces false = inp
  rec-R'-reduces true = inp

  -----------------------------------------------------------

  {- General Properties -}

  ¬IO-fsub : ∀{f g x} → x ∈ dom f → ¬ FairSubtypingS (inp f) (out g)
  ¬IO-fsub {x = false} ok fs with fs (R-out-f-comp ok) ε
  ... | _ , ε , win#def (out e) _ = ⊥-elim (e false out)
  ... | _ , sync () (out _) ◅ _ , _
  ¬IO-fsub {x = true} ok fs with fs (R-out-t-comp ok) ε
  ... | _ , ε , win#def (out e) _ = ⊥-elim (e true out)
  ... | _ , sync () (out _) ◅ _ , _

  ¬OI-fsub : ∀{f g x} → x ∈ dom f → ¬ FairSubtypingS (out f) (inp g)
  ¬OI-fsub ok fs with fs (R-in-both-comp ok) ε
  ... | _ , ε , win#def () _
  ... | _ , sync () inp ◅ _ , _

  ¬Inil-fsub : ∀{f} → ¬ (FairSubtypingS (inp f) nil)
  ¬Inil-fsub fs with fs (end-def-fcomp inp) ε
  ... | _ , ε , win#def _ ()
  ... | _ , sync _ () ◅ _ , _

  ¬Onil-fsub : ∀{f} → ¬ (FairSubtypingS (out f) nil)
  ¬Onil-fsub fs with fs (end-def-fcomp out) ε
  ... | _ , ε , win#def _ ()
  ... | _ , sync _ () ◅ _ , _

  {- 
    Transitions preserve Specification
    Proof scheme : 
      1. Find a client leading to R and its compliance proof
        a. (inp {x = t}) inp: go to R on t branch, nil otherwise
        b. (out f) with only x ∈ dom f: go to R on both branches
        c. (out f) with t/¬t ∈ dom f: go to R on t branch, win otherwise
      2. Apply fair Subtyping
      3. According to the applied rule, find the right premise
  -}

  transition-preserves-FSSpec : ∀{T T' S S' α} → FSSpec-⊢ (T , S) → Transition T α T' → Transition S α S' → FSSpec-⊢ (T' , S')
  transition-preserves-FSSpec {inp f} fs (inp {x = false}) tr-S {R} fc with Defined? R
  transition-preserves-FSSpec {inp f} fs (inp {x = false}) tr-S {R} fc | yes def-R with fs (send-R-⊢-inp false def-R fc) .CoInd⟦_⟧.unfold
  transition-preserves-FSSpec {inp f} {S' = _} {I false} fs (inp {_} {.false}) tr-S {R} fc | yes def-R | client-end , ((_ , (win , _)) , _) , refl , _ = ⊥-elim (win-not-reduce win (send-R-reduces false def-R))
  transition-preserves-FSSpec {inp f} {S' = _} {I false} fs (inp {_} {.false}) inp {R} fc | yes def-R | oi-true , ((_ , (() , _)) , _) , refl , _
  transition-preserves-FSSpec {inp f} {S' = _} {I false} fs (inp {_} {.false}) inp {R} fc | yes def-R | oi-false , _ , refl , pr = pr zero
  transition-preserves-FSSpec {inp f} {S' = _} {I false} fs (inp {_} {.false}) inp {R} fc | yes def-R | oi-both , ((_ , (() , _)) , _) , refl , _
  transition-preserves-FSSpec {inp f} fs (inp {x = false}) tr-S {R} fc | no ¬def-R = ⊥-elim (¬nil-⊢ (subst (λ T → T ⊢ _) (not-def->nil ¬def-R) fc))
  transition-preserves-FSSpec {inp f} fs (inp {x = true}) tr-S {R} fc with Defined? R
  transition-preserves-FSSpec {inp f} fs (inp {x = true}) tr-S {R} fc | yes def-R with fs (send-R-⊢-inp true def-R fc) .CoInd⟦_⟧.unfold
  transition-preserves-FSSpec {inp f} {S' = _} {I true} fs (inp {_} {.true}) tr-S {R} fc | yes def-R | client-end , ((_ , (win , _)) , _) , refl , _ = ⊥-elim (win-not-reduce win (send-R-reduces true def-R))
  transition-preserves-FSSpec {inp f} {S' = _} {I true} fs (inp {_} {.true}) inp {R} fc | yes def-R | oi-true , _ , refl , pr = pr zero
  transition-preserves-FSSpec {inp f} {S' = _} {I true} fs (inp {_} {.true}) inp {R} fc | yes def-R | oi-false , ((_ , (() , _)) , _) , refl , _ 
  transition-preserves-FSSpec {inp f} {S' = _} {I true} fs (inp {_} {.true}) inp {R} fc | yes def-R | oi-both , ((_ , (_ , ())) , _) , refl , _
  transition-preserves-FSSpec {inp f} fs (inp {x = true}) tr-S {R} fc | no ¬def-R = ⊥-elim (¬nil-⊢ (subst (λ T → T ⊢ _) (not-def->nil ¬def-R) fc))
  transition-preserves-FSSpec {out f} fs (out {x = t} ok) tr-S {R} fc with not t ∈? f
  transition-preserves-FSSpec {out f} fs (out {x = t} ok) (out ok') {R} fc | yes ok-not-x with fs (rec-R'-⊢-out t ok ok-not-x fc) .CoInd⟦_⟧.unfold
  transition-preserves-FSSpec {out f} fs (out {x = t} ok) (out ok') {R} fc | yes ok-not-x | client-end , ((_ , (win , _)) , _) , refl , _ = ⊥-elim (win-not-reduce win ((rec-R'-reduces t)))
  transition-preserves-FSSpec {out f} {_} {_} {_} {O false} fs (out {x = false} ok) (out ok') {R} fc | yes ok-not-x | io-true , ((_ , (_ , no-f)) , _) , refl , _ =  ⊥-elim (no-f ok')
  transition-preserves-FSSpec {out f} {_} {_} {_} {O true} fs (out {x = true} ok) (out ok') {R} fc | yes ok-not-x | io-true , _ , refl , pr = pr zero
  transition-preserves-FSSpec {out f} {_} {_} {_} {O false} fs (out {x = false} ok) (out ok') {R} fc | yes ok-not-x | io-false , _ , refl , pr = pr zero
  transition-preserves-FSSpec {out f} {_} {_} {_} {O true} fs (out {x = true} ok) (out ok') {R} fc | yes ok-not-x | io-false , ((_ , (_ , no-t)) , _) , refl , _ = ⊥-elim (no-t ok')
  transition-preserves-FSSpec {out f} fs (out {x = false} ok) (out ok') {R} fc | yes ok-not-x | io-both , _ , refl , pr = pr (suc zero)
  transition-preserves-FSSpec {out f} fs (out {x = true} ok) (out ok') {R} fc | yes ok-not-x | io-both , _ , refl , pr = pr zero
  transition-preserves-FSSpec {out f} fs (out {x = t} ok) tr-S {R} fc | no no-not-x with fs (rec-R-⊢-out t ok no-not-x fc) .CoInd⟦_⟧.unfold
  transition-preserves-FSSpec {out f} fs (out {x = t} ok) tr-S {R} fc | no no-not-x | client-end , ((_ , (win , _)) , _) , refl , _ = ⊥-elim (win-not-reduce win (rec-R-reduces t))
  transition-preserves-FSSpec {out f} {S' = _} {O false} fs (out {x = false} ok) (out {x = .false} ok') {R} fc | no no-not-x | io-true , ((_ , (ok-t , no-f)) , _) , refl , _ = ⊥-elim (no-f ok')
  transition-preserves-FSSpec {out f} {S' = _} {O true} fs (out {x = true} ok) (out {x = .true} ok') {R} fc | no no-not-x | io-true , _ , refl , pr = pr zero
  transition-preserves-FSSpec {out f} {S' = _} {O false} fs (out {x = false} ok) (out {x = .false} ok') {R} fc | no no-not-x | io-false , _ , refl , pr = pr zero
  transition-preserves-FSSpec {out f} {S' = _} {O true} fs (out {x = true} ok) (out {x = .true} ok') {R} fc | no no-not-x | io-false , ((_ , (ok-f , no-t)) , _) , refl , _ = ⊥-elim (no-t ok')
  transition-preserves-FSSpec {out f} {S' = _} {O false} fs (out {x = false} ok) (out {x = .false} ok') {R} fc | no no-not-x | io-both , ((_ , (ok-t , ok-f)) , _) , refl , pr = pr (suc zero)
  transition-preserves-FSSpec {out f} {S' = _} {O true} fs (out {x = true} ok) (out {x = .true} ok') {R} fc | no no-not-x | io-both , ((_ , (ok-t , ok-f)) , _) , refl , pr = pr zero

  transition-preserves-FairSubSpec : ∀{T T' S S' α} → FairSubtypingS T S → Transition T α T' → Transition S α S' → FairSubtypingS T' S'
  transition-preserves-FairSubSpec fs tr-T tr-S = spec-complete (transition-preserves-FSSpec (spec-sound fs) tr-T tr-S)

  -- Inputs without domain inclusion
  ¬II-fsub-no-dom-incl : ∀{f g} → ¬ (dom f ⊆ dom g) → ¬ (FairSubtypingS (inp f) (inp g)) 
  ¬II-fsub-no-dom-incl {f} {g} no-incl fs with true ∈? f | false ∈? f
  ¬II-fsub-no-dom-incl {f} {g} no-incl fs | yes ok-t | yes ok-f with true ∈? g
  ¬II-fsub-no-dom-incl {f} {g} no-incl fs | yes ok-t | yes ok-f | yes ok-t-g with false ∈? g
  ¬II-fsub-no-dom-incl {f} {g} no-incl fs | yes ok-t | yes ok-f | yes ok-t-g | yes ok-f-g =
    no-incl (dom-incl-full {f} {g} ok-t-g ok-f-g)
  ¬II-fsub-no-dom-incl {f} {g} no-incl fs | yes ok-t | yes ok-f | yes ok-t-g | no no-f-g with fs (R-out-f-comp ok-f) ε
  ... | _ , ε , win#def (out e) _ = e false out
  ... | _ , sync (out _) (inp {x = false}) ◅ ε , win#def _ def = no-f-g def
  ... | _ , sync (out _) (inp {x = false}) ◅ sync _ r ◅ red , Succ = no-f-g (transition->defined r)
  ¬II-fsub-no-dom-incl {f} {g} no-incl fs | yes ok-t | yes ok-f | no no-t-g with fs (R-out-t-comp ok-t) ε
  ... | _ , ε , win#def (out e) _ = e true out
  ... | _ , sync (out _) (inp {x = true}) ◅ ε , win#def _ def = no-t-g def
  ... | _ , sync (out _) (inp {x = true}) ◅ sync _ r ◅ red , Succ = no-t-g (transition->defined r)
  ¬II-fsub-no-dom-incl {f} {g} no-incl fs | no no-t | yes ok-f with false ∈? g
  ¬II-fsub-no-dom-incl {f} {g} no-incl fs | no no-t | yes ok-f | yes ok-f-g =
    no-incl (dom-incl-single {f} {g} false no-t ok-f ok-f-g)   
  ¬II-fsub-no-dom-incl {f} {g} no-incl fs | no no-t | yes ok-f | no no-f-g with fs (R-out-f-comp ok-f) ε
  ... | _ , ε , win#def (out e) _ = e false out
  ... | _ , sync (out _) (inp {x = false}) ◅ ε , win#def _ def = no-f-g def
  ... | _ , sync (out _) (inp {x = false}) ◅ sync _ r ◅ red , Succ = no-f-g (transition->defined r)
  ¬II-fsub-no-dom-incl {f} {g} no-incl fs | yes ok-t | no no-f with true ∈? g
  ¬II-fsub-no-dom-incl {f} {g} no-incl fs | yes ok-t | no no-f | yes ok-t-g = 
    no-incl (dom-incl-single {f} {g} true no-f ok-t ok-t-g)
  ¬II-fsub-no-dom-incl {f} {g} no-incl fs | yes ok-t | no no-f | no no-t-g with fs (R-out-t-comp ok-t) ε
  ... | _ , ε , win#def (out e) _ = e true out
  ... | _ , sync (out _) (inp {x = true}) ◅ ε , win#def _ def = no-t-g def
  ... | _ , sync (out _) (inp {x = true}) ◅ sync _ r ◅ red , Succ = no-t-g (transition->defined r)
  ¬II-fsub-no-dom-incl {f} {g} no-incl fs | no no-t | no no-f = no-incl (dom-incl-empty {f} {g} no-t no-f)

  ¬II-fsspec : ∀{f g} → ¬ (dom f ⊆ dom g) → ¬ (FSSpec-⊢ (inp f , inp g))
  ¬II-fsspec no-incl fs = ¬II-fsub-no-dom-incl no-incl (spec-complete fs) 

  -- Fair Subtyping between outputs implies end or dom inclusion
  FSSpec->end-incl : ∀{f g} → FSSpec-⊢ (out f , out g) → End (out f) ⊎ Witness g × dom g ⊆ dom f
  FSSpec->end-incl {f} {g} fs with true ∈? f | false ∈? f
  FSSpec->end-incl {f} {g} fs | yes ok-t | yes ok-f with fs (R-in-both-⊢-out ok-f) .CoInd⟦_⟧.unfold
  ... | client-end , ((_ , (() , _)) , _) , refl , _
  ... | io-true , ((_ , (ok-t-g , _)) , _) , refl , _ = inj₂ ((true , ok-t-g) , dom-incl-full {g} {f} ok-t ok-f)
  ... | io-false , ((_ , (ok-f-g , _)) , _) , refl , _ = inj₂ ((false , ok-f-g) , dom-incl-full {g} {f} ok-t ok-f)
  ... | io-both , ((_ , (ok-t-g , _)) , _) , refl , pr = inj₂ ((true , ok-t-g) , dom-incl-full {g} {f} ok-t ok-f)
  FSSpec->end-incl {f} {g} fs | no no-t | yes ok-f with fs (R-in-f-⊢-out ok-f no-t) .CoInd⟦_⟧.unfold
  ... | client-end , ((_ , (() , _)) , _) , refl , _
  ... | io-true , _ , refl , pr = ⊥-elim (¬nil-⊢ (pr zero))
  ... | io-false , ((_ , (ok-f-g , no-t-g)) , _) , refl , _ = inj₂ ((false , ok-f-g) , (dom-incl-single {g} {f} false no-t-g ok-f-g ok-f))
  ... | io-both , _ , refl , pr = ⊥-elim (¬nil-⊢ (pr zero))
  FSSpec->end-incl {f} {g} fs | yes ok-t | no no-f with fs (R-in-t-⊢-out ok-t no-f) .CoInd⟦_⟧.unfold
  ... | client-end , ((_ , (() , _)) , _) , refl , _
  ... | io-true , ((_ , (ok-t-g , no-f-g)) , _) , refl , _ = inj₂ ((true , ok-t-g) , (dom-incl-single {g} {f} true no-f-g ok-t-g ok-t))
  ... | io-false , _ , refl , pr = ⊥-elim (¬nil-⊢ (pr zero))
  ... | io-both , _ , refl , pr = ⊥-elim (¬nil-⊢ (pr (suc zero)))
  FSSpec->end-incl {f} {g} fs | no no-t | no no-f = inj₁ (out λ{true → no-t ; false → no-f})

  -- FSSpec implies Unfair Subtyping
  fsspec->sub : ∀{T S} → FSSpec-⊢ (T , S) → ∀{i} → Sub T S i
  fsspec->sub {nil} {_} _ = nil<:any
  fsspec->sub {inp f} {nil} fs = ⊥-elim (¬Inil-fsub (spec-complete fs))
  fsspec->sub {inp f} {inp g} fs with true ∈? f | false ∈? f
  fsspec->sub {inp f} {inp g} fs | yes ok-t | yes ok-f with true ∈? g
  fsspec->sub {inp f} {inp g} fs | yes ok-t | yes ok-f | yes ok-t-g with false ∈? g
  ... | yes ok-f-g = inp<:inp (dom-incl-full {f} {g} ok-t-g ok-f-g) F
    where
      F : ∀ x → Thunk (Sub (f x .force) (g x .force)) _
      F false = λ where .force → fsspec->sub (transition-preserves-FSSpec fs inp inp)
      F true = λ where .force → fsspec->sub (transition-preserves-FSSpec fs inp inp)
  ... | no no-f-g = ⊥-elim (¬II-fsspec (¬dom-incl {f} {g} _ ok-f no-f-g) fs)
  fsspec->sub {inp f} {inp g} fs | yes ok-t | yes ok-f | no no-t-g = 
    ⊥-elim (¬II-fsspec (¬dom-incl {f} {g} _ ok-t no-t-g) fs)
  fsspec->sub {inp f} {inp g} fs | no no-t | yes ok-f with false ∈? g
  ... | yes ok-f-g = inp<:inp (dom-incl-single {f} {g} _ no-t ok-f ok-f-g) F
    where
      F : ∀ x → Thunk (Sub (f x .force) (g x .force)) _
      F false = λ where .force → fsspec->sub (transition-preserves-FSSpec fs inp inp)
      F true = λ where .force → fsspec->sub (transition-preserves-FSSpec fs inp inp)
  ... | no no-f-g = ⊥-elim (¬II-fsspec (¬dom-incl {f} {g} _ ok-f no-f-g) fs)
  fsspec->sub {inp f} {inp g} fs | yes ok-t | no no-f with true ∈? g
  ... | yes ok-t-g = inp<:inp (dom-incl-single {f} {g} _ no-f ok-t ok-t-g) F
    where
      F : ∀ x → Thunk (Sub (f x .force) (g x .force)) _
      F false = λ where .force → fsspec->sub (transition-preserves-FSSpec fs inp inp)
      F true = λ where .force → fsspec->sub (transition-preserves-FSSpec fs inp inp)
  ... | no no-t-g = ⊥-elim (¬II-fsspec (¬dom-incl {f} {g} _ ok-t no-t-g) fs)
  fsspec->sub {inp f} {inp g} fs | no no-t | no no-f = 
    inp<:inp (dom-incl-empty {f} {g} no-t no-f) F
    where
      F : ∀ x → Thunk (Sub (f x .force) (g x .force)) _
      F false = λ where .force → fsspec->sub (transition-preserves-FSSpec fs inp inp)
      F true = λ where .force → fsspec->sub (transition-preserves-FSSpec fs inp inp)
  fsspec->sub {inp f} {out g} fs with true ∈? f
  ... | yes ok-t = ⊥-elim (¬IO-fsub ok-t (spec-complete fs))
  ... | no no-t with false ∈? f
  ... | yes ok-f = ⊥-elim (¬IO-fsub ok-f (spec-complete fs))
  ... | no no-f = end<:def (inp (λ{true → no-t ; false → no-f})) out
  fsspec->sub {out f} {nil} fs = ⊥-elim (¬Onil-fsub (spec-complete fs))
  fsspec->sub {out f} {inp g} fs with true ∈? f
  ... | yes ok-t = ⊥-elim (¬OI-fsub ok-t (spec-complete fs))
  ... | no no-t with false ∈? f
  ... | yes ok-f = ⊥-elim (¬OI-fsub ok-f (spec-complete fs))
  ... | no no-f = end<:def (out (λ{true → no-t ; false → no-f})) inp
  fsspec->sub {out f} {out g} fs with FSSpec->end-incl fs
  fsspec->sub {out f} {out g} fs | inj₁ end = end<:def end out
  fsspec->sub {out f} {out g} fs | inj₂ ((false , ok-f) , dom-incl) with true ∈? g
  ... | yes ok-t = out<:out (false , ok-f) dom-incl F
    where
      F : ∀{x} → x ∈ dom g → Thunk (Sub (f x .force) (g x .force)) _
      F {false} _ = λ where .force → fsspec->sub (transition-preserves-FSSpec fs (out (dom-incl ok-f)) (out ok-f))
      F {true} _ = λ where .force → fsspec->sub (transition-preserves-FSSpec fs (out (dom-incl ok-t)) (out ok-t))
  ... | no no-t = out<:out (false , ok-f) dom-incl F
    where
      F : ∀{x} → x ∈ dom g → Thunk (Sub (f x .force) (g x .force)) _
      F {false} _ = λ where .force → fsspec->sub (transition-preserves-FSSpec fs (out (dom-incl ok-f)) (out ok-f))
      F {true} ok-t = ⊥-elim (no-t ok-t)
  fsspec->sub {out f} {out g} fs | inj₂ ((true , ok-t) , dom-incl) with false ∈? g
  ... | yes ok-f = out<:out (true , ok-t) dom-incl F
    where
      F : ∀{x} → x ∈ dom g → Thunk (Sub (f x .force) (g x .force)) _
      F {false} _ = λ where .force → fsspec->sub (transition-preserves-FSSpec fs (out (dom-incl ok-f)) (out ok-f))
      F {true} _ = λ where .force → fsspec->sub (transition-preserves-FSSpec fs (out (dom-incl ok-t)) (out ok-t))
  ... | no no-f = out<:out (true , ok-t) dom-incl F
    where
      F : ∀{x} → x ∈ dom g → Thunk (Sub (f x .force) (g x .force)) _
      F {false} ok-f = ⊥-elim (no-f ok-f)
      F {true} _ = λ where .force → fsspec->sub (transition-preserves-FSSpec fs (out (dom-incl ok-t)) (out ok-t))

-----------------------------------------------------------------

  {- Soundness -}

  nil-no-trace : ∀{ϕ} → ¬ (nil HasTrace ϕ)
  nil-no-trace (.(inp _) , inp , step () _)
  nil-no-trace (.(out _) , out , step () _)

  nil-converges : ∀{S} → nil ↓ S
  nil-converges {S} = converge λ tφ _ → ⊥-elim (nil-no-trace tφ)

  empty-inp-has-empty-trace : ∀{f ϕ} → EmptyContinuation f → (inp f) HasTrace ϕ → ϕ ≡ []
  empty-inp-has-empty-trace e (_ , _ , refl) = refl
  empty-inp-has-empty-trace {f} e (_ , _ , step (inp {x = x}) reds) with Defined? (f x .force)
  empty-inp-has-empty-trace {f} e (_ , def , step (inp {x = _}) refl) | no ¬def = ⊥-elim (¬def def)
  empty-inp-has-empty-trace {f} e (_ , _ , step (inp {x = _}) (step t _)) | no ¬def = ⊥-elim (¬def (transition->defined t))
  ... | yes def = ⊥-elim (e _ def)

  empty-out-has-empty-trace : ∀{f ϕ} → EmptyContinuation f → (out f) HasTrace ϕ → ϕ ≡ []
  empty-out-has-empty-trace e (_ , _ , refl) = refl
  empty-out-has-empty-trace e (_ , _ , step (out def) _) = ⊥-elim (e _ def)

  end-converges : ∀{T S} → End T → Defined S → T ↓ S
  end-converges (inp e) def = converge λ tφ sφ → 
    let eq = empty-inp-has-empty-trace e tφ in 
    ⊥-elim (sφ (subst (λ ψ → _ HasTrace ψ) (sym eq) (_ , def , refl)))
  end-converges (out e) def = converge λ tφ sφ →
    let eq = empty-out-has-empty-trace e tφ in 
    ⊥-elim (sφ (subst (λ ψ → _ HasTrace ψ) (sym eq) (_ , def , refl)))

  trace-after-in : ∀{f x ϕ} → (inp f) HasTrace (I x ∷ ϕ) → (f x .force) HasTrace ϕ
  trace-after-in (_ , def , step inp red) = _ , def , red

  not-trace-after-in : ∀{f x ϕ} → ¬ ((inp f) HasTrace (I x ∷ ϕ)) → ¬ ((f x .force) HasTrace ϕ)
  not-trace-after-in no-ht ht = no-ht (inp-has-trace ht)

  pre-conv-back : ∀{f g} 
    → PreConvergence _↓_ (f true .force) (g true .force) 
    → PreConvergence _↓_ (f false .force) (g false .force)
    → PreConvergence _↓_ (inp f) (inp g)
  pre-conv-back conv-t conv-f {[]} ok-tr no-tr = ⊥-elim (no-tr (_ , inp , refl))
  pre-conv-back conv-t conv-f {I false ∷ tr} ok-tr no-tr = 
    let ψ , a , (pref , ok-tr-l , ok-tr-r , pr) = conv-f (trace-after-in ok-tr) (not-trace-after-in no-tr) in
    I false ∷ ψ , a , (some pref , inp-has-trace ok-tr-l , inp-has-trace ok-tr-r , pr)
  pre-conv-back conv-t conv-f {I true ∷ tr} ok-tr no-tr =
    let ψ , a , (pref , ok-tr-l , ok-tr-r , pr) = conv-t (trace-after-in ok-tr) (not-trace-after-in no-tr) in
    I true ∷ ψ , a , (some pref , inp-has-trace ok-tr-l , inp-has-trace ok-tr-r , pr)
  pre-conv-back _ _ {O _ ∷ _} (_ , _ , step () _) _
  
  ≤Fᵢ-to-↓ : ∀{T S} → T ≤Fᵢ S → T ↓ S
  ≤Fᵢ-to-↓ {T} {S} (fold (inj₁ nil-any , _ , refl , _)) = nil-converges
  ≤Fᵢ-to-↓ {T} {S} (fold (inj₁ end-def , (_ , (end , def)) , refl , _)) = end-converges end def
  ≤Fᵢ-to-↓ {inp f} {inp g} (fold (inj₁ inp-inp , _ , refl , pr)) with ≤Fᵢ-to-↓ (pr zero) | ≤Fᵢ-to-↓ (pr (suc zero))
  ... | converge conv-t | converge conv-f = converge (pre-conv-back conv-t conv-f)
  ≤Fᵢ-to-↓ {out f} {out g} (fold (inj₁ out-out-true , (_ , (_ , dom-incl , ok-t , _)) , refl , pr)) = 
    let rec = ≤Fᵢ-to-↓ (pr zero) in
    let f-step = f true .force , dom-incl ok-t , step (out (dom-incl ok-t)) refl in
    let g-step = g true .force , ok-t , step (out ok-t) refl in
    converge λ tφ sφ → [] , true , none , (f-step , g-step , rec)
  ≤Fᵢ-to-↓ {out f} {out g} (fold (inj₁ out-out-false , (_ , (_ , dom-incl , ok-f , _)) , refl , pr)) = 
    let rec = ≤Fᵢ-to-↓ (pr zero) in
    let f-step = f false .force , dom-incl ok-f , step (out (dom-incl ok-f)) refl in
    let g-step = g false .force , ok-f , step (out ok-f) refl in
    converge λ tφ sφ → [] , false , none , (f-step , g-step , rec)
  ≤Fᵢ-to-↓ {out f} {out g} (fold (inj₁ out-out-both , (_ , (_ , dom-incl , ok-t , _)) , refl , pr)) = 
    let rec = ≤Fᵢ-to-↓ (pr zero) in
    let f-step = f true .force , dom-incl ok-t , step (out (dom-incl ok-t)) refl in
    let g-step = g true .force , ok-t , step (out ok-t) refl in
    converge λ tφ sφ → [] , true , none , (f-step , g-step , rec)
  ≤Fᵢ-to-↓ {T} {S} (fold (inj₂ co-conv , (_ , conv) , refl , _)) = conv

  ↓-to-≤Fᵢ : ∀{T S} → T ↓ S → T ≤Fᵢ S
  ↓-to-≤Fᵢ conv = apply-ind (inj₂ co-conv) (_ , conv) λ ()
  
  build-F-true : ∀{i}{f g : Continuation} 
    → true ∈ dom g → ¬ (false ∈ dom g) 
    → Thunk (FairSub (f true .force) (g true .force)) i 
    → (∀{x} (!x : x ∈ dom g) -> Thunk (FairSub (f x .force) (g x .force)) i)
  build-F-true ok-t no-f pr {x = false} def = ⊥-elim (no-f def)
  build-F-true ok-t no-f pr {x = true} def = pr

  build-F-false : ∀{i}{f g : Continuation} 
    → false ∈ dom g → ¬ (true ∈ dom g) 
    → Thunk (FairSub (f false .force) (g false .force)) i 
    → (∀{x} (!x : x ∈ dom g) -> Thunk (FairSub (f x .force) (g x .force)) i)
  build-F-false ok-f no-t pr {x = false} def = pr
  build-F-false ok-f no-t pr {x = true} def = ⊥-elim (no-t def)
  
  build-F-both : ∀{i}{f g : Continuation} 
    → true ∈ dom g → false ∈ dom g
    → Thunk (FairSub (f true .force) (g true .force)) i 
    → Thunk (FairSub (f false .force) (g false .force)) i 
    → (∀{x} (!x : x ∈ dom g) -> Thunk (FairSub (f x .force) (g x .force)) i)
  build-F-both ok-t ok-f pr-t pr-f {x = false} _ = pr-f
  build-F-both ok-t ok-f pr-t pr-f {x = true} _ = pr-t

  ≤F-to-FairSub : ∀{T S} → T ≤F S → ∀{i} → FairSub T S i
  ≤F-to-FairSub fs with fs .CoInd⟦_⟧.unfold
  ... | nil-any , _ , refl , _ = nil<|any
  ... | end-def , ((_ , (end , def)) , _) , refl , _ = end<|def end def
  ... | inp-inp , ((_ , dom-incl) , ind) , refl , pr = 
    inp<|inp (≤Fᵢ-to-↓ ind) dom-incl λ{true → (λ where .force → ≤F-to-FairSub (pr zero)) ; false → λ where .force → ≤F-to-FairSub (pr (suc zero))}
  ... | out-out-true , (((f , g) , (wit , dom-incl , ok-t , no-f)) , ind) , refl , pr = 
    out<|out (≤Fᵢ-to-↓ ind) wit dom-incl (build-F-true {_} {f} {g} ok-t no-f λ where .force → ≤F-to-FairSub (pr zero))
  ... | out-out-false , (((f , g) , (wit , dom-incl , ok-f , no-t)) , ind) , refl , pr =
    out<|out (≤Fᵢ-to-↓ ind) wit dom-incl (build-F-false {_} {f} {g} ok-f no-t λ where .force → ≤F-to-FairSub (pr zero))
  ... | out-out-both , (((f , g) , (wit , dom-incl , ok-t , ok-f)) , ind) , refl , pr =
    out<|out (≤Fᵢ-to-↓ ind) wit dom-incl (build-F-both {_} {f} {g} ok-t ok-f (λ where .force → ≤F-to-FairSub (pr zero)) λ where .force → ≤F-to-FairSub (pr (suc zero)))

  fs-sound : ∀{T S} → T ≤F S → FairSubtypingS T S
  fs-sound fs fc = FS.sub-sound fc (≤F-to-FairSub fs)

  -------------------------------------------------------
    
  {- Boundedness -}

  postulate
    not-conv-div : ∀{T S} → ¬ T ↓ S → T ↑ S

  fs-convergence : ∀{T S} → FairSubtypingS T S → T ↓ S
  fs-convergence {T} {S} fs with excluded-middle {T ↓ S}
  fs-convergence {T} {S} fs | yes p = p
  fs-convergence {T} {S} fs | no p =
    let div = not-conv-div p in
    let sub = fsspec->sub (spec-sound fs) in
    let d-comp = discriminator-compliant sub div in
    let ¬d-comp = discriminator-not-compliant sub div in
    ⊥-elim (¬d-comp (fs d-comp))
  
  fs-bounded : ∀{T S} → FairSubtypingS T S → T ≤Fᵢ S
  fs-bounded fs = ↓-to-≤Fᵢ (fs-convergence fs)

  -----------------------------------------------------

  {- Consistency -}

  fs-consistent : ∀{T S} → FairSubtypingS T S → ISF[ FSubIS ] (λ{(T , S) → FairSubtypingS T S}) (T , S)
  fs-consistent {nil} {S} _ = nil-any , S , refl , λ ()
  fs-consistent {inp f} {nil} fs = ⊥-elim (¬Inil-fsub fs)
  fs-consistent {inp f} {inp g} fs with true ∈? f | false ∈? f
  fs-consistent {inp f} {inp g} fs | yes ok-t | yes ok-f with true ∈? g
  fs-consistent {inp f} {inp g} fs | yes ok-t | yes ok-f | yes ok-t-g with false ∈? g
  fs-consistent {inp f} {inp g} fs | yes ok-t | yes ok-f | yes ok-t-g | yes ok-f-g =
    let prems = λ{
          zero → transition-preserves-FairSubSpec fs inp inp ;
          (suc zero) → transition-preserves-FairSubSpec fs inp inp
          } in
    inp-inp , (_ , dom-incl-full {f} {g} ok-t-g ok-f-g) , refl , prems
  fs-consistent {inp f} {inp g} fs | yes ok-t | yes ok-f | yes ok-t-g | no no-f-g =
    ⊥-elim (¬II-fsub-no-dom-incl (¬dom-incl {f} {g} false ok-f no-f-g) fs)
  fs-consistent {inp f} {inp g} fs | yes ok-t | yes ok-f | no no-t-g =
    ⊥-elim (¬II-fsub-no-dom-incl (¬dom-incl {f} {g} true ok-t no-t-g) fs)
  fs-consistent {inp f} {inp g} fs | no no-t | yes ok-f with false ∈? g
  fs-consistent {inp f} {inp g} fs | no no-t | yes ok-f | yes ok-f-g =
    let prems = λ{
          zero → transition-preserves-FairSubSpec fs inp inp ;
          (suc zero) → transition-preserves-FairSubSpec fs inp inp
          } in
    inp-inp , (_ , dom-incl-single {f} {g} false no-t ok-f ok-f-g) , refl , prems
  fs-consistent {inp f} {inp g} fs | no no-t | yes ok-f | no no-f-g = ⊥-elim (¬II-fsub-no-dom-incl (¬dom-incl {f} {g} false ok-f no-f-g) fs)
  fs-consistent {inp f} {inp g} fs | yes ok-t | no no-f with true ∈? g
  fs-consistent {inp f} {inp g} fs | yes ok-t | no no-f | yes ok-t-g = 
    let prems = λ{
          zero → transition-preserves-FairSubSpec fs inp inp ;
          (suc zero) → transition-preserves-FairSubSpec fs inp inp
          } in
    inp-inp , (_ , dom-incl-single {f} {g} true no-f ok-t ok-t-g) , refl , prems
  fs-consistent {inp f} {inp g} fs | yes ok-t | no no-f | no no-t-g = ⊥-elim (¬II-fsub-no-dom-incl (¬dom-incl {f} {g} true ok-t no-t-g) fs)
  fs-consistent {inp f} {inp g} fs | no no-t | no no-f = end-def , (_ , (inp (λ{true → no-t ; false → no-f}) , inp)) , refl , λ ()
  fs-consistent {inp f} {out g} fs with true ∈? f
  ... | yes ok-t = ⊥-elim (¬IO-fsub ok-t fs)
  ... | no no-t with false ∈? f
  ... | yes ok-f = ⊥-elim (¬IO-fsub ok-f fs)
  ... | no no-f = end-def , (_ , (inp (λ{true → no-t ; false → no-f}) , out)) , refl , λ ()
  fs-consistent {out f} {nil} fs = ⊥-elim (¬Onil-fsub fs)
  fs-consistent {out f} {inp g} fs with true ∈? f | false ∈? f
  ... | yes ok-t | yes ok-f = ⊥-elim (¬OI-fsub ok-f fs)
  ... | no no-t | yes ok-f = ⊥-elim (¬OI-fsub ok-f fs)
  ... | yes ok-t | no no-f = ⊥-elim (¬OI-fsub ok-t fs)
  ... | no no-t | no no-f = end-def , (_ , (out (λ{true → no-t ; false → no-f}) , inp)) , refl , λ ()
  fs-consistent {out f} {out g} fs with FSSpec->end-incl (spec-sound fs)
  ... | inj₁ end = end-def , (_ , (end , out)) , refl , λ ()
  ... | inj₂ (wit , incl) with true ∈? g | false ∈? g
  ... | yes ok-t | yes ok-f =
      let prems = λ{
            zero → transition-preserves-FairSubSpec fs (out (incl ok-t)) (out ok-t) ; 
            (suc zero) → transition-preserves-FairSubSpec fs (out (incl ok-f)) (out ok-f)
            } in
      out-out-both , (_ , (wit , incl , ok-t , ok-f)) , refl , prems  
  ... | no no-t | yes ok-f = 
      out-out-false , (_ , (wit , incl , ok-f , no-t)) , refl , λ{zero → transition-preserves-FairSubSpec fs (out (incl ok-f)) (out ok-f)}
  ... | yes ok-t | no no-f = 
      out-out-true , (_ , (wit , incl , ok-t , no-f)) , refl , λ{zero → transition-preserves-FairSubSpec fs (out (incl ok-t)) (out ok-t)}
  fs-consistent {out f} {out g} fs | inj₂ ((false , ok-f) , incl) | no no-t | no no-f = ⊥-elim (no-f ok-f)
  fs-consistent {out f} {out g} fs | inj₂ ((true , ok-t) , incl) | no no-t | no no-f = ⊥-elim (no-t ok-t)

----------------------------------------------------------

{- Completeness -}

  fs-complete : ∀{T S} → FairSubtypingS T S → T ≤F S
  fs-complete = bounded-coind[ FSubIS , FSubCOIS ] (λ{(T , S) → FairSubtypingS T S}) fs-bounded fs-consistent