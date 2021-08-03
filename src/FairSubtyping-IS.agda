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

{-# OPTIONS --guardedness --sized-types #-}

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
open import Common using (Message)

module FairSubtyping-IS {𝕋 : Set} (message : Message 𝕋) where

  open Message message
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
  open import FairCompliance-IS message

  private
    U : Set
    U = SessionType × SessionType

  data FSubIS-RN : Set where
    nil-any end-def : FSubIS-RN
    ii oo : FSubIS-RN

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

  ii-r : MetaRule U
  ii-r .Ctx = Σ[ (f , g) ∈ Continuation × Continuation ] dom f ⊆ dom g
  ii-r .Pos ((f , _) , _) = Σ[ t ∈ 𝕋 ] t ∈ dom f
  ii-r .prems ((f , g) , _) (t , _) = f t .force , g t .force
  ii-r .conclu ((f , g) , _) = inp f , inp g

  oo-r : MetaRule U
  oo-r .Ctx = Σ[ (f , g) ∈ Continuation × Continuation ] dom g ⊆ dom f × Witness g
  oo-r .Pos ((_ , g) , _) = Σ[ t ∈ 𝕋 ] t ∈ dom g
  oo-r .prems ((f , g) , _) (t , _) = f t .force , g t .force
  oo-r .conclu ((f , g) , _) = out f , out g

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
  FSubIS .rules ii = ii-r
  FSubIS .rules oo = oo-r

  FSubCOIS : IS U
  FSubCOIS .Names = FSubCOIS-RN
  FSubCOIS .rules co-conv = from co-conv-r

  _≤F_ : SessionType → SessionType → Set
  T ≤F S = FCoInd⟦ FSubIS , FSubCOIS ⟧ (T , S)

  _≤Fᵢ_ : SessionType → SessionType → Set
  T ≤Fᵢ S = Ind⟦ FSubIS ∪ FSubCOIS ⟧ (T , S)

  _≤Fc_ : SessionType → SessionType → Set
  T ≤Fc S = CoInd⟦ FSubIS ⟧ (T , S)


  {- Specification using _⊢_ is correct wrt FairSubtypingS -}

  FSSpec-⊢ : U → Set
  FSSpec-⊢ (T , S) = ∀{R} → R ⊢ T → R ⊢ S
  
  spec-sound : ∀{T S} → FairSubtypingS T S → FSSpec-⊢ (T , S)
  spec-sound fs fc = fc-complete (fs (fc-sound fc))

  spec-complete : ∀{T S} → FSSpec-⊢ (T , S) → FairSubtypingS T S
  spec-complete fs fc = fc-sound (fs (fc-complete fc))

  ------------------------------------------------------

  {- Soundness -}
  -- Using bounded coinduction wrt SpecAux

  ≤Fᵢ->↓ : ∀{S T} → S ≤Fᵢ T → S ↓ T
  ≤Fᵢ->↓ (fold (inj₁ nil-any , _ , refl , _)) = nil-converges
  ≤Fᵢ->↓ (fold (inj₁ end-def , (_ , (end , def)) , refl , _)) = end-converges end def
  ≤Fᵢ->↓ (fold (inj₁ ii , _ , refl , pr)) = converge (pre-conv-inp-back λ x → ↓->preconv (≤Fᵢ->↓ (pr (_ , x))))
  ≤Fᵢ->↓ (fold (inj₁ oo , (_ , (incl , (t , ok-t))) , refl , pr)) = 
    converge 
      λ _ _ → [] , t , none , (_ , incl ok-t , step (out (incl ok-t)) refl) , (_ , ok-t , step (out ok-t) refl) , ≤Fᵢ->↓ (pr (t , ok-t))
  ≤Fᵢ->↓ (fold (inj₂ co-conv , (_ , conv) , refl , _)) = conv

  SpecAux : U → Set
  SpecAux (R , T) = Σ[ S ∈ SessionType ] S ≤F T × R ⊢ S 

  ≤Fᵢ->defined : ∀{S T} → Defined S → S ≤Fᵢ T → Defined T
  ≤Fᵢ->defined def fs = conv->defined def (≤Fᵢ->↓ fs)

  spec-bounded-rec : ∀{R S} T → T ≤Fᵢ S → R ⊢ T → R ⊢ᵢ S
  spec-bounded-rec _ fs fc =     
    let _ , reds , succ = con-sound (≤Fᵢ->↓ fs) (fc-sound fc) in
    maysucceed->⊢ᵢ reds succ

  spec-bounded : SpecAux ⊆ λ (R , S) → R ⊢ᵢ S
  spec-bounded (T , fs , fc) = spec-bounded-rec T (fcoind-to-ind fs) fc

  spec-cons : SpecAux ⊆ ISF[ FCompIS ] SpecAux
  spec-cons {(R , T)} (S , fs , fc) with fc .CoInd⟦_⟧.unfold
  spec-cons {(R , T)} (S , fs , fc) | client-end , ((_ , (win , def)) , _) , refl , _ = 
    client-end , ((R , _) , (win , ≤Fᵢ->defined def (fcoind-to-ind fs))) , refl , λ ()
  spec-cons {(out r , _)} ((inp f) , fs , fc) | oi , (((.r , .f) , wit-r) , _) , refl , pr with fs .CoInd⟦_⟧.unfold
  ... | end-def , (((.(inp f) , _) , (inp e , _)) , _) , refl , _ = ⊥-elim (e _ (proj₂ (fc->defined (pr wit-r))))
  ... | ii , (((.f , g) , _) , _) , refl , pr' = oi , (_ , wit-r) , refl , λ wit → _ , pr' (_ , proj₂ (fc->defined (pr wit))) , pr wit
  spec-cons {(inp r , T)} (out f , fs , fc) | io , (((.r , .f) , wit-f) , _) , refl , pr with fs .CoInd⟦_⟧.unfold
  ... | end-def , (((.(out f) , _) , (out e , _)) , _) , refl , _ = ⊥-elim (e _ (proj₂ wit-f))
  ... | oo , (((.f , g) , (incl , wit-g)) , _) , refl , pr' = io , (_ , wit-g) , refl , λ wit → _ , pr' wit , pr (_ , incl (proj₂ wit))

  spec-aux-sound : SpecAux ⊆ λ (R , S) → R ⊢ S
  spec-aux-sound = bounded-coind[ FCompIS , FCompCOIS ] SpecAux spec-bounded spec-cons

  fs-sound : ∀{T S} → T ≤F S → FSSpec-⊢ (T , S)
  fs-sound {T} fs fc = spec-aux-sound (T , fs , fc)

  {- Soundness & Completeness of Sub wrt ≤Fc -}

  ≤Fc->sub : ∀{S T} → S ≤Fc T → ∀ {i} → Sub S T i
  ≤Fc->sub fs with fs .CoInd⟦_⟧.unfold
  ... | nil-any , _ , refl , _ = nil<:any
  ... | end-def , (_ , (end , def)) , refl , _ = end<:def end def
  ... | ii , ((f , g) , incl) , refl , pr = inp<:inp incl λ x → λ where .force → if-def x
    where 
      if-def : (t : 𝕋) → ∀{i} → Sub (f t .force) (g t .force) i
      if-def t with t ∈? f
      ... | yes ok-t = ≤Fc->sub (pr (_ , ok-t))
      ... | no no-t = subst (λ x → Sub x (g t .force) _) (sym (not-def->nil no-t)) nil<:any
  ... | oo , (_ , (incl , wit)) , refl , pr = out<:out wit incl λ ok-x → λ where .force → ≤Fc->sub (pr (_ , ok-x))

  sub->≤Fc : ∀{S T} → (∀{i} → Sub S T i) → S ≤Fc T
  CoInd⟦_⟧.unfold (sub->≤Fc fs) with fs
  ... | nil<:any = nil-any , _ , refl , λ ()
  ... | end<:def end def = end-def , (_ , (end , def)) , refl , λ ()
  ... | inp<:inp incl pr = ii , (_ , incl) , refl , λ (p , _) → sub->≤Fc (pr p .force)
  ... | out<:out wit incl pr = oo , (_ , (incl , wit)) , refl , λ (_ , ok) → sub->≤Fc (pr ok .force)

  {- Auxiliary -}

  -- Only premise for rules using sample-cont in ⊢
  sample-cont-prem : ∀{f : Continuation}{t R} → R ⊢ f t .force 
    → (pos : Σ[ p ∈ 𝕋 ] p ∈ dom (sample-cont t R nil)) → (sample-cont t R nil) (proj₁ pos) .force ⊢ f (proj₁ pos) .force
  sample-cont-prem {f} {t} pr (p , ok-p) with p ?= t
  ... | yes refl = pr
  sample-cont-prem {f} {t} pr (p , ()) | no ¬eq

  -- Premises using sample-cont-dual in ⊢
  sample-cont-prems : ∀{f : Continuation}{t} → t ∉ dom f 
    → (pos : Σ[ p ∈ 𝕋 ] p ∈ dom f) → (sample-cont t nil win) (proj₁ pos) .force ⊢ f (proj₁ pos) .force
  sample-cont-prems {f} {t} no-t (p , ok-p) with p ?= t
  ... | yes refl = ⊥-elim (no-t ok-p)
  ... | no ¬eq = win⊢def ok-p

  -- Premises using sample-cont-dual in ⊢
  sample-cont-prems' : ∀{f : Continuation}{t R} → R ⊢ f t .force 
    → (pos : Σ[ p ∈ 𝕋 ] p ∈ dom f) → (sample-cont t R win) (proj₁ pos) .force ⊢ f (proj₁ pos) .force
  sample-cont-prems' {f} {t} pr (p , ok-p) with p ?= t
  ... | yes refl = pr
  ... | no ¬eq = win⊢def ok-p

  spec-inp->incl : ∀{f g} → FSSpec-⊢ (inp f , inp g) → dom f ⊆ dom g
  spec-inp->incl {f} {g} fs {t} ok-t with fs (apply-fcoind oi ((sample-cont t win nil , f) , wit-cont out) (sample-cont-prem {f} {t} (win⊢def ok-t))) .CoInd⟦_⟧.unfold
  ... | client-end , ((_ , (out e , _)) , _) , refl , _ = ⊥-elim (e t (proj₂ (wit-cont out)))
  ... | oi , _ , refl , pr = proj₂ (fc->defined (pr (t , proj₂ (wit-cont out))))

  spec-out->incl : ∀{f g} → FSSpec-⊢ (out f , out g) → Witness f → dom g ⊆ dom f
  spec-out->incl {f} {g} fs wit {t} ok-t with t ∈? f
  ... | yes ok = ok
  ... | no no-t with (fs (apply-fcoind io ((sample-cont t nil win ,  f) , wit) (sample-cont-prems {f} {t} no-t))) .CoInd⟦_⟧.unfold
  ... | client-end , ((_ , (() , _)) , _) , refl , _
  ... | io , _ , refl , pr = ⊥-elim (cont-not-def (proj₁ (fc->defined (pr (t , ok-t)))))

  spec-out->wit : ∀{f g} → Witness f →  FSSpec-⊢ (out f , out g) → Witness g
  spec-out->wit {f} {g} wit-f fs with Empty? g
  ... | inj₂ wit = wit
  ... | inj₁ e with (fs (apply-fcoind io ((full-cont win , f) , wit-f) λ (_ , ok) → win⊢def ok)) .CoInd⟦_⟧.unfold 
  ... | client-end , ((_ , (() , _)) , _) , refl , _
  ... | io , ((_ , wit-g) , _) , refl , _ = ⊥-elim (e _ (proj₂ wit-g))
  
  {- Boundedness & Consistency -}
  
  fsspec-cons : FSSpec-⊢ ⊆ ISF[ FSubIS ] FSSpec-⊢
  fsspec-cons {nil , T} fs = nil-any , _ , refl , λ ()
  fsspec-cons {inp f , nil} fs with (fs (apply-fcoind client-end ((win , _) , (Win-win , inp)) λ ())) .CoInd⟦_⟧.unfold
  ... | client-end , ((_ , (_ , ())) , _) , refl , _
  fsspec-cons {inp f , inp g} fs = ii , ((f , g) , spec-inp->incl fs) , refl , 
    λ (p , _) {R} fc-r-f → 
      let wit = wit-cont (proj₁ (fc->defined fc-r-f)) in
      let fc-Or-Ig = fs (apply-fcoind oi ((sample-cont p R nil , f) , wit) (sample-cont-prem {f} {p} fc-r-f)) in
      let fc-r-g = ⊢-after-out {sample-cont p R nil} {g} {p} (proj₂ wit) fc-Or-Ig in
      subst (λ x → x ⊢ g p .force) (sym force-eq) fc-r-g
  fsspec-cons {inp f , out g} fs with Empty? f
  ... | inj₁ e = end-def , (_ , (inp e , out)) , refl , λ ()
  ... | inj₂ (t , ok-t) with (fs (apply-fcoind oi ((sample-cont t win nil , f) , wit-cont out) (sample-cont-prem {f} {t} (win⊢def ok-t)))) .CoInd⟦_⟧.unfold
  ... | client-end , ((_ , (out e , out)) , _) , refl , _ = ⊥-elim (e t (proj₂ (wit-cont out)))
  fsspec-cons {out f , nil} fs with (fs (apply-fcoind client-end ((win , _) , (Win-win , out)) λ ())) .CoInd⟦_⟧.unfold
  ... | client-end , ((_ , (_ , ())) , _) , refl , _
  fsspec-cons {out f , inp g} fs with Empty? f
  ... | inj₁ e = end-def , (_ , (out e , inp)) , refl , λ ()
  ... | inj₂ (t , ok-t) with (fs (apply-fcoind io ((full-cont win , f) , (t , ok-t)) λ (_ , ok-p) → win⊢def ok-p)) .CoInd⟦_⟧.unfold
  ... | client-end , ((_ , (() , inp)) , _) , refl , _
  fsspec-cons {out f , out g} fs with Empty? f
  ... | inj₁ e = end-def , (_ , (out e , out)) , refl , λ ()
  ... | inj₂ (t , ok-t) = 
    let wit-g = spec-out->wit (t , ok-t) fs in
    let incl = spec-out->incl fs (t , ok-t) in 
    oo , ((f , g) , (incl , wit-g)) , refl , λ (p , ok-p) {R} fc-r-f → 
      let fc-Ir-Og = fs (apply-fcoind io ((sample-cont p R win , f) , (t , ok-t)) (sample-cont-prems' {f} {p} fc-r-f)) in
      let fc-r-g = ⊢-after-in {sample-cont p R win} {g} {p} ok-p fc-Ir-Og in
      subst (λ x → x ⊢ g p .force) (sym force-eq) fc-r-g

  fsspec->sub : ∀{S T} → FSSpec-⊢ (S , T) → S ≤Fc T
  fsspec->sub = coind[ FSubIS ] FSSpec-⊢ fsspec-cons

  postulate
    not-conv-div : ∀{T S} → ¬ T ↓ S → T ↑ S

  fs-convergence : ∀{T S} → FairSubtypingS T S → T ↓ S
  fs-convergence {T} {S} fs with Common.excluded-middle {T ↓ S}
  fs-convergence {T} {S} fs | yes p = p
  fs-convergence {T} {S} fs | no p =
    let div = not-conv-div p in
    let sub = ≤Fc->sub (fsspec->sub (spec-sound fs)) in
    let d-comp = discriminator-compliant sub div in
    let ¬d-comp = discriminator-not-compliant sub div in
    ⊥-elim (¬d-comp (fs d-comp))
  
  fsspec-bounded : ∀{S T} → FSSpec-⊢ (S , T) → S ≤Fᵢ T
  fsspec-bounded fs = apply-ind (inj₂ co-conv) (_ , (fs-convergence (spec-complete fs))) λ ()

  {- Completeness -}

  fs-complete : ∀{S T} → FSSpec-⊢ (S , T) → S ≤F T
  fs-complete = bounded-coind[ FSubIS , FSubCOIS ] FSSpec-⊢ fsspec-bounded fsspec-cons