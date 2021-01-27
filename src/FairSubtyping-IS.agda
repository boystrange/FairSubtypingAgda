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
open import Data.Unit
open import Data.Fin
open import Data.Bool renaming (Bool to 𝔹)
open import Relation.Unary using (_∈_; _⊆_;_∉_)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Size
open import Codata.Thunk

open import is-meta.InfSys as IS
open MetaRule
open IS.IS
open import is-meta.InfSys.Properties
open import is-meta.InfSys.Principles

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
  open import FairCompliance message
  open import Trace message
  open import FairCompliance-IS
  
  
  --U : Set
  --U = SessionType × SessionType

  data FSubIS-RN : Set where
    nil-any end-def inp-inp : FSubIS-RN
    out-out-true out-out-false out-out-both : FSubIS-RN

  data FSubCOIS-RN : Set where
    co-conv : FSubCOIS-RN

  nil-any-r : MetaRule U
  nil-any-r .C = SessionType
  nil-any-r .comp T =
    [] ,
    ------------------
    (nil , T) , ⊤

  end-def-r : MetaRule U
  end-def-r .C = SessionType × SessionType
  end-def-r .comp (T , S) =
    [] ,
    ------------------
    (T , S) , (End T × Defined S)

  inp-inp-r : MetaRule U
  inp-inp-r .C = Continuation × Continuation
  inp-inp-r .comp (f , g) =
    (f true .force , g true .force) ∷ (f false .force , g false .force) ∷ [] ,
    ------------------
    (inp f , inp g) , (dom f ⊆ dom g)

  out-out-true-r : MetaRule U
  out-out-true-r .C = Continuation × Continuation
  out-out-true-r .comp (f , g) =
    (f true .force , g true .force) ∷ [] ,
    ------------------
    (out f , out g) , (Witness g × dom g ⊆ dom f × true ∈ dom g × ¬ false ∈ dom g)

  out-out-false-r : MetaRule U
  out-out-false-r .C = Continuation × Continuation
  out-out-false-r .comp (f , g) =
    (f false .force , g false .force) ∷ [] ,
    ------------------
    (out f , out g) , (Witness g × dom g ⊆ dom f × false ∈ dom g × ¬ true ∈ dom g)

  out-out-both-r : MetaRule U
  out-out-both-r .C = Continuation × Continuation
  out-out-both-r .comp (f , g) =
    (f true .force , g true .force) ∷ (f false .force , g false .force) ∷ [] ,
    ------------------
    (out f , out g) , (Witness g × dom g ⊆ dom f × true ∈ dom g × false ∈ dom g)

  co-conv-r : MetaRule U
  co-conv-r .C = SessionType × SessionType
  co-conv-r .comp (T , S) =
    [] ,
    ------------------
    (T , S) , (T ↓ S)

  FSubIS : IS U
  FSubIS .Names = FSubIS-RN
  FSubIS .rules nil-any = nil-any-r
  FSubIS .rules end-def = end-def-r
  FSubIS .rules inp-inp = inp-inp-r
  FSubIS .rules out-out-true = out-out-true-r
  FSubIS .rules out-out-false = out-out-false-r
  FSubIS .rules out-out-both = out-out-both-r

  FSubCOIS : IS U
  FSubCOIS .Names = FSubCOIS-RN
  FSubCOIS .rules co-conv = co-conv-r

  _≤F_ : SessionType → SessionType → Set
  T ≤F S = Gen⟦ FSubIS , FSubCOIS ⟧ (T , S)

  _≤Fᵢ_ : SessionType → SessionType → Set
  T ≤Fᵢ S = Ind⟦ FSubIS ∪ FSubCOIS ⟧ (T , S)

  postulate
    end-reduces-⊥ : ∀{S S' α } → End S → Transition S α S' → ⊥

  transition-preserves-≤F : ∀{T T' S S' α} → T ≤F S → Transition T α T' → Transition S α S' → T' ≤F S'
  transition-preserves-≤F fs red-T red-S with fs .CoInd⟦_⟧.unfold
  transition-preserves-≤F fs () red-S | nil-any , _ , refl , _
  transition-preserves-≤F fs red-T red-S | end-def , _ , refl , ((end , _) , _) , _ = ⊥-elim (end-reduces-⊥ end red-T)
  transition-preserves-≤F fs (inp {x = false}) inp | inp-inp , _ , refl , _ , pr = pr (suc zero)
  transition-preserves-≤F fs (inp {x = true}) inp | inp-inp , _ , refl , _ , pr = pr zero
  transition-preserves-≤F fs (out _) (out {x = false} ok-f) | out-out-true , _ , refl , ((_ , _ , _ , no-f) , _) , _ = ⊥-elim (no-f ok-f)
  transition-preserves-≤F fs (out _) (out {x = true} ok-t) | out-out-true , _ , refl , _ , pr = pr zero
  transition-preserves-≤F fs (out _) (out {x = false} ok-f) | out-out-false , _ , refl , _ , pr = pr zero
  transition-preserves-≤F fs (out _) (out {x = true} ok-t) | out-out-false , _ , refl , ((_ , _ , _ , no-t) , _) , _ = ⊥-elim (no-t ok-t)
  transition-preserves-≤F fs (out {x = false} _) (out _) | out-out-both , _ , refl , _ , pr = pr (suc zero)
  transition-preserves-≤F fs (out {x = true} _) (out _) | out-out-both , _ , refl , _ , pr = pr zero



  {- Specification -}
  FSSpec-⊢ : U → Set
  FSSpec-⊢ (T , S) = ∀{R} → R ⊢ T → R ⊢ S

  {- Soundness and Completeness of Specifications -}
  
  spec-sound : ∀{T S} → FairSubtypingS T S → FSSpec-⊢ (T , S)
  spec-sound fs fc = fc-complete (fs (fc-sound fc))

  spec-complete : ∀{T S} → FSSpec-⊢ (T , S) → FairSubtypingS T S
  spec-complete fs fc = fc-sound (fs (fc-complete fc))

  ------------------------------------------------------

  fc-nil-⊥ : ∀{S} → S ⊢ nil → ⊥
  fc-nil-⊥ fc with fc .CoInd⟦_⟧.unfold
  fc-nil-⊥ fc | client-end , _ , refl , ((_ , ()) , _) , _

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
  ≤Fᵢ-to-↓ {T} {S} (fold (inj₁ end-def , _ , refl , (end , def) , _)) = end-converges end def
  ≤Fᵢ-to-↓ {inp f} {inp g} (fold (inj₁ inp-inp , _ , refl , _ , pr)) with ≤Fᵢ-to-↓ (pr zero) | ≤Fᵢ-to-↓ (pr (suc zero))
  ... | converge conv-t | converge conv-f = converge (pre-conv-back conv-t conv-f)
  ≤Fᵢ-to-↓ {out f} {out g} (fold (inj₁ out-out-true , _ , refl , (_ , dom-incl , ok-t , _) , pr)) = 
    let rec = ≤Fᵢ-to-↓ (pr zero) in
    let f-step = f true .force , dom-incl ok-t , step (out (dom-incl ok-t)) refl in
    let g-step = g true .force , ok-t , step (out ok-t) refl in
    converge λ tφ sφ → [] , true , none , (f-step , g-step , rec)
  ≤Fᵢ-to-↓ {out f} {out g} (fold (inj₁ out-out-false , _ , refl , (_ , dom-incl , ok-f , _) , pr)) = 
    let rec = ≤Fᵢ-to-↓ (pr zero) in
    let f-step = f false .force , dom-incl ok-f , step (out (dom-incl ok-f)) refl in
    let g-step = g false .force , ok-f , step (out ok-f) refl in
    converge λ tφ sφ → [] , false , none , (f-step , g-step , rec)
  ≤Fᵢ-to-↓ {out f} {out g} (fold (inj₁ out-out-both , _ , refl , (_ , dom-incl , ok-t , _) , pr)) = 
    let rec = ≤Fᵢ-to-↓ (pr zero) in
    let f-step = f true .force , dom-incl ok-t , step (out (dom-incl ok-t)) refl in
    let g-step = g true .force , ok-t , step (out ok-t) refl in
    converge λ tφ sφ → [] , true , none , (f-step , g-step , rec)
  ≤Fᵢ-to-↓ {T} {S} (fold (inj₂ co-conv , _ , refl , conv , _)) = conv

  ↓-to-≤Fᵢ : ∀{T S} → T ↓ S → T ≤Fᵢ S
  ↓-to-≤Fᵢ conv = apply-ind (inj₂ co-conv , refl) conv λ ()
  
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

  ≤F-to-FairSub : ∀{T S} → T ≤F S → (∀{i} → FairSub T S i)
  ≤F-to-FairSub fs with fs .CoInd⟦_⟧.unfold
  ... | nil-any , _ , refl , _ = nil<|any
  ... | end-def , _ , refl , ((end , def) , _) , _ = end<|def end def
  ... | inp-inp , _ , refl , (dom-incl , ind) , pr = 
    inp<|inp (≤Fᵢ-to-↓ ind) dom-incl λ{true → (λ where .force → ≤F-to-FairSub (pr zero)) ; false → λ where .force → ≤F-to-FairSub (pr (suc zero))}
  ... | out-out-true , (f , g) , refl , ((wit , dom-incl , ok-t , no-f) , ind) , pr = 
    out<|out (≤Fᵢ-to-↓ ind) wit dom-incl (build-F-true {_} {f} {g} ok-t no-f λ where .force → ≤F-to-FairSub (pr zero))
  ... | out-out-false , (f , g) , refl , ((wit , dom-incl , ok-f , no-t) , ind) , pr =
    out<|out (≤Fᵢ-to-↓ ind) wit dom-incl (build-F-false {_} {f} {g} ok-f no-t λ where .force → ≤F-to-FairSub (pr zero))
  ... | out-out-both , (f , g) , refl , ((wit , dom-incl , ok-t , ok-f) , ind) , pr =
    out<|out (≤Fᵢ-to-↓ ind) wit dom-incl (build-F-both {_} {f} {g} ok-t ok-f (λ where .force → ≤F-to-FairSub (pr zero)) λ where .force → ≤F-to-FairSub (pr (suc zero)))

  fs-sound : ∀{T S} → T ≤F S → FairSubtypingS T S
  fs-sound fs fc = FS.sub-sound fc (≤F-to-FairSub fs)
    
  {- Boundedness-}
  postulate
    not-conv-div : ∀{T S} → ¬ T ↓ S → T ↑ S
    fsub-implies-sub : ∀{T S} → FairSubtypingS T S → T <: S

  fs-convergence : ∀{T S} → FairSubtypingS T S → T ↓ S
  fs-convergence {T} {S} fs with excluded-middle {T ↓ S}
  fs-convergence {T} {S} fs | yes p = p
  fs-convergence {T} {S} fs | no p =
    let div = not-conv-div p in
    let sub = fsub-implies-sub fs in
    let d-comp = discriminator-compliant sub div in
    let ¬d-comp = discriminator-not-compliant sub div in
    ⊥-elim (¬d-comp (fs d-comp))
  
  fs-bounded : ∀{T S} → FairSubtypingS T S → T ≤Fᵢ S
  fs-bounded fs = ↓-to-≤Fᵢ (fs-convergence fs)

  {- Sample SessionType -}
  cont : SessionType → Continuation
  cont S false = box S
  cont S true = box S

  cont-true : SessionType → Continuation
  cont-true S false = box nil
  cont-true S true = box S

  cont-false : SessionType → Continuation
  cont-false S false = box S
  cont-false S true = box nil

  cont-ch : 𝔹 → SessionType → Continuation
  cont-ch false S = cont-false S
  cont-ch true S = cont-true S

  R-out-t : SessionType
  R-out-t = out (cont-true win)

  R-out-f : SessionType
  R-out-f = out (cont-false win)

  R-in-t : SessionType
  R-in-t = inp (cont-true win)

  R-in-f : SessionType
  R-in-f = inp (cont-false win)

  R-in-both : SessionType
  R-in-both = inp (cont win)

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

  {- Transitions preserve Specification-}
  send-R : 𝔹 → SessionType → SessionType
  send-R b S = out (cont-ch b S)

  rec-R : SessionType → SessionType
  rec-R S = inp (cont S) 

  rec-R' : 𝔹 → SessionType → SessionType
  rec-R' false S = inp λ{true → box win ; false → box S}
  rec-R' true S = inp λ{true → box S ; false → box win}

  send-R-⊢-inp : ∀{R f} x → Defined R → R ⊢ f x .force → send-R x R ⊢ inp f
  send-R-⊢-inp false def prem = apply-gen (oi-false , refl) (def , λ ()) λ{zero → prem}
  send-R-⊢-inp true def prem = apply-gen (oi-true , refl) (def , λ ()) λ{zero → prem}

  rec-R-⊢-out : ∀{R f} x → x ∈ dom f → ¬ (not x ∈ dom f) → R ⊢ f x .force → rec-R R ⊢ out f
  rec-R-⊢-out false ok-x no-x prem = apply-gen (io-false , refl) (ok-x , no-x) λ{zero → prem}
  rec-R-⊢-out true ok-x no-x prem = apply-gen (io-true , refl) (ok-x , no-x) λ{zero → prem}

  rec-R'-⊢-out : ∀{R f} x → x ∈ dom f → not x ∈ dom f → R ⊢ f x .force → rec-R' x R ⊢ out f
  rec-R'-⊢-out false ok ok' prem = apply-gen (io-both , refl) (ok' , ok) λ{zero → apply-gen (client-end , refl) (Win-win , ok') λ () ; (suc zero) → prem}
  rec-R'-⊢-out true ok ok' prem = apply-gen (io-both , refl) (ok , ok') λ{zero → prem ; (suc zero) → apply-gen (client-end , refl) (Win-win , ok') λ ()}

  send-R-reduces : ∀{S} b → Defined S → Transition (send-R b S) (O b) S
  send-R-reduces false def = out def
  send-R-reduces true def = out def

  rec-R-reduces : ∀{S} b → Transition (rec-R S) (I b) S
  rec-R-reduces false = inp
  rec-R-reduces true = inp

  rec-R'-reduces : ∀{S} b → Transition (rec-R' b S) (I b) S
  rec-R'-reduces false = inp
  rec-R'-reduces true = inp

  not-def->nil : ∀{T} → ¬ (Defined T) → T ≡ nil
  not-def->nil {nil} nd = refl
  not-def->nil {inp f} nd = ⊥-elim (nd inp)
  not-def->nil {out f} nd = ⊥-elim (nd out)
  
  ¬nil-⊢ : ∀{S} → ¬ (nil ⊢ S)
  ¬nil-⊢ fc with fc .CoInd⟦_⟧.unfold
  ... | client-end , _ , refl , ((() , _) , _) , _
  
  {- 
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
  transition-preserves-FSSpec {inp f} {S' = _} {I false} fs (inp {_} {.false}) tr-S {R} fc | yes def-R | client-end , _ , refl , ((win , _) , _) , _ = ⊥-elim (win-not-reduce win (send-R-reduces false def-R))
  transition-preserves-FSSpec {inp f} {S' = _} {I false} fs (inp {_} {.false}) inp {R} fc | yes def-R | oi-true , _ , refl , ((() , _) , _) , _
  transition-preserves-FSSpec {inp f} {S' = _} {I false} fs (inp {_} {.false}) inp {R} fc | yes def-R | oi-false , _ , refl , _ , pr = pr zero
  transition-preserves-FSSpec {inp f} {S' = _} {I false} fs (inp {_} {.false}) inp {R} fc | yes def-R | oi-both , _ , refl , ((() , _) , _) , _
  transition-preserves-FSSpec {inp f} fs (inp {x = false}) tr-S {R} fc | no ¬def-R = ⊥-elim (¬nil-⊢ (subst (λ T → T ⊢ _) (not-def->nil ¬def-R) fc))
  transition-preserves-FSSpec {inp f} fs (inp {x = true}) tr-S {R} fc with Defined? R
  transition-preserves-FSSpec {inp f} fs (inp {x = true}) tr-S {R} fc | yes def-R with fs (send-R-⊢-inp true def-R fc) .CoInd⟦_⟧.unfold
  transition-preserves-FSSpec {inp f} {S' = _} {I true} fs (inp {_} {.true}) tr-S {R} fc | yes def-R | client-end , _ , refl , ((win , _) , _) , _ = ⊥-elim (win-not-reduce win (send-R-reduces true def-R))
  transition-preserves-FSSpec {inp f} {S' = _} {I true} fs (inp {_} {.true}) inp {R} fc | yes def-R | oi-true , _ , refl , _ , pr = pr zero
  transition-preserves-FSSpec {inp f} {S' = _} {I true} fs (inp {_} {.true}) inp {R} fc | yes def-R | oi-false , _ , refl , ((() , _) , _) , _ 
  transition-preserves-FSSpec {inp f} {S' = _} {I true} fs (inp {_} {.true}) inp {R} fc | yes def-R | oi-both , _ , refl , ((_ , ()) , _) , _
  transition-preserves-FSSpec {inp f} fs (inp {x = true}) tr-S {R} fc | no ¬def-R = ⊥-elim (¬nil-⊢ (subst (λ T → T ⊢ _) (not-def->nil ¬def-R) fc))
  transition-preserves-FSSpec {out f} fs (out {x = t} ok) tr-S {R} fc with not t ∈? f
  transition-preserves-FSSpec {out f} fs (out {x = t} ok) (out ok') {R} fc | yes ok-not-x with fs (rec-R'-⊢-out t ok ok-not-x fc) .CoInd⟦_⟧.unfold
  transition-preserves-FSSpec {out f} fs (out {x = t} ok) (out ok') {R} fc | yes ok-not-x | client-end , _ , refl , ((win , _) , _) , _ = ⊥-elim (win-not-reduce win ((rec-R'-reduces t)))
  transition-preserves-FSSpec {out f} {_} {_} {_} {O false} fs (out {x = false} ok) (out ok') {R} fc | yes ok-not-x | io-true , _ , refl , ((_ , no-f) , _) , _ =  ⊥-elim (no-f ok')
  transition-preserves-FSSpec {out f} {_} {_} {_} {O true} fs (out {x = true} ok) (out ok') {R} fc | yes ok-not-x | io-true , _ , refl , _ , pr = pr zero
  transition-preserves-FSSpec {out f} {_} {_} {_} {O false} fs (out {x = false} ok) (out ok') {R} fc | yes ok-not-x | io-false , _ , refl , _ , pr = pr zero
  transition-preserves-FSSpec {out f} {_} {_} {_} {O true} fs (out {x = true} ok) (out ok') {R} fc | yes ok-not-x | io-false , _ , refl , ((_ , no-t) , _) , _ = ⊥-elim (no-t ok')
  transition-preserves-FSSpec {out f} fs (out {x = false} ok) (out ok') {R} fc | yes ok-not-x | io-both , _ , refl , _ , pr = pr (suc zero)
  transition-preserves-FSSpec {out f} fs (out {x = true} ok) (out ok') {R} fc | yes ok-not-x | io-both , _ , refl , _ , pr = pr zero
  transition-preserves-FSSpec {out f} fs (out {x = t} ok) tr-S {R} fc | no no-not-x with fs (rec-R-⊢-out t ok no-not-x fc) .CoInd⟦_⟧.unfold
  transition-preserves-FSSpec {out f} fs (out {x = t} ok) tr-S {R} fc | no no-not-x | client-end , _ , refl , ((win , _) , _) , _ = ⊥-elim (win-not-reduce win (rec-R-reduces t))
  transition-preserves-FSSpec {out f} {S' = _} {O false} fs (out {x = false} ok) (out {x = .false} ok') {R} fc | no no-not-x | io-true , _ , refl , ((ok-t , no-f) , _) , _ = ⊥-elim (no-f ok')
  transition-preserves-FSSpec {out f} {S' = _} {O true} fs (out {x = true} ok) (out {x = .true} ok') {R} fc | no no-not-x | io-true , _ , refl , _ , pr = pr zero
  transition-preserves-FSSpec {out f} {S' = _} {O false} fs (out {x = false} ok) (out {x = .false} ok') {R} fc | no no-not-x | io-false , _ , refl , _ , pr = pr zero
  transition-preserves-FSSpec {out f} {S' = _} {O true} fs (out {x = true} ok) (out {x = .true} ok') {R} fc | no no-not-x | io-false , _ , refl , ((ok-f , no-t) , _) , _ = ⊥-elim (no-t ok')
  transition-preserves-FSSpec {out f} {S' = _} {O false} fs (out {x = false} ok) (out {x = .false} ok') {R} fc | no no-not-x | io-both , _ , refl , ((ok-t , ok-f) , _) , pr = pr (suc zero)
  transition-preserves-FSSpec {out f} {S' = _} {O true} fs (out {x = true} ok) (out {x = .true} ok') {R} fc | no no-not-x | io-both , _ , refl , ((ok-t , ok-f) , _) , pr = pr zero

  transition-preserves-FairSubSpec : ∀{T T' S S' α} → FairSubtypingS T S → Transition T α T' → Transition S α S' → FairSubtypingS T' S'
  transition-preserves-FairSubSpec fs tr-T tr-S = spec-complete (transition-preserves-FSSpec (spec-sound fs) tr-T tr-S)
--------------------------------------------------------

  {- inp-inp without dom inclusion -}
  left-right-incl : ∀{f g} x → not x ∉ dom f → x ∈ dom f → x ∈ dom g → dom f ⊆ dom g
  left-right-incl false _ _ ok {false} _ = ok
  left-right-incl false no-x _ _ {true} ok = ⊥-elim (no-x ok)
  left-right-incl true no-x _ _ {false} ok = ⊥-elim (no-x ok)
  left-right-incl true _ _ ok {true} _ = ok

  left-right-incl-empty : ∀{f g} → true ∉ dom f → false ∉ dom f → dom f ⊆ dom g
  left-right-incl-empty no-x _ {true} ok = ⊥-elim (no-x ok)
  left-right-incl-empty _ no-x {false} ok = ⊥-elim (no-x ok)

  incl-full : ∀{f g} → true ∈ dom g → false ∈ dom g → dom f ⊆ dom g
  incl-full {f} {g} ok-t ok-f {false} _ = ok-f
  incl-full {f} {g} ok-t ok-f {true} _ = ok-t

  ¬left-right-incl : ∀{f g} x → x ∈ dom f → x ∉ dom g → ¬ (dom f ⊆ dom g)
  ¬left-right-incl b ok no-x incl = no-x (incl ok)

  -- FairSubtypingS leads to reduction of non-defined branches
  -- FSSPec gives information onyl about output domains
  ¬II-fsub : ∀{f g} → ¬ (dom f ⊆ dom g) → ¬ (FairSubtypingS (inp f) (inp g)) 
  ¬II-fsub {f} {g} no-incl fs with true ∈? f | false ∈? f
  ¬II-fsub {f} {g} no-incl fs | yes ok-t | yes ok-f with true ∈? g
  ¬II-fsub {f} {g} no-incl fs | yes ok-t | yes ok-f | yes ok-t-g with false ∈? g
  ¬II-fsub {f} {g} no-incl fs | yes ok-t | yes ok-f | yes ok-t-g | yes ok-f-g =
    no-incl (incl-full {f} {g} ok-t-g ok-f-g)
  ¬II-fsub {f} {g} no-incl fs | yes ok-t | yes ok-f | yes ok-t-g | no no-f-g with fs (R-out-f-comp ok-f) ε
  ... | _ , ε , win#def (out e) _ = e false out
  ... | _ , sync (out _) (inp {x = false}) ◅ ε , win#def _ def = no-f-g def
  ... | _ , sync (out _) (inp {x = false}) ◅ sync _ r ◅ red , Succ = no-f-g (transition->defined r)
  ¬II-fsub {f} {g} no-incl fs | yes ok-t | yes ok-f | no no-t-g with fs (R-out-t-comp ok-t) ε
  ... | _ , ε , win#def (out e) _ = e true out
  ... | _ , sync (out _) (inp {x = true}) ◅ ε , win#def _ def = no-t-g def
  ... | _ , sync (out _) (inp {x = true}) ◅ sync _ r ◅ red , Succ = no-t-g (transition->defined r)
  ¬II-fsub {f} {g} no-incl fs | no no-t | yes ok-f with false ∈? g
  ¬II-fsub {f} {g} no-incl fs | no no-t | yes ok-f | yes ok-f-g =
    no-incl (left-right-incl {f} {g} false no-t ok-f ok-f-g)   
  ¬II-fsub {f} {g} no-incl fs | no no-t | yes ok-f | no no-f-g with fs (R-out-f-comp ok-f) ε
  ... | _ , ε , win#def (out e) _ = e false out
  ... | _ , sync (out _) (inp {x = false}) ◅ ε , win#def _ def = no-f-g def
  ... | _ , sync (out _) (inp {x = false}) ◅ sync _ r ◅ red , Succ = no-f-g (transition->defined r)
  ¬II-fsub {f} {g} no-incl fs | yes ok-t | no no-f with true ∈? g
  ¬II-fsub {f} {g} no-incl fs | yes ok-t | no no-f | yes ok-t-g = 
    no-incl (left-right-incl {f} {g} true no-f ok-t ok-t-g)
  ¬II-fsub {f} {g} no-incl fs | yes ok-t | no no-f | no no-t-g with fs (R-out-t-comp ok-t) ε
  ... | _ , ε , win#def (out e) _ = e true out
  ... | _ , sync (out _) (inp {x = true}) ◅ ε , win#def _ def = no-t-g def
  ... | _ , sync (out _) (inp {x = true}) ◅ sync _ r ◅ red , Succ = no-t-g (transition->defined r)
  ¬II-fsub {f} {g} no-incl fs | no no-t | no no-f = no-incl (left-right-incl-empty {f} {g} no-t no-f)
  --------------------------------------------------------

  {- out-out implied end or dom inclusion -}
  FSSpec->end-incl : ∀{f g} → FSSpec-⊢ (out f , out g) → End (out f) ⊎ Witness g × dom g ⊆ dom f
  FSSpec->end-incl {f} {g} fs with true ∈? f | false ∈? f
  FSSpec->end-incl {f} {g} fs | yes ok-t | yes ok-f with fs (R-in-both-⊢-out ok-f) .CoInd⟦_⟧.unfold
  ... | client-end , _ , refl , ((() , _) , _) , _
  ... | io-true , _ , refl , ((ok-t-g , _) , _) , _ = inj₂ ((true , ok-t-g) , incl-full {g} {f} ok-t ok-f)
  ... | io-false , _ , refl , ((ok-f-g , _) , _) , _ = inj₂ ((false , ok-f-g) , incl-full {g} {f} ok-t ok-f)
  ... | io-both , _ , refl , ((ok-t-g , _) , _) , pr = inj₂ ((true , ok-t-g) , incl-full {g} {f} ok-t ok-f)
  FSSpec->end-incl {f} {g} fs | no no-t | yes ok-f with fs (R-in-f-⊢-out ok-f no-t) .CoInd⟦_⟧.unfold
  ... | client-end , _ , refl , ((() , _) , _) , _
  ... | io-true , _ , refl , _ , pr = ⊥-elim (¬nil-⊢ (pr zero))
  ... | io-false , _ , refl , ((ok-f-g , no-t-g) , _) , _ = inj₂ ((false , ok-f-g) , (left-right-incl {g} {f} false no-t-g ok-f-g ok-f))
  ... | io-both , _ , refl , _ , pr = ⊥-elim (¬nil-⊢ (pr zero))
  FSSpec->end-incl {f} {g} fs | yes ok-t | no no-f with fs (R-in-t-⊢-out ok-t no-f) .CoInd⟦_⟧.unfold
  ... | client-end , _ , refl , ((() , _) , _) , _
  ... | io-true , _ , refl , ((ok-t-g , no-f-g) , _) , _ = inj₂ ((true , ok-t-g) , (left-right-incl {g} {f} true no-f-g ok-t-g ok-t))
  ... | io-false , _ , refl , _ , pr = ⊥-elim (¬nil-⊢ (pr zero))
  ... | io-both , _ , refl , _ , pr = ⊥-elim (¬nil-⊢ (pr (suc zero)))
  FSSpec->end-incl {f} {g} fs | no no-t | no no-f = inj₁ (out λ{true → no-t ; false → no-f})
  --------------------------------------------------------

  fs-consistent : ∀{T S} → FairSubtypingS T S → ISF[ FSubIS ] (λ{(T , S) → FairSubtypingS T S}) (T , S)
  fs-consistent {nil} {S} _ = nil-any , S , refl , tt , λ ()
  fs-consistent {inp f} {nil} fs = ⊥-elim (¬Inil-fsub fs)
  fs-consistent {inp f} {inp g} fs with true ∈? f | false ∈? f
  fs-consistent {inp f} {inp g} fs | yes ok-t | yes ok-f with true ∈? g
  fs-consistent {inp f} {inp g} fs | yes ok-t | yes ok-f | yes ok-t-g with false ∈? g
  fs-consistent {inp f} {inp g} fs | yes ok-t | yes ok-f | yes ok-t-g | yes ok-f-g =
    let prems = λ{
          zero → transition-preserves-FairSubSpec fs inp inp ;
          (suc zero) → transition-preserves-FairSubSpec fs inp inp
          } in
    inp-inp , _ , refl , incl-full {f} {g} ok-t-g ok-f-g , prems
  fs-consistent {inp f} {inp g} fs | yes ok-t | yes ok-f | yes ok-t-g | no no-f-g =
    ⊥-elim (¬II-fsub (¬left-right-incl {f} {g} false ok-f no-f-g) fs)
  fs-consistent {inp f} {inp g} fs | yes ok-t | yes ok-f | no no-t-g =
    ⊥-elim (¬II-fsub (¬left-right-incl {f} {g} true ok-t no-t-g) fs)
  fs-consistent {inp f} {inp g} fs | no no-t | yes ok-f with false ∈? g
  fs-consistent {inp f} {inp g} fs | no no-t | yes ok-f | yes ok-f-g =
    let prems = λ{
          zero → transition-preserves-FairSubSpec fs inp inp ;
          (suc zero) → transition-preserves-FairSubSpec fs inp inp
          } in
    inp-inp , _ , refl , left-right-incl {f} {g} false no-t ok-f ok-f-g , prems
  fs-consistent {inp f} {inp g} fs | no no-t | yes ok-f | no no-f-g = ⊥-elim (¬II-fsub (¬left-right-incl {f} {g} false ok-f no-f-g) fs)
  fs-consistent {inp f} {inp g} fs | yes ok-t | no no-f with true ∈? g
  fs-consistent {inp f} {inp g} fs | yes ok-t | no no-f | yes ok-t-g = 
    let prems = λ{
          zero → transition-preserves-FairSubSpec fs inp inp ;
          (suc zero) → transition-preserves-FairSubSpec fs inp inp
          } in
    inp-inp , _ , refl , left-right-incl {f} {g} true no-f ok-t ok-t-g , prems
  fs-consistent {inp f} {inp g} fs | yes ok-t | no no-f | no no-t-g = ⊥-elim (¬II-fsub (¬left-right-incl {f} {g} true ok-t no-t-g) fs)
  fs-consistent {inp f} {inp g} fs | no no-t | no no-f = end-def , _ , refl , (inp (λ{true → no-t ; false → no-f}) , inp) , λ ()
  fs-consistent {inp f} {out g} fs with true ∈? f
  ... | yes ok-t = ⊥-elim (¬IO-fsub ok-t fs)
  ... | no no-t with false ∈? f
  ... | yes ok-f = ⊥-elim (¬IO-fsub ok-f fs)
  ... | no no-f = end-def , _ , refl , (inp (λ{true → no-t ; false → no-f}) , out) , λ ()
  fs-consistent {out f} {nil} fs = ⊥-elim (¬Onil-fsub fs)
  fs-consistent {out f} {inp g} fs with true ∈? f | false ∈? f
  ... | yes ok-t | yes ok-f = ⊥-elim (¬OI-fsub ok-f fs)
  ... | no no-t | yes ok-f = ⊥-elim (¬OI-fsub ok-f fs)
  ... | yes ok-t | no no-f = ⊥-elim (¬OI-fsub ok-t fs)
  ... | no no-t | no no-f = end-def , _ , refl , (out (λ{true → no-t ; false → no-f}) , inp) , λ ()
  fs-consistent {out f} {out g} fs with FSSpec->end-incl (spec-sound fs)
  ... | inj₁ end = end-def , _ , refl , (end , out) , λ ()
  ... | inj₂ (wit , incl) with true ∈? g | false ∈? g
  ... | yes ok-t | yes ok-f =
      let prems = λ{
            zero → transition-preserves-FairSubSpec fs (out (incl ok-t)) (out ok-t) ; 
            (suc zero) → transition-preserves-FairSubSpec fs (out (incl ok-f)) (out ok-f)
            } in
      out-out-both , _ , refl , (wit , incl , ok-t , ok-f) , prems  
  ... | no no-t | yes ok-f = 
      out-out-false , _ , refl , (wit , incl , ok-f , no-t) , λ{zero → transition-preserves-FairSubSpec fs (out (incl ok-f)) (out ok-f)}
  ... | yes ok-t | no no-f = 
      out-out-true , _ , refl , (wit , incl , ok-t , no-f) , λ{zero → transition-preserves-FairSubSpec fs (out (incl ok-t)) (out ok-t)}
  fs-consistent {out f} {out g} fs | inj₂ ((false , ok-f) , incl) | no no-t | no no-f = ⊥-elim (no-f ok-f)
  fs-consistent {out f} {out g} fs | inj₂ ((true , ok-t) , incl) | no no-t | no no-f = ⊥-elim (no-t ok-t)

  fs-complete : ∀{T S} → FairSubtypingS T S → T ≤F S
  fs-complete = bounded-coind[ FSubIS , FSubCOIS ] (λ{(T , S) → FairSubtypingS T S}) fs-bounded fs-consistent
