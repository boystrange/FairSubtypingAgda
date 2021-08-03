--------------------------------------------------------------------------------
-- This is part of Agda Inference Systems 

{-# OPTIONS --guardedness #-}

module is-lib.InfSys {𝓁} where
  open import is-lib.InfSys.Base {𝓁} public 
  open import is-lib.InfSys.Induction {𝓁} public
  open import is-lib.InfSys.Coinduction {𝓁} public
  open import is-lib.InfSys.FlexCoinduction {𝓁} public
  open MetaRule public
  open FinMetaRule public
  open IS public