--------------------------------------------------------------------------------
-- This is part of Agda Inference Systems 

{-# OPTIONS --sized-types #-}

module is-lib.SInfSys {𝓁} where
  open import is-lib.InfSys.Base {𝓁} public 
  open import is-lib.InfSys.Induction {𝓁} public
  open import is-lib.InfSys.SCoinduction {𝓁} public
  open import is-lib.InfSys.FlexSCoinduction {𝓁} public
  open MetaRule public
  open FinMetaRule public
  open IS public