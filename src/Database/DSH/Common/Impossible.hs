{-# LANGUAGE TemplateHaskell #-}

module Database.DSH.Common.Impossible (impossible, unimplemented) where

import qualified Language.Haskell.TH as TH

impossible :: TH.ExpQ
impossible = do
  loc <- TH.location
  let pos =  (TH.loc_filename loc, fst (TH.loc_start loc), snd (TH.loc_start loc))
  let message = "DSH: Impossible happened at " ++ show pos
  return (TH.AppE (TH.VarE 'error) (TH.LitE (TH.StringL message)))

unimplemented :: TH.ExpQ
unimplemented = do
  loc <- TH.location
  let pos =  (TH.loc_filename loc, fst (TH.loc_start loc), snd (TH.loc_start loc))
  let message = "DSH: Unimplemented at " ++ show pos
  return (TH.AppE (TH.VarE 'error) (TH.LitE (TH.StringL message)))
