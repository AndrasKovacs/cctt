
module Conversion where

import Common
import Core
import Interval
import Substitution

{-|
TODO: conversion is not the best possible here, it pushes and stores
substitutions on each iteration.  It would be better to have *two* substitutions
as args, one for each side, and force each side with the respective
substitution.

Since we're mostly interested in closed evaluation benchmarks which compute to
small values, this doesn't matter much.
-}

convCl :: IDomArg => NCofArg => DomArg => Closure -> Closure -> Bool
convCl t t' = bind \v -> conv (capp t v) (capp t' v)
{-# inline convCl #-}

convICl :: IDomArg => NCofArg => DomArg => IClosure -> IClosure -> Bool
convICl t t' = bindI \(IVar -> i) -> conv (icapp t i) (icapp t' i)
{-# inline convICl #-}

convIVar :: NCofArg => IVar -> IVar -> Bool
convIVar r r' = unF (forceIVar r) == unF (forceIVar r')
{-# inline convIVar #-}

convI :: NCofArg => I -> I -> Bool
convI r r' = unF (forceI r) == unF (forceI r')
{-# inline convI #-}

convNCof :: NeCof -> NeCof -> Bool
convNCof ncof ncof' = case (ncof, ncof') of
  (NCEq i j    , NCEq i' j'    ) -> i == i' && j == j'
  (NCAnd c1 c2 , NCAnd c1' c2' ) -> convNCof c1 c1' && convNCof c2 c2'
  _                              -> False

convCof :: F VCof -> F VCof -> Bool
convCof cof cof' = case (unF cof, unF cof') of
  (VCTrue      , VCTrue       ) -> True
  (VCFalse     , VCFalse      ) -> True
  (VCNe ncof _ , VCNe ncof' _ ) -> convNCof ncof ncof'
  _                             -> False

convNSys :: IDomArg => NCofArg => DomArg => NSystem VCof -> NSystem VCof -> Bool
convNSys sys sys' = case (sys, sys') of
  (NSEmpty, NSEmpty) -> True
  (NSCons cof t sys, NSCons cof' t' sys') ->
       convCof (forceCof cof) (forceCof cof')
    && bindI (\_ -> bindCof (forceCof cof) (conv t t')) && convNSys sys sys'
  _ -> False

-- | Assumption: takes stuck neutrals. But note: values in stuck neutrals are
--   *not* forced! Only the head computation is stuck in a neutral.
convNe :: IDomArg => NCofArg => DomArg => Ne -> Ne -> Bool
convNe t t' = case (,) $$! unSubNe t $$! unSubNe t' of
  (NLocalVar x   , NLocalVar x'      ) -> x == x'
  (NApp t u      , NApp t' u'        ) -> convNe t t' && conv u u'
  (NPApp p t u r , NPApp p' t' u' r' ) -> convNe p p' && convI r r'
  (NProj1 n      , NProj1 n'         ) -> convNe n n'
  (NProj2 n      , NProj2 n'         ) -> convNe n n'

  (NCoe r1 r2 _ a t, NCoe r1' r2' _ a' t') ->
    convI r1 r1' && convI r2 r2' && bindI (\_ -> conv a a') && conv t t'

  (NHCom r1 r2 _ a sys t, NHCom r1' r2' _ a' sys' t') ->
    convI r1 r1' && convI r2 r2' && bindI (\_ -> conv a a') && convNSys sys sys' && conv t t'

  (NUnglue a sys , NUnglue a' sys' ) -> conv a a' && convNSys sys sys'
  (NGlue a sys   , NGlue a' sys'   ) -> conv a a' && convNSys sys sys'

  (NNatElim p z s n, NNatElim p' z' s' n') -> conv p p' && conv z z' && conv s s' && convNe n n'
  _ -> False


conv :: IDomArg => NCofArg => DomArg => Val -> Val -> Bool
conv t t' = case (,) $$! unF (force t) $$! unF (force t') of

  -- canonical
  (VNe n _        , VNe n' _          ) -> convNe n n'
  (VGlueTy a sys  , VGlueTy a' sys'   ) -> conv a a' && convNSys (_nsys sys) (_nsys sys)
  (VPi _ a b      , VPi _ a' b'       ) -> conv a a' && convCl b b'
  (VLam _ t       , VLam _ t'         ) -> convCl t t'
  (VPathP _ p t u , VPathP _ p' t' u' ) -> convICl p p' && conv t t' && conv u u'
  (VPLam _ _ _ t  , VPLam _ _ _ t'    ) -> convICl t t'
  (VSg _ a b      , VSg _ a' b'       ) -> conv a a' && convCl b b'
  (VPair t u      , VPair t' u'       ) -> conv t t' && conv u u'
  (VU             , VU                ) -> True
  (VNat           , VNat              ) -> True
  (VZero          , VZero             ) -> True
  (VSuc n         , VSuc n'           ) -> conv n n'

  -- eta rules
  (VLam _ t      , F -> t'            ) -> bind \v -> conv (capp t v) (app t' v)
  (F -> t        , VLam _ t'          ) -> bind \v -> conv (app t v) (capp t' v)
  (VPair t u     , F -> t'            ) -> conv t (proj1 t') && conv u (proj2 t')
  (F -> t        , VPair t' u'        ) -> conv (proj1 t) t' && conv (proj2 t) u'
  (VPLam l r _ t , F -> t'            ) -> bindI \(IVar -> i) -> conv (icapp t i) (papp t' l r (F i))
  (F -> t        , VPLam l r _ t'     ) -> bindI \(IVar -> i) -> conv (papp t l r (F i)) (icapp t' i)
  _                                     -> False
