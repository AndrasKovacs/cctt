
module Conversion where

import Common
import CoreTypes
import Core hiding (freshIS)
import Interval
import Substitution

----------------------------------------------------------------------------------------------------

type Subl = (?subl :: Sub)
type Subr = (?subr :: Sub)

class Conv a where
  conv  :: NCofArg => DomArg => a -> a -> Bool
  convS :: NCofArg => DomArg => Subl => Subr => a -> a -> Bool

frcSl :: Subl => NCofArg => DomArg => Force a b => a -> F b
frcSl a = let ?sub = ?subl in frcS a; {-# inline frcSl #-}

frcSr :: Subr => NCofArg => DomArg => Force a b => a -> F b
frcSr a = let ?sub = ?subr in frcS a; {-# inline frcSr #-}

freshIS :: (Subl => Subr => NCofArg => IVar -> a) -> (Subl => Subr => NCofArg => a)
freshIS act =
  let fresh = dom ?cof in
  let ?subl = setDom (fresh+1) ?subl `ext` IVar fresh in
  let ?subr = setDom (fresh+1) ?subr `ext` IVar fresh in
  let ?cof  = setDom (fresh+1) ?cof  `ext` IVar fresh in
  act fresh
{-# inline freshIS #-}

instance Conv Val where
  conv t t' = case (,) $$! unF (frc t) $$! unF (frc t') of

    -- canonical
    (VNe n _        , VNe n' _          ) -> conv n n'
    (VGlueTy a sys _, VGlueTy a' sys' _ ) -> conv a a' && conv sys sys'
    (VPi a b        , VPi a' b'         ) -> conv a a' && conv b b'
    (VLam t         , VLam t'           ) -> conv t t'
    (VPathP a t u   , VPathP a' t' u'   ) -> conv a a' && conv t t' && conv u u'
    (VPLam _ _ t    , VPLam _ _ t'      ) -> conv t t'
    (VSg a b        , VSg a' b'         ) -> conv a a' && conv b b'
    (VPair t u      , VPair t' u'       ) -> conv t t' && conv u u'
    (VU             , VU                ) -> True
    (VNat           , VNat              ) -> True
    (VZero          , VZero             ) -> True
    (VSuc n         , VSuc n'           ) -> conv n n'

    -- eta rules
    (VLam t      , F -> t'      ) -> fresh \x -> conv (t ∙ x) (t' ∙ x)
    (F -> t      , VLam t'      ) -> fresh \x -> conv (t ∙ x) (t' ∙ x)
    (VPair t u   , F -> t'      ) -> conv t (proj1 t') && conv u (proj2 t')
    (F -> t      , VPair t' u'  ) -> conv (proj1 t) t' && conv (proj2 t) u'
    (VPLam l r t , F -> t'      ) -> freshI \(IVar -> i) -> conv (t ∙ i) (papp t' l r (F i))
    (F -> t      , VPLam l r t' ) -> freshI \(IVar -> i) -> conv (papp t l r (F i)) (t' ∙ i)
    _                             -> False

  convS t t' = case (,) $$! unF (frcSl t) $$! unF (frcSr t') of

    -- canonical
    (VNe n _        , VNe n' _          ) -> convS n n'
    (VGlueTy a sys _, VGlueTy a' sys' _ ) -> convS a a' && convS sys sys'
    (VPi a b        , VPi a' b'         ) -> convS a a' && convS b b'
    (VLam t         , VLam t'           ) -> convS t t'
    (VPathP a t u   , VPathP a' t' u'   ) -> convS a a' && convS t t' && convS u u'
    (VPLam _ _ t    , VPLam _ _ t'      ) -> convS t t'
    (VSg a b        , VSg a' b'         ) -> convS a a' && convS b b'
    (VPair t u      , VPair t' u'       ) -> convS t t' && convS u u'
    (VU             , VU                ) -> True
    (VNat           , VNat              ) -> True
    (VZero          , VZero             ) -> True
    (VSuc n         , VSuc n'           ) -> convS n n'

    -- eta rules
    (VLam t      , F -> t'      ) -> fresh \x -> convS (t ∙ x) (t' ∙ x)
    (F -> t      , VLam t'      ) -> fresh \x -> convS (t ∙ x) (t' ∙ x)
    (VPair t u   , F -> t'      ) -> convS t (proj1 t') && convS u (proj2 t')
    (F -> t      , VPair t' u'  ) -> convS (proj1 t) t' && convS (proj2 t) u'
    (VPLam l r t , F -> t'      ) -> freshIS \(IVar -> i) -> convS (t ∙ i) (papp t' l r (F i))
    (F -> t      , VPLam l r t' ) -> freshIS \(IVar -> i) -> convS (papp t l r (F i)) (t' ∙ i)
    _                             -> False

instance Conv Ne where

  conv t t' = case (t, t') of
    (NLocalVar x   , NLocalVar x'      ) -> x == x'
    (NApp t u      , NApp t' u'        ) -> conv t t' && conv u u'
    (NPApp p t u r , NPApp p' t' u' r' ) -> conv p p' && conv r r'
    (NProj1 n      , NProj1 n'         ) -> conv n n'
    (NProj2 n      , NProj2 n'         ) -> conv n n'

    (NCoe r1 r2 a t, NCoe r1' r2' a' t') ->
      conv r1 r1' && conv r2 r2' && conv a a' && conv t t'

    (NHCom r1 r2 a sys t, NHCom r1' r2' a' sys' t') ->
      conv r1 r1' && conv r2 r2' && conv a a' && conv sys sys' && conv t t'

    (NUnglue a sys    , NUnglue a' sys'      ) -> conv a a' && conv sys sys'
    (NGlue a sys      , NGlue a' sys'        ) -> conv a a' && conv sys sys'
    (NNatElim p z s n , NNatElim p' z' s' n' ) -> conv p p' && conv z z' && conv s s' && conv n n'

    (NSub t s , t'        ) -> let ?subl = s; ?subr = idSub (dom ?cof) in convS t t'
    (t        , NSub t' s ) -> let ?subl = idSub (dom ?cof); ?subr = s in convS t t'
    _                       -> False

  convS t t' = case (t, t') of
    (NLocalVar x   , NLocalVar x'      ) -> x == x'
    (NApp t u      , NApp t' u'        ) -> convS t t' && convS u u'
    (NPApp p t u r , NPApp p' t' u' r' ) -> convS p p' && convS r r'
    (NProj1 n      , NProj1 n'         ) -> convS n n'
    (NProj2 n      , NProj2 n'         ) -> convS n n'

    (NCoe r1 r2 a t, NCoe r1' r2' a' t') ->
      convS r1 r1' && convS r2 r2' && convS a a' && convS t t'

    (NHCom r1 r2 a sys t, NHCom r1' r2' a' sys' t') ->
      convS r1 r1' && convS r2 r2' && convS a a' && convS sys sys' && convS t t'

    (NUnglue a sys    , NUnglue a' sys'      ) -> convS a a' && convS sys sys'
    (NGlue a sys      , NGlue a' sys'        ) -> convS a a' && convS sys sys'
    (NNatElim p z s n , NNatElim p' z' s' n' ) -> convS p p' && convS z z' && convS s s' && convS n n'

    (NSub t s , t'        ) -> let ?subl = doSub ?subl s in convS t t'
    (t        , NSub t' s ) -> let ?subr = doSub ?subr s in convS t t'
    _                       -> False

instance Conv (BindI Val) where
  conv  t t' = freshI  \(IVar -> i) -> conv (t ∙ i) (t' ∙ i); {-# inline conv #-}
  convS t t' = freshIS \(IVar -> i) -> convS (t ∙ i) (t' ∙ i); {-# inline convS #-}

instance Conv (BindILazy Val) where
  conv  t t' = freshI  \(IVar -> i) -> conv (t ∙ i) (t' ∙ i); {-# inline conv #-}
  convS t t' = freshIS \(IVar -> i) -> convS (t ∙ i) (t' ∙ i); {-# inline convS #-}

instance Conv (BindNeCofLazy Val) where
  conv t t' = uf
  convS t t' = uf

instance Conv (BindNeCof a) where
  conv t t' = uf
  convS t t' = uf

instance Conv I where
  conv  r r' = frc r   == frc r'  ; {-# inline conv #-}
  convS r r' = frcSl r == frcSr r'; {-# inline convS #-}

instance Conv NeSys where
  conv t t' = case (t, t') of
    (NSEmpty      , NSEmpty        ) -> True
    (NSCons t sys , NSCons t' sys' ) -> conv t t' && conv sys sys'
    _ -> False

  convS t t' = case (t, t') of
    (NSEmpty      , NSEmpty        ) -> True
    (NSCons t sys , NSCons t' sys' ) -> convS t t' && convS sys sys'
    _ -> False

instance Conv NeSysHCom where
  conv t t' = case (t, t') of
    (NSHEmpty      , NSHEmpty        ) -> True
    (NSHCons t sys , NSHCons t' sys' ) -> conv t t' && conv sys sys'
    _ -> False

  convS t t' = case (t, t') of
    (NSHEmpty      , NSHEmpty        ) -> True
    (NSHCons t sys , NSHCons t' sys' ) -> convS t t' && convS sys sys'
    _ -> False

instance Conv VSys where
instance Conv VSysHCom where

instance Conv NeSysSub where
  conv  t t' = conv (frc t) (frc t')
  convS t t' = convS (frc

instance Conv NeSysHComSub where

instance Conv NamedClosure where

instance Conv NamedIClosure where
