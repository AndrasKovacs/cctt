
module Conversion where

import Common
import CoreTypes
import Core
import Interval
import Substitution

----------------------------------------------------------------------------------------------------

class Conv a where
  conv :: NCofArg => DomArg => a -> a -> Bool

instance Conv Val where
  conv t t' = case (,) $$! unF (frc t) $$! unF (frc t') of

    -- rigid match
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

    -- eta
    (VLam t         , F -> t'           ) -> fresh \x -> conv (t ∙ x) (t' ∙ x)
    (F -> t         , VLam t'           ) -> fresh \x -> conv (t ∙ x) (t' ∙ x)
    (VPair t u      , F -> t'           ) -> conv t (proj1 t') && conv u (proj2 t')
    (F -> t         , VPair t' u'       ) -> conv (proj1 t) t' && conv (proj2 t) u'
    (VPLam l r t    , F -> t'           ) -> freshI \(IVar -> i) -> conv (t ∙ i) (papp l r t' (F i))
    (F -> t         , VPLam l r t'      ) -> freshI \(IVar -> i) -> conv (papp l r t (F i)) (t' ∙ i)

    (VSub{}         , _                 ) -> impossible
    (_              , VSub{}            ) -> impossible
    _                                     -> False

instance Conv Ne where

  conv t t' = case (,) $$! unSubNe t $$! unSubNe t' of
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

    (NSub{} , _      ) -> impossible
    (t      , NSub{} ) -> impossible
    _                  -> False

instance Conv NeCof where
  conv c c' = case (c, c') of
    (NCEq i j   , NCEq i' j'   ) -> conv i i' && conv j j'
    (NCAnd c1 c2, NCAnd c1' c2') -> conv c1 c1' && conv c2 c2'
    _                            -> False

instance Conv (BindI Val) where
  conv t t' = freshI \(IVar -> i) -> conv (t ∙ i) (t' ∙ i); {-# inline conv #-}

instance Conv (BindILazy Val) where
  conv t t' = freshI \(IVar -> i) -> conv (t ∙ i) (t' ∙ i); {-# inline conv #-}

instance Conv a => Conv (BindCofLazy a) where
  conv t t' = conv (t^.binds) (t'^.binds)
           && assumeCof (t^.binds) (conv (t^.body) (t'^.body))
  {-# inline conv #-}

instance Conv a => Conv (BindCof a) where
  conv t t' = conv (t^.binds) (t'^.binds)
           && assumeCof (t^.binds) (conv (t^.body) (t'^.body))
  {-# inline conv #-}

instance Conv I where
  conv r r' = r == r'; {-# inline conv #-}

instance Conv NeSys where
  conv t t' = case (t, t') of
    (NSEmpty      , NSEmpty        ) -> True
    (NSCons t sys , NSCons t' sys' ) -> conv t t' && conv sys sys'
    _                                -> False

instance Conv NeSysHCom where
  conv t t' = case (t, t') of
    (NSHEmpty      , NSHEmpty        ) -> True
    (NSHCons t sys , NSHCons t' sys' ) -> conv t t' && conv sys sys'
    _                                  -> False

instance Conv NamedClosure where
  conv t t' = fresh \x -> conv (t ∙ x) (t' ∙ x); {-# inline conv #-}

instance Conv NamedIClosure where
  conv t t' = freshI \(IVar -> i) -> conv (t ∙ i) (t' ∙ i); {-# inline conv #-}

instance Conv VCof where
  conv c c' = case (c, c') of
    (VCTrue   , VCTrue    ) -> True
    (VCFalse  , VCFalse   ) -> True
    (VCNe c _ , VCNe c' _ ) -> conv c c'
    _                       -> False
  {-# inline conv #-}
