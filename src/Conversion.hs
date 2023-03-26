
module Conversion where

import Common
import CoreTypes
import Core
import Interval

-- NOTE: every conv method expects forced arguments, except Val which forces its argument.
-- A sneaky complication is in NLApp where a forced NLApp t i does *not* imply that "i" is forced!
----------------------------------------------------------------------------------------------------

class Conv a where
  conv :: NCofArg => DomArg => a -> a -> Bool

instance Conv Val where
  conv t t' = case frc t // frc t' of

    -- rigid match
    (VNe n _        , VNe n' _          ) -> conv n n'
    (VGlueTy a sys  , VGlueTy a' sys'   ) -> conv a a' && conv (fst sys) (fst sys')
    (VPi a b        , VPi a' b'         ) -> conv a a' && conv b b'
    (VLam t         , VLam t'           ) -> conv t t'
    (VPath a t u    , VPath a' t' u'    ) -> conv a a' && conv t t' && conv u u'
    (VPLam _ _ t    , VPLam _ _ t'      ) -> conv t t'
    (VSg a b        , VSg a' b'         ) -> conv a a' && conv b b'
    (VPair t u      , VPair t' u'       ) -> conv t t' && conv u u'
    (VU             , VU                ) -> True
    (VLine a        , VLine a'          ) -> conv a a'
    (VLLam t        , VLLam t'          ) -> conv t t'
    (VTyCon x ts    , VTyCon x' ts'     ) -> x == x' && conv ts ts'
    (VDCon _ i sp   , VDCon _ i' sp'    ) -> i == i' && conv sp sp'

    -- This is useful for testing elaboration, where it's annoying to fail on
    -- TODO. This is safe (doesn't affect type safety & termination), but of
    -- course it can be unsound.
    (VTODO          , VTODO             ) -> True

    -- eta
    (VLam t         , t'                ) -> fresh \x -> conv (t ∙ x) (t' ∙ x)
    (t              , VLam t'           ) -> fresh \x -> conv (t ∙ x) (t' ∙ x)
    (VPair t u      , t'                ) -> conv t (proj1 t') && conv u (proj2 t')
    (t              , VPair t' u'       ) -> conv (proj1 t) t' && conv (proj2 t) u'
    (VPLam l r t    , t'                ) -> freshI \(IVar -> i) -> conv (t ∙ i) (papp l r t' i)
    (t              , VPLam l r t'      ) -> freshI \(IVar -> i) -> conv (papp l r t i) (t' ∙ i)
    (VLLam t        , t'                ) -> freshI \(IVar -> i) -> conv (t ∙ i) (lapp t' i)
    (t              , VLLam t'          ) -> freshI \(IVar -> i) -> conv (lapp t i) (t' ∙ i)

    (VSub{}         , _                 ) -> impossible
    (ft             , VSub{}            ) -> impossible
    _                                     -> False

instance Conv Ne where

  conv t t' = case unSubNe t // unSubNe t' of
    (NLocalVar x   , NLocalVar x'      ) -> x == x'
    (NApp t u      , NApp t' u'        ) -> conv t t' && conv u u'
    (NPApp p t u r , NPApp p' t' u' r' ) -> conv p p' && conv r r'
    (NProj1 n      , NProj1 n'         ) -> conv n n'
    (NProj2 n      , NProj2 n'         ) -> conv n n'
    (NLApp t i     , NLApp t' i'       ) -> conv t t' && conv (frc i) (frc i')

    (NCoe r1 r2 a t, NCoe r1' r2' a' t') ->
      conv r1 r1' && conv r2 r2' && conv a a' && conv t t'

    (NHCom r1 r2 _ sys t, NHCom r1' r2' _ sys' t') ->
      conv r1 r1' && conv r2 r2' && conv sys sys' && conv t t'

    -- the types of the "a"-s can be different Glue-s a priori, that's
    -- why we first convert sys-es. Neutrals of different types can
    -- be converted, and then the type equality is part of the output,
    -- but the "a" here aren't neutrals!
    (NUnglue a sys    , NUnglue a' sys'      ) -> conv sys sys' && conv a a'


    (NElim _   ms t   , NElim _ ms' t'       ) -> conv t t' && conv ms ms'
    (NGlue b _ fib    , NGlue b' _ fib'      ) -> conv b b' && conv fib fib'

    -- Glue eta
    -- A bit ugly that we put "mempty"-s there, and potentially dodgy, but the only
    -- way conversion checking can succeed here is when the VNe-s are immediately consumed.
    (NGlue b sys fib  , t'                   ) -> conv b (VNe (NUnglue t' sys) mempty)
    (t                , NGlue b' sys' fib'   ) -> conv (VNe (NUnglue t sys') mempty) b'

    (NSub{} , _      ) -> impossible
    (t      , NSub{} ) -> impossible
    _                  -> False

instance Conv NeCof where
  conv c c' = case (c, c') of
    (NCEq i j   , NCEq i' j'   ) -> conv i i' && conv j j'
    (NCAnd c1 c2, NCAnd c1' c2') -> conv c1 c1' && conv c2 c2'
    _                            -> False

instance Conv VDSpine where
  conv sp sp' = case (sp, sp') of
    (VDNil         , VDNil           ) -> True
    (VDInd t sp    , VDInd t' sp'    ) -> conv t t' && conv sp sp'
    (VDHInd t _ sp , VDHInd t' _ sp' ) -> conv t t' && conv sp sp'
    (VDExt t _ sp  , VDExt t' _ sp'  ) -> conv t t' && conv sp sp'
    _                                  -> impossible

instance Conv VMethods where
  conv ms ms' = case (ms, ms') of
    (VMNil         , VMNil          ) -> True
    (VMCons xs t ms, VMCons _ t' ms') -> convMethod xs t t' && conv ms ms'
    _                                 -> impossible

convMethod :: NCofArg => DomArg => [Name] -> EvalClosure -> EvalClosure -> Bool
convMethod xs (EC s e t) (EC s' e' t') = case xs of
  []   -> conv (let ?env = e; ?sub = s in eval t) (let ?env = e'; ?sub = s' in eval t')
  _:xs -> fresh \x -> convMethod xs (EC s (EDef e x) t) (EC s' (EDef e x) t')

instance Conv a => Conv [a] where
  conv as as' = case (as, as') of
    ([], [])       -> True
    (a:as, a':as') -> conv a a' && conv as as'
    _              -> False
  {-# inline conv #-}

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

instance Conv NeCof' where
  conv (NeCof' _ c) (NeCof' _ c') = conv c c'
  {-# inline conv #-}

instance Conv Env where
  conv e e' = case (e, e') of
    (ENil     , ENil       ) -> True
    (EDef e t , EDef e' t' ) -> conv e e' && conv t t'
    _                        -> False
