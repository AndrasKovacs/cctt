
-- https://github.com/RedPRL/redtt/blob/master/library/cool/s3-to-join.red

import prelude
import data.s1
import data.s2
import data.s3
import data.join
import basics.isotoequiv

-- forward map

-- pseudo-connection
def s3→join/cnx (b : s1) (i m : 𝕀) : join s1 s1 =
  comp 0 i (inl base) [
  | m=0 → refl
  | m=1 i → push base b i
  ]

def s3→join/k01 :
  [i j m] join s1 s1 [
  | i=1 | ∂[j] → s3→join/cnx base i m
  | m=0 → inl base
  | m=1 → push (loop j) base i
  ]
  =
  λ i j m →
    comp 1 i (s3→join/cnx base 1 m) [
    | ∂[j] i → s3→join/cnx base i m
    | m=0 → refl
    | m=1 i → push (loop j) base i
    ]

def s3→join/cube/filler (i j k m : 𝕀) : join s1 s1 =
  comp 1 m (push (loop j) (loop k) i) [
  | i=1 | ∂[j] → s3→join/cnx (loop k) i
  | (i=0 | ∂[k]) m → s3→join/k01 i j m
  ]

def s3→join : s3 → join s1 s1 =
  elim [
  | base → inl base
  | cube i j k → s3→join/cube/filler i j k 0
  ]
