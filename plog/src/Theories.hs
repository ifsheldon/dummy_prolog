module Theories
  ( Theory,
  )
where

import SigmaSignature

data Theory = Theory [Formula]
