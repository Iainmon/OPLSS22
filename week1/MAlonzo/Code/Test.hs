{-# LANGUAGE EmptyDataDecls, ExistentialQuantification,
  ScopedTypeVariables, NoMonomorphismRestriction, Rank2Types #-}
module MAlonzo.Code.Test where
import qualified MAlonzo.RTE
name3 = "Test.Bool.false"
name4 = "Test.\172"
d4 (C2) = MAlonzo.RTE.mazCoerce C3
d4 v0 = MAlonzo.RTE.mazCoerce (d_1_4 (MAlonzo.RTE.mazCoerce v0))
  where d_1_4 (C3) = MAlonzo.RTE.mazCoerce C2
        d_1_4 v0 = MAlonzo.RTE.mazIncompleteMatch name4
name2 = "Test.Bool.true"
name1 = "Test.Bool"
d1 = ()
 
data T1 = C2
        | C3