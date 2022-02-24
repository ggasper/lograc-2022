{-# LANGUAGE BangPatterns, EmptyDataDecls, EmptyCase,
             ExistentialQuantification, ScopedTypeVariables,
             NoMonomorphismRestriction, RankNTypes, PatternSynonyms,
             OverloadedStrings #-}
module MAlonzo.Code.Ex1 where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text

-- Ex1.Bool
d_Bool_2 = ()
data T_Bool_2 = C_true_4 | C_false_6
-- Ex1._⊕_
d__'8853'__8 :: T_Bool_2 -> T_Bool_2 -> T_Bool_2
d__'8853'__8 v0 v1
  = case coe v0 of
      C_true_4
        -> case coe v1 of
             C_true_4 -> coe C_false_6
             C_false_6 -> coe v0
             _ -> MAlonzo.RTE.mazUnreachableError
      C_false_6 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Ex1.ℕ
d_ℕ_12 = ()
data T_ℕ_12 = C_zero_14 | C_suc_16 Integer
-- Ex1.incr
d_incr_18 :: Integer -> Integer
d_incr_18 v0 = coe addInt (coe (1 :: Integer)) (coe v0)
-- Ex1.decr
d_decr_22 :: Integer -> Integer
d_decr_22 v0
  = case coe v0 of
      0 -> coe (0 :: Integer)
      _ -> coe subInt (coe v0) (coe (1 :: Integer))
-- Ex1.triple
d_triple_26 :: Integer -> Integer
d_triple_26 v0
  = case coe v0 of
      0 -> coe (0 :: Integer)
      _ -> let v1 = subInt (coe v0) (coe (1 :: Integer)) in
           coe addInt (coe (3 :: Integer)) (coe d_triple_26 (coe v1))
-- Ex1._+_
d__'43'__30 = ((+) :: Integer -> Integer -> Integer)
-- Ex1._*_
d__'42'__38 = ((*) :: Integer -> Integer -> Integer)
-- Ex1._^_
d__'94'__46 :: Integer -> Integer -> Integer
d__'94'__46 v0 v1
  = case coe v1 of
      0 -> coe (1 :: Integer)
      _ -> let v2 = subInt (coe v1) (coe (1 :: Integer)) in
           coe mulInt (coe v0) (coe d__'94'__46 (coe v0) (coe v2))
-- Ex1.Bin
d_Bin_54 = ()
data T_Bin_54
  = C_'10216''10217'_56 | C__O_58 T_Bin_54 | C__I_60 T_Bin_54
-- Ex1.b-incr
d_b'45'incr_62 :: T_Bin_54 -> T_Bin_54
d_b'45'incr_62 v0
  = case coe v0 of
      C_'10216''10217'_56 -> coe C__I_60 (coe v0)
      C__O_58 v1 -> coe C__I_60 (coe v1)
      C__I_60 v1 -> coe C__O_58 (coe d_b'45'incr_62 (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Ex1.to
d_to_68 :: Integer -> T_Bin_54
d_to_68 v0
  = case coe v0 of
      0 -> coe C__O_58 (coe C_'10216''10217'_56)
      _ -> let v1 = subInt (coe v0) (coe (1 :: Integer)) in
           coe d_b'45'incr_62 (coe d_to_68 (coe v1))
-- Ex1.double
d_double_72 :: Integer -> Integer
d_double_72 v0
  = case coe v0 of
      0 -> coe (0 :: Integer)
      _ -> let v1 = subInt (coe v0) (coe (1 :: Integer)) in
           coe addInt (coe (2 :: Integer)) (coe d_double_72 (coe v1))
-- Ex1.from
d_from_76 :: T_Bin_54 -> Integer
d_from_76 v0
  = case coe v0 of
      C_'10216''10217'_56 -> coe (0 :: Integer)
      C__O_58 v1 -> coe d_double_72 (coe d_from_76 (coe v1))
      C__I_60 v1
        -> coe
             addInt (coe (1 :: Integer))
             (coe d_double_72 (coe d_from_76 (coe v1)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Ex1.Even
d_Even_82 a0 = ()
data T_Even_82 = C_even'45'z_84 | C_even'45'ss_88 T_Even_82
-- Ex1.Even₂
d_Even'8322'_90 a0 = ()
data T_Even'8322'_90 = C_even'45'b_94
-- Ex1.to-even
d_to'45'even_98 :: Integer -> T_Even_82 -> T_Even'8322'_90
d_to'45'even_98 ~v0 v1 = du_to'45'even_98 v1
du_to'45'even_98 :: T_Even_82 -> T_Even'8322'_90
du_to'45'even_98 v0
  = case coe v0 of
      C_even'45'z_84 -> coe C_even'45'b_94
      C_even'45'ss_88 v2
        -> coe du_to'45'even'45'aux_108 (coe du_to'45'even_98 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Ex1._.to-even-aux
d_to'45'even'45'aux_108 ::
  Integer ->
  T_Even_82 -> T_Bin_54 -> T_Even'8322'_90 -> T_Even'8322'_90
d_to'45'even'45'aux_108 ~v0 ~v1 ~v2 v3
  = du_to'45'even'45'aux_108 v3
du_to'45'even'45'aux_108 :: T_Even'8322'_90 -> T_Even'8322'_90
du_to'45'even'45'aux_108 v0 = coe seq (coe v0) (coe C_even'45'b_94)
-- Ex1.NonEmptyBin
d_NonEmptyBin_110 a0 = ()
data T_NonEmptyBin_110 = C_n'45'bin'45'0_114 | C_n'45'bin'45'1_118
-- Ex1.⊥
d_'8869'_120 = ()
data T_'8869'_120
-- Ex1.⟨⟩-empty
d_'10216''10217''45'empty_122 :: T_NonEmptyBin_110 -> T_'8869'_120
d_'10216''10217''45'empty_122 = erased
-- Ex1.from-ne
d_from'45'ne_126 :: T_Bin_54 -> T_NonEmptyBin_110 -> Integer
d_from'45'ne_126 v0 v1
  = case coe v0 of
      C__O_58 v2
        -> case coe v2 of
             C_'10216''10217'_56 -> coe seq (coe v1) (coe (0 :: Integer))
             C__O_58 v3
               -> coe
                    mulInt (coe (2 :: Integer))
                    (coe d_from'45'ne_126 (coe v2) (coe C_n'45'bin'45'0_114))
             C__I_60 v3
               -> coe
                    mulInt (coe (2 :: Integer))
                    (coe d_from'45'ne_126 (coe v2) (coe C_n'45'bin'45'1_118))
             _ -> MAlonzo.RTE.mazUnreachableError
      C__I_60 v2
        -> case coe v2 of
             C_'10216''10217'_56 -> coe seq (coe v1) (coe (1 :: Integer))
             C__O_58 v3
               -> coe
                    addInt (coe (1 :: Integer))
                    (coe
                       mulInt (coe (2 :: Integer))
                       (coe d_from'45'ne_126 (coe v2) (coe C_n'45'bin'45'0_114)))
             C__I_60 v3
               -> coe
                    addInt (coe (1 :: Integer))
                    (coe
                       mulInt (coe (2 :: Integer))
                       (coe d_from'45'ne_126 (coe v2) (coe C_n'45'bin'45'1_118)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Ex1.List
type T_List_138 = []
d_List_138 a0 = ()
pattern C_'91''93'_142 = []
pattern C__'8759'__144 a0 a1 = (:) a0 a1
-- Ex1.map
d_map_150 ::
  () -> () -> (AgdaAny -> AgdaAny) -> [AgdaAny] -> [AgdaAny]
d_map_150 ~v0 ~v1 v2 v3 = du_map_150 v2 v3
du_map_150 :: (AgdaAny -> AgdaAny) -> [AgdaAny] -> [AgdaAny]
du_map_150 v0 v1
  = case coe v1 of
      [] -> coe v1
      (:) v2 v3
        -> coe
             C__'8759'__144 (coe v0 v2) (coe du_map_150 (coe v0) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Ex1.length
d_length_162 :: () -> [AgdaAny] -> Integer
d_length_162 ~v0 v1 = du_length_162 v1
du_length_162 :: [AgdaAny] -> Integer
du_length_162 v0
  = case coe v0 of
      [] -> coe (0 :: Integer)
      (:) v1 v2
        -> coe addInt (coe (1 :: Integer)) (coe du_length_162 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Ex1._≡ᴺ_
d__'8801''7482'__168 a0 a1 = ()
data T__'8801''7482'__168
  = C_z'8801''7482'z_170 | C_s'8801''7482's_176 T__'8801''7482'__168
-- Ex1.map-≡ᴺ
d_map'45''8801''7482'_186 ::
  () ->
  () -> (AgdaAny -> AgdaAny) -> [AgdaAny] -> T__'8801''7482'__168
d_map'45''8801''7482'_186 ~v0 ~v1 ~v2 v3
  = du_map'45''8801''7482'_186 v3
du_map'45''8801''7482'_186 :: [AgdaAny] -> T__'8801''7482'__168
du_map'45''8801''7482'_186 v0
  = case coe v0 of
      [] -> coe C_z'8801''7482'z_170
      (:) v1 v2
        -> coe
             C_s'8801''7482's_176 (coe du_map'45''8801''7482'_186 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Ex1._≤_
d__'8804'__192 a0 a1 = ()
data T__'8804'__192
  = C_z'8804'n_196 | C_s'8804's_202 T__'8804'__192
-- Ex1._≤ᴸ_
d__'8804''7480'__206 a0 a1 a2 = ()
data T__'8804''7480'__206
  = C_n'8804'l_212 | C_l'8321''8804'l'8322'_222 T__'8804''7480'__206
-- Ex1.length-≤ᴸ-≦
d_length'45''8804''7480''45''8806'_230 ::
  () ->
  [AgdaAny] -> [AgdaAny] -> T__'8804''7480'__206 -> T__'8804'__192
d_length'45''8804''7480''45''8806'_230 ~v0 v1 v2 v3
  = du_length'45''8804''7480''45''8806'_230 v1 v2 v3
du_length'45''8804''7480''45''8806'_230 ::
  [AgdaAny] -> [AgdaAny] -> T__'8804''7480'__206 -> T__'8804'__192
du_length'45''8804''7480''45''8806'_230 v0 v1 v2
  = case coe v2 of
      C_n'8804'l_212 -> coe C_z'8804'n_196
      C_l'8321''8804'l'8322'_222 v7
        -> case coe v0 of
             (:) v8 v9
               -> case coe v1 of
                    (:) v10 v11
                      -> coe
                           C_s'8804's_202
                           (coe
                              du_length'45''8804''7480''45''8806'_230 (coe v9) (coe v11)
                              (coe v7))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Ex1.length-≤-≦ᴸ
d_length'45''8804''45''8806''7480'_240 ::
  () ->
  [AgdaAny] -> [AgdaAny] -> T__'8804'__192 -> T__'8804''7480'__206
d_length'45''8804''45''8806''7480'_240 ~v0 v1 v2 v3
  = du_length'45''8804''45''8806''7480'_240 v1 v2 v3
du_length'45''8804''45''8806''7480'_240 ::
  [AgdaAny] -> [AgdaAny] -> T__'8804'__192 -> T__'8804''7480'__206
du_length'45''8804''45''8806''7480'_240 v0 v1 v2
  = case coe v0 of
      [] -> coe C_n'8804'l_212
      (:) v3 v4
        -> case coe v1 of
             (:) v5 v6
               -> case coe v2 of
                    C_s'8804's_202 v9
                      -> coe
                           C_l'8321''8804'l'8322'_222
                           (coe
                              du_length'45''8804''45''8806''7480'_240 (coe v4) (coe v6) (coe v9))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Ex1._+ᵇ_
d__'43''7495'__256 :: T_Bin_54 -> T_Bin_54 -> T_Bin_54
d__'43''7495'__256 v0 v1
  = coe du_bin'45'add'45'aux_266 (coe v0) (coe v1) (coe C_false_6)
-- Ex1._.bin-add-aux
d_bin'45'add'45'aux_266 ::
  T_Bin_54 ->
  T_Bin_54 -> T_Bin_54 -> T_Bin_54 -> T_Bool_2 -> T_Bin_54
d_bin'45'add'45'aux_266 ~v0 ~v1 v2 v3 v4
  = du_bin'45'add'45'aux_266 v2 v3 v4
du_bin'45'add'45'aux_266 ::
  T_Bin_54 -> T_Bin_54 -> T_Bool_2 -> T_Bin_54
du_bin'45'add'45'aux_266 v0 v1 v2
  = case coe v0 of
      C_'10216''10217'_56
        -> case coe v1 of
             C_'10216''10217'_56
               -> case coe v2 of
                    C_true_4 -> coe C__I_60 (coe v1)
                    C_false_6 -> coe C__O_58 (coe v1)
                    _ -> MAlonzo.RTE.mazUnreachableError
             C__O_58 v3
               -> case coe v2 of
                    C_true_4 -> coe C__I_60 (coe v3)
                    C_false_6 -> coe v1
                    _ -> MAlonzo.RTE.mazUnreachableError
             C__I_60 v3
               -> case coe v2 of
                    C_true_4 -> coe C__O_58 (coe d_b'45'incr_62 (coe v3))
                    C_false_6 -> coe v1
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C__O_58 v3
        -> case coe v1 of
             C_'10216''10217'_56
               -> case coe v2 of
                    C_true_4 -> coe C__I_60 (coe v3)
                    C_false_6 -> coe v0
                    _ -> MAlonzo.RTE.mazUnreachableError
             C__O_58 v4
               -> case coe v2 of
                    C_true_4
                      -> coe
                           C__I_60
                           (coe du_bin'45'add'45'aux_266 (coe v3) (coe v4) (coe C_false_6))
                    C_false_6
                      -> coe
                           C__O_58 (coe du_bin'45'add'45'aux_266 (coe v3) (coe v4) (coe v2))
                    _ -> MAlonzo.RTE.mazUnreachableError
             C__I_60 v4
               -> case coe v2 of
                    C_true_4
                      -> coe
                           C__O_58 (coe du_bin'45'add'45'aux_266 (coe v3) (coe v4) (coe v2))
                    C_false_6
                      -> coe
                           C__I_60 (coe du_bin'45'add'45'aux_266 (coe v3) (coe v4) (coe v2))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C__I_60 v3
        -> case coe v1 of
             C_'10216''10217'_56
               -> case coe v2 of
                    C_true_4 -> coe d_b'45'incr_62 (coe v0)
                    C_false_6 -> coe v0
                    _ -> MAlonzo.RTE.mazUnreachableError
             C__O_58 v4
               -> case coe v2 of
                    C_true_4
                      -> coe
                           C__O_58 (coe du_bin'45'add'45'aux_266 (coe v3) (coe v4) (coe v2))
                    C_false_6
                      -> coe
                           C__I_60 (coe du_bin'45'add'45'aux_266 (coe v3) (coe v4) (coe v2))
                    _ -> MAlonzo.RTE.mazUnreachableError
             C__I_60 v4
               -> case coe v2 of
                    C_true_4
                      -> coe
                           C__I_60 (coe du_bin'45'add'45'aux_266 (coe v3) (coe v4) (coe v2))
                    C_false_6
                      -> coe
                           C__O_58
                           (coe du_bin'45'add'45'aux_266 (coe v3) (coe v4) (coe C_true_4))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Ex1._*ᵇ_
d__'42''7495'__316 :: T_Bin_54 -> T_Bin_54 -> T_Bin_54
d__'42''7495'__316 v0 v1
  = case coe v1 of
      C_'10216''10217'_56 -> coe C__O_58 (coe v1)
      C__O_58 v2
        -> coe C__O_58 (coe d__'42''7495'__316 (coe v0) (coe v2))
      C__I_60 v2
        -> coe
             d__'43''7495'__256
             (coe C__O_58 (coe d__'42''7495'__316 (coe v0) (coe v2))) (coe v0)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Ex1._=ᵇ_
d__'61''7495'__328 a0 a1 = ()
data T__'61''7495'__328
  = C_e'61''7495'e_330 | C_c0'61''7495'c0_336 T__'61''7495'__328 |
    C_c1'61''7495'c1_342 T__'61''7495'__328
-- Ex1._≤ᵇ_
d__'8804''7495'__344 a0 a1 = ()
data T__'8804''7495'__344
  = C_e'8804''7495'b_348 |
    C_s'8804''7495's_354 T_Bin_54 T_Bin_54 T__'8804''7495'__344
-- Ex1.double-even
d_double'45'even_358 :: Integer -> T_Even_82
d_double'45'even_358 v0
  = case coe v0 of
      0 -> coe C_even'45'z_84
      _ -> let v1 = subInt (coe v0) (coe (1 :: Integer)) in
           coe C_even'45'ss_88 (d_double'45'even_358 (coe v1))
-- Ex1.from-even
d_from'45'even_364 :: T_Bin_54 -> T_Even'8322'_90 -> T_Even_82
d_from'45'even_364 v0 ~v1 = du_from'45'even_364 v0
du_from'45'even_364 :: T_Bin_54 -> T_Even_82
du_from'45'even_364 v0
  = case coe v0 of
      C__O_58 v1 -> coe d_double'45'even_358 (coe d_from_76 (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
