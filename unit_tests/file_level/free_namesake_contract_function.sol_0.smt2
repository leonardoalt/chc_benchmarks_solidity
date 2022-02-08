(set-logic HORN)

(declare-datatypes ((|state_type| 0)) (((|state_type| (|balances| (Array Int Int))))))
(declare-datatypes ((|bytes_tuple| 0)) (((|bytes_tuple| (|bytes_tuple_accessor_array| (Array Int Int)) (|bytes_tuple_accessor_length| Int)))))
(declare-datatypes ((|tx_type| 0)) (((|tx_type| (|block.basefee| Int) (|block.chainid| Int) (|block.coinbase| Int) (|block.difficulty| Int) (|block.gaslimit| Int) (|block.number| Int) (|block.timestamp| Int) (|blockhash| (Array Int Int)) (|msg.data| |bytes_tuple|) (|msg.sender| Int) (|msg.sig| Int) (|msg.value| Int) (|tx.gasprice| Int) (|tx.origin| Int)))))
(declare-datatypes ((|ecrecover_input_type| 0)) (((|ecrecover_input_type| (|hash| Int) (|v| Int) (|r| Int) (|s| Int)))))
(declare-datatypes ((|crypto_type| 0)) (((|crypto_type| (|ecrecover| (Array |ecrecover_input_type| Int)) (|keccak256| (Array |bytes_tuple| Int)) (|ripemd160| (Array |bytes_tuple| Int)) (|sha256| (Array |bytes_tuple| Int))))))
(declare-datatypes ((|abi_type| 0)) (((|abi_type|))))
(declare-fun |interface_0_C_35_0| (Int |abi_type| |crypto_type| |state_type| ) Bool)
(declare-fun |nondet_interface_1_C_35_0| (Int Int |abi_type| |crypto_type| |state_type| |state_type| ) Bool)
(declare-fun |summary_constructor_2_C_35_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (= error_0 0) (nondet_interface_1_C_35_0 error_0 this_0 abi_0 crypto_0 state_0 state_0))))


(declare-fun |summary_3_function_f__8_35_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(declare-fun |summary_4_function_g__26_35_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(declare-fun |summary_5_function_g__26_35_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (nondet_interface_1_C_35_0 error_0 this_0 abi_0 crypto_0 state_0 state_1) true) (and (= error_0 0) (summary_5_function_g__26_35_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2))) (nondet_interface_1_C_35_0 error_1 this_0 abi_0 crypto_0 state_0 state_2))))


(declare-fun |summary_6_function_f__34_35_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(declare-fun |block_7_function_f__8_35_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(declare-fun |block_8_f_7_35_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(assert
(forall ( (_29_1 Int) (_3_0 Int) (_3_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(block_7_function_f__8_35_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _3_1)))


(assert
(forall ( (_29_1 Int) (_3_0 Int) (_3_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_7_function_f__8_35_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _3_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) true) true) true)) true) (block_8_f_7_35_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _3_1))))


(declare-fun |block_9_return_function_f__8_35_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(assert
(forall ( (_29_1 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_5_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_8_f_7_35_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _3_1) (and (= _3_2 expr_5_0) (and (=> true true) (and (= expr_5_0 1337) (and (= _3_1 0) true))))) true) (block_9_return_function_f__8_35_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _3_2))))


(declare-fun |block_10_return_ghost_f_6_35_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(assert
(forall ( (_29_1 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_5_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_10_return_ghost_f_6_35_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _3_2) (and (= _3_2 expr_5_0) (and (=> true true) (and (= expr_5_0 1337) (and (= _3_1 0) true))))) true) (block_9_return_function_f__8_35_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _3_2))))


(assert
(forall ( (_29_1 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_5_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_9_return_function_f__8_35_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _3_1) true) true) (summary_3_function_f__8_35_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _3_1))))


(declare-fun |block_11_function_g__26_35_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(declare-fun |block_12_g_25_35_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (_29_1 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_5_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(block_11_function_g__26_35_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1)))


(assert
(forall ( (_29_1 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_5_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_11_function_g__26_35_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) true) true) true)) true) (block_12_g_25_35_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |block_13_return_function_g__26_35_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(declare-fun |summary_14_function_f__34_35_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(assert
(forall ( (_29_1 Int) (_29_2 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_5_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (t_function_internal_pure$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (summary_6_function_f__34_35_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _29_2) (summary_14_function_f__34_35_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _29_2))))


(assert
(forall ( (_29_1 Int) (_29_2 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_5_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (t_function_internal_pure$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_12_g_25_35_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (summary_14_function_f__34_35_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_1 _29_2) (and true true))) (> error_1 0)) (summary_4_function_g__26_35_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |block_15_function_g__26_35_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (_29_1 Int) (_29_2 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Bool) (expr_5_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (t_function_internal_pure$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_12_g_25_35_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (= expr_15_1 (= expr_13_0 expr_14_0)) (and (=> true true) (and (= expr_14_0 42) (and (=> true (and (>= expr_13_0 0) (<= expr_13_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_13_0 _29_2) (and (= error_1 0) (and (summary_14_function_f__34_35_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_1 _29_2) (and true true))))))))) (and (not expr_15_1) (= error_2 1))) (block_15_function_g__26_35_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (_29_1 Int) (_29_2 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Bool) (expr_5_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (t_function_internal_pure$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (block_15_function_g__26_35_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (summary_4_function_g__26_35_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |summary_16_function_f__34_35_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(assert
(forall ( (_29_1 Int) (_29_2 Int) (_29_3 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Bool) (expr_5_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (t_function_internal_pure$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (summary_6_function_f__34_35_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _29_3) (summary_16_function_f__34_35_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _29_3))))


(assert
(forall ( (_29_1 Int) (_29_2 Int) (_29_3 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Bool) (expr_5_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (t_function_internal_pure$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_12_g_25_35_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (summary_16_function_f__34_35_0 error_3 this_0 abi_0 crypto_0 tx_0 state_1 state_1 _29_3) (and (= error_2 error_1) (and (= expr_15_1 (= expr_13_0 expr_14_0)) (and (=> true true) (and (= expr_14_0 42) (and (=> true (and (>= expr_13_0 0) (<= expr_13_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_13_0 _29_2) (and (= error_1 0) (and (summary_14_function_f__34_35_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_1 _29_2) (and true true))))))))))) (> error_3 0)) (summary_4_function_g__26_35_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |block_17_function_g__26_35_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (_29_1 Int) (_29_2 Int) (_29_3 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Bool) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Bool) (expr_5_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (t_function_internal_pure$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_12_g_25_35_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (= expr_22_1 (= expr_20_0 expr_21_0)) (and (=> true true) (and (= expr_21_0 1337) (and (=> true (and (>= expr_20_0 0) (<= expr_20_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_20_0 _29_3) (and (= error_3 0) (and (summary_16_function_f__34_35_0 error_3 this_0 abi_0 crypto_0 tx_0 state_1 state_1 _29_3) (and (= error_2 error_1) (and (= expr_15_1 (= expr_13_0 expr_14_0)) (and (=> true true) (and (= expr_14_0 42) (and (=> true (and (>= expr_13_0 0) (<= expr_13_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_13_0 _29_2) (and (= error_1 0) (and (summary_14_function_f__34_35_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_1 _29_2) (and true true))))))))))))))))) (and (not expr_22_1) (= error_4 2))) (block_17_function_g__26_35_0 error_4 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (_29_1 Int) (_29_2 Int) (_29_3 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Bool) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Bool) (expr_5_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (t_function_internal_pure$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (block_17_function_g__26_35_0 error_4 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (summary_4_function_g__26_35_0 error_4 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (_29_1 Int) (_29_2 Int) (_29_3 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Bool) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Bool) (expr_5_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (t_function_internal_pure$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_12_g_25_35_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (= error_4 error_3) (and (= expr_22_1 (= expr_20_0 expr_21_0)) (and (=> true true) (and (= expr_21_0 1337) (and (=> true (and (>= expr_20_0 0) (<= expr_20_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_20_0 _29_3) (and (= error_3 0) (and (summary_16_function_f__34_35_0 error_3 this_0 abi_0 crypto_0 tx_0 state_1 state_1 _29_3) (and (= error_2 error_1) (and (= expr_15_1 (= expr_13_0 expr_14_0)) (and (=> true true) (and (= expr_14_0 42) (and (=> true (and (>= expr_13_0 0) (<= expr_13_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_13_0 _29_2) (and (= error_1 0) (and (summary_14_function_f__34_35_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_1 _29_2) (and true true)))))))))))))))))) true) (block_13_return_function_g__26_35_0 error_4 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (_29_1 Int) (_29_2 Int) (_29_3 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Bool) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Bool) (expr_5_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (t_function_internal_pure$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_13_return_function_g__26_35_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) true) (summary_4_function_g__26_35_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |block_18_function_g__26_35_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (_29_1 Int) (_29_2 Int) (_29_3 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Bool) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Bool) (expr_5_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (t_function_internal_pure$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|))
(block_18_function_g__26_35_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1)))


(assert
(forall ( (_29_1 Int) (_29_2 Int) (_29_3 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Bool) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Bool) (expr_5_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_18_function_g__26_35_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (summary_4_function_g__26_35_0 error_1 this_0 abi_0 crypto_0 tx_0 state_2 state_3) (and (= state_2 (|state_type| (store (|balances| state_1) this_0 (+ (select (|balances| state_1) this_0) funds_3_0)))) (and (and (>= (+ (select (|balances| state_1) this_0) funds_3_0) 0) (<= (+ (select (|balances| state_1) this_0) funds_3_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= funds_3_0 (|msg.value| tx_0)) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (and (and (and (and (and (= (|msg.value| tx_0) 0) (= (|msg.sig| tx_0) 3793197966)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 0) 226)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 1) 23)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 2) 155)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 3) 142)) (>= (|bytes_tuple_accessor_length| (|msg.data| tx_0)) 4))) (and (and (and (and (= state_1 state_0) (= error_0 0)) true) true) true))))))) true) (summary_5_function_g__26_35_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_3))))


(assert
(forall ( (_29_1 Int) (_29_2 Int) (_29_3 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Bool) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Bool) (expr_5_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (interface_0_C_35_0 this_0 abi_0 crypto_0 state_0) true) (and (summary_5_function_g__26_35_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (= error_0 0))) (interface_0_C_35_0 this_0 abi_0 crypto_0 state_1))))


(declare-fun |block_19_function_f__34_35_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(declare-fun |block_20_f_33_35_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(assert
(forall ( (_29_0 Int) (_29_1 Int) (_29_2 Int) (_29_3 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Bool) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Bool) (expr_5_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|))
(block_19_function_f__34_35_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _29_1)))


(assert
(forall ( (_29_0 Int) (_29_1 Int) (_29_2 Int) (_29_3 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Bool) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Bool) (expr_5_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_19_function_f__34_35_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _29_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) true) true) true)) true) (block_20_f_33_35_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _29_1))))


(declare-fun |block_21_return_function_f__34_35_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(assert
(forall ( (_29_0 Int) (_29_1 Int) (_29_2 Int) (_29_3 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Bool) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Bool) (expr_31_0 Int) (expr_5_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_20_f_33_35_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _29_1) (and (= _29_2 expr_31_0) (and (=> true true) (and (= expr_31_0 42) (and (= _29_1 0) true))))) true) (block_21_return_function_f__34_35_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _29_2))))


(declare-fun |block_22_return_ghost_f_32_35_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(assert
(forall ( (_29_0 Int) (_29_1 Int) (_29_2 Int) (_29_3 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Bool) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Bool) (expr_31_0 Int) (expr_5_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_22_return_ghost_f_32_35_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _29_2) (and (= _29_2 expr_31_0) (and (=> true true) (and (= expr_31_0 42) (and (= _29_1 0) true))))) true) (block_21_return_function_f__34_35_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _29_2))))


(assert
(forall ( (_29_0 Int) (_29_1 Int) (_29_2 Int) (_29_3 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Bool) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Bool) (expr_31_0 Int) (expr_5_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_21_return_function_f__34_35_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _29_1) true) true) (summary_6_function_f__34_35_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _29_1))))


(declare-fun |contract_initializer_23_C_35_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(declare-fun |contract_initializer_entry_24_C_35_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (_29_0 Int) (_29_1 Int) (_29_2 Int) (_29_3 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Bool) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Bool) (expr_31_0 Int) (expr_5_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (= state_1 state_0) (= error_0 0)) true) (contract_initializer_entry_24_C_35_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |contract_initializer_after_init_25_C_35_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (_29_0 Int) (_29_1 Int) (_29_2 Int) (_29_3 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Bool) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Bool) (expr_31_0 Int) (expr_5_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (contract_initializer_entry_24_C_35_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) true) (contract_initializer_after_init_25_C_35_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (_29_0 Int) (_29_1 Int) (_29_2 Int) (_29_3 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Bool) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Bool) (expr_31_0 Int) (expr_5_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (contract_initializer_after_init_25_C_35_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) true) (contract_initializer_23_C_35_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |implicit_constructor_entry_26_C_35_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (_29_0 Int) (_29_1 Int) (_29_2 Int) (_29_3 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Bool) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Bool) (expr_31_0 Int) (expr_5_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (and (and (= state_1 state_0) (= error_0 0)) true) true) (>= (select (|balances| state_1) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_26_C_35_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (_29_0 Int) (_29_1 Int) (_29_2 Int) (_29_3 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Bool) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Bool) (expr_31_0 Int) (expr_5_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (implicit_constructor_entry_26_C_35_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (contract_initializer_23_C_35_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2) true)) (> error_1 0)) (summary_constructor_2_C_35_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2))))


(assert
(forall ( (_29_0 Int) (_29_1 Int) (_29_2 Int) (_29_3 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Bool) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Bool) (expr_31_0 Int) (expr_5_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (implicit_constructor_entry_26_C_35_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (= error_1 0) (and (contract_initializer_23_C_35_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2) true))) true) (summary_constructor_2_C_35_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2))))


(assert
(forall ( (_29_0 Int) (_29_1 Int) (_29_2 Int) (_29_3 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Bool) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Bool) (expr_31_0 Int) (expr_5_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (summary_constructor_2_C_35_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 0))) (interface_0_C_35_0 this_0 abi_0 crypto_0 state_1))))


(declare-fun |error_target_4_0| () Bool)
(assert
(forall ( (_29_0 Int) (_29_1 Int) (_29_2 Int) (_29_3 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Bool) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Bool) (expr_31_0 Int) (expr_5_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (interface_0_C_35_0 this_0 abi_0 crypto_0 state_0) true) (and (summary_5_function_g__26_35_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (= error_0 1))) error_target_4_0)))


(assert
(forall ( (_29_0 Int) (_29_1 Int) (_29_2 Int) (_29_3 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Bool) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Bool) (expr_31_0 Int) (expr_5_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|))
(=> error_target_4_0 false)))
(check-sat)