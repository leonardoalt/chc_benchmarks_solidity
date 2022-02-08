(set-logic HORN)

(declare-datatypes ((|state_type| 0)) (((|state_type| (|balances| (Array Int Int))))))
(declare-datatypes ((|bytes_tuple| 0)) (((|bytes_tuple| (|bytes_tuple_accessor_array| (Array Int Int)) (|bytes_tuple_accessor_length| Int)))))
(declare-datatypes ((|tx_type| 0)) (((|tx_type| (|block.basefee| Int) (|block.chainid| Int) (|block.coinbase| Int) (|block.difficulty| Int) (|block.gaslimit| Int) (|block.number| Int) (|block.timestamp| Int) (|blockhash| (Array Int Int)) (|msg.data| |bytes_tuple|) (|msg.sender| Int) (|msg.sig| Int) (|msg.value| Int) (|tx.gasprice| Int) (|tx.origin| Int)))))
(declare-datatypes ((|ecrecover_input_type| 0)) (((|ecrecover_input_type| (|hash| Int) (|v| Int) (|r| Int) (|s| Int)))))
(declare-datatypes ((|crypto_type| 0)) (((|crypto_type| (|ecrecover| (Array |ecrecover_input_type| Int)) (|keccak256| (Array |bytes_tuple| Int)) (|ripemd160| (Array |bytes_tuple| Int)) (|sha256| (Array |bytes_tuple| Int))))))
(declare-datatypes ((|abi_type| 0)) (((|abi_type|))))
(declare-fun |interface_0_C_41_0| (Int |abi_type| |crypto_type| |state_type| Int Int Int ) Bool)
(declare-fun |nondet_interface_1_C_41_0| (Int Int |abi_type| |crypto_type| |state_type| Int Int Int |state_type| Int Int Int ) Bool)
(declare-fun |summary_constructor_2_C_41_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int Int Int Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (abi_0 |abi_type|) (b_4_0 Int) (c_6_0 Int) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (= error_0 0) (nondet_interface_1_C_41_0 error_0 this_0 abi_0 crypto_0 state_0 a_2_0 b_4_0 c_6_0 state_0 a_2_0 b_4_0 c_6_0))))


(declare-fun |summary_3_function_test__40_41_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int Int |state_type| Int Int Int ) Bool)
(declare-fun |summary_4_function_test__40_41_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int Int |state_type| Int Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (b_4_0 Int) (b_4_1 Int) (b_4_2 Int) (c_6_0 Int) (c_6_1 Int) (c_6_2 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (nondet_interface_1_C_41_0 error_0 this_0 abi_0 crypto_0 state_0 a_2_0 b_4_0 c_6_0 state_1 a_2_1 b_4_1 c_6_1) true) (and (= error_0 0) (summary_4_function_test__40_41_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 b_4_1 c_6_1 state_2 a_2_2 b_4_2 c_6_2))) (nondet_interface_1_C_41_0 error_1 this_0 abi_0 crypto_0 state_0 a_2_0 b_4_0 c_6_0 state_2 a_2_2 b_4_2 c_6_2))))


(declare-fun |block_5_function_test__40_41_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int Int |state_type| Int Int Int ) Bool)
(declare-fun |block_6_test_39_41_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int Int |state_type| Int Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (b_4_0 Int) (b_4_1 Int) (b_4_2 Int) (c_6_0 Int) (c_6_1 Int) (c_6_2 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(block_5_function_test__40_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 b_4_0 c_6_0 state_1 a_2_1 b_4_1 c_6_1)))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (b_4_0 Int) (b_4_1 Int) (b_4_2 Int) (c_6_0 Int) (c_6_1 Int) (c_6_2 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_5_function_test__40_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 b_4_0 c_6_0 state_1 a_2_1 b_4_1 c_6_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and (and (and true (= a_2_1 a_2_0)) (= b_4_1 b_4_0)) (= c_6_1 c_6_0))) true) true)) true) (block_6_test_39_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 b_4_0 c_6_0 state_1 a_2_1 b_4_1 c_6_1))))


(declare-fun |block_7_return_function_test__40_41_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int Int |state_type| Int Int Int ) Bool)
(declare-fun |block_8_if_header_test_24_41_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int Int |state_type| Int Int Int ) Bool)
(declare-fun |block_9_if_true_test_23_41_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int Int |state_type| Int Int Int ) Bool)
(declare-fun |block_10_test_39_41_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int Int |state_type| Int Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (b_4_0 Int) (b_4_1 Int) (b_4_2 Int) (c_6_0 Int) (c_6_1 Int) (c_6_2 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_6_test_39_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 b_4_0 c_6_0 state_1 a_2_1 b_4_1 c_6_1) true) true) (block_8_if_header_test_24_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 b_4_0 c_6_0 state_1 a_2_1 b_4_1 c_6_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (b_4_0 Int) (b_4_1 Int) (b_4_2 Int) (c_6_0 Int) (c_6_1 Int) (c_6_2 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_8_if_header_test_24_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 b_4_0 c_6_0 state_1 a_2_1 b_4_1 c_6_1) (and (= expr_11_1 (= expr_9_0 expr_10_0)) (and (=> true true) (and (= expr_10_0 0) (and (=> true (and (>= expr_9_0 0) (<= expr_9_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_9_0 a_2_1) true)))))) expr_11_1) (block_9_if_true_test_23_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 b_4_0 c_6_0 state_1 a_2_1 b_4_1 c_6_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (b_4_0 Int) (b_4_1 Int) (b_4_2 Int) (c_6_0 Int) (c_6_1 Int) (c_6_2 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_8_if_header_test_24_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 b_4_0 c_6_0 state_1 a_2_1 b_4_1 c_6_1) (and (= expr_11_1 (= expr_9_0 expr_10_0)) (and (=> true true) (and (= expr_10_0 0) (and (=> true (and (>= expr_9_0 0) (<= expr_9_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_9_0 a_2_1) true)))))) (not expr_11_1)) (block_10_test_39_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 b_4_0 c_6_0 state_1 a_2_1 b_4_1 c_6_1))))


(declare-fun |block_11_if_header_test_22_41_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int Int |state_type| Int Int Int ) Bool)
(declare-fun |block_12_if_true_test_21_41_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int Int |state_type| Int Int Int ) Bool)
(declare-fun |block_13_test_39_41_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int Int |state_type| Int Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (b_4_0 Int) (b_4_1 Int) (b_4_2 Int) (c_6_0 Int) (c_6_1 Int) (c_6_2 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_9_if_true_test_23_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 b_4_0 c_6_0 state_1 a_2_1 b_4_1 c_6_1) true) true) (block_11_if_header_test_22_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 b_4_0 c_6_0 state_1 a_2_1 b_4_1 c_6_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (b_4_0 Int) (b_4_1 Int) (b_4_2 Int) (c_6_0 Int) (c_6_1 Int) (c_6_2 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_11_if_header_test_22_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 b_4_0 c_6_0 state_1 a_2_1 b_4_1 c_6_1) (and (= expr_14_1 (= expr_12_0 expr_13_0)) (and (=> true true) (and (= expr_13_0 0) (and (=> true (and (>= expr_12_0 0) (<= expr_12_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_12_0 b_4_1) true)))))) expr_14_1) (block_12_if_true_test_21_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 b_4_0 c_6_0 state_1 a_2_1 b_4_1 c_6_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (b_4_0 Int) (b_4_1 Int) (b_4_2 Int) (c_6_0 Int) (c_6_1 Int) (c_6_2 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_11_if_header_test_22_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 b_4_0 c_6_0 state_1 a_2_1 b_4_1 c_6_1) (and (= expr_14_1 (= expr_12_0 expr_13_0)) (and (=> true true) (and (= expr_13_0 0) (and (=> true (and (>= expr_12_0 0) (<= expr_12_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_12_0 b_4_1) true)))))) (not expr_14_1)) (block_13_test_39_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 b_4_0 c_6_0 state_1 a_2_1 b_4_1 c_6_1))))


(declare-fun |block_14_if_header_test_20_41_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int Int |state_type| Int Int Int ) Bool)
(declare-fun |block_15_if_true_test_19_41_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int Int |state_type| Int Int Int ) Bool)
(declare-fun |block_16_test_39_41_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int Int |state_type| Int Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (b_4_0 Int) (b_4_1 Int) (b_4_2 Int) (c_6_0 Int) (c_6_1 Int) (c_6_2 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_12_if_true_test_21_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 b_4_0 c_6_0 state_1 a_2_1 b_4_1 c_6_1) true) true) (block_14_if_header_test_20_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 b_4_0 c_6_0 state_1 a_2_1 b_4_1 c_6_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (b_4_0 Int) (b_4_1 Int) (b_4_2 Int) (c_6_0 Int) (c_6_1 Int) (c_6_2 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_14_if_header_test_20_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 b_4_0 c_6_0 state_1 a_2_1 b_4_1 c_6_1) (and (= expr_17_1 (= expr_15_0 expr_16_0)) (and (=> true true) (and (= expr_16_0 0) (and (=> true (and (>= expr_15_0 0) (<= expr_15_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_15_0 c_6_1) true)))))) expr_17_1) (block_15_if_true_test_19_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 b_4_0 c_6_0 state_1 a_2_1 b_4_1 c_6_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (b_4_0 Int) (b_4_1 Int) (b_4_2 Int) (c_6_0 Int) (c_6_1 Int) (c_6_2 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_14_if_header_test_20_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 b_4_0 c_6_0 state_1 a_2_1 b_4_1 c_6_1) (and (= expr_17_1 (= expr_15_0 expr_16_0)) (and (=> true true) (and (= expr_16_0 0) (and (=> true (and (>= expr_15_0 0) (<= expr_15_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_15_0 c_6_1) true)))))) (not expr_17_1)) (block_16_test_39_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 b_4_0 c_6_0 state_1 a_2_1 b_4_1 c_6_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (b_4_0 Int) (b_4_1 Int) (b_4_2 Int) (c_6_0 Int) (c_6_1 Int) (c_6_2 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_15_if_true_test_19_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 b_4_0 c_6_0 state_1 a_2_1 b_4_1 c_6_1) true) true) (block_7_return_function_test__40_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 b_4_0 c_6_0 state_1 a_2_1 b_4_1 c_6_1))))


(declare-fun |block_17_return_ghost_test_18_41_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int Int |state_type| Int Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (b_4_0 Int) (b_4_1 Int) (b_4_2 Int) (c_6_0 Int) (c_6_1 Int) (c_6_2 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_17_return_ghost_test_18_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 b_4_0 c_6_0 state_1 a_2_1 b_4_1 c_6_1) true) true) (block_16_test_39_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 b_4_0 c_6_0 state_1 a_2_1 b_4_1 c_6_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (b_4_0 Int) (b_4_1 Int) (b_4_2 Int) (c_6_0 Int) (c_6_1 Int) (c_6_2 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_16_test_39_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 b_4_0 c_6_0 state_1 a_2_1 b_4_1 c_6_1) true) true) (block_13_test_39_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 b_4_0 c_6_0 state_1 a_2_1 b_4_1 c_6_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (b_4_0 Int) (b_4_1 Int) (b_4_2 Int) (c_6_0 Int) (c_6_1 Int) (c_6_2 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_13_test_39_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 b_4_0 c_6_0 state_1 a_2_1 b_4_1 c_6_1) true) true) (block_10_test_39_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 b_4_0 c_6_0 state_1 a_2_1 b_4_1 c_6_1))))


(declare-fun |block_18_function_test__40_41_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int Int |state_type| Int Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (b_4_0 Int) (b_4_1 Int) (b_4_2 Int) (c_6_0 Int) (c_6_1 Int) (c_6_2 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_26_0 Int) (expr_27_0 Int) (expr_28_1 Bool) (expr_29_0 Int) (expr_30_0 Int) (expr_31_1 Bool) (expr_32_0 Bool) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Bool) (expr_36_0 Bool) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_10_test_39_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 b_4_0 c_6_0 state_1 a_2_1 b_4_1 c_6_1) (and (= expr_36_0 (or expr_32_0 expr_35_1)) (and (= expr_35_1 (not (= expr_33_0 expr_34_0))) (and (=> (and true (not expr_32_0)) true) (and (= expr_34_0 0) (and (=> (and true (not expr_32_0)) (and (>= expr_33_0 0) (<= expr_33_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_33_0 c_6_1) (and (= expr_32_0 (or expr_28_1 expr_31_1)) (and (= expr_31_1 (not (= expr_29_0 expr_30_0))) (and (=> (and true (not expr_28_1)) true) (and (= expr_30_0 0) (and (=> (and true (not expr_28_1)) (and (>= expr_29_0 0) (<= expr_29_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_29_0 b_4_1) (and (= expr_28_1 (not (= expr_26_0 expr_27_0))) (and (=> true true) (and (= expr_27_0 0) (and (=> true (and (>= expr_26_0 0) (<= expr_26_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_26_0 a_2_1) true)))))))))))))))))) (and (not expr_36_0) (= error_1 1))) (block_18_function_test__40_41_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 b_4_0 c_6_0 state_1 a_2_1 b_4_1 c_6_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (b_4_0 Int) (b_4_1 Int) (b_4_2 Int) (c_6_0 Int) (c_6_1 Int) (c_6_2 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_26_0 Int) (expr_27_0 Int) (expr_28_1 Bool) (expr_29_0 Int) (expr_30_0 Int) (expr_31_1 Bool) (expr_32_0 Bool) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Bool) (expr_36_0 Bool) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (block_18_function_test__40_41_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 b_4_0 c_6_0 state_1 a_2_1 b_4_1 c_6_1) (summary_3_function_test__40_41_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 b_4_0 c_6_0 state_1 a_2_1 b_4_1 c_6_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (b_4_0 Int) (b_4_1 Int) (b_4_2 Int) (c_6_0 Int) (c_6_1 Int) (c_6_2 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_26_0 Int) (expr_27_0 Int) (expr_28_1 Bool) (expr_29_0 Int) (expr_30_0 Int) (expr_31_1 Bool) (expr_32_0 Bool) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Bool) (expr_36_0 Bool) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_10_test_39_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 b_4_0 c_6_0 state_1 a_2_1 b_4_1 c_6_1) (and (= error_1 error_0) (and (= expr_36_0 (or expr_32_0 expr_35_1)) (and (= expr_35_1 (not (= expr_33_0 expr_34_0))) (and (=> (and true (not expr_32_0)) true) (and (= expr_34_0 0) (and (=> (and true (not expr_32_0)) (and (>= expr_33_0 0) (<= expr_33_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_33_0 c_6_1) (and (= expr_32_0 (or expr_28_1 expr_31_1)) (and (= expr_31_1 (not (= expr_29_0 expr_30_0))) (and (=> (and true (not expr_28_1)) true) (and (= expr_30_0 0) (and (=> (and true (not expr_28_1)) (and (>= expr_29_0 0) (<= expr_29_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_29_0 b_4_1) (and (= expr_28_1 (not (= expr_26_0 expr_27_0))) (and (=> true true) (and (= expr_27_0 0) (and (=> true (and (>= expr_26_0 0) (<= expr_26_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_26_0 a_2_1) true))))))))))))))))))) true) (block_7_return_function_test__40_41_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 b_4_0 c_6_0 state_1 a_2_1 b_4_1 c_6_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (b_4_0 Int) (b_4_1 Int) (b_4_2 Int) (c_6_0 Int) (c_6_1 Int) (c_6_2 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_26_0 Int) (expr_27_0 Int) (expr_28_1 Bool) (expr_29_0 Int) (expr_30_0 Int) (expr_31_1 Bool) (expr_32_0 Bool) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Bool) (expr_36_0 Bool) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_7_return_function_test__40_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 b_4_0 c_6_0 state_1 a_2_1 b_4_1 c_6_1) true) true) (summary_3_function_test__40_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 b_4_0 c_6_0 state_1 a_2_1 b_4_1 c_6_1))))


(declare-fun |block_19_function_test__40_41_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int Int |state_type| Int Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (b_4_0 Int) (b_4_1 Int) (b_4_2 Int) (c_6_0 Int) (c_6_1 Int) (c_6_2 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_26_0 Int) (expr_27_0 Int) (expr_28_1 Bool) (expr_29_0 Int) (expr_30_0 Int) (expr_31_1 Bool) (expr_32_0 Bool) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Bool) (expr_36_0 Bool) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(block_19_function_test__40_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 b_4_0 c_6_0 state_1 a_2_1 b_4_1 c_6_1)))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (b_4_0 Int) (b_4_1 Int) (b_4_2 Int) (c_6_0 Int) (c_6_1 Int) (c_6_2 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_26_0 Int) (expr_27_0 Int) (expr_28_1 Bool) (expr_29_0 Int) (expr_30_0 Int) (expr_31_1 Bool) (expr_32_0 Bool) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Bool) (expr_36_0 Bool) (expr_9_0 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_19_function_test__40_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 b_4_0 c_6_0 state_1 a_2_1 b_4_1 c_6_1) (and (summary_3_function_test__40_41_0 error_1 this_0 abi_0 crypto_0 tx_0 state_2 a_2_1 b_4_1 c_6_1 state_3 a_2_2 b_4_2 c_6_2) (and (= state_2 (|state_type| (store (|balances| state_1) this_0 (+ (select (|balances| state_1) this_0) funds_2_0)))) (and (and (>= (+ (select (|balances| state_1) this_0) funds_2_0) 0) (<= (+ (select (|balances| state_1) this_0) funds_2_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= funds_2_0 (|msg.value| tx_0)) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (and (and (and (and (and (= (|msg.value| tx_0) 0) (= (|msg.sig| tx_0) 4171824493)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 0) 248)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 1) 168)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 2) 253)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 3) 109)) (>= (|bytes_tuple_accessor_length| (|msg.data| tx_0)) 4))) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and (and (and true (= a_2_1 a_2_0)) (= b_4_1 b_4_0)) (= c_6_1 c_6_0))) true) true))))))) true) (summary_4_function_test__40_41_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 b_4_0 c_6_0 state_3 a_2_2 b_4_2 c_6_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (b_4_0 Int) (b_4_1 Int) (b_4_2 Int) (c_6_0 Int) (c_6_1 Int) (c_6_2 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_26_0 Int) (expr_27_0 Int) (expr_28_1 Bool) (expr_29_0 Int) (expr_30_0 Int) (expr_31_1 Bool) (expr_32_0 Bool) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Bool) (expr_36_0 Bool) (expr_9_0 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (interface_0_C_41_0 this_0 abi_0 crypto_0 state_0 a_2_0 b_4_0 c_6_0) true) (and (summary_4_function_test__40_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 b_4_0 c_6_0 state_1 a_2_1 b_4_1 c_6_1) (= error_0 0))) (interface_0_C_41_0 this_0 abi_0 crypto_0 state_1 a_2_1 b_4_1 c_6_1))))


(declare-fun |contract_initializer_20_C_41_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int Int Int Int Int ) Bool)
(declare-fun |contract_initializer_entry_21_C_41_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int Int Int Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (b_4_0 Int) (b_4_1 Int) (b_4_2 Int) (c_6_0 Int) (c_6_1 Int) (c_6_2 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_26_0 Int) (expr_27_0 Int) (expr_28_1 Bool) (expr_29_0 Int) (expr_30_0 Int) (expr_31_1 Bool) (expr_32_0 Bool) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Bool) (expr_36_0 Bool) (expr_9_0 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (= state_1 state_0) (= error_0 0)) (and (and (and true (= a_2_1 a_2_0)) (= b_4_1 b_4_0)) (= c_6_1 c_6_0))) (contract_initializer_entry_21_C_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 b_4_0 c_6_0 a_2_1 b_4_1 c_6_1))))


(declare-fun |contract_initializer_after_init_22_C_41_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int Int Int Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (b_4_0 Int) (b_4_1 Int) (b_4_2 Int) (c_6_0 Int) (c_6_1 Int) (c_6_2 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_26_0 Int) (expr_27_0 Int) (expr_28_1 Bool) (expr_29_0 Int) (expr_30_0 Int) (expr_31_1 Bool) (expr_32_0 Bool) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Bool) (expr_36_0 Bool) (expr_9_0 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (contract_initializer_entry_21_C_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 b_4_0 c_6_0 a_2_1 b_4_1 c_6_1) true) true) (contract_initializer_after_init_22_C_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 b_4_0 c_6_0 a_2_1 b_4_1 c_6_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (b_4_0 Int) (b_4_1 Int) (b_4_2 Int) (c_6_0 Int) (c_6_1 Int) (c_6_2 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_26_0 Int) (expr_27_0 Int) (expr_28_1 Bool) (expr_29_0 Int) (expr_30_0 Int) (expr_31_1 Bool) (expr_32_0 Bool) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Bool) (expr_36_0 Bool) (expr_9_0 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (contract_initializer_after_init_22_C_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 b_4_0 c_6_0 a_2_1 b_4_1 c_6_1) true) true) (contract_initializer_20_C_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 b_4_0 c_6_0 a_2_1 b_4_1 c_6_1))))


(declare-fun |implicit_constructor_entry_23_C_41_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int Int Int Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (b_4_0 Int) (b_4_1 Int) (b_4_2 Int) (c_6_0 Int) (c_6_1 Int) (c_6_2 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_26_0 Int) (expr_27_0 Int) (expr_28_1 Bool) (expr_29_0 Int) (expr_30_0 Int) (expr_31_1 Bool) (expr_32_0 Bool) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Bool) (expr_36_0 Bool) (expr_9_0 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (and (and (= state_1 state_0) (= error_0 0)) (and (and (and true (= a_2_1 a_2_0)) (= b_4_1 b_4_0)) (= c_6_1 c_6_0))) (and (and (and true (= a_2_1 0)) (= b_4_1 0)) (= c_6_1 0))) (>= (select (|balances| state_1) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_23_C_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 b_4_0 c_6_0 a_2_1 b_4_1 c_6_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (b_4_0 Int) (b_4_1 Int) (b_4_2 Int) (c_6_0 Int) (c_6_1 Int) (c_6_2 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_26_0 Int) (expr_27_0 Int) (expr_28_1 Bool) (expr_29_0 Int) (expr_30_0 Int) (expr_31_1 Bool) (expr_32_0 Bool) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Bool) (expr_36_0 Bool) (expr_9_0 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (implicit_constructor_entry_23_C_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 b_4_0 c_6_0 a_2_1 b_4_1 c_6_1) (and (contract_initializer_20_C_41_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 a_2_1 b_4_1 c_6_1 a_2_2 b_4_2 c_6_2) true)) (> error_1 0)) (summary_constructor_2_C_41_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 a_2_0 b_4_0 c_6_0 a_2_2 b_4_2 c_6_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (b_4_0 Int) (b_4_1 Int) (b_4_2 Int) (c_6_0 Int) (c_6_1 Int) (c_6_2 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_26_0 Int) (expr_27_0 Int) (expr_28_1 Bool) (expr_29_0 Int) (expr_30_0 Int) (expr_31_1 Bool) (expr_32_0 Bool) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Bool) (expr_36_0 Bool) (expr_9_0 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (implicit_constructor_entry_23_C_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 b_4_0 c_6_0 a_2_1 b_4_1 c_6_1) (and (= error_1 0) (and (contract_initializer_20_C_41_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 a_2_1 b_4_1 c_6_1 a_2_2 b_4_2 c_6_2) true))) true) (summary_constructor_2_C_41_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 a_2_0 b_4_0 c_6_0 a_2_2 b_4_2 c_6_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (b_4_0 Int) (b_4_1 Int) (b_4_2 Int) (c_6_0 Int) (c_6_1 Int) (c_6_2 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_26_0 Int) (expr_27_0 Int) (expr_28_1 Bool) (expr_29_0 Int) (expr_30_0 Int) (expr_31_1 Bool) (expr_32_0 Bool) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Bool) (expr_36_0 Bool) (expr_9_0 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (summary_constructor_2_C_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 b_4_0 c_6_0 a_2_1 b_4_1 c_6_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 0))) (interface_0_C_41_0 this_0 abi_0 crypto_0 state_1 a_2_1 b_4_1 c_6_1))))


(declare-fun |error_target_3_0| () Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (b_4_0 Int) (b_4_1 Int) (b_4_2 Int) (c_6_0 Int) (c_6_1 Int) (c_6_2 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_26_0 Int) (expr_27_0 Int) (expr_28_1 Bool) (expr_29_0 Int) (expr_30_0 Int) (expr_31_1 Bool) (expr_32_0 Bool) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Bool) (expr_36_0 Bool) (expr_9_0 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (interface_0_C_41_0 this_0 abi_0 crypto_0 state_0 a_2_0 b_4_0 c_6_0) true) (and (summary_4_function_test__40_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 b_4_0 c_6_0 state_1 a_2_1 b_4_1 c_6_1) (= error_0 1))) error_target_3_0)))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (b_4_0 Int) (b_4_1 Int) (b_4_2 Int) (c_6_0 Int) (c_6_1 Int) (c_6_2 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_26_0 Int) (expr_27_0 Int) (expr_28_1 Bool) (expr_29_0 Int) (expr_30_0 Int) (expr_31_1 Bool) (expr_32_0 Bool) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Bool) (expr_36_0 Bool) (expr_9_0 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> error_target_3_0 false)))
(check-sat)