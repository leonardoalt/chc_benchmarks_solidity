(set-logic HORN)

(declare-datatypes ((|state_type| 0)) (((|state_type| (|balances| (Array Int Int))))))
(declare-datatypes ((|bytes_tuple| 0)) (((|bytes_tuple| (|bytes_tuple_accessor_array| (Array Int Int)) (|bytes_tuple_accessor_length| Int)))))
(declare-datatypes ((|tx_type| 0)) (((|tx_type| (|block.basefee| Int) (|block.chainid| Int) (|block.coinbase| Int) (|block.difficulty| Int) (|block.gaslimit| Int) (|block.number| Int) (|block.timestamp| Int) (|blockhash| (Array Int Int)) (|msg.data| |bytes_tuple|) (|msg.sender| Int) (|msg.sig| Int) (|msg.value| Int) (|tx.gasprice| Int) (|tx.origin| Int)))))
(declare-datatypes ((|ecrecover_input_type| 0)) (((|ecrecover_input_type| (|hash| Int) (|v| Int) (|r| Int) (|s| Int)))))
(declare-datatypes ((|crypto_type| 0)) (((|crypto_type| (|ecrecover| (Array |ecrecover_input_type| Int)) (|keccak256| (Array |bytes_tuple| Int)) (|ripemd160| (Array |bytes_tuple| Int)) (|sha256| (Array |bytes_tuple| Int))))))
(declare-datatypes ((|abi_type| 0)) (((|abi_type|))))
(declare-fun |interface_0_C_40_0| (Int |abi_type| |crypto_type| |state_type| ) Bool)
(declare-fun |nondet_interface_1_C_40_0| (Int Int |abi_type| |crypto_type| |state_type| |state_type| ) Bool)
(declare-fun |summary_constructor_2_C_40_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (= error_0 0) (nondet_interface_1_C_40_0 error_0 this_0 abi_0 crypto_0 state_0 state_0))))


(declare-fun |summary_3_function_f__39_40_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Bool Int |state_type| Bool Int ) Bool)
(declare-fun |summary_4_function_f__39_40_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Bool Int |state_type| Bool Int ) Bool)
(assert
(forall ( (a_4_0 Int) (a_4_1 Int) (abi_0 |abi_type|) (b_2_0 Bool) (b_2_1 Bool) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (nondet_interface_1_C_40_0 error_0 this_0 abi_0 crypto_0 state_0 state_1) true) (and (= error_0 0) (summary_4_function_f__39_40_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 b_2_0 a_4_0 state_2 b_2_1 a_4_1))) (nondet_interface_1_C_40_0 error_1 this_0 abi_0 crypto_0 state_0 state_2))))


(declare-fun |block_5_function_f__39_40_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Bool Int |state_type| Bool Int Int ) Bool)
(declare-fun |block_6_f_38_40_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Bool Int |state_type| Bool Int Int ) Bool)
(assert
(forall ( (a_4_0 Int) (a_4_1 Int) (abi_0 |abi_type|) (b_2_0 Bool) (b_2_1 Bool) (c_19_0 Int) (c_19_1 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(block_5_function_f__39_40_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 b_2_0 a_4_0 state_1 b_2_1 a_4_1 c_19_1)))


(assert
(forall ( (a_4_0 Int) (a_4_1 Int) (abi_0 |abi_type|) (b_2_0 Bool) (b_2_1 Bool) (c_19_0 Int) (c_19_1 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_5_function_f__39_40_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 b_2_0 a_4_0 state_1 b_2_1 a_4_1 c_19_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) true) (and (and true (= b_2_1 b_2_0)) (= a_4_1 a_4_0))) true)) true) (block_6_f_38_40_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 b_2_0 a_4_0 state_1 b_2_1 a_4_1 c_19_1))))


(declare-fun |block_7_return_function_f__39_40_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Bool Int |state_type| Bool Int Int ) Bool)
(declare-fun |block_8_if_header_f_17_40_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Bool Int |state_type| Bool Int Int ) Bool)
(declare-fun |block_9_if_true_f_16_40_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Bool Int |state_type| Bool Int Int ) Bool)
(declare-fun |block_10_f_38_40_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Bool Int |state_type| Bool Int Int ) Bool)
(assert
(forall ( (a_4_0 Int) (a_4_1 Int) (abi_0 |abi_type|) (b_2_0 Bool) (b_2_1 Bool) (c_19_0 Int) (c_19_1 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_6_f_38_40_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 b_2_0 a_4_0 state_1 b_2_1 a_4_1 c_19_1) (and (=> true expr_10_1) (and (= expr_10_1 (<= expr_8_0 expr_9_0)) (and (=> true true) (and (= expr_9_0 256) (and (=> true (and (>= expr_8_0 0) (<= expr_8_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_8_0 a_4_1) (and (and (>= a_4_1 0) (<= a_4_1 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and true (and (= c_19_1 0) true)))))))))) true) (block_8_if_header_f_17_40_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 b_2_0 a_4_0 state_1 b_2_1 a_4_1 c_19_1))))


(assert
(forall ( (a_4_0 Int) (a_4_1 Int) (abi_0 |abi_type|) (b_2_0 Bool) (b_2_1 Bool) (c_19_0 Int) (c_19_1 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_13_0 Bool) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_8_if_header_f_17_40_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 b_2_0 a_4_0 state_1 b_2_1 a_4_1 c_19_1) (and (= expr_13_0 b_2_1) true)) expr_13_0) (block_9_if_true_f_16_40_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 b_2_0 a_4_0 state_1 b_2_1 a_4_1 c_19_1))))


(assert
(forall ( (a_4_0 Int) (a_4_1 Int) (abi_0 |abi_type|) (b_2_0 Bool) (b_2_1 Bool) (c_19_0 Int) (c_19_1 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_13_0 Bool) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_8_if_header_f_17_40_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 b_2_0 a_4_0 state_1 b_2_1 a_4_1 c_19_1) (and (= expr_13_0 b_2_1) true)) (not expr_13_0)) (block_10_f_38_40_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 b_2_0 a_4_0 state_1 b_2_1 a_4_1 c_19_1))))


(assert
(forall ( (a_4_0 Int) (a_4_1 Int) (abi_0 |abi_type|) (b_2_0 Bool) (b_2_1 Bool) (c_19_0 Int) (c_19_1 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_13_0 Bool) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_9_if_true_f_16_40_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 b_2_0 a_4_0 state_1 b_2_1 a_4_1 c_19_1) (and (=> true false) true)) true) (block_10_f_38_40_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 b_2_0 a_4_0 state_1 b_2_1 a_4_1 c_19_1))))


(declare-fun |block_11_if_header_f_31_40_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Bool Int |state_type| Bool Int Int ) Bool)
(declare-fun |block_12_if_true_f_27_40_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Bool Int |state_type| Bool Int Int ) Bool)
(declare-fun |block_13_if_false_f_30_40_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Bool Int |state_type| Bool Int Int ) Bool)
(declare-fun |block_14_f_38_40_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Bool Int |state_type| Bool Int Int ) Bool)
(assert
(forall ( (a_4_0 Int) (a_4_1 Int) (abi_0 |abi_type|) (b_2_0 Bool) (b_2_1 Bool) (c_19_0 Int) (c_19_1 Int) (c_19_2 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_13_0 Bool) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_10_f_38_40_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 b_2_0 a_4_0 state_1 b_2_1 a_4_1 c_19_1) (and (= c_19_2 expr_22_1) (and (=> true (and (>= expr_22_1 0) (<= expr_22_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_22_1 (+ expr_20_0 expr_21_0)) (and (=> true true) (and (= expr_21_0 1) (and (=> true (and (>= expr_20_0 0) (<= expr_20_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_20_0 a_4_1) true)))))))) true) (block_11_if_header_f_31_40_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 b_2_0 a_4_0 state_1 b_2_1 a_4_1 c_19_2))))


(assert
(forall ( (a_4_0 Int) (a_4_1 Int) (abi_0 |abi_type|) (b_2_0 Bool) (b_2_1 Bool) (c_19_0 Int) (c_19_1 Int) (c_19_2 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_13_0 Bool) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_24_0 Bool) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_11_if_header_f_31_40_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 b_2_0 a_4_0 state_1 b_2_1 a_4_1 c_19_1) (and (= expr_24_0 b_2_1) true)) expr_24_0) (block_12_if_true_f_27_40_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 b_2_0 a_4_0 state_1 b_2_1 a_4_1 c_19_1))))


(assert
(forall ( (a_4_0 Int) (a_4_1 Int) (abi_0 |abi_type|) (b_2_0 Bool) (b_2_1 Bool) (c_19_0 Int) (c_19_1 Int) (c_19_2 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_13_0 Bool) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_24_0 Bool) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_11_if_header_f_31_40_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 b_2_0 a_4_0 state_1 b_2_1 a_4_1 c_19_1) (and (= expr_24_0 b_2_1) true)) (not expr_24_0)) (block_13_if_false_f_30_40_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 b_2_0 a_4_0 state_1 b_2_1 a_4_1 c_19_1))))


(assert
(forall ( (a_4_0 Int) (a_4_1 Int) (abi_0 |abi_type|) (b_2_0 Bool) (b_2_1 Bool) (c_19_0 Int) (c_19_1 Int) (c_19_2 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_13_0 Bool) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_24_0 Bool) (expr_25_0 Int) (expr_26_1 Int) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_12_if_true_f_27_40_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 b_2_0 a_4_0 state_1 b_2_1 a_4_1 c_19_1) (and (= c_19_2 (- expr_25_0 1)) (and (=> true (and (>= expr_26_1 0) (<= expr_26_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_26_1 expr_25_0) (and (=> true (and (>= expr_25_0 0) (<= expr_25_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_25_0 c_19_1) true)))))) true) (block_14_f_38_40_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 b_2_0 a_4_0 state_1 b_2_1 a_4_1 c_19_2))))


(assert
(forall ( (a_4_0 Int) (a_4_1 Int) (abi_0 |abi_type|) (b_2_0 Bool) (b_2_1 Bool) (c_19_0 Int) (c_19_1 Int) (c_19_2 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_13_0 Bool) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_24_0 Bool) (expr_25_0 Int) (expr_26_1 Int) (expr_28_0 Int) (expr_29_1 Int) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_13_if_false_f_30_40_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 b_2_0 a_4_0 state_1 b_2_1 a_4_1 c_19_1) (and (= c_19_2 (+ expr_28_0 1)) (and (=> true (and (>= expr_29_1 0) (<= expr_29_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_29_1 expr_28_0) (and (=> true (and (>= expr_28_0 0) (<= expr_28_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_28_0 c_19_1) true)))))) true) (block_14_f_38_40_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 b_2_0 a_4_0 state_1 b_2_1 a_4_1 c_19_2))))


(declare-fun |block_15_function_f__39_40_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Bool Int |state_type| Bool Int Int ) Bool)
(assert
(forall ( (a_4_0 Int) (a_4_1 Int) (abi_0 |abi_type|) (b_2_0 Bool) (b_2_1 Bool) (c_19_0 Int) (c_19_1 Int) (c_19_2 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_13_0 Bool) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_24_0 Bool) (expr_25_0 Int) (expr_26_1 Int) (expr_28_0 Int) (expr_29_1 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_14_f_38_40_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 b_2_0 a_4_0 state_1 b_2_1 a_4_1 c_19_1) (and (= expr_35_1 (= expr_33_0 expr_34_0)) (and (=> true (and (>= expr_34_0 0) (<= expr_34_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_34_0 a_4_1) (and (=> true (and (>= expr_33_0 0) (<= expr_33_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_33_0 c_19_1) true)))))) (and (not expr_35_1) (= error_1 1))) (block_15_function_f__39_40_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 b_2_0 a_4_0 state_1 b_2_1 a_4_1 c_19_1))))


(assert
(forall ( (a_4_0 Int) (a_4_1 Int) (abi_0 |abi_type|) (b_2_0 Bool) (b_2_1 Bool) (c_19_0 Int) (c_19_1 Int) (c_19_2 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_13_0 Bool) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_24_0 Bool) (expr_25_0 Int) (expr_26_1 Int) (expr_28_0 Int) (expr_29_1 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (block_15_function_f__39_40_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 b_2_0 a_4_0 state_1 b_2_1 a_4_1 c_19_1) (summary_3_function_f__39_40_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 b_2_0 a_4_0 state_1 b_2_1 a_4_1))))


(assert
(forall ( (a_4_0 Int) (a_4_1 Int) (abi_0 |abi_type|) (b_2_0 Bool) (b_2_1 Bool) (c_19_0 Int) (c_19_1 Int) (c_19_2 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_13_0 Bool) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_24_0 Bool) (expr_25_0 Int) (expr_26_1 Int) (expr_28_0 Int) (expr_29_1 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_14_f_38_40_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 b_2_0 a_4_0 state_1 b_2_1 a_4_1 c_19_1) (and (= error_1 error_0) (and (= expr_35_1 (= expr_33_0 expr_34_0)) (and (=> true (and (>= expr_34_0 0) (<= expr_34_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_34_0 a_4_1) (and (=> true (and (>= expr_33_0 0) (<= expr_33_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_33_0 c_19_1) true))))))) true) (block_7_return_function_f__39_40_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 b_2_0 a_4_0 state_1 b_2_1 a_4_1 c_19_1))))


(assert
(forall ( (a_4_0 Int) (a_4_1 Int) (abi_0 |abi_type|) (b_2_0 Bool) (b_2_1 Bool) (c_19_0 Int) (c_19_1 Int) (c_19_2 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_13_0 Bool) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_24_0 Bool) (expr_25_0 Int) (expr_26_1 Int) (expr_28_0 Int) (expr_29_1 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_7_return_function_f__39_40_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 b_2_0 a_4_0 state_1 b_2_1 a_4_1 c_19_1) true) true) (summary_3_function_f__39_40_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 b_2_0 a_4_0 state_1 b_2_1 a_4_1))))


(declare-fun |block_16_function_f__39_40_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Bool Int |state_type| Bool Int Int ) Bool)
(assert
(forall ( (a_4_0 Int) (a_4_1 Int) (abi_0 |abi_type|) (b_2_0 Bool) (b_2_1 Bool) (c_19_0 Int) (c_19_1 Int) (c_19_2 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_13_0 Bool) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_24_0 Bool) (expr_25_0 Int) (expr_26_1 Int) (expr_28_0 Int) (expr_29_1 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(block_16_function_f__39_40_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 b_2_0 a_4_0 state_1 b_2_1 a_4_1 c_19_1)))


(assert
(forall ( (a_4_0 Int) (a_4_1 Int) (a_4_2 Int) (abi_0 |abi_type|) (b_2_0 Bool) (b_2_1 Bool) (b_2_2 Bool) (c_19_0 Int) (c_19_1 Int) (c_19_2 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_13_0 Bool) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_24_0 Bool) (expr_25_0 Int) (expr_26_1 Int) (expr_28_0 Int) (expr_29_1 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_16_function_f__39_40_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 b_2_0 a_4_0 state_1 b_2_1 a_4_1 c_19_1) (and (summary_3_function_f__39_40_0 error_1 this_0 abi_0 crypto_0 tx_0 state_2 b_2_1 a_4_1 state_3 b_2_2 a_4_2) (and (= state_2 (|state_type| (store (|balances| state_1) this_0 (+ (select (|balances| state_1) this_0) funds_2_0)))) (and (and (>= (+ (select (|balances| state_1) this_0) funds_2_0) 0) (<= (+ (select (|balances| state_1) this_0) funds_2_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= funds_2_0 (|msg.value| tx_0)) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (and (and (and (and (and (= (|msg.value| tx_0) 0) (= (|msg.sig| tx_0) 2592619581)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 0) 154)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 1) 136)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 2) 60)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 3) 61)) (>= (|bytes_tuple_accessor_length| (|msg.data| tx_0)) 4))) (and (and (and (and (= state_1 state_0) (= error_0 0)) true) (and (and true (= b_2_1 b_2_0)) (= a_4_1 a_4_0))) true))))))) true) (summary_4_function_f__39_40_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 b_2_0 a_4_0 state_3 b_2_2 a_4_2))))


(assert
(forall ( (a_4_0 Int) (a_4_1 Int) (a_4_2 Int) (abi_0 |abi_type|) (b_2_0 Bool) (b_2_1 Bool) (b_2_2 Bool) (c_19_0 Int) (c_19_1 Int) (c_19_2 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_13_0 Bool) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_24_0 Bool) (expr_25_0 Int) (expr_26_1 Int) (expr_28_0 Int) (expr_29_1 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (interface_0_C_40_0 this_0 abi_0 crypto_0 state_0) true) (and (summary_4_function_f__39_40_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 b_2_0 a_4_0 state_1 b_2_1 a_4_1) (= error_0 0))) (interface_0_C_40_0 this_0 abi_0 crypto_0 state_1))))


(declare-fun |contract_initializer_17_C_40_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(declare-fun |contract_initializer_entry_18_C_40_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (a_4_0 Int) (a_4_1 Int) (a_4_2 Int) (abi_0 |abi_type|) (b_2_0 Bool) (b_2_1 Bool) (b_2_2 Bool) (c_19_0 Int) (c_19_1 Int) (c_19_2 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_13_0 Bool) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_24_0 Bool) (expr_25_0 Int) (expr_26_1 Int) (expr_28_0 Int) (expr_29_1 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (= state_1 state_0) (= error_0 0)) true) (contract_initializer_entry_18_C_40_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |contract_initializer_after_init_19_C_40_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (a_4_0 Int) (a_4_1 Int) (a_4_2 Int) (abi_0 |abi_type|) (b_2_0 Bool) (b_2_1 Bool) (b_2_2 Bool) (c_19_0 Int) (c_19_1 Int) (c_19_2 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_13_0 Bool) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_24_0 Bool) (expr_25_0 Int) (expr_26_1 Int) (expr_28_0 Int) (expr_29_1 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (contract_initializer_entry_18_C_40_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) true) (contract_initializer_after_init_19_C_40_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (a_4_0 Int) (a_4_1 Int) (a_4_2 Int) (abi_0 |abi_type|) (b_2_0 Bool) (b_2_1 Bool) (b_2_2 Bool) (c_19_0 Int) (c_19_1 Int) (c_19_2 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_13_0 Bool) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_24_0 Bool) (expr_25_0 Int) (expr_26_1 Int) (expr_28_0 Int) (expr_29_1 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (contract_initializer_after_init_19_C_40_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) true) (contract_initializer_17_C_40_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |implicit_constructor_entry_20_C_40_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (a_4_0 Int) (a_4_1 Int) (a_4_2 Int) (abi_0 |abi_type|) (b_2_0 Bool) (b_2_1 Bool) (b_2_2 Bool) (c_19_0 Int) (c_19_1 Int) (c_19_2 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_13_0 Bool) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_24_0 Bool) (expr_25_0 Int) (expr_26_1 Int) (expr_28_0 Int) (expr_29_1 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (and (and (= state_1 state_0) (= error_0 0)) true) true) (>= (select (|balances| state_1) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_20_C_40_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (a_4_0 Int) (a_4_1 Int) (a_4_2 Int) (abi_0 |abi_type|) (b_2_0 Bool) (b_2_1 Bool) (b_2_2 Bool) (c_19_0 Int) (c_19_1 Int) (c_19_2 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_13_0 Bool) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_24_0 Bool) (expr_25_0 Int) (expr_26_1 Int) (expr_28_0 Int) (expr_29_1 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (implicit_constructor_entry_20_C_40_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (contract_initializer_17_C_40_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2) true)) (> error_1 0)) (summary_constructor_2_C_40_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2))))


(assert
(forall ( (a_4_0 Int) (a_4_1 Int) (a_4_2 Int) (abi_0 |abi_type|) (b_2_0 Bool) (b_2_1 Bool) (b_2_2 Bool) (c_19_0 Int) (c_19_1 Int) (c_19_2 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_13_0 Bool) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_24_0 Bool) (expr_25_0 Int) (expr_26_1 Int) (expr_28_0 Int) (expr_29_1 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (implicit_constructor_entry_20_C_40_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (= error_1 0) (and (contract_initializer_17_C_40_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2) true))) true) (summary_constructor_2_C_40_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2))))


(assert
(forall ( (a_4_0 Int) (a_4_1 Int) (a_4_2 Int) (abi_0 |abi_type|) (b_2_0 Bool) (b_2_1 Bool) (b_2_2 Bool) (c_19_0 Int) (c_19_1 Int) (c_19_2 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_13_0 Bool) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_24_0 Bool) (expr_25_0 Int) (expr_26_1 Int) (expr_28_0 Int) (expr_29_1 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (summary_constructor_2_C_40_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 0))) (interface_0_C_40_0 this_0 abi_0 crypto_0 state_1))))


(declare-fun |error_target_3_0| () Bool)
(assert
(forall ( (a_4_0 Int) (a_4_1 Int) (a_4_2 Int) (abi_0 |abi_type|) (b_2_0 Bool) (b_2_1 Bool) (b_2_2 Bool) (c_19_0 Int) (c_19_1 Int) (c_19_2 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_13_0 Bool) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_24_0 Bool) (expr_25_0 Int) (expr_26_1 Int) (expr_28_0 Int) (expr_29_1 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (interface_0_C_40_0 this_0 abi_0 crypto_0 state_0) true) (and (summary_4_function_f__39_40_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 b_2_0 a_4_0 state_1 b_2_1 a_4_1) (= error_0 1))) error_target_3_0)))


(assert
(forall ( (a_4_0 Int) (a_4_1 Int) (a_4_2 Int) (abi_0 |abi_type|) (b_2_0 Bool) (b_2_1 Bool) (b_2_2 Bool) (c_19_0 Int) (c_19_1 Int) (c_19_2 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_13_0 Bool) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_24_0 Bool) (expr_25_0 Int) (expr_26_1 Int) (expr_28_0 Int) (expr_29_1 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> error_target_3_0 false)))
(check-sat)