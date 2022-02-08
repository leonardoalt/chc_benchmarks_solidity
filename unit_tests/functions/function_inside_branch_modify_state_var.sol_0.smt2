(set-logic HORN)

(declare-datatypes ((|state_type| 0)) (((|state_type| (|balances| (Array Int Int))))))
(declare-datatypes ((|bytes_tuple| 0)) (((|bytes_tuple| (|bytes_tuple_accessor_array| (Array Int Int)) (|bytes_tuple_accessor_length| Int)))))
(declare-datatypes ((|tx_type| 0)) (((|tx_type| (|block.basefee| Int) (|block.chainid| Int) (|block.coinbase| Int) (|block.difficulty| Int) (|block.gaslimit| Int) (|block.number| Int) (|block.timestamp| Int) (|blockhash| (Array Int Int)) (|msg.data| |bytes_tuple|) (|msg.sender| Int) (|msg.sig| Int) (|msg.value| Int) (|tx.gasprice| Int) (|tx.origin| Int)))))
(declare-datatypes ((|ecrecover_input_type| 0)) (((|ecrecover_input_type| (|hash| Int) (|v| Int) (|r| Int) (|s| Int)))))
(declare-datatypes ((|crypto_type| 0)) (((|crypto_type| (|ecrecover| (Array |ecrecover_input_type| Int)) (|keccak256| (Array |bytes_tuple| Int)) (|ripemd160| (Array |bytes_tuple| Int)) (|sha256| (Array |bytes_tuple| Int))))))
(declare-datatypes ((|abi_type| 0)) (((|abi_type|))))
(declare-datatypes ((|tuple()| 0)) (((|tuple()|))))
(declare-fun |interface_0_C_40_0| (Int |abi_type| |crypto_type| |state_type| Int ) Bool)
(declare-fun |nondet_interface_1_C_40_0| (Int Int |abi_type| |crypto_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_constructor_2_C_40_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int))
(=> (= error_0 0) (nondet_interface_1_C_40_0 error_0 this_0 abi_0 crypto_0 state_0 x_2_0 state_0 x_2_0))))


(declare-fun |summary_3_function_f__18_40_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_4_function_g__39_40_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Bool |state_type| Int Bool ) Bool)
(declare-fun |summary_5_function_g__39_40_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Bool |state_type| Int Bool ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (b_20_0 Bool) (b_20_1 Bool) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (nondet_interface_1_C_40_0 error_0 this_0 abi_0 crypto_0 state_0 x_2_0 state_1 x_2_1) true) (and (= error_0 0) (summary_5_function_g__39_40_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 b_20_0 state_2 x_2_2 b_20_1))) (nondet_interface_1_C_40_0 error_1 this_0 abi_0 crypto_0 state_0 x_2_0 state_2 x_2_2))))


(declare-fun |block_6_function_f__18_40_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_7_f_17_40_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (b_20_0 Bool) (b_20_1 Bool) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(block_6_function_f__18_40_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1)))


(assert
(forall ( (abi_0 |abi_type|) (b_20_0 Bool) (b_20_1 Bool) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (block_6_function_f__18_40_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_2_1 x_2_0))) true) true)) true) (block_7_f_17_40_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(declare-fun |block_8_return_function_f__18_40_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (b_20_0 Bool) (b_20_1 Bool) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_11_0 Int) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Int) (expr_15_1 Int) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (block_7_f_17_40_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (= x_2_2 expr_15_1) (and (=> true (and (>= expr_15_1 0) (<= expr_15_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_15_1 expr_14_1) (and (=> true (and (>= expr_11_0 0) (<= expr_11_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_11_0 x_2_1) (and (=> true (and (>= expr_14_1 0) (<= expr_14_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_14_1 (+ expr_12_0 expr_13_0)) (and (=> true true) (and (= expr_13_0 1) (and (=> true (and (>= expr_12_0 0) (<= expr_12_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_12_0 x_2_1) (and (=> true expr_8_1) (and (= expr_8_1 (< expr_6_0 expr_7_0)) (and (=> true true) (and (= expr_7_0 10000) (and (=> true (and (>= expr_6_0 0) (<= expr_6_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_6_0 x_2_1) true)))))))))))))))))) true) (block_8_return_function_f__18_40_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (b_20_0 Bool) (b_20_1 Bool) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_11_0 Int) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Int) (expr_15_1 Int) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (block_8_return_function_f__18_40_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) true) true) (summary_3_function_f__18_40_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(declare-fun |block_9_function_g__39_40_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Bool |state_type| Int Bool ) Bool)
(declare-fun |block_10_g_38_40_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Bool |state_type| Int Bool ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (b_20_0 Bool) (b_20_1 Bool) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_11_0 Int) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Int) (expr_15_1 Int) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(block_9_function_g__39_40_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 b_20_0 state_1 x_2_1 b_20_1)))


(assert
(forall ( (abi_0 |abi_type|) (b_20_0 Bool) (b_20_1 Bool) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_11_0 Int) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Int) (expr_15_1 Int) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (block_9_function_g__39_40_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 b_20_0 state_1 x_2_1 b_20_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_2_1 x_2_0))) (and true (= b_20_1 b_20_0))) true)) true) (block_10_g_38_40_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 b_20_0 state_1 x_2_1 b_20_1))))


(declare-fun |block_11_return_function_g__39_40_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Bool |state_type| Int Bool ) Bool)
(declare-fun |block_12_if_header_g_31_40_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Bool |state_type| Int Bool ) Bool)
(declare-fun |block_13_if_true_g_30_40_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Bool |state_type| Int Bool ) Bool)
(declare-fun |block_14_g_38_40_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Bool |state_type| Int Bool ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (b_20_0 Bool) (b_20_1 Bool) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_11_0 Int) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Int) (expr_15_1 Int) (expr_23_0 Int) (expr_24_0 Int) (expr_25_1 Int) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (block_10_g_38_40_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 b_20_0 state_1 x_2_1 b_20_1) (and (= x_2_2 expr_25_1) (and (=> true (and (>= expr_25_1 0) (<= expr_25_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_25_1 expr_24_0) (and (=> true (and (>= expr_23_0 0) (<= expr_23_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_23_0 x_2_1) (and (=> true true) (and (= expr_24_0 0) (and true true))))))))) true) (block_12_if_header_g_31_40_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 b_20_0 state_1 x_2_2 b_20_1))))


(assert
(forall ( (abi_0 |abi_type|) (b_20_0 Bool) (b_20_1 Bool) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_11_0 Int) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Int) (expr_15_1 Int) (expr_23_0 Int) (expr_24_0 Int) (expr_25_1 Int) (expr_27_0 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (block_12_if_header_g_31_40_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 b_20_0 state_1 x_2_1 b_20_1) (and (= expr_27_0 b_20_1) true)) expr_27_0) (block_13_if_true_g_30_40_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 b_20_0 state_1 x_2_1 b_20_1))))


(assert
(forall ( (abi_0 |abi_type|) (b_20_0 Bool) (b_20_1 Bool) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_11_0 Int) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Int) (expr_15_1 Int) (expr_23_0 Int) (expr_24_0 Int) (expr_25_1 Int) (expr_27_0 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (block_12_if_header_g_31_40_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 b_20_0 state_1 x_2_1 b_20_1) (and (= expr_27_0 b_20_1) true)) (not expr_27_0)) (block_14_g_38_40_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 b_20_0 state_1 x_2_1 b_20_1))))


(declare-fun |summary_15_function_f__18_40_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (b_20_0 Bool) (b_20_1 Bool) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_11_0 Int) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Int) (expr_15_1 Int) (expr_23_0 Int) (expr_24_0 Int) (expr_25_1 Int) (expr_27_0 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (summary_3_function_f__18_40_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2) (summary_15_function_f__18_40_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (b_20_0 Bool) (b_20_1 Bool) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_11_0 Int) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Int) (expr_15_1 Int) (expr_23_0 Int) (expr_24_0 Int) (expr_25_1 Int) (expr_27_0 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (block_13_if_true_g_30_40_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 b_20_0 state_1 x_2_1 b_20_1) (and (summary_15_function_f__18_40_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 state_2 x_2_2) true)) (> error_1 0)) (summary_4_function_g__39_40_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 b_20_0 state_2 x_2_2 b_20_1))))


(assert
(forall ( (abi_0 |abi_type|) (b_20_0 Bool) (b_20_1 Bool) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_11_0 Int) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Int) (expr_15_1 Int) (expr_23_0 Int) (expr_24_0 Int) (expr_25_1 Int) (expr_27_0 Bool) (expr_29_1 |tuple()|) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (block_13_if_true_g_30_40_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 b_20_0 state_1 x_2_1 b_20_1) (and (= error_1 0) (and (summary_15_function_f__18_40_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 state_2 x_2_2) true))) true) (block_14_g_38_40_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 b_20_0 state_2 x_2_2 b_20_1))))


(declare-fun |block_16_function_g__39_40_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Bool |state_type| Int Bool ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (b_20_0 Bool) (b_20_1 Bool) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_11_0 Int) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Int) (expr_15_1 Int) (expr_23_0 Int) (expr_24_0 Int) (expr_25_1 Int) (expr_27_0 Bool) (expr_29_1 |tuple()|) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (block_14_g_38_40_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 b_20_0 state_1 x_2_1 b_20_1) (and (= expr_35_1 (= expr_33_0 expr_34_0)) (and (=> true true) (and (= expr_34_0 0) (and (=> true (and (>= expr_33_0 0) (<= expr_33_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_33_0 x_2_1) true)))))) (and (not expr_35_1) (= error_1 1))) (block_16_function_g__39_40_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 b_20_0 state_1 x_2_1 b_20_1))))


(assert
(forall ( (abi_0 |abi_type|) (b_20_0 Bool) (b_20_1 Bool) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_11_0 Int) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Int) (expr_15_1 Int) (expr_23_0 Int) (expr_24_0 Int) (expr_25_1 Int) (expr_27_0 Bool) (expr_29_1 |tuple()|) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (block_16_function_g__39_40_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 b_20_0 state_1 x_2_1 b_20_1) (summary_4_function_g__39_40_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 b_20_0 state_1 x_2_1 b_20_1))))


(assert
(forall ( (abi_0 |abi_type|) (b_20_0 Bool) (b_20_1 Bool) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_11_0 Int) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Int) (expr_15_1 Int) (expr_23_0 Int) (expr_24_0 Int) (expr_25_1 Int) (expr_27_0 Bool) (expr_29_1 |tuple()|) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (block_14_g_38_40_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 b_20_0 state_1 x_2_1 b_20_1) (and (= error_1 error_0) (and (= expr_35_1 (= expr_33_0 expr_34_0)) (and (=> true true) (and (= expr_34_0 0) (and (=> true (and (>= expr_33_0 0) (<= expr_33_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_33_0 x_2_1) true))))))) true) (block_11_return_function_g__39_40_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 b_20_0 state_1 x_2_1 b_20_1))))


(assert
(forall ( (abi_0 |abi_type|) (b_20_0 Bool) (b_20_1 Bool) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_11_0 Int) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Int) (expr_15_1 Int) (expr_23_0 Int) (expr_24_0 Int) (expr_25_1 Int) (expr_27_0 Bool) (expr_29_1 |tuple()|) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (block_11_return_function_g__39_40_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 b_20_0 state_1 x_2_1 b_20_1) true) true) (summary_4_function_g__39_40_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 b_20_0 state_1 x_2_1 b_20_1))))


(declare-fun |block_17_function_g__39_40_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Bool |state_type| Int Bool ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (b_20_0 Bool) (b_20_1 Bool) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_11_0 Int) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Int) (expr_15_1 Int) (expr_23_0 Int) (expr_24_0 Int) (expr_25_1 Int) (expr_27_0 Bool) (expr_29_1 |tuple()|) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(block_17_function_g__39_40_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 b_20_0 state_1 x_2_1 b_20_1)))


(assert
(forall ( (abi_0 |abi_type|) (b_20_0 Bool) (b_20_1 Bool) (b_20_2 Bool) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_11_0 Int) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Int) (expr_15_1 Int) (expr_23_0 Int) (expr_24_0 Int) (expr_25_1 Int) (expr_27_0 Bool) (expr_29_1 |tuple()|) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Bool) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (block_17_function_g__39_40_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 b_20_0 state_1 x_2_1 b_20_1) (and (summary_4_function_g__39_40_0 error_1 this_0 abi_0 crypto_0 tx_0 state_2 x_2_1 b_20_1 state_3 x_2_2 b_20_2) (and (= state_2 (|state_type| (store (|balances| state_1) this_0 (+ (select (|balances| state_1) this_0) funds_2_0)))) (and (and (>= (+ (select (|balances| state_1) this_0) funds_2_0) 0) (<= (+ (select (|balances| state_1) this_0) funds_2_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= funds_2_0 (|msg.value| tx_0)) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (and (and (and (and (and (= (|msg.value| tx_0) 0) (= (|msg.sig| tx_0) 3565196023)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 0) 212)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 1) 128)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 2) 146)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 3) 247)) (>= (|bytes_tuple_accessor_length| (|msg.data| tx_0)) 4))) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_2_1 x_2_0))) (and true (= b_20_1 b_20_0))) true))))))) true) (summary_5_function_g__39_40_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 b_20_0 state_3 x_2_2 b_20_2))))


(assert
(forall ( (abi_0 |abi_type|) (b_20_0 Bool) (b_20_1 Bool) (b_20_2 Bool) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_11_0 Int) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Int) (expr_15_1 Int) (expr_23_0 Int) (expr_24_0 Int) (expr_25_1 Int) (expr_27_0 Bool) (expr_29_1 |tuple()|) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Bool) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (interface_0_C_40_0 this_0 abi_0 crypto_0 state_0 x_2_0) true) (and (summary_5_function_g__39_40_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 b_20_0 state_1 x_2_1 b_20_1) (= error_0 0))) (interface_0_C_40_0 this_0 abi_0 crypto_0 state_1 x_2_1))))


(declare-fun |contract_initializer_18_C_40_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(declare-fun |contract_initializer_entry_19_C_40_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (b_20_0 Bool) (b_20_1 Bool) (b_20_2 Bool) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_11_0 Int) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Int) (expr_15_1 Int) (expr_23_0 Int) (expr_24_0 Int) (expr_25_1 Int) (expr_27_0 Bool) (expr_29_1 |tuple()|) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Bool) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_2_1 x_2_0))) (contract_initializer_entry_19_C_40_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1))))


(declare-fun |contract_initializer_after_init_20_C_40_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (b_20_0 Bool) (b_20_1 Bool) (b_20_2 Bool) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_11_0 Int) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Int) (expr_15_1 Int) (expr_23_0 Int) (expr_24_0 Int) (expr_25_1 Int) (expr_27_0 Bool) (expr_29_1 |tuple()|) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Bool) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (contract_initializer_entry_19_C_40_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1) true) true) (contract_initializer_after_init_20_C_40_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1))))


(assert
(forall ( (abi_0 |abi_type|) (b_20_0 Bool) (b_20_1 Bool) (b_20_2 Bool) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_11_0 Int) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Int) (expr_15_1 Int) (expr_23_0 Int) (expr_24_0 Int) (expr_25_1 Int) (expr_27_0 Bool) (expr_29_1 |tuple()|) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Bool) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (contract_initializer_after_init_20_C_40_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1) true) true) (contract_initializer_18_C_40_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1))))


(declare-fun |implicit_constructor_entry_21_C_40_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (b_20_0 Bool) (b_20_1 Bool) (b_20_2 Bool) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_11_0 Int) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Int) (expr_15_1 Int) (expr_23_0 Int) (expr_24_0 Int) (expr_25_1 Int) (expr_27_0 Bool) (expr_29_1 |tuple()|) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Bool) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_2_1 x_2_0))) (and true (= x_2_1 0))) (>= (select (|balances| state_1) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_21_C_40_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1))))


(assert
(forall ( (abi_0 |abi_type|) (b_20_0 Bool) (b_20_1 Bool) (b_20_2 Bool) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_11_0 Int) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Int) (expr_15_1 Int) (expr_23_0 Int) (expr_24_0 Int) (expr_25_1 Int) (expr_27_0 Bool) (expr_29_1 |tuple()|) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Bool) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (implicit_constructor_entry_21_C_40_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1) (and (contract_initializer_18_C_40_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 x_2_1 x_2_2) true)) (> error_1 0)) (summary_constructor_2_C_40_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 x_2_0 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (b_20_0 Bool) (b_20_1 Bool) (b_20_2 Bool) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_11_0 Int) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Int) (expr_15_1 Int) (expr_23_0 Int) (expr_24_0 Int) (expr_25_1 Int) (expr_27_0 Bool) (expr_29_1 |tuple()|) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Bool) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (implicit_constructor_entry_21_C_40_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1) (and (= error_1 0) (and (contract_initializer_18_C_40_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 x_2_1 x_2_2) true))) true) (summary_constructor_2_C_40_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 x_2_0 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (b_20_0 Bool) (b_20_1 Bool) (b_20_2 Bool) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_11_0 Int) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Int) (expr_15_1 Int) (expr_23_0 Int) (expr_24_0 Int) (expr_25_1 Int) (expr_27_0 Bool) (expr_29_1 |tuple()|) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Bool) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (summary_constructor_2_C_40_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 0))) (interface_0_C_40_0 this_0 abi_0 crypto_0 state_1 x_2_1))))


(declare-fun |error_target_3_0| () Bool)
(assert
(forall ( (abi_0 |abi_type|) (b_20_0 Bool) (b_20_1 Bool) (b_20_2 Bool) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_11_0 Int) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Int) (expr_15_1 Int) (expr_23_0 Int) (expr_24_0 Int) (expr_25_1 Int) (expr_27_0 Bool) (expr_29_1 |tuple()|) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Bool) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (interface_0_C_40_0 this_0 abi_0 crypto_0 state_0 x_2_0) true) (and (summary_5_function_g__39_40_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 b_20_0 state_1 x_2_1 b_20_1) (= error_0 1))) error_target_3_0)))


(assert
(forall ( (abi_0 |abi_type|) (b_20_0 Bool) (b_20_1 Bool) (b_20_2 Bool) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_11_0 Int) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Int) (expr_15_1 Int) (expr_23_0 Int) (expr_24_0 Int) (expr_25_1 Int) (expr_27_0 Bool) (expr_29_1 |tuple()|) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Bool) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> error_target_3_0 false)))
(check-sat)