(set-logic HORN)

(declare-datatypes ((|state_type| 0)) (((|state_type| (|balances| (Array Int Int))))))
(declare-datatypes ((|bytes_tuple| 0)) (((|bytes_tuple| (|bytes_tuple_accessor_array| (Array Int Int)) (|bytes_tuple_accessor_length| Int)))))
(declare-datatypes ((|tx_type| 0)) (((|tx_type| (|block.basefee| Int) (|block.chainid| Int) (|block.coinbase| Int) (|block.difficulty| Int) (|block.gaslimit| Int) (|block.number| Int) (|block.timestamp| Int) (|blockhash| (Array Int Int)) (|msg.data| |bytes_tuple|) (|msg.sender| Int) (|msg.sig| Int) (|msg.value| Int) (|tx.gasprice| Int) (|tx.origin| Int)))))
(declare-datatypes ((|ecrecover_input_type| 0)) (((|ecrecover_input_type| (|hash| Int) (|v| Int) (|r| Int) (|s| Int)))))
(declare-datatypes ((|crypto_type| 0)) (((|crypto_type| (|ecrecover| (Array |ecrecover_input_type| Int)) (|keccak256| (Array |bytes_tuple| Int)) (|ripemd160| (Array |bytes_tuple| Int)) (|sha256| (Array |bytes_tuple| Int))))))
(declare-datatypes ((|abi_type| 0)) (((|abi_type|))))
(declare-fun |interface_0_Simple_47_0| (Int |abi_type| |crypto_type| |state_type| ) Bool)
(declare-fun |nondet_interface_1_Simple_47_0| (Int Int |abi_type| |crypto_type| |state_type| |state_type| ) Bool)
(declare-fun |summary_constructor_2_Simple_47_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (= error_0 0) (nondet_interface_1_Simple_47_0 error_0 this_0 abi_0 crypto_0 state_0 state_0))))


(declare-fun |summary_3_function_f__46_47_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(declare-fun |summary_4_function_f__46_47_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (nondet_interface_1_Simple_47_0 error_0 this_0 abi_0 crypto_0 state_0 state_1) true) (and (= error_0 0) (summary_4_function_f__46_47_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2))) (nondet_interface_1_Simple_47_0 error_1 this_0 abi_0 crypto_0 state_0 state_2))))


(declare-fun |block_5_function_f__46_47_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(declare-fun |block_6_f_45_47_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (y_7_0 Int) (y_7_1 Int))
(block_5_function_f__46_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_4_1 y_7_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (y_7_0 Int) (y_7_1 Int))
(=> (and (and (block_5_function_f__46_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_4_1 y_7_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) true) true) true)) true) (block_6_f_45_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_4_1 y_7_1))))


(declare-fun |block_7_return_function_f__46_47_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(declare-fun |block_8_for_header_f_38_47_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(declare-fun |block_9_for_body_f_37_47_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(declare-fun |block_10_f_45_47_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(declare-fun |block_11_for_post_f_18_47_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_0 Int) (expr_11_1 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (y_7_0 Int) (y_7_1 Int))
(=> (and (and (block_6_f_45_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_4_1 y_7_1) (and (= x_4_2 expr_11_1) (and (=> true (and (>= expr_11_1 0) (<= expr_11_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_11_1 expr_10_0) (and (=> true (and (>= expr_9_0 0) (<= expr_9_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_9_0 x_4_1) (and (=> true true) (and (= expr_10_0 10) (and (= y_7_1 0) (and (= x_4_1 0) true)))))))))) true) (block_8_for_header_f_38_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_4_2 y_7_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_0 Int) (expr_11_1 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Bool) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (y_7_0 Int) (y_7_1 Int))
(=> (and (and (block_8_for_header_f_38_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_4_1 y_7_1) (and (= expr_15_1 (< expr_13_0 expr_14_0)) (and (=> true (and (>= expr_14_0 0) (<= expr_14_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_14_0 x_4_1) (and (=> true (and (>= expr_13_0 0) (<= expr_13_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_13_0 y_7_1) true)))))) expr_15_1) (block_9_for_body_f_37_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_4_1 y_7_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_0 Int) (expr_11_1 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Bool) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (y_7_0 Int) (y_7_1 Int))
(=> (and (and (block_8_for_header_f_38_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_4_1 y_7_1) (and (= expr_15_1 (< expr_13_0 expr_14_0)) (and (=> true (and (>= expr_14_0 0) (<= expr_14_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_14_0 x_4_1) (and (=> true (and (>= expr_13_0 0) (<= expr_13_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_13_0 y_7_1) true)))))) (not expr_15_1)) (block_10_f_45_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_4_1 y_7_1))))


(declare-fun |block_12_for_header_f_30_47_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(declare-fun |block_13_for_body_f_29_47_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(declare-fun |block_14_f_45_47_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(declare-fun |block_15_for_post_f_28_47_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_0 Int) (expr_11_1 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Bool) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (y_7_0 Int) (y_7_1 Int))
(=> (and (and (block_9_for_body_f_37_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_4_1 y_7_1) (and (= x_4_2 expr_21_1) (and (=> true (and (>= expr_21_1 0) (<= expr_21_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_21_1 expr_20_0) (and (=> true (and (>= expr_19_0 0) (<= expr_19_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_19_0 x_4_1) (and (=> true true) (and (= expr_20_0 0) true)))))))) true) (block_12_for_header_f_30_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_4_2 y_7_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_0 Int) (expr_11_1 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Bool) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_23_0 Int) (expr_24_0 Int) (expr_25_1 Bool) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (y_7_0 Int) (y_7_1 Int))
(=> (and (and (block_12_for_header_f_30_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_4_1 y_7_1) (and (= expr_25_1 (< expr_23_0 expr_24_0)) (and (=> true true) (and (= expr_24_0 10) (and (=> true (and (>= expr_23_0 0) (<= expr_23_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_23_0 x_4_1) true)))))) expr_25_1) (block_13_for_body_f_29_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_4_1 y_7_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_0 Int) (expr_11_1 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Bool) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_23_0 Int) (expr_24_0 Int) (expr_25_1 Bool) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (y_7_0 Int) (y_7_1 Int))
(=> (and (and (block_12_for_header_f_30_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_4_1 y_7_1) (and (= expr_25_1 (< expr_23_0 expr_24_0)) (and (=> true true) (and (= expr_24_0 10) (and (=> true (and (>= expr_23_0 0) (<= expr_23_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_23_0 x_4_1) true)))))) (not expr_25_1)) (block_14_f_45_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_4_1 y_7_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_0 Int) (expr_11_1 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Bool) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_23_0 Int) (expr_24_0 Int) (expr_25_1 Bool) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (y_7_0 Int) (y_7_1 Int))
(=> (and (and (block_13_for_body_f_29_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_4_1 y_7_1) true) true) (block_15_for_post_f_28_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_4_1 y_7_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_0 Int) (expr_11_1 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Bool) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_23_0 Int) (expr_24_0 Int) (expr_25_1 Bool) (expr_26_0 Int) (expr_27_1 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (y_7_0 Int) (y_7_1 Int))
(=> (and (and (block_15_for_post_f_28_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_4_1 y_7_1) (and (= x_4_2 (+ expr_26_0 1)) (and (=> true (and (>= expr_27_1 0) (<= expr_27_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_27_1 (+ expr_26_0 1)) (and (=> true (and (>= expr_26_0 0) (<= expr_26_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_26_0 x_4_1) true)))))) true) (block_12_for_header_f_30_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_4_2 y_7_1))))


(declare-fun |block_16_function_f__46_47_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_0 Int) (expr_11_1 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Bool) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_23_0 Int) (expr_24_0 Int) (expr_25_1 Bool) (expr_26_0 Int) (expr_27_1 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (y_7_0 Int) (y_7_1 Int))
(=> (and (and (block_14_f_45_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_4_1 y_7_1) (and (= expr_34_1 (= expr_32_0 expr_33_0)) (and (=> true true) (and (= expr_33_0 10) (and (=> true (and (>= expr_32_0 0) (<= expr_32_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_32_0 x_4_1) true)))))) (and (not expr_34_1) (= error_1 1))) (block_16_function_f__46_47_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_4_1 y_7_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_0 Int) (expr_11_1 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Bool) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_23_0 Int) (expr_24_0 Int) (expr_25_1 Bool) (expr_26_0 Int) (expr_27_1 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (y_7_0 Int) (y_7_1 Int))
(=> (block_16_function_f__46_47_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_4_1 y_7_1) (summary_3_function_f__46_47_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_0 Int) (expr_11_1 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Bool) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_23_0 Int) (expr_24_0 Int) (expr_25_1 Bool) (expr_26_0 Int) (expr_27_1 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (y_7_0 Int) (y_7_1 Int))
(=> (and (and (block_14_f_45_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_4_1 y_7_1) (and (= error_1 error_0) (and (= expr_34_1 (= expr_32_0 expr_33_0)) (and (=> true true) (and (= expr_33_0 10) (and (=> true (and (>= expr_32_0 0) (<= expr_32_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_32_0 x_4_1) true))))))) true) (block_11_for_post_f_18_47_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_4_1 y_7_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_0 Int) (expr_11_1 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Bool) (expr_16_0 Int) (expr_17_1 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_23_0 Int) (expr_24_0 Int) (expr_25_1 Bool) (expr_26_0 Int) (expr_27_1 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (y_7_0 Int) (y_7_1 Int) (y_7_2 Int))
(=> (and (and (block_11_for_post_f_18_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_4_1 y_7_1) (and (= y_7_2 (+ expr_16_0 1)) (and (=> true (and (>= expr_17_1 0) (<= expr_17_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_17_1 (+ expr_16_0 1)) (and (=> true (and (>= expr_16_0 0) (<= expr_16_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_16_0 y_7_1) true)))))) true) (block_8_for_header_f_38_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_4_1 y_7_2))))


(declare-fun |block_17_function_f__46_47_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_0 Int) (expr_11_1 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Bool) (expr_16_0 Int) (expr_17_1 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_23_0 Int) (expr_24_0 Int) (expr_25_1 Bool) (expr_26_0 Int) (expr_27_1 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_40_0 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (y_7_0 Int) (y_7_1 Int) (y_7_2 Int))
(=> (and (and (block_10_f_45_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_4_1 y_7_1) (and (= expr_42_1 (= expr_40_0 expr_41_0)) (and (=> true (and (>= expr_41_0 0) (<= expr_41_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_41_0 x_4_1) (and (=> true (and (>= expr_40_0 0) (<= expr_40_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_40_0 y_7_1) true)))))) (and (not expr_42_1) (= error_1 2))) (block_17_function_f__46_47_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_4_1 y_7_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_0 Int) (expr_11_1 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Bool) (expr_16_0 Int) (expr_17_1 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_23_0 Int) (expr_24_0 Int) (expr_25_1 Bool) (expr_26_0 Int) (expr_27_1 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_40_0 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (y_7_0 Int) (y_7_1 Int) (y_7_2 Int))
(=> (block_17_function_f__46_47_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_4_1 y_7_1) (summary_3_function_f__46_47_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_0 Int) (expr_11_1 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Bool) (expr_16_0 Int) (expr_17_1 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_23_0 Int) (expr_24_0 Int) (expr_25_1 Bool) (expr_26_0 Int) (expr_27_1 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_40_0 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (y_7_0 Int) (y_7_1 Int) (y_7_2 Int))
(=> (and (and (block_10_f_45_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_4_1 y_7_1) (and (= error_1 error_0) (and (= expr_42_1 (= expr_40_0 expr_41_0)) (and (=> true (and (>= expr_41_0 0) (<= expr_41_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_41_0 x_4_1) (and (=> true (and (>= expr_40_0 0) (<= expr_40_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_40_0 y_7_1) true))))))) true) (block_7_return_function_f__46_47_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_4_1 y_7_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_0 Int) (expr_11_1 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Bool) (expr_16_0 Int) (expr_17_1 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_23_0 Int) (expr_24_0 Int) (expr_25_1 Bool) (expr_26_0 Int) (expr_27_1 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_40_0 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (y_7_0 Int) (y_7_1 Int) (y_7_2 Int))
(=> (and (and (block_7_return_function_f__46_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_4_1 y_7_1) true) true) (summary_3_function_f__46_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |block_18_function_f__46_47_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_0 Int) (expr_11_1 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Bool) (expr_16_0 Int) (expr_17_1 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_23_0 Int) (expr_24_0 Int) (expr_25_1 Bool) (expr_26_0 Int) (expr_27_1 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_40_0 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (y_7_0 Int) (y_7_1 Int) (y_7_2 Int))
(block_18_function_f__46_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_4_1 y_7_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_0 Int) (expr_11_1 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Bool) (expr_16_0 Int) (expr_17_1 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_23_0 Int) (expr_24_0 Int) (expr_25_1 Bool) (expr_26_0 Int) (expr_27_1 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_40_0 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_9_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (y_7_0 Int) (y_7_1 Int) (y_7_2 Int))
(=> (and (and (block_18_function_f__46_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_4_1 y_7_1) (and (summary_3_function_f__46_47_0 error_1 this_0 abi_0 crypto_0 tx_0 state_2 state_3) (and (= state_2 (|state_type| (store (|balances| state_1) this_0 (+ (select (|balances| state_1) this_0) funds_3_0)))) (and (and (>= (+ (select (|balances| state_1) this_0) funds_3_0) 0) (<= (+ (select (|balances| state_1) this_0) funds_3_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= funds_3_0 (|msg.value| tx_0)) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (and (and (and (and (and (= (|msg.value| tx_0) 0) (= (|msg.sig| tx_0) 638722032)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 0) 38)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 1) 18)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 2) 31)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 3) 240)) (>= (|bytes_tuple_accessor_length| (|msg.data| tx_0)) 4))) (and (and (and (and (= state_1 state_0) (= error_0 0)) true) true) true))))))) true) (summary_4_function_f__46_47_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_3))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_0 Int) (expr_11_1 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Bool) (expr_16_0 Int) (expr_17_1 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_23_0 Int) (expr_24_0 Int) (expr_25_1 Bool) (expr_26_0 Int) (expr_27_1 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_40_0 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_9_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (y_7_0 Int) (y_7_1 Int) (y_7_2 Int))
(=> (and (and (interface_0_Simple_47_0 this_0 abi_0 crypto_0 state_0) true) (and (summary_4_function_f__46_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (= error_0 0))) (interface_0_Simple_47_0 this_0 abi_0 crypto_0 state_1))))


(declare-fun |contract_initializer_19_Simple_47_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(declare-fun |contract_initializer_entry_20_Simple_47_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_0 Int) (expr_11_1 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Bool) (expr_16_0 Int) (expr_17_1 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_23_0 Int) (expr_24_0 Int) (expr_25_1 Bool) (expr_26_0 Int) (expr_27_1 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_40_0 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_9_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (y_7_0 Int) (y_7_1 Int) (y_7_2 Int))
(=> (and (and (= state_1 state_0) (= error_0 0)) true) (contract_initializer_entry_20_Simple_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |contract_initializer_after_init_21_Simple_47_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_0 Int) (expr_11_1 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Bool) (expr_16_0 Int) (expr_17_1 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_23_0 Int) (expr_24_0 Int) (expr_25_1 Bool) (expr_26_0 Int) (expr_27_1 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_40_0 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_9_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (y_7_0 Int) (y_7_1 Int) (y_7_2 Int))
(=> (and (and (contract_initializer_entry_20_Simple_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) true) (contract_initializer_after_init_21_Simple_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_0 Int) (expr_11_1 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Bool) (expr_16_0 Int) (expr_17_1 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_23_0 Int) (expr_24_0 Int) (expr_25_1 Bool) (expr_26_0 Int) (expr_27_1 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_40_0 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_9_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (y_7_0 Int) (y_7_1 Int) (y_7_2 Int))
(=> (and (and (contract_initializer_after_init_21_Simple_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) true) (contract_initializer_19_Simple_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |implicit_constructor_entry_22_Simple_47_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_0 Int) (expr_11_1 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Bool) (expr_16_0 Int) (expr_17_1 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_23_0 Int) (expr_24_0 Int) (expr_25_1 Bool) (expr_26_0 Int) (expr_27_1 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_40_0 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_9_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (y_7_0 Int) (y_7_1 Int) (y_7_2 Int))
(=> (and (and (and (and (= state_1 state_0) (= error_0 0)) true) true) (>= (select (|balances| state_1) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_22_Simple_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_0 Int) (expr_11_1 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Bool) (expr_16_0 Int) (expr_17_1 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_23_0 Int) (expr_24_0 Int) (expr_25_1 Bool) (expr_26_0 Int) (expr_27_1 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_40_0 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_9_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (y_7_0 Int) (y_7_1 Int) (y_7_2 Int))
(=> (and (and (implicit_constructor_entry_22_Simple_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (contract_initializer_19_Simple_47_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2) true)) (> error_1 0)) (summary_constructor_2_Simple_47_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_0 Int) (expr_11_1 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Bool) (expr_16_0 Int) (expr_17_1 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_23_0 Int) (expr_24_0 Int) (expr_25_1 Bool) (expr_26_0 Int) (expr_27_1 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_40_0 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_9_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (y_7_0 Int) (y_7_1 Int) (y_7_2 Int))
(=> (and (and (implicit_constructor_entry_22_Simple_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (= error_1 0) (and (contract_initializer_19_Simple_47_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2) true))) true) (summary_constructor_2_Simple_47_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_0 Int) (expr_11_1 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Bool) (expr_16_0 Int) (expr_17_1 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_23_0 Int) (expr_24_0 Int) (expr_25_1 Bool) (expr_26_0 Int) (expr_27_1 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_40_0 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_9_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (y_7_0 Int) (y_7_1 Int) (y_7_2 Int))
(=> (and (and (summary_constructor_2_Simple_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 0))) (interface_0_Simple_47_0 this_0 abi_0 crypto_0 state_1))))


(declare-fun |error_target_4_0| () Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_0 Int) (expr_11_1 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Bool) (expr_16_0 Int) (expr_17_1 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_23_0 Int) (expr_24_0 Int) (expr_25_1 Bool) (expr_26_0 Int) (expr_27_1 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_40_0 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_9_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (y_7_0 Int) (y_7_1 Int) (y_7_2 Int))
(=> (and (and (interface_0_Simple_47_0 this_0 abi_0 crypto_0 state_0) true) (and (summary_4_function_f__46_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (= error_0 1))) error_target_4_0)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_0 Int) (expr_11_1 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Bool) (expr_16_0 Int) (expr_17_1 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_23_0 Int) (expr_24_0 Int) (expr_25_1 Bool) (expr_26_0 Int) (expr_27_1 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_40_0 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_9_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (y_7_0 Int) (y_7_1 Int) (y_7_2 Int))
(=> error_target_4_0 false)))
(check-sat)