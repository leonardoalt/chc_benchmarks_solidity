(set-logic HORN)

(declare-datatypes ((|state_type| 0)) (((|state_type| (|balances| (Array Int Int))))))
(declare-datatypes ((|bytes_tuple| 0)) (((|bytes_tuple| (|bytes_tuple_accessor_array| (Array Int Int)) (|bytes_tuple_accessor_length| Int)))))
(declare-datatypes ((|tx_type| 0)) (((|tx_type| (|block.basefee| Int) (|block.chainid| Int) (|block.coinbase| Int) (|block.difficulty| Int) (|block.gaslimit| Int) (|block.number| Int) (|block.timestamp| Int) (|blockhash| (Array Int Int)) (|msg.data| |bytes_tuple|) (|msg.sender| Int) (|msg.sig| Int) (|msg.value| Int) (|tx.gasprice| Int) (|tx.origin| Int)))))
(declare-datatypes ((|ecrecover_input_type| 0)) (((|ecrecover_input_type| (|hash| Int) (|v| Int) (|r| Int) (|s| Int)))))
(declare-datatypes ((|crypto_type| 0)) (((|crypto_type| (|ecrecover| (Array |ecrecover_input_type| Int)) (|keccak256| (Array |bytes_tuple| Int)) (|ripemd160| (Array |bytes_tuple| Int)) (|sha256| (Array |bytes_tuple| Int))))))
(declare-datatypes ((|abi_type| 0)) (((|abi_type|))))
(declare-fun |interface_0_C_39_0| (Int |abi_type| |crypto_type| |state_type| ) Bool)
(declare-fun |nondet_interface_1_C_39_0| (Int Int |abi_type| |crypto_type| |state_type| |state_type| ) Bool)
(declare-fun |summary_constructor_2_C_39_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (= error_0 0) (nondet_interface_1_C_39_0 error_0 this_0 abi_0 crypto_0 state_0 state_0))))


(declare-fun |summary_3_function_f__38_39_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Bool |state_type| Bool ) Bool)
(declare-fun |summary_4_function_f__38_39_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Bool |state_type| Bool ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (b_2_0 Bool) (b_2_1 Bool) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (nondet_interface_1_C_39_0 error_0 this_0 abi_0 crypto_0 state_0 state_1) true) (and (= error_0 0) (summary_4_function_f__38_39_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 b_2_0 state_2 b_2_1))) (nondet_interface_1_C_39_0 error_1 this_0 abi_0 crypto_0 state_0 state_2))))


(declare-fun |block_5_function_f__38_39_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Bool |state_type| Bool Int ) Bool)
(declare-fun |block_6_f_37_39_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Bool |state_type| Bool Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (b_2_0 Bool) (b_2_1 Bool) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_6_0 Int) (x_6_1 Int))
(block_5_function_f__38_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 b_2_0 state_1 b_2_1 x_6_1)))


(assert
(forall ( (abi_0 |abi_type|) (b_2_0 Bool) (b_2_1 Bool) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_6_0 Int) (x_6_1 Int))
(=> (and (and (block_5_function_f__38_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 b_2_0 state_1 b_2_1 x_6_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) true) (and true (= b_2_1 b_2_0))) true)) true) (block_6_f_37_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 b_2_0 state_1 b_2_1 x_6_1))))


(declare-fun |block_7_return_function_f__38_39_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Bool |state_type| Bool Int ) Bool)
(declare-fun |block_8_if_header_f_13_39_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Bool |state_type| Bool Int ) Bool)
(declare-fun |block_9_if_true_f_12_39_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Bool |state_type| Bool Int ) Bool)
(declare-fun |block_10_f_37_39_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Bool |state_type| Bool Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (b_2_0 Bool) (b_2_1 Bool) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_6_0 Int) (x_6_1 Int))
(=> (and (and (block_6_f_37_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 b_2_0 state_1 b_2_1 x_6_1) (and true (and (= x_6_1 0) true))) true) (block_8_if_header_f_13_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 b_2_0 state_1 b_2_1 x_6_1))))


(assert
(forall ( (abi_0 |abi_type|) (b_2_0 Bool) (b_2_1 Bool) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_8_0 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_6_0 Int) (x_6_1 Int))
(=> (and (and (block_8_if_header_f_13_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 b_2_0 state_1 b_2_1 x_6_1) (and (= expr_8_0 b_2_1) true)) expr_8_0) (block_9_if_true_f_12_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 b_2_0 state_1 b_2_1 x_6_1))))


(assert
(forall ( (abi_0 |abi_type|) (b_2_0 Bool) (b_2_1 Bool) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_8_0 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_6_0 Int) (x_6_1 Int))
(=> (and (and (block_8_if_header_f_13_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 b_2_0 state_1 b_2_1 x_6_1) (and (= expr_8_0 b_2_1) true)) (not expr_8_0)) (block_10_f_37_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 b_2_0 state_1 b_2_1 x_6_1))))


(assert
(forall ( (abi_0 |abi_type|) (b_2_0 Bool) (b_2_1 Bool) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Int) (expr_11_1 Int) (expr_8_0 Bool) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_6_0 Int) (x_6_1 Int) (x_6_2 Int))
(=> (and (and (block_9_if_true_f_12_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 b_2_0 state_1 b_2_1 x_6_1) (and (= x_6_2 (+ expr_9_0 1)) (and (=> true (and (>= expr_11_1 0) (<= expr_11_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_11_1 (+ expr_9_0 1)) (and (=> true (and (>= expr_10_1 0) (<= expr_10_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_10_1 expr_9_0) (and (=> true (and (>= expr_9_0 0) (<= expr_9_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_9_0 x_6_1) true)))))))) true) (block_10_f_37_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 b_2_0 state_1 b_2_1 x_6_2))))


(declare-fun |block_11_if_header_f_19_39_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Bool |state_type| Bool Int ) Bool)
(declare-fun |block_12_if_true_f_18_39_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Bool |state_type| Bool Int ) Bool)
(declare-fun |block_13_f_37_39_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Bool |state_type| Bool Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (b_2_0 Bool) (b_2_1 Bool) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Int) (expr_11_1 Int) (expr_8_0 Bool) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_6_0 Int) (x_6_1 Int) (x_6_2 Int))
(=> (and (and (block_10_f_37_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 b_2_0 state_1 b_2_1 x_6_1) true) true) (block_11_if_header_f_19_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 b_2_0 state_1 b_2_1 x_6_1))))


(assert
(forall ( (abi_0 |abi_type|) (b_2_0 Bool) (b_2_1 Bool) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Int) (expr_11_1 Int) (expr_14_0 Bool) (expr_8_0 Bool) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_6_0 Int) (x_6_1 Int) (x_6_2 Int))
(=> (and (and (block_11_if_header_f_19_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 b_2_0 state_1 b_2_1 x_6_1) (and (= expr_14_0 b_2_1) true)) expr_14_0) (block_12_if_true_f_18_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 b_2_0 state_1 b_2_1 x_6_1))))


(assert
(forall ( (abi_0 |abi_type|) (b_2_0 Bool) (b_2_1 Bool) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Int) (expr_11_1 Int) (expr_14_0 Bool) (expr_8_0 Bool) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_6_0 Int) (x_6_1 Int) (x_6_2 Int))
(=> (and (and (block_11_if_header_f_19_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 b_2_0 state_1 b_2_1 x_6_1) (and (= expr_14_0 b_2_1) true)) (not expr_14_0)) (block_13_f_37_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 b_2_0 state_1 b_2_1 x_6_1))))


(assert
(forall ( (abi_0 |abi_type|) (b_2_0 Bool) (b_2_1 Bool) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Int) (expr_11_1 Int) (expr_14_0 Bool) (expr_15_0 Int) (expr_16_1 Int) (expr_17_1 Int) (expr_8_0 Bool) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_6_0 Int) (x_6_1 Int) (x_6_2 Int))
(=> (and (and (block_12_if_true_f_18_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 b_2_0 state_1 b_2_1 x_6_1) (and (= x_6_2 (- expr_15_0 1)) (and (=> true (and (>= expr_17_1 0) (<= expr_17_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_17_1 (- expr_15_0 1)) (and (=> true (and (>= expr_16_1 0) (<= expr_16_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_16_1 expr_15_0) (and (=> true (and (>= expr_15_0 0) (<= expr_15_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_15_0 x_6_1) true)))))))) true) (block_13_f_37_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 b_2_0 state_1 b_2_1 x_6_2))))


(declare-fun |block_14_if_header_f_25_39_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Bool |state_type| Bool Int ) Bool)
(declare-fun |block_15_if_true_f_24_39_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Bool |state_type| Bool Int ) Bool)
(declare-fun |block_16_f_37_39_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Bool |state_type| Bool Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (b_2_0 Bool) (b_2_1 Bool) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Int) (expr_11_1 Int) (expr_14_0 Bool) (expr_15_0 Int) (expr_16_1 Int) (expr_17_1 Int) (expr_8_0 Bool) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_6_0 Int) (x_6_1 Int) (x_6_2 Int))
(=> (and (and (block_13_f_37_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 b_2_0 state_1 b_2_1 x_6_1) true) true) (block_14_if_header_f_25_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 b_2_0 state_1 b_2_1 x_6_1))))


(assert
(forall ( (abi_0 |abi_type|) (b_2_0 Bool) (b_2_1 Bool) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Int) (expr_11_1 Int) (expr_14_0 Bool) (expr_15_0 Int) (expr_16_1 Int) (expr_17_1 Int) (expr_20_0 Bool) (expr_8_0 Bool) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_6_0 Int) (x_6_1 Int) (x_6_2 Int))
(=> (and (and (block_14_if_header_f_25_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 b_2_0 state_1 b_2_1 x_6_1) (and (= expr_20_0 b_2_1) true)) expr_20_0) (block_15_if_true_f_24_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 b_2_0 state_1 b_2_1 x_6_1))))


(assert
(forall ( (abi_0 |abi_type|) (b_2_0 Bool) (b_2_1 Bool) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Int) (expr_11_1 Int) (expr_14_0 Bool) (expr_15_0 Int) (expr_16_1 Int) (expr_17_1 Int) (expr_20_0 Bool) (expr_8_0 Bool) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_6_0 Int) (x_6_1 Int) (x_6_2 Int))
(=> (and (and (block_14_if_header_f_25_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 b_2_0 state_1 b_2_1 x_6_1) (and (= expr_20_0 b_2_1) true)) (not expr_20_0)) (block_16_f_37_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 b_2_0 state_1 b_2_1 x_6_1))))


(assert
(forall ( (abi_0 |abi_type|) (b_2_0 Bool) (b_2_1 Bool) (b_2_2 Bool) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Int) (expr_11_1 Int) (expr_14_0 Bool) (expr_15_0 Int) (expr_16_1 Int) (expr_17_1 Int) (expr_20_0 Bool) (expr_21_0 Bool) (expr_22_1 Bool) (expr_8_0 Bool) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_6_0 Int) (x_6_1 Int) (x_6_2 Int))
(=> (and (and (block_15_if_true_f_24_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 b_2_0 state_1 b_2_1 x_6_1) (and (= b_2_2 false) (and (= expr_22_1 expr_21_0) (and (= expr_21_0 b_2_1) true)))) true) (block_16_f_37_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 b_2_0 state_1 b_2_2 x_6_1))))


(declare-fun |block_17_function_f__38_39_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Bool |state_type| Bool Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (b_2_0 Bool) (b_2_1 Bool) (b_2_2 Bool) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Int) (expr_11_1 Int) (expr_14_0 Bool) (expr_15_0 Int) (expr_16_1 Int) (expr_17_1 Int) (expr_20_0 Bool) (expr_21_0 Bool) (expr_22_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_8_0 Bool) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_6_0 Int) (x_6_1 Int) (x_6_2 Int))
(=> (and (and (block_16_f_37_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 b_2_0 state_1 b_2_1 x_6_1) (and (= expr_29_1 (= expr_27_0 expr_28_0)) (and (=> true true) (and (= expr_28_0 0) (and (=> true (and (>= expr_27_0 0) (<= expr_27_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_27_0 x_6_1) true)))))) (and (not expr_29_1) (= error_1 1))) (block_17_function_f__38_39_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 b_2_0 state_1 b_2_1 x_6_1))))


(assert
(forall ( (abi_0 |abi_type|) (b_2_0 Bool) (b_2_1 Bool) (b_2_2 Bool) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Int) (expr_11_1 Int) (expr_14_0 Bool) (expr_15_0 Int) (expr_16_1 Int) (expr_17_1 Int) (expr_20_0 Bool) (expr_21_0 Bool) (expr_22_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_8_0 Bool) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_6_0 Int) (x_6_1 Int) (x_6_2 Int))
(=> (block_17_function_f__38_39_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 b_2_0 state_1 b_2_1 x_6_1) (summary_3_function_f__38_39_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 b_2_0 state_1 b_2_1))))


(declare-fun |block_18_function_f__38_39_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Bool |state_type| Bool Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (b_2_0 Bool) (b_2_1 Bool) (b_2_2 Bool) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_1 Int) (expr_11_1 Int) (expr_14_0 Bool) (expr_15_0 Int) (expr_16_1 Int) (expr_17_1 Int) (expr_20_0 Bool) (expr_21_0 Bool) (expr_22_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_33_0 Bool) (expr_34_1 Bool) (expr_8_0 Bool) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_6_0 Int) (x_6_1 Int) (x_6_2 Int))
(=> (and (and (block_16_f_37_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 b_2_0 state_1 b_2_1 x_6_1) (and (= expr_34_1 (not expr_33_0)) (and (= expr_33_0 b_2_1) (and (= error_1 error_0) (and (= expr_29_1 (= expr_27_0 expr_28_0)) (and (=> true true) (and (= expr_28_0 0) (and (=> true (and (>= expr_27_0 0) (<= expr_27_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_27_0 x_6_1) true))))))))) (and (not expr_34_1) (= error_2 2))) (block_18_function_f__38_39_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 b_2_0 state_1 b_2_1 x_6_1))))


(assert
(forall ( (abi_0 |abi_type|) (b_2_0 Bool) (b_2_1 Bool) (b_2_2 Bool) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_1 Int) (expr_11_1 Int) (expr_14_0 Bool) (expr_15_0 Int) (expr_16_1 Int) (expr_17_1 Int) (expr_20_0 Bool) (expr_21_0 Bool) (expr_22_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_33_0 Bool) (expr_34_1 Bool) (expr_8_0 Bool) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_6_0 Int) (x_6_1 Int) (x_6_2 Int))
(=> (block_18_function_f__38_39_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 b_2_0 state_1 b_2_1 x_6_1) (summary_3_function_f__38_39_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 b_2_0 state_1 b_2_1))))


(assert
(forall ( (abi_0 |abi_type|) (b_2_0 Bool) (b_2_1 Bool) (b_2_2 Bool) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_1 Int) (expr_11_1 Int) (expr_14_0 Bool) (expr_15_0 Int) (expr_16_1 Int) (expr_17_1 Int) (expr_20_0 Bool) (expr_21_0 Bool) (expr_22_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_33_0 Bool) (expr_34_1 Bool) (expr_8_0 Bool) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_6_0 Int) (x_6_1 Int) (x_6_2 Int))
(=> (and (and (block_16_f_37_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 b_2_0 state_1 b_2_1 x_6_1) (and (= error_2 error_1) (and (= expr_34_1 (not expr_33_0)) (and (= expr_33_0 b_2_1) (and (= error_1 error_0) (and (= expr_29_1 (= expr_27_0 expr_28_0)) (and (=> true true) (and (= expr_28_0 0) (and (=> true (and (>= expr_27_0 0) (<= expr_27_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_27_0 x_6_1) true)))))))))) true) (block_7_return_function_f__38_39_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 b_2_0 state_1 b_2_1 x_6_1))))


(assert
(forall ( (abi_0 |abi_type|) (b_2_0 Bool) (b_2_1 Bool) (b_2_2 Bool) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_1 Int) (expr_11_1 Int) (expr_14_0 Bool) (expr_15_0 Int) (expr_16_1 Int) (expr_17_1 Int) (expr_20_0 Bool) (expr_21_0 Bool) (expr_22_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_33_0 Bool) (expr_34_1 Bool) (expr_8_0 Bool) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_6_0 Int) (x_6_1 Int) (x_6_2 Int))
(=> (and (and (block_7_return_function_f__38_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 b_2_0 state_1 b_2_1 x_6_1) true) true) (summary_3_function_f__38_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 b_2_0 state_1 b_2_1))))


(declare-fun |block_19_function_f__38_39_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Bool |state_type| Bool Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (b_2_0 Bool) (b_2_1 Bool) (b_2_2 Bool) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_1 Int) (expr_11_1 Int) (expr_14_0 Bool) (expr_15_0 Int) (expr_16_1 Int) (expr_17_1 Int) (expr_20_0 Bool) (expr_21_0 Bool) (expr_22_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_33_0 Bool) (expr_34_1 Bool) (expr_8_0 Bool) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_6_0 Int) (x_6_1 Int) (x_6_2 Int))
(block_19_function_f__38_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 b_2_0 state_1 b_2_1 x_6_1)))


(assert
(forall ( (abi_0 |abi_type|) (b_2_0 Bool) (b_2_1 Bool) (b_2_2 Bool) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_1 Int) (expr_11_1 Int) (expr_14_0 Bool) (expr_15_0 Int) (expr_16_1 Int) (expr_17_1 Int) (expr_20_0 Bool) (expr_21_0 Bool) (expr_22_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_33_0 Bool) (expr_34_1 Bool) (expr_8_0 Bool) (expr_9_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_6_0 Int) (x_6_1 Int) (x_6_2 Int))
(=> (and (and (block_19_function_f__38_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 b_2_0 state_1 b_2_1 x_6_1) (and (summary_3_function_f__38_39_0 error_1 this_0 abi_0 crypto_0 tx_0 state_2 b_2_1 state_3 b_2_2) (and (= state_2 (|state_type| (store (|balances| state_1) this_0 (+ (select (|balances| state_1) this_0) funds_3_0)))) (and (and (>= (+ (select (|balances| state_1) this_0) funds_3_0) 0) (<= (+ (select (|balances| state_1) this_0) funds_3_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= funds_3_0 (|msg.value| tx_0)) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (and (and (and (and (and (= (|msg.value| tx_0) 0) (= (|msg.sig| tx_0) 2562959041)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 0) 152)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 1) 195)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 2) 166)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 3) 193)) (>= (|bytes_tuple_accessor_length| (|msg.data| tx_0)) 4))) (and (and (and (and (= state_1 state_0) (= error_0 0)) true) (and true (= b_2_1 b_2_0))) true))))))) true) (summary_4_function_f__38_39_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 b_2_0 state_3 b_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (b_2_0 Bool) (b_2_1 Bool) (b_2_2 Bool) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_1 Int) (expr_11_1 Int) (expr_14_0 Bool) (expr_15_0 Int) (expr_16_1 Int) (expr_17_1 Int) (expr_20_0 Bool) (expr_21_0 Bool) (expr_22_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_33_0 Bool) (expr_34_1 Bool) (expr_8_0 Bool) (expr_9_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_6_0 Int) (x_6_1 Int) (x_6_2 Int))
(=> (and (and (interface_0_C_39_0 this_0 abi_0 crypto_0 state_0) true) (and (summary_4_function_f__38_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 b_2_0 state_1 b_2_1) (= error_0 0))) (interface_0_C_39_0 this_0 abi_0 crypto_0 state_1))))


(declare-fun |contract_initializer_20_C_39_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(declare-fun |contract_initializer_entry_21_C_39_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (b_2_0 Bool) (b_2_1 Bool) (b_2_2 Bool) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_1 Int) (expr_11_1 Int) (expr_14_0 Bool) (expr_15_0 Int) (expr_16_1 Int) (expr_17_1 Int) (expr_20_0 Bool) (expr_21_0 Bool) (expr_22_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_33_0 Bool) (expr_34_1 Bool) (expr_8_0 Bool) (expr_9_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_6_0 Int) (x_6_1 Int) (x_6_2 Int))
(=> (and (and (= state_1 state_0) (= error_0 0)) true) (contract_initializer_entry_21_C_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |contract_initializer_after_init_22_C_39_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (b_2_0 Bool) (b_2_1 Bool) (b_2_2 Bool) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_1 Int) (expr_11_1 Int) (expr_14_0 Bool) (expr_15_0 Int) (expr_16_1 Int) (expr_17_1 Int) (expr_20_0 Bool) (expr_21_0 Bool) (expr_22_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_33_0 Bool) (expr_34_1 Bool) (expr_8_0 Bool) (expr_9_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_6_0 Int) (x_6_1 Int) (x_6_2 Int))
(=> (and (and (contract_initializer_entry_21_C_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) true) (contract_initializer_after_init_22_C_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (abi_0 |abi_type|) (b_2_0 Bool) (b_2_1 Bool) (b_2_2 Bool) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_1 Int) (expr_11_1 Int) (expr_14_0 Bool) (expr_15_0 Int) (expr_16_1 Int) (expr_17_1 Int) (expr_20_0 Bool) (expr_21_0 Bool) (expr_22_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_33_0 Bool) (expr_34_1 Bool) (expr_8_0 Bool) (expr_9_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_6_0 Int) (x_6_1 Int) (x_6_2 Int))
(=> (and (and (contract_initializer_after_init_22_C_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) true) (contract_initializer_20_C_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |implicit_constructor_entry_23_C_39_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (b_2_0 Bool) (b_2_1 Bool) (b_2_2 Bool) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_1 Int) (expr_11_1 Int) (expr_14_0 Bool) (expr_15_0 Int) (expr_16_1 Int) (expr_17_1 Int) (expr_20_0 Bool) (expr_21_0 Bool) (expr_22_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_33_0 Bool) (expr_34_1 Bool) (expr_8_0 Bool) (expr_9_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_6_0 Int) (x_6_1 Int) (x_6_2 Int))
(=> (and (and (and (and (= state_1 state_0) (= error_0 0)) true) true) (>= (select (|balances| state_1) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_23_C_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (abi_0 |abi_type|) (b_2_0 Bool) (b_2_1 Bool) (b_2_2 Bool) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_1 Int) (expr_11_1 Int) (expr_14_0 Bool) (expr_15_0 Int) (expr_16_1 Int) (expr_17_1 Int) (expr_20_0 Bool) (expr_21_0 Bool) (expr_22_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_33_0 Bool) (expr_34_1 Bool) (expr_8_0 Bool) (expr_9_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_6_0 Int) (x_6_1 Int) (x_6_2 Int))
(=> (and (and (implicit_constructor_entry_23_C_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (contract_initializer_20_C_39_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2) true)) (> error_1 0)) (summary_constructor_2_C_39_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2))))


(assert
(forall ( (abi_0 |abi_type|) (b_2_0 Bool) (b_2_1 Bool) (b_2_2 Bool) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_1 Int) (expr_11_1 Int) (expr_14_0 Bool) (expr_15_0 Int) (expr_16_1 Int) (expr_17_1 Int) (expr_20_0 Bool) (expr_21_0 Bool) (expr_22_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_33_0 Bool) (expr_34_1 Bool) (expr_8_0 Bool) (expr_9_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_6_0 Int) (x_6_1 Int) (x_6_2 Int))
(=> (and (and (implicit_constructor_entry_23_C_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (= error_1 0) (and (contract_initializer_20_C_39_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2) true))) true) (summary_constructor_2_C_39_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2))))


(assert
(forall ( (abi_0 |abi_type|) (b_2_0 Bool) (b_2_1 Bool) (b_2_2 Bool) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_1 Int) (expr_11_1 Int) (expr_14_0 Bool) (expr_15_0 Int) (expr_16_1 Int) (expr_17_1 Int) (expr_20_0 Bool) (expr_21_0 Bool) (expr_22_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_33_0 Bool) (expr_34_1 Bool) (expr_8_0 Bool) (expr_9_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_6_0 Int) (x_6_1 Int) (x_6_2 Int))
(=> (and (and (summary_constructor_2_C_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 0))) (interface_0_C_39_0 this_0 abi_0 crypto_0 state_1))))


(declare-fun |error_target_4_0| () Bool)
(assert
(forall ( (abi_0 |abi_type|) (b_2_0 Bool) (b_2_1 Bool) (b_2_2 Bool) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_1 Int) (expr_11_1 Int) (expr_14_0 Bool) (expr_15_0 Int) (expr_16_1 Int) (expr_17_1 Int) (expr_20_0 Bool) (expr_21_0 Bool) (expr_22_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_33_0 Bool) (expr_34_1 Bool) (expr_8_0 Bool) (expr_9_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_6_0 Int) (x_6_1 Int) (x_6_2 Int))
(=> (and (and (interface_0_C_39_0 this_0 abi_0 crypto_0 state_0) true) (and (summary_4_function_f__38_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 b_2_0 state_1 b_2_1) (= error_0 1))) error_target_4_0)))


(declare-fun |error_target_5_0| () Bool)
(assert
(forall ( (abi_0 |abi_type|) (b_2_0 Bool) (b_2_1 Bool) (b_2_2 Bool) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_1 Int) (expr_11_1 Int) (expr_14_0 Bool) (expr_15_0 Int) (expr_16_1 Int) (expr_17_1 Int) (expr_20_0 Bool) (expr_21_0 Bool) (expr_22_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_33_0 Bool) (expr_34_1 Bool) (expr_8_0 Bool) (expr_9_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_6_0 Int) (x_6_1 Int) (x_6_2 Int))
(=> (and (and (interface_0_C_39_0 this_0 abi_0 crypto_0 state_0) true) (and (summary_4_function_f__38_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 b_2_0 state_1 b_2_1) (= error_0 2))) error_target_5_0)))


(assert
(forall ( (abi_0 |abi_type|) (b_2_0 Bool) (b_2_1 Bool) (b_2_2 Bool) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_1 Int) (expr_11_1 Int) (expr_14_0 Bool) (expr_15_0 Int) (expr_16_1 Int) (expr_17_1 Int) (expr_20_0 Bool) (expr_21_0 Bool) (expr_22_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_33_0 Bool) (expr_34_1 Bool) (expr_8_0 Bool) (expr_9_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_6_0 Int) (x_6_1 Int) (x_6_2 Int))
(=> error_target_5_0 false)))
(check-sat)