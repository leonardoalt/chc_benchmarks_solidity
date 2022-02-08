(set-logic HORN)

(declare-datatypes ((|state_type| 0)) (((|state_type| (|balances| (Array Int Int))))))
(declare-datatypes ((|bytes_tuple| 0)) (((|bytes_tuple| (|bytes_tuple_accessor_array| (Array Int Int)) (|bytes_tuple_accessor_length| Int)))))
(declare-datatypes ((|tx_type| 0)) (((|tx_type| (|block.basefee| Int) (|block.chainid| Int) (|block.coinbase| Int) (|block.difficulty| Int) (|block.gaslimit| Int) (|block.number| Int) (|block.timestamp| Int) (|blockhash| (Array Int Int)) (|msg.data| |bytes_tuple|) (|msg.sender| Int) (|msg.sig| Int) (|msg.value| Int) (|tx.gasprice| Int) (|tx.origin| Int)))))
(declare-datatypes ((|ecrecover_input_type| 0)) (((|ecrecover_input_type| (|hash| Int) (|v| Int) (|r| Int) (|s| Int)))))
(declare-datatypes ((|crypto_type| 0)) (((|crypto_type| (|ecrecover| (Array |ecrecover_input_type| Int)) (|keccak256| (Array |bytes_tuple| Int)) (|ripemd160| (Array |bytes_tuple| Int)) (|sha256| (Array |bytes_tuple| Int))))))
(declare-datatypes ((|abi_type| 0)) (((|abi_type|))))
(declare-datatypes ((|tuple()| 0)) (((|tuple()|))))
(declare-fun |interface_0_C_54_0| (Int |abi_type| |crypto_type| |state_type| Int ) Bool)
(declare-fun |nondet_interface_1_C_54_0| (Int Int |abi_type| |crypto_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_constructor_2_C_54_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_8_0 Int))
(=> (= error_0 0) (nondet_interface_1_C_54_0 error_0 this_0 abi_0 crypto_0 state_0 x_8_0 state_0 x_8_0))))


(declare-fun |summary_3_function_l__6_54_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |summary_4_function_f__53_54_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |summary_5_function_f__53_54_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (a_10_0 Int) (a_10_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_8_0 Int) (x_8_1 Int) (x_8_2 Int))
(=> (and (and (nondet_interface_1_C_54_0 error_0 this_0 abi_0 crypto_0 state_0 x_8_0 state_1 x_8_1) true) (and (= error_0 0) (summary_5_function_f__53_54_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_8_1 a_10_0 state_2 x_8_2 a_10_1))) (nondet_interface_1_C_54_0 error_1 this_0 abi_0 crypto_0 state_0 x_8_0 state_2 x_8_2))))


(declare-fun |block_6_function_l__6_54_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |block_7_l_5_54_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (a_10_0 Int) (a_10_1 Int) (a_2_0 Int) (a_2_1 Int) (abi_0 |abi_type|) (b1_21_1 Int) (b2_33_1 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_8_0 Int) (x_8_1 Int) (x_8_2 Int))
(block_6_function_l__6_54_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_8_0 a_2_0 state_1 x_8_1 a_2_1)))


(assert
(forall ( (a_10_0 Int) (a_10_1 Int) (a_2_0 Int) (a_2_1 Int) (abi_0 |abi_type|) (b1_21_1 Int) (b2_33_1 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_8_0 Int) (x_8_1 Int) (x_8_2 Int))
(=> (and (and (block_6_function_l__6_54_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_8_0 a_2_0 state_1 x_8_1 a_2_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_8_1 x_8_0))) (and true (= a_2_1 a_2_0))) true)) true) (block_7_l_5_54_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_8_0 a_2_0 state_1 x_8_1 a_2_1))))


(declare-fun |block_8_return_function_l__6_54_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (a_10_0 Int) (a_10_1 Int) (a_2_0 Int) (a_2_1 Int) (abi_0 |abi_type|) (b1_21_1 Int) (b2_33_1 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_8_0 Int) (x_8_1 Int) (x_8_2 Int))
(=> (and (and (block_7_l_5_54_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_8_0 a_2_0 state_1 x_8_1 a_2_1) (and (and (>= a_2_1 0) (<= a_2_1 1461501637330902918203684832716283019655932542975)) true)) true) (block_8_return_function_l__6_54_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_8_0 a_2_0 state_1 x_8_1 a_2_1))))


(assert
(forall ( (a_10_0 Int) (a_10_1 Int) (a_2_0 Int) (a_2_1 Int) (abi_0 |abi_type|) (b1_21_1 Int) (b2_33_1 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_8_0 Int) (x_8_1 Int) (x_8_2 Int))
(=> (and (and (block_8_return_function_l__6_54_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_8_0 a_2_0 state_1 x_8_1 a_2_1) true) true) (summary_3_function_l__6_54_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_8_0 a_2_0 state_1 x_8_1 a_2_1))))


(declare-fun |block_9_function_f__53_54_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int Int Int ) Bool)
(declare-fun |block_10_f_52_54_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int Int Int ) Bool)
(assert
(forall ( (a_10_0 Int) (a_10_1 Int) (a_2_0 Int) (a_2_1 Int) (abi_0 |abi_type|) (b1_21_0 Int) (b1_21_1 Int) (b2_33_0 Int) (b2_33_1 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_8_0 Int) (x_8_1 Int) (x_8_2 Int))
(block_9_function_f__53_54_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_8_0 a_10_0 state_1 x_8_1 a_10_1 b1_21_1 b2_33_1)))


(assert
(forall ( (a_10_0 Int) (a_10_1 Int) (a_2_0 Int) (a_2_1 Int) (abi_0 |abi_type|) (b1_21_0 Int) (b1_21_1 Int) (b2_33_0 Int) (b2_33_1 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_8_0 Int) (x_8_1 Int) (x_8_2 Int))
(=> (and (and (block_9_function_f__53_54_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_8_0 a_10_0 state_1 x_8_1 a_10_1 b1_21_1 b2_33_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_8_1 x_8_0))) (and true (= a_10_1 a_10_0))) true)) true) (block_10_f_52_54_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_8_0 a_10_0 state_1 x_8_1 a_10_1 b1_21_1 b2_33_1))))


(declare-fun |block_11_return_function_f__53_54_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int Int Int ) Bool)
(declare-fun |summary_12_function_l__6_54_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (a_10_0 Int) (a_10_1 Int) (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (b1_21_0 Int) (b1_21_1 Int) (b1_21_2 Int) (b2_33_0 Int) (b2_33_1 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_15_1 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_1 Int) (expr_26_1 Int) (expr_29_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_8_0 Int) (x_8_1 Int) (x_8_2 Int))
(=> (summary_3_function_l__6_54_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_8_0 a_2_0 state_2 x_8_2 a_2_2) (summary_12_function_l__6_54_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_8_0 a_2_0 state_2 x_8_2 a_2_2))))


(assert
(forall ( (a_10_0 Int) (a_10_1 Int) (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (b1_21_0 Int) (b1_21_1 Int) (b1_21_2 Int) (b2_33_0 Int) (b2_33_1 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_15_1 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_1 Int) (expr_26_1 Int) (expr_29_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_8_0 Int) (x_8_1 Int) (x_8_2 Int))
(=> (and (and (block_10_f_52_54_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_8_0 a_10_0 state_1 x_8_1 a_10_1 b1_21_1 b2_33_1) (and (summary_12_function_l__6_54_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_8_1 expr_29_0 state_2 x_8_2 a_2_2) (and (=> true (and (>= expr_29_0 0) (<= expr_29_0 1461501637330902918203684832716283019655932542975))) (and (= expr_29_0 a_10_1) (and (= b1_21_2 expr_26_1) (and (and (>= expr_26_1 0) (<= expr_26_1 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (=> true (and (>= expr_26_1 0) (<= expr_26_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_26_1 (select (|balances| state_1) expr_25_1)) (and (=> true (and (>= expr_25_1 0) (<= expr_25_1 1461501637330902918203684832716283019655932542975))) (and (= expr_25_1 expr_24_0) (and (=> true true) (and (= expr_24_0 this_0) (and (=> true expr_17_1) (and (= expr_17_1 (> expr_15_1 expr_16_0)) (and (=> true true) (and (= expr_16_0 1) (and (=> true (and (>= expr_15_1 0) (<= expr_15_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_15_1 (|msg.value| tx_0)) (and (and (>= a_10_1 0) (<= a_10_1 1461501637330902918203684832716283019655932542975)) (and (= b2_33_1 0) (and (= b1_21_1 0) true))))))))))))))))))))) (> error_1 0)) (summary_4_function_f__53_54_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_8_0 a_10_0 state_2 x_8_2 a_10_1))))


(declare-fun |block_13_function_f__53_54_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int Int Int ) Bool)
(assert
(forall ( (a_10_0 Int) (a_10_1 Int) (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (b1_21_0 Int) (b1_21_1 Int) (b1_21_2 Int) (b2_33_0 Int) (b2_33_1 Int) (b2_33_2 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_15_1 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_1 Int) (expr_26_1 Int) (expr_29_0 Int) (expr_30_1 |tuple()|) (expr_36_0 Int) (expr_37_1 Int) (expr_38_1 Int) (expr_41_0 Int) (expr_42_0 Int) (expr_43_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_8_0 Int) (x_8_1 Int) (x_8_2 Int))
(=> (and (and (block_10_f_52_54_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_8_0 a_10_0 state_1 x_8_1 a_10_1 b1_21_1 b2_33_1) (and (= expr_43_1 (= expr_41_0 expr_42_0)) (and (=> true (and (>= expr_42_0 0) (<= expr_42_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_42_0 b2_33_2) (and (=> true (and (>= expr_41_0 0) (<= expr_41_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_41_0 b1_21_2) (and (= b2_33_2 expr_38_1) (and (and (>= expr_38_1 0) (<= expr_38_1 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (=> true (and (>= expr_38_1 0) (<= expr_38_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_38_1 (select (|balances| state_2) expr_37_1)) (and (=> true (and (>= expr_37_1 0) (<= expr_37_1 1461501637330902918203684832716283019655932542975))) (and (= expr_37_1 expr_36_0) (and (=> true true) (and (= expr_36_0 this_0) (and (= error_1 0) (and (summary_12_function_l__6_54_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_8_1 expr_29_0 state_2 x_8_2 a_2_2) (and (=> true (and (>= expr_29_0 0) (<= expr_29_0 1461501637330902918203684832716283019655932542975))) (and (= expr_29_0 a_10_1) (and (= b1_21_2 expr_26_1) (and (and (>= expr_26_1 0) (<= expr_26_1 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (=> true (and (>= expr_26_1 0) (<= expr_26_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_26_1 (select (|balances| state_1) expr_25_1)) (and (=> true (and (>= expr_25_1 0) (<= expr_25_1 1461501637330902918203684832716283019655932542975))) (and (= expr_25_1 expr_24_0) (and (=> true true) (and (= expr_24_0 this_0) (and (=> true expr_17_1) (and (= expr_17_1 (> expr_15_1 expr_16_0)) (and (=> true true) (and (= expr_16_0 1) (and (=> true (and (>= expr_15_1 0) (<= expr_15_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_15_1 (|msg.value| tx_0)) (and (and (>= a_10_1 0) (<= a_10_1 1461501637330902918203684832716283019655932542975)) (and (= b2_33_1 0) (and (= b1_21_1 0) true))))))))))))))))))))))))))))))))))) (and (not expr_43_1) (= error_2 1))) (block_13_function_f__53_54_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_8_0 a_10_0 state_2 x_8_2 a_10_1 b1_21_2 b2_33_2))))


(assert
(forall ( (a_10_0 Int) (a_10_1 Int) (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (b1_21_0 Int) (b1_21_1 Int) (b1_21_2 Int) (b2_33_0 Int) (b2_33_1 Int) (b2_33_2 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_15_1 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_1 Int) (expr_26_1 Int) (expr_29_0 Int) (expr_30_1 |tuple()|) (expr_36_0 Int) (expr_37_1 Int) (expr_38_1 Int) (expr_41_0 Int) (expr_42_0 Int) (expr_43_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_8_0 Int) (x_8_1 Int) (x_8_2 Int))
(=> (block_13_function_f__53_54_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_8_0 a_10_0 state_2 x_8_2 a_10_1 b1_21_2 b2_33_2) (summary_4_function_f__53_54_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_8_0 a_10_0 state_2 x_8_2 a_10_1))))


(declare-fun |block_14_function_f__53_54_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int Int Int ) Bool)
(assert
(forall ( (a_10_0 Int) (a_10_1 Int) (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (b1_21_0 Int) (b1_21_1 Int) (b1_21_2 Int) (b2_33_0 Int) (b2_33_1 Int) (b2_33_2 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_15_1 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_1 Int) (expr_26_1 Int) (expr_29_0 Int) (expr_30_1 |tuple()|) (expr_36_0 Int) (expr_37_1 Int) (expr_38_1 Int) (expr_41_0 Int) (expr_42_0 Int) (expr_43_1 Bool) (expr_47_0 Int) (expr_48_0 Int) (expr_49_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_8_0 Int) (x_8_1 Int) (x_8_2 Int))
(=> (and (and (block_10_f_52_54_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_8_0 a_10_0 state_1 x_8_1 a_10_1 b1_21_1 b2_33_1) (and (= expr_49_1 (= expr_47_0 expr_48_0)) (and (=> true true) (and (= expr_48_0 0) (and (=> true (and (>= expr_47_0 0) (<= expr_47_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_47_0 x_8_2) (and (= error_2 error_1) (and (= expr_43_1 (= expr_41_0 expr_42_0)) (and (=> true (and (>= expr_42_0 0) (<= expr_42_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_42_0 b2_33_2) (and (=> true (and (>= expr_41_0 0) (<= expr_41_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_41_0 b1_21_2) (and (= b2_33_2 expr_38_1) (and (and (>= expr_38_1 0) (<= expr_38_1 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (=> true (and (>= expr_38_1 0) (<= expr_38_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_38_1 (select (|balances| state_2) expr_37_1)) (and (=> true (and (>= expr_37_1 0) (<= expr_37_1 1461501637330902918203684832716283019655932542975))) (and (= expr_37_1 expr_36_0) (and (=> true true) (and (= expr_36_0 this_0) (and (= error_1 0) (and (summary_12_function_l__6_54_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_8_1 expr_29_0 state_2 x_8_2 a_2_2) (and (=> true (and (>= expr_29_0 0) (<= expr_29_0 1461501637330902918203684832716283019655932542975))) (and (= expr_29_0 a_10_1) (and (= b1_21_2 expr_26_1) (and (and (>= expr_26_1 0) (<= expr_26_1 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (=> true (and (>= expr_26_1 0) (<= expr_26_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_26_1 (select (|balances| state_1) expr_25_1)) (and (=> true (and (>= expr_25_1 0) (<= expr_25_1 1461501637330902918203684832716283019655932542975))) (and (= expr_25_1 expr_24_0) (and (=> true true) (and (= expr_24_0 this_0) (and (=> true expr_17_1) (and (= expr_17_1 (> expr_15_1 expr_16_0)) (and (=> true true) (and (= expr_16_0 1) (and (=> true (and (>= expr_15_1 0) (<= expr_15_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_15_1 (|msg.value| tx_0)) (and (and (>= a_10_1 0) (<= a_10_1 1461501637330902918203684832716283019655932542975)) (and (= b2_33_1 0) (and (= b1_21_1 0) true))))))))))))))))))))))))))))))))))))))))) (and (not expr_49_1) (= error_3 2))) (block_14_function_f__53_54_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 x_8_0 a_10_0 state_2 x_8_2 a_10_1 b1_21_2 b2_33_2))))


(assert
(forall ( (a_10_0 Int) (a_10_1 Int) (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (b1_21_0 Int) (b1_21_1 Int) (b1_21_2 Int) (b2_33_0 Int) (b2_33_1 Int) (b2_33_2 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_15_1 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_1 Int) (expr_26_1 Int) (expr_29_0 Int) (expr_30_1 |tuple()|) (expr_36_0 Int) (expr_37_1 Int) (expr_38_1 Int) (expr_41_0 Int) (expr_42_0 Int) (expr_43_1 Bool) (expr_47_0 Int) (expr_48_0 Int) (expr_49_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_8_0 Int) (x_8_1 Int) (x_8_2 Int))
(=> (block_14_function_f__53_54_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 x_8_0 a_10_0 state_2 x_8_2 a_10_1 b1_21_2 b2_33_2) (summary_4_function_f__53_54_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 x_8_0 a_10_0 state_2 x_8_2 a_10_1))))


(assert
(forall ( (a_10_0 Int) (a_10_1 Int) (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (b1_21_0 Int) (b1_21_1 Int) (b1_21_2 Int) (b2_33_0 Int) (b2_33_1 Int) (b2_33_2 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_15_1 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_1 Int) (expr_26_1 Int) (expr_29_0 Int) (expr_30_1 |tuple()|) (expr_36_0 Int) (expr_37_1 Int) (expr_38_1 Int) (expr_41_0 Int) (expr_42_0 Int) (expr_43_1 Bool) (expr_47_0 Int) (expr_48_0 Int) (expr_49_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_8_0 Int) (x_8_1 Int) (x_8_2 Int))
(=> (and (and (block_10_f_52_54_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_8_0 a_10_0 state_1 x_8_1 a_10_1 b1_21_1 b2_33_1) (and (= error_3 error_2) (and (= expr_49_1 (= expr_47_0 expr_48_0)) (and (=> true true) (and (= expr_48_0 0) (and (=> true (and (>= expr_47_0 0) (<= expr_47_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_47_0 x_8_2) (and (= error_2 error_1) (and (= expr_43_1 (= expr_41_0 expr_42_0)) (and (=> true (and (>= expr_42_0 0) (<= expr_42_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_42_0 b2_33_2) (and (=> true (and (>= expr_41_0 0) (<= expr_41_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_41_0 b1_21_2) (and (= b2_33_2 expr_38_1) (and (and (>= expr_38_1 0) (<= expr_38_1 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (=> true (and (>= expr_38_1 0) (<= expr_38_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_38_1 (select (|balances| state_2) expr_37_1)) (and (=> true (and (>= expr_37_1 0) (<= expr_37_1 1461501637330902918203684832716283019655932542975))) (and (= expr_37_1 expr_36_0) (and (=> true true) (and (= expr_36_0 this_0) (and (= error_1 0) (and (summary_12_function_l__6_54_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_8_1 expr_29_0 state_2 x_8_2 a_2_2) (and (=> true (and (>= expr_29_0 0) (<= expr_29_0 1461501637330902918203684832716283019655932542975))) (and (= expr_29_0 a_10_1) (and (= b1_21_2 expr_26_1) (and (and (>= expr_26_1 0) (<= expr_26_1 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (=> true (and (>= expr_26_1 0) (<= expr_26_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_26_1 (select (|balances| state_1) expr_25_1)) (and (=> true (and (>= expr_25_1 0) (<= expr_25_1 1461501637330902918203684832716283019655932542975))) (and (= expr_25_1 expr_24_0) (and (=> true true) (and (= expr_24_0 this_0) (and (=> true expr_17_1) (and (= expr_17_1 (> expr_15_1 expr_16_0)) (and (=> true true) (and (= expr_16_0 1) (and (=> true (and (>= expr_15_1 0) (<= expr_15_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_15_1 (|msg.value| tx_0)) (and (and (>= a_10_1 0) (<= a_10_1 1461501637330902918203684832716283019655932542975)) (and (= b2_33_1 0) (and (= b1_21_1 0) true)))))))))))))))))))))))))))))))))))))))))) true) (block_11_return_function_f__53_54_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 x_8_0 a_10_0 state_2 x_8_2 a_10_1 b1_21_2 b2_33_2))))


(assert
(forall ( (a_10_0 Int) (a_10_1 Int) (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (b1_21_0 Int) (b1_21_1 Int) (b1_21_2 Int) (b2_33_0 Int) (b2_33_1 Int) (b2_33_2 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_15_1 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_1 Int) (expr_26_1 Int) (expr_29_0 Int) (expr_30_1 |tuple()|) (expr_36_0 Int) (expr_37_1 Int) (expr_38_1 Int) (expr_41_0 Int) (expr_42_0 Int) (expr_43_1 Bool) (expr_47_0 Int) (expr_48_0 Int) (expr_49_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_8_0 Int) (x_8_1 Int) (x_8_2 Int))
(=> (and (and (block_11_return_function_f__53_54_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_8_0 a_10_0 state_1 x_8_1 a_10_1 b1_21_1 b2_33_1) true) true) (summary_4_function_f__53_54_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_8_0 a_10_0 state_1 x_8_1 a_10_1))))


(declare-fun |block_15_function_f__53_54_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int Int Int ) Bool)
(assert
(forall ( (a_10_0 Int) (a_10_1 Int) (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (b1_21_0 Int) (b1_21_1 Int) (b1_21_2 Int) (b2_33_0 Int) (b2_33_1 Int) (b2_33_2 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_15_1 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_1 Int) (expr_26_1 Int) (expr_29_0 Int) (expr_30_1 |tuple()|) (expr_36_0 Int) (expr_37_1 Int) (expr_38_1 Int) (expr_41_0 Int) (expr_42_0 Int) (expr_43_1 Bool) (expr_47_0 Int) (expr_48_0 Int) (expr_49_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_8_0 Int) (x_8_1 Int) (x_8_2 Int))
(block_15_function_f__53_54_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_8_0 a_10_0 state_1 x_8_1 a_10_1 b1_21_1 b2_33_1)))


(assert
(forall ( (a_10_0 Int) (a_10_1 Int) (a_10_2 Int) (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (b1_21_0 Int) (b1_21_1 Int) (b1_21_2 Int) (b2_33_0 Int) (b2_33_1 Int) (b2_33_2 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_15_1 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_1 Int) (expr_26_1 Int) (expr_29_0 Int) (expr_30_1 |tuple()|) (expr_36_0 Int) (expr_37_1 Int) (expr_38_1 Int) (expr_41_0 Int) (expr_42_0 Int) (expr_43_1 Bool) (expr_47_0 Int) (expr_48_0 Int) (expr_49_1 Bool) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_8_0 Int) (x_8_1 Int) (x_8_2 Int))
(=> (and (and (block_15_function_f__53_54_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_8_0 a_10_0 state_1 x_8_1 a_10_1 b1_21_1 b2_33_1) (and (summary_4_function_f__53_54_0 error_1 this_0 abi_0 crypto_0 tx_0 state_2 x_8_1 a_10_1 state_3 x_8_2 a_10_2) (and (= state_2 (|state_type| (store (|balances| state_1) this_0 (+ (select (|balances| state_1) this_0) funds_3_0)))) (and (and (>= (+ (select (|balances| state_1) this_0) funds_3_0) 0) (<= (+ (select (|balances| state_1) this_0) funds_3_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= funds_3_0 (|msg.value| tx_0)) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (and (and (and (and (and true (= (|msg.sig| tx_0) 4234695194)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 0) 252)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 1) 104)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 2) 82)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 3) 26)) (>= (|bytes_tuple_accessor_length| (|msg.data| tx_0)) 4))) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_8_1 x_8_0))) (and true (= a_10_1 a_10_0))) true))))))) true) (summary_5_function_f__53_54_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_8_0 a_10_0 state_3 x_8_2 a_10_2))))


(assert
(forall ( (a_10_0 Int) (a_10_1 Int) (a_10_2 Int) (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (b1_21_0 Int) (b1_21_1 Int) (b1_21_2 Int) (b2_33_0 Int) (b2_33_1 Int) (b2_33_2 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_15_1 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_1 Int) (expr_26_1 Int) (expr_29_0 Int) (expr_30_1 |tuple()|) (expr_36_0 Int) (expr_37_1 Int) (expr_38_1 Int) (expr_41_0 Int) (expr_42_0 Int) (expr_43_1 Bool) (expr_47_0 Int) (expr_48_0 Int) (expr_49_1 Bool) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_8_0 Int) (x_8_1 Int) (x_8_2 Int))
(=> (and (and (interface_0_C_54_0 this_0 abi_0 crypto_0 state_0 x_8_0) true) (and (summary_5_function_f__53_54_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_8_0 a_10_0 state_1 x_8_1 a_10_1) (= error_0 0))) (interface_0_C_54_0 this_0 abi_0 crypto_0 state_1 x_8_1))))


(declare-fun |contract_initializer_16_C_54_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(declare-fun |contract_initializer_entry_17_C_54_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (a_10_0 Int) (a_10_1 Int) (a_10_2 Int) (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (b1_21_0 Int) (b1_21_1 Int) (b1_21_2 Int) (b2_33_0 Int) (b2_33_1 Int) (b2_33_2 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_15_1 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_1 Int) (expr_26_1 Int) (expr_29_0 Int) (expr_30_1 |tuple()|) (expr_36_0 Int) (expr_37_1 Int) (expr_38_1 Int) (expr_41_0 Int) (expr_42_0 Int) (expr_43_1 Bool) (expr_47_0 Int) (expr_48_0 Int) (expr_49_1 Bool) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_8_0 Int) (x_8_1 Int) (x_8_2 Int))
(=> (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_8_1 x_8_0))) (contract_initializer_entry_17_C_54_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_8_0 x_8_1))))


(declare-fun |contract_initializer_after_init_18_C_54_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (a_10_0 Int) (a_10_1 Int) (a_10_2 Int) (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (b1_21_0 Int) (b1_21_1 Int) (b1_21_2 Int) (b2_33_0 Int) (b2_33_1 Int) (b2_33_2 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_15_1 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_1 Int) (expr_26_1 Int) (expr_29_0 Int) (expr_30_1 |tuple()|) (expr_36_0 Int) (expr_37_1 Int) (expr_38_1 Int) (expr_41_0 Int) (expr_42_0 Int) (expr_43_1 Bool) (expr_47_0 Int) (expr_48_0 Int) (expr_49_1 Bool) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_8_0 Int) (x_8_1 Int) (x_8_2 Int))
(=> (and (and (contract_initializer_entry_17_C_54_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_8_0 x_8_1) true) true) (contract_initializer_after_init_18_C_54_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_8_0 x_8_1))))


(assert
(forall ( (a_10_0 Int) (a_10_1 Int) (a_10_2 Int) (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (b1_21_0 Int) (b1_21_1 Int) (b1_21_2 Int) (b2_33_0 Int) (b2_33_1 Int) (b2_33_2 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_15_1 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_1 Int) (expr_26_1 Int) (expr_29_0 Int) (expr_30_1 |tuple()|) (expr_36_0 Int) (expr_37_1 Int) (expr_38_1 Int) (expr_41_0 Int) (expr_42_0 Int) (expr_43_1 Bool) (expr_47_0 Int) (expr_48_0 Int) (expr_49_1 Bool) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_8_0 Int) (x_8_1 Int) (x_8_2 Int))
(=> (and (and (contract_initializer_after_init_18_C_54_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_8_0 x_8_1) true) true) (contract_initializer_16_C_54_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_8_0 x_8_1))))


(declare-fun |implicit_constructor_entry_19_C_54_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (a_10_0 Int) (a_10_1 Int) (a_10_2 Int) (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (b1_21_0 Int) (b1_21_1 Int) (b1_21_2 Int) (b2_33_0 Int) (b2_33_1 Int) (b2_33_2 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_15_1 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_1 Int) (expr_26_1 Int) (expr_29_0 Int) (expr_30_1 |tuple()|) (expr_36_0 Int) (expr_37_1 Int) (expr_38_1 Int) (expr_41_0 Int) (expr_42_0 Int) (expr_43_1 Bool) (expr_47_0 Int) (expr_48_0 Int) (expr_49_1 Bool) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_8_0 Int) (x_8_1 Int) (x_8_2 Int))
(=> (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_8_1 x_8_0))) (and true (= x_8_1 0))) (>= (select (|balances| state_1) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_19_C_54_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_8_0 x_8_1))))


(assert
(forall ( (a_10_0 Int) (a_10_1 Int) (a_10_2 Int) (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (b1_21_0 Int) (b1_21_1 Int) (b1_21_2 Int) (b2_33_0 Int) (b2_33_1 Int) (b2_33_2 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_15_1 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_1 Int) (expr_26_1 Int) (expr_29_0 Int) (expr_30_1 |tuple()|) (expr_36_0 Int) (expr_37_1 Int) (expr_38_1 Int) (expr_41_0 Int) (expr_42_0 Int) (expr_43_1 Bool) (expr_47_0 Int) (expr_48_0 Int) (expr_49_1 Bool) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_8_0 Int) (x_8_1 Int) (x_8_2 Int))
(=> (and (and (implicit_constructor_entry_19_C_54_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_8_0 x_8_1) (and (contract_initializer_16_C_54_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 x_8_1 x_8_2) true)) (> error_1 0)) (summary_constructor_2_C_54_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 x_8_0 x_8_2))))


(assert
(forall ( (a_10_0 Int) (a_10_1 Int) (a_10_2 Int) (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (b1_21_0 Int) (b1_21_1 Int) (b1_21_2 Int) (b2_33_0 Int) (b2_33_1 Int) (b2_33_2 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_15_1 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_1 Int) (expr_26_1 Int) (expr_29_0 Int) (expr_30_1 |tuple()|) (expr_36_0 Int) (expr_37_1 Int) (expr_38_1 Int) (expr_41_0 Int) (expr_42_0 Int) (expr_43_1 Bool) (expr_47_0 Int) (expr_48_0 Int) (expr_49_1 Bool) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_8_0 Int) (x_8_1 Int) (x_8_2 Int))
(=> (and (and (implicit_constructor_entry_19_C_54_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_8_0 x_8_1) (and (= error_1 0) (and (contract_initializer_16_C_54_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 x_8_1 x_8_2) true))) true) (summary_constructor_2_C_54_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 x_8_0 x_8_2))))


(assert
(forall ( (a_10_0 Int) (a_10_1 Int) (a_10_2 Int) (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (b1_21_0 Int) (b1_21_1 Int) (b1_21_2 Int) (b2_33_0 Int) (b2_33_1 Int) (b2_33_2 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_15_1 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_1 Int) (expr_26_1 Int) (expr_29_0 Int) (expr_30_1 |tuple()|) (expr_36_0 Int) (expr_37_1 Int) (expr_38_1 Int) (expr_41_0 Int) (expr_42_0 Int) (expr_43_1 Bool) (expr_47_0 Int) (expr_48_0 Int) (expr_49_1 Bool) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_8_0 Int) (x_8_1 Int) (x_8_2 Int))
(=> (and (and (summary_constructor_2_C_54_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_8_0 x_8_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 0))) (interface_0_C_54_0 this_0 abi_0 crypto_0 state_1 x_8_1))))


(declare-fun |error_target_4_0| () Bool)
(assert
(forall ( (a_10_0 Int) (a_10_1 Int) (a_10_2 Int) (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (b1_21_0 Int) (b1_21_1 Int) (b1_21_2 Int) (b2_33_0 Int) (b2_33_1 Int) (b2_33_2 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_15_1 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_1 Int) (expr_26_1 Int) (expr_29_0 Int) (expr_30_1 |tuple()|) (expr_36_0 Int) (expr_37_1 Int) (expr_38_1 Int) (expr_41_0 Int) (expr_42_0 Int) (expr_43_1 Bool) (expr_47_0 Int) (expr_48_0 Int) (expr_49_1 Bool) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_8_0 Int) (x_8_1 Int) (x_8_2 Int))
(=> (and (and (interface_0_C_54_0 this_0 abi_0 crypto_0 state_0 x_8_0) true) (and (summary_5_function_f__53_54_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_8_0 a_10_0 state_1 x_8_1 a_10_1) (= error_0 1))) error_target_4_0)))


(declare-fun |error_target_5_0| () Bool)
(assert
(forall ( (a_10_0 Int) (a_10_1 Int) (a_10_2 Int) (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (b1_21_0 Int) (b1_21_1 Int) (b1_21_2 Int) (b2_33_0 Int) (b2_33_1 Int) (b2_33_2 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_15_1 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_1 Int) (expr_26_1 Int) (expr_29_0 Int) (expr_30_1 |tuple()|) (expr_36_0 Int) (expr_37_1 Int) (expr_38_1 Int) (expr_41_0 Int) (expr_42_0 Int) (expr_43_1 Bool) (expr_47_0 Int) (expr_48_0 Int) (expr_49_1 Bool) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_8_0 Int) (x_8_1 Int) (x_8_2 Int))
(=> (and (and (interface_0_C_54_0 this_0 abi_0 crypto_0 state_0 x_8_0) true) (and (summary_5_function_f__53_54_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_8_0 a_10_0 state_1 x_8_1 a_10_1) (= error_0 2))) error_target_5_0)))


(assert
(forall ( (a_10_0 Int) (a_10_1 Int) (a_10_2 Int) (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (b1_21_0 Int) (b1_21_1 Int) (b1_21_2 Int) (b2_33_0 Int) (b2_33_1 Int) (b2_33_2 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_15_1 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_1 Int) (expr_26_1 Int) (expr_29_0 Int) (expr_30_1 |tuple()|) (expr_36_0 Int) (expr_37_1 Int) (expr_38_1 Int) (expr_41_0 Int) (expr_42_0 Int) (expr_43_1 Bool) (expr_47_0 Int) (expr_48_0 Int) (expr_49_1 Bool) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_8_0 Int) (x_8_1 Int) (x_8_2 Int))
(=> error_target_5_0 false)))
(check-sat)