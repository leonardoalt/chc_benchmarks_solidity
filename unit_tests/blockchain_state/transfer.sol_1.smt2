(set-logic HORN)

(declare-datatypes ((|state_type| 0)) (((|state_type| (|balances| (Array Int Int))))))
(declare-datatypes ((|bytes_tuple| 0)) (((|bytes_tuple| (|bytes_tuple_accessor_array| (Array Int Int)) (|bytes_tuple_accessor_length| Int)))))
(declare-datatypes ((|tx_type| 0)) (((|tx_type| (|block.basefee| Int) (|block.chainid| Int) (|block.coinbase| Int) (|block.difficulty| Int) (|block.gaslimit| Int) (|block.number| Int) (|block.timestamp| Int) (|blockhash| (Array Int Int)) (|msg.data| |bytes_tuple|) (|msg.sender| Int) (|msg.sig| Int) (|msg.value| Int) (|tx.gasprice| Int) (|tx.origin| Int)))))
(declare-datatypes ((|ecrecover_input_type| 0)) (((|ecrecover_input_type| (|hash| Int) (|v| Int) (|r| Int) (|s| Int)))))
(declare-datatypes ((|crypto_type| 0)) (((|crypto_type| (|ecrecover| (Array |ecrecover_input_type| Int)) (|keccak256| (Array |bytes_tuple| Int)) (|ripemd160| (Array |bytes_tuple| Int)) (|sha256| (Array |bytes_tuple| Int))))))
(declare-datatypes ((|abi_type| 0)) (((|abi_type|))))
(declare-fun |interface_0_C_43_0| (Int |abi_type| |crypto_type| |state_type| ) Bool)
(declare-fun |nondet_interface_1_C_43_0| (Int Int |abi_type| |crypto_type| |state_type| |state_type| ) Bool)
(declare-fun |summary_constructor_2_C_43_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (= error_0 0) (nondet_interface_1_C_43_0 error_0 this_0 abi_0 crypto_0 state_0 state_0))))


(declare-fun |summary_3_function_f__42_43_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_4_function_f__42_43_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (nondet_interface_1_C_43_0 error_0 this_0 abi_0 crypto_0 state_0 state_1) true) (and (= error_0 0) (summary_4_function_f__42_43_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_0 state_2 a_2_1))) (nondet_interface_1_C_43_0 error_1 this_0 abi_0 crypto_0 state_0 state_2))))


(declare-fun |block_5_function_f__42_43_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_6_f_41_43_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(block_5_function_f__42_43_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1)))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_5_function_f__42_43_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) true) (and true (= a_2_1 a_2_0))) true)) true) (block_6_f_41_43_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(declare-fun |block_7_return_function_f__42_43_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_8_function_f__42_43_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Int) (expr_11_0 Int) (expr_12_1 Bool) (expr_15_0 Int) (expr_18_0 Int) (expr_24_0 Int) (expr_25_1 Int) (expr_26_1 Int) (expr_27_0 Int) (expr_28_1 Bool) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_6_f_41_43_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (= expr_28_1 (> expr_26_1 expr_27_0)) (and (=> true true) (and (= expr_27_0 100) (and (and (>= expr_26_1 0) (<= expr_26_1 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (=> true (and (>= expr_26_1 0) (<= expr_26_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_26_1 (select (|balances| state_4) expr_25_1)) (and (=> true (and (>= expr_25_1 0) (<= expr_25_1 1461501637330902918203684832716283019655932542975))) (and (= expr_25_1 expr_24_0) (and (=> true true) (and (= expr_24_0 this_0) (and (= state_4 (ite (= this_0 expr_15_0) state_1 state_3)) (and (= state_3 (|state_type| (store (|balances| state_2) expr_15_0 (+ (select (|balances| state_2) expr_15_0) expr_18_0)))) (and (= state_2 (|state_type| (store (|balances| state_1) this_0 (+ (select (|balances| state_1) this_0) (- 0 expr_18_0))))) (and (and (>= (select (|balances| state_1) this_0) 0) (<= (select (|balances| state_1) this_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (=> true true) (and (= expr_18_0 666) (and (=> true (and (>= expr_15_0 0) (<= expr_15_0 1461501637330902918203684832716283019655932542975))) (and (= expr_15_0 a_2_1) (and (=> true expr_12_1) (and (= expr_12_1 (> expr_10_1 expr_11_0)) (and (=> true true) (and (= expr_11_0 1000) (and (and (>= expr_10_1 0) (<= expr_10_1 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (=> true (and (>= expr_10_1 0) (<= expr_10_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_10_1 (select (|balances| state_1) expr_9_1)) (and (=> true (and (>= expr_9_1 0) (<= expr_9_1 1461501637330902918203684832716283019655932542975))) (and (= expr_9_1 expr_8_0) (and (=> true true) (and (= expr_8_0 this_0) (and (and (>= a_2_1 0) (<= a_2_1 1461501637330902918203684832716283019655932542975)) true))))))))))))))))))))))))))))))) (and (not expr_28_1) (= error_1 1))) (block_8_function_f__42_43_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_4 a_2_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Int) (expr_11_0 Int) (expr_12_1 Bool) (expr_15_0 Int) (expr_18_0 Int) (expr_24_0 Int) (expr_25_1 Int) (expr_26_1 Int) (expr_27_0 Int) (expr_28_1 Bool) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (block_8_function_f__42_43_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_4 a_2_1) (summary_3_function_f__42_43_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_4 a_2_1))))


(declare-fun |block_9_function_f__42_43_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_1 Int) (expr_11_0 Int) (expr_12_1 Bool) (expr_15_0 Int) (expr_18_0 Int) (expr_24_0 Int) (expr_25_1 Int) (expr_26_1 Int) (expr_27_0 Int) (expr_28_1 Bool) (expr_34_0 Int) (expr_35_1 Int) (expr_36_1 Int) (expr_37_0 Int) (expr_38_1 Bool) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_6_f_41_43_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (= expr_38_1 (> expr_36_1 expr_37_0)) (and (=> true true) (and (= expr_37_0 500) (and (and (>= expr_36_1 0) (<= expr_36_1 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (=> true (and (>= expr_36_1 0) (<= expr_36_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_36_1 (select (|balances| state_4) expr_35_1)) (and (=> true (and (>= expr_35_1 0) (<= expr_35_1 1461501637330902918203684832716283019655932542975))) (and (= expr_35_1 expr_34_0) (and (=> true true) (and (= expr_34_0 this_0) (and (= error_1 error_0) (and (= expr_28_1 (> expr_26_1 expr_27_0)) (and (=> true true) (and (= expr_27_0 100) (and (and (>= expr_26_1 0) (<= expr_26_1 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (=> true (and (>= expr_26_1 0) (<= expr_26_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_26_1 (select (|balances| state_4) expr_25_1)) (and (=> true (and (>= expr_25_1 0) (<= expr_25_1 1461501637330902918203684832716283019655932542975))) (and (= expr_25_1 expr_24_0) (and (=> true true) (and (= expr_24_0 this_0) (and (= state_4 (ite (= this_0 expr_15_0) state_1 state_3)) (and (= state_3 (|state_type| (store (|balances| state_2) expr_15_0 (+ (select (|balances| state_2) expr_15_0) expr_18_0)))) (and (= state_2 (|state_type| (store (|balances| state_1) this_0 (+ (select (|balances| state_1) this_0) (- 0 expr_18_0))))) (and (and (>= (select (|balances| state_1) this_0) 0) (<= (select (|balances| state_1) this_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (=> true true) (and (= expr_18_0 666) (and (=> true (and (>= expr_15_0 0) (<= expr_15_0 1461501637330902918203684832716283019655932542975))) (and (= expr_15_0 a_2_1) (and (=> true expr_12_1) (and (= expr_12_1 (> expr_10_1 expr_11_0)) (and (=> true true) (and (= expr_11_0 1000) (and (and (>= expr_10_1 0) (<= expr_10_1 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (=> true (and (>= expr_10_1 0) (<= expr_10_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_10_1 (select (|balances| state_1) expr_9_1)) (and (=> true (and (>= expr_9_1 0) (<= expr_9_1 1461501637330902918203684832716283019655932542975))) (and (= expr_9_1 expr_8_0) (and (=> true true) (and (= expr_8_0 this_0) (and (and (>= a_2_1 0) (<= a_2_1 1461501637330902918203684832716283019655932542975)) true)))))))))))))))))))))))))))))))))))))))))) (and (not expr_38_1) (= error_2 2))) (block_9_function_f__42_43_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_4 a_2_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_1 Int) (expr_11_0 Int) (expr_12_1 Bool) (expr_15_0 Int) (expr_18_0 Int) (expr_24_0 Int) (expr_25_1 Int) (expr_26_1 Int) (expr_27_0 Int) (expr_28_1 Bool) (expr_34_0 Int) (expr_35_1 Int) (expr_36_1 Int) (expr_37_0 Int) (expr_38_1 Bool) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (block_9_function_f__42_43_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_4 a_2_1) (summary_3_function_f__42_43_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_4 a_2_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_1 Int) (expr_11_0 Int) (expr_12_1 Bool) (expr_15_0 Int) (expr_18_0 Int) (expr_24_0 Int) (expr_25_1 Int) (expr_26_1 Int) (expr_27_0 Int) (expr_28_1 Bool) (expr_34_0 Int) (expr_35_1 Int) (expr_36_1 Int) (expr_37_0 Int) (expr_38_1 Bool) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_6_f_41_43_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (= error_2 error_1) (and (= expr_38_1 (> expr_36_1 expr_37_0)) (and (=> true true) (and (= expr_37_0 500) (and (and (>= expr_36_1 0) (<= expr_36_1 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (=> true (and (>= expr_36_1 0) (<= expr_36_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_36_1 (select (|balances| state_4) expr_35_1)) (and (=> true (and (>= expr_35_1 0) (<= expr_35_1 1461501637330902918203684832716283019655932542975))) (and (= expr_35_1 expr_34_0) (and (=> true true) (and (= expr_34_0 this_0) (and (= error_1 error_0) (and (= expr_28_1 (> expr_26_1 expr_27_0)) (and (=> true true) (and (= expr_27_0 100) (and (and (>= expr_26_1 0) (<= expr_26_1 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (=> true (and (>= expr_26_1 0) (<= expr_26_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_26_1 (select (|balances| state_4) expr_25_1)) (and (=> true (and (>= expr_25_1 0) (<= expr_25_1 1461501637330902918203684832716283019655932542975))) (and (= expr_25_1 expr_24_0) (and (=> true true) (and (= expr_24_0 this_0) (and (= state_4 (ite (= this_0 expr_15_0) state_1 state_3)) (and (= state_3 (|state_type| (store (|balances| state_2) expr_15_0 (+ (select (|balances| state_2) expr_15_0) expr_18_0)))) (and (= state_2 (|state_type| (store (|balances| state_1) this_0 (+ (select (|balances| state_1) this_0) (- 0 expr_18_0))))) (and (and (>= (select (|balances| state_1) this_0) 0) (<= (select (|balances| state_1) this_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (=> true true) (and (= expr_18_0 666) (and (=> true (and (>= expr_15_0 0) (<= expr_15_0 1461501637330902918203684832716283019655932542975))) (and (= expr_15_0 a_2_1) (and (=> true expr_12_1) (and (= expr_12_1 (> expr_10_1 expr_11_0)) (and (=> true true) (and (= expr_11_0 1000) (and (and (>= expr_10_1 0) (<= expr_10_1 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (=> true (and (>= expr_10_1 0) (<= expr_10_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_10_1 (select (|balances| state_1) expr_9_1)) (and (=> true (and (>= expr_9_1 0) (<= expr_9_1 1461501637330902918203684832716283019655932542975))) (and (= expr_9_1 expr_8_0) (and (=> true true) (and (= expr_8_0 this_0) (and (and (>= a_2_1 0) (<= a_2_1 1461501637330902918203684832716283019655932542975)) true))))))))))))))))))))))))))))))))))))))))))) true) (block_7_return_function_f__42_43_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_4 a_2_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_1 Int) (expr_11_0 Int) (expr_12_1 Bool) (expr_15_0 Int) (expr_18_0 Int) (expr_24_0 Int) (expr_25_1 Int) (expr_26_1 Int) (expr_27_0 Int) (expr_28_1 Bool) (expr_34_0 Int) (expr_35_1 Int) (expr_36_1 Int) (expr_37_0 Int) (expr_38_1 Bool) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_7_return_function_f__42_43_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) true) true) (summary_3_function_f__42_43_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(declare-fun |block_10_function_f__42_43_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_1 Int) (expr_11_0 Int) (expr_12_1 Bool) (expr_15_0 Int) (expr_18_0 Int) (expr_24_0 Int) (expr_25_1 Int) (expr_26_1 Int) (expr_27_0 Int) (expr_28_1 Bool) (expr_34_0 Int) (expr_35_1 Int) (expr_36_1 Int) (expr_37_0 Int) (expr_38_1 Bool) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(block_10_function_f__42_43_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1)))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_1 Int) (expr_11_0 Int) (expr_12_1 Bool) (expr_15_0 Int) (expr_18_0 Int) (expr_24_0 Int) (expr_25_1 Int) (expr_26_1 Int) (expr_27_0 Int) (expr_28_1 Bool) (expr_34_0 Int) (expr_35_1 Int) (expr_36_1 Int) (expr_37_0 Int) (expr_38_1 Bool) (expr_8_0 Int) (expr_9_1 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_10_function_f__42_43_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (summary_3_function_f__42_43_0 error_1 this_0 abi_0 crypto_0 tx_0 state_2 a_2_1 state_3 a_2_2) (and (= state_2 (|state_type| (store (|balances| state_1) this_0 (+ (select (|balances| state_1) this_0) funds_3_0)))) (and (and (>= (+ (select (|balances| state_1) this_0) funds_3_0) 0) (<= (+ (select (|balances| state_1) this_0) funds_3_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= funds_3_0 (|msg.value| tx_0)) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (and (and (and (and (and (= (|msg.value| tx_0) 0) (= (|msg.sig| tx_0) 4234695194)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 0) 252)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 1) 104)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 2) 82)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 3) 26)) (>= (|bytes_tuple_accessor_length| (|msg.data| tx_0)) 4))) (and (and (and (and (= state_1 state_0) (= error_0 0)) true) (and true (= a_2_1 a_2_0))) true))))))) true) (summary_4_function_f__42_43_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_3 a_2_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_1 Int) (expr_11_0 Int) (expr_12_1 Bool) (expr_15_0 Int) (expr_18_0 Int) (expr_24_0 Int) (expr_25_1 Int) (expr_26_1 Int) (expr_27_0 Int) (expr_28_1 Bool) (expr_34_0 Int) (expr_35_1 Int) (expr_36_1 Int) (expr_37_0 Int) (expr_38_1 Bool) (expr_8_0 Int) (expr_9_1 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (interface_0_C_43_0 this_0 abi_0 crypto_0 state_0) true) (and (summary_4_function_f__42_43_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (= error_0 0))) (interface_0_C_43_0 this_0 abi_0 crypto_0 state_1))))


(declare-fun |contract_initializer_11_C_43_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(declare-fun |contract_initializer_entry_12_C_43_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_1 Int) (expr_11_0 Int) (expr_12_1 Bool) (expr_15_0 Int) (expr_18_0 Int) (expr_24_0 Int) (expr_25_1 Int) (expr_26_1 Int) (expr_27_0 Int) (expr_28_1 Bool) (expr_34_0 Int) (expr_35_1 Int) (expr_36_1 Int) (expr_37_0 Int) (expr_38_1 Bool) (expr_8_0 Int) (expr_9_1 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (= state_1 state_0) (= error_0 0)) true) (contract_initializer_entry_12_C_43_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |contract_initializer_after_init_13_C_43_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_1 Int) (expr_11_0 Int) (expr_12_1 Bool) (expr_15_0 Int) (expr_18_0 Int) (expr_24_0 Int) (expr_25_1 Int) (expr_26_1 Int) (expr_27_0 Int) (expr_28_1 Bool) (expr_34_0 Int) (expr_35_1 Int) (expr_36_1 Int) (expr_37_0 Int) (expr_38_1 Bool) (expr_8_0 Int) (expr_9_1 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (contract_initializer_entry_12_C_43_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) true) (contract_initializer_after_init_13_C_43_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_1 Int) (expr_11_0 Int) (expr_12_1 Bool) (expr_15_0 Int) (expr_18_0 Int) (expr_24_0 Int) (expr_25_1 Int) (expr_26_1 Int) (expr_27_0 Int) (expr_28_1 Bool) (expr_34_0 Int) (expr_35_1 Int) (expr_36_1 Int) (expr_37_0 Int) (expr_38_1 Bool) (expr_8_0 Int) (expr_9_1 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (contract_initializer_after_init_13_C_43_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) true) (contract_initializer_11_C_43_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |implicit_constructor_entry_14_C_43_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_1 Int) (expr_11_0 Int) (expr_12_1 Bool) (expr_15_0 Int) (expr_18_0 Int) (expr_24_0 Int) (expr_25_1 Int) (expr_26_1 Int) (expr_27_0 Int) (expr_28_1 Bool) (expr_34_0 Int) (expr_35_1 Int) (expr_36_1 Int) (expr_37_0 Int) (expr_38_1 Bool) (expr_8_0 Int) (expr_9_1 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (and (and (= state_1 state_0) (= error_0 0)) true) true) (>= (select (|balances| state_1) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_14_C_43_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_1 Int) (expr_11_0 Int) (expr_12_1 Bool) (expr_15_0 Int) (expr_18_0 Int) (expr_24_0 Int) (expr_25_1 Int) (expr_26_1 Int) (expr_27_0 Int) (expr_28_1 Bool) (expr_34_0 Int) (expr_35_1 Int) (expr_36_1 Int) (expr_37_0 Int) (expr_38_1 Bool) (expr_8_0 Int) (expr_9_1 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (implicit_constructor_entry_14_C_43_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (contract_initializer_11_C_43_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2) true)) (> error_1 0)) (summary_constructor_2_C_43_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_1 Int) (expr_11_0 Int) (expr_12_1 Bool) (expr_15_0 Int) (expr_18_0 Int) (expr_24_0 Int) (expr_25_1 Int) (expr_26_1 Int) (expr_27_0 Int) (expr_28_1 Bool) (expr_34_0 Int) (expr_35_1 Int) (expr_36_1 Int) (expr_37_0 Int) (expr_38_1 Bool) (expr_8_0 Int) (expr_9_1 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (implicit_constructor_entry_14_C_43_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (= error_1 0) (and (contract_initializer_11_C_43_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2) true))) true) (summary_constructor_2_C_43_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_1 Int) (expr_11_0 Int) (expr_12_1 Bool) (expr_15_0 Int) (expr_18_0 Int) (expr_24_0 Int) (expr_25_1 Int) (expr_26_1 Int) (expr_27_0 Int) (expr_28_1 Bool) (expr_34_0 Int) (expr_35_1 Int) (expr_36_1 Int) (expr_37_0 Int) (expr_38_1 Bool) (expr_8_0 Int) (expr_9_1 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (summary_constructor_2_C_43_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 0))) (interface_0_C_43_0 this_0 abi_0 crypto_0 state_1))))


(declare-fun |error_target_4_0| () Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_1 Int) (expr_11_0 Int) (expr_12_1 Bool) (expr_15_0 Int) (expr_18_0 Int) (expr_24_0 Int) (expr_25_1 Int) (expr_26_1 Int) (expr_27_0 Int) (expr_28_1 Bool) (expr_34_0 Int) (expr_35_1 Int) (expr_36_1 Int) (expr_37_0 Int) (expr_38_1 Bool) (expr_8_0 Int) (expr_9_1 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (interface_0_C_43_0 this_0 abi_0 crypto_0 state_0) true) (and (summary_4_function_f__42_43_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (= error_0 1))) error_target_4_0)))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_1 Int) (expr_11_0 Int) (expr_12_1 Bool) (expr_15_0 Int) (expr_18_0 Int) (expr_24_0 Int) (expr_25_1 Int) (expr_26_1 Int) (expr_27_0 Int) (expr_28_1 Bool) (expr_34_0 Int) (expr_35_1 Int) (expr_36_1 Int) (expr_37_0 Int) (expr_38_1 Bool) (expr_8_0 Int) (expr_9_1 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> error_target_4_0 false)))
(check-sat)