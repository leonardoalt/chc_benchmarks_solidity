(set-logic HORN)

(declare-datatypes ((|state_type| 0)) (((|state_type| (|balances| (Array Int Int))))))
(declare-datatypes ((|bytes_tuple| 0)) (((|bytes_tuple| (|bytes_tuple_accessor_array| (Array Int Int)) (|bytes_tuple_accessor_length| Int)))))
(declare-datatypes ((|tx_type| 0)) (((|tx_type| (|block.basefee| Int) (|block.chainid| Int) (|block.coinbase| Int) (|block.difficulty| Int) (|block.gaslimit| Int) (|block.number| Int) (|block.timestamp| Int) (|blockhash| (Array Int Int)) (|msg.data| |bytes_tuple|) (|msg.sender| Int) (|msg.sig| Int) (|msg.value| Int) (|tx.gasprice| Int) (|tx.origin| Int)))))
(declare-datatypes ((|ecrecover_input_type| 0)) (((|ecrecover_input_type| (|hash| Int) (|v| Int) (|r| Int) (|s| Int)))))
(declare-datatypes ((|crypto_type| 0)) (((|crypto_type| (|ecrecover| (Array |ecrecover_input_type| Int)) (|keccak256| (Array |bytes_tuple| Int)) (|ripemd160| (Array |bytes_tuple| Int)) (|sha256| (Array |bytes_tuple| Int))))))
(declare-datatypes ((|abi_type| 0)) (((|abi_type|))))
(declare-fun |interface_0_C_36_0| (Int |abi_type| |crypto_type| |state_type| Int ) Bool)
(declare-fun |nondet_interface_1_C_36_0| (Int Int |abi_type| |crypto_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_constructor_2_C_36_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int Int |state_type| Int Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int))
(=> (= error_0 0) (nondet_interface_1_C_36_0 error_0 this_0 abi_0 crypto_0 state_0 x_3_0 state_0 x_3_0))))


(declare-fun |summary_3_constructor_23_36_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int Int |state_type| Int Int Int ) Bool)
(declare-fun |summary_4_function_f__35_36_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |summary_5_function_f__35_36_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (y_25_0 Int) (y_25_1 Int))
(=> (and (and (nondet_interface_1_C_36_0 error_0 this_0 abi_0 crypto_0 state_0 x_3_0 state_1 x_3_1) true) (and (= error_0 0) (summary_5_function_f__35_36_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_3_1 y_25_0 state_2 x_3_2 y_25_1))) (nondet_interface_1_C_36_0 error_1 this_0 abi_0 crypto_0 state_0 x_3_0 state_2 x_3_2))))


(declare-fun |block_6_function_f__35_36_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |block_7_f_34_36_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (a_5_1 Int) (abi_0 |abi_type|) (b_7_1 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (y_25_0 Int) (y_25_1 Int))
(block_6_function_f__35_36_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 y_25_0 state_1 x_3_1 y_25_1)))


(assert
(forall ( (a_5_1 Int) (abi_0 |abi_type|) (b_7_1 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (y_25_0 Int) (y_25_1 Int))
(=> (and (and (block_6_function_f__35_36_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 y_25_0 state_1 x_3_1 y_25_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_3_1 x_3_0))) (and true (= y_25_1 y_25_0))) true)) true) (block_7_f_34_36_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 y_25_0 state_1 x_3_1 y_25_1))))


(declare-fun |block_8_return_function_f__35_36_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |block_9_function_f__35_36_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (a_5_1 Int) (abi_0 |abi_type|) (b_7_1 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_29_0 Int) (expr_30_0 Int) (expr_31_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (y_25_0 Int) (y_25_1 Int))
(=> (and (and (block_7_f_34_36_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 y_25_0 state_1 x_3_1 y_25_1) (and (= expr_31_1 (= expr_29_0 expr_30_0)) (and (=> true (and (>= expr_30_0 0) (<= expr_30_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_30_0 x_3_1) (and (=> true (and (>= expr_29_0 0) (<= expr_29_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_29_0 y_25_1) (and (and (>= y_25_1 0) (<= y_25_1 115792089237316195423570985008687907853269984665640564039457584007913129639935)) true))))))) (and (not expr_31_1) (= error_1 1))) (block_9_function_f__35_36_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 y_25_0 state_1 x_3_1 y_25_1))))


(assert
(forall ( (a_5_1 Int) (abi_0 |abi_type|) (b_7_1 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_29_0 Int) (expr_30_0 Int) (expr_31_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (y_25_0 Int) (y_25_1 Int))
(=> (block_9_function_f__35_36_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 y_25_0 state_1 x_3_1 y_25_1) (summary_4_function_f__35_36_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 y_25_0 state_1 x_3_1 y_25_1))))


(assert
(forall ( (a_5_1 Int) (abi_0 |abi_type|) (b_7_1 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_29_0 Int) (expr_30_0 Int) (expr_31_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (y_25_0 Int) (y_25_1 Int))
(=> (and (and (block_7_f_34_36_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 y_25_0 state_1 x_3_1 y_25_1) (and (= error_1 error_0) (and (= expr_31_1 (= expr_29_0 expr_30_0)) (and (=> true (and (>= expr_30_0 0) (<= expr_30_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_30_0 x_3_1) (and (=> true (and (>= expr_29_0 0) (<= expr_29_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_29_0 y_25_1) (and (and (>= y_25_1 0) (<= y_25_1 115792089237316195423570985008687907853269984665640564039457584007913129639935)) true)))))))) true) (block_8_return_function_f__35_36_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 y_25_0 state_1 x_3_1 y_25_1))))


(assert
(forall ( (a_5_1 Int) (abi_0 |abi_type|) (b_7_1 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_29_0 Int) (expr_30_0 Int) (expr_31_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (y_25_0 Int) (y_25_1 Int))
(=> (and (and (block_8_return_function_f__35_36_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 y_25_0 state_1 x_3_1 y_25_1) true) true) (summary_4_function_f__35_36_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 y_25_0 state_1 x_3_1 y_25_1))))


(declare-fun |block_10_function_f__35_36_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (a_5_1 Int) (abi_0 |abi_type|) (b_7_1 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_29_0 Int) (expr_30_0 Int) (expr_31_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (y_25_0 Int) (y_25_1 Int))
(block_10_function_f__35_36_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 y_25_0 state_1 x_3_1 y_25_1)))


(assert
(forall ( (a_5_1 Int) (abi_0 |abi_type|) (b_7_1 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_29_0 Int) (expr_30_0 Int) (expr_31_1 Bool) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (y_25_0 Int) (y_25_1 Int) (y_25_2 Int))
(=> (and (and (block_10_function_f__35_36_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 y_25_0 state_1 x_3_1 y_25_1) (and (summary_4_function_f__35_36_0 error_1 this_0 abi_0 crypto_0 tx_0 state_2 x_3_1 y_25_1 state_3 x_3_2 y_25_2) (and (= state_2 (|state_type| (store (|balances| state_1) this_0 (+ (select (|balances| state_1) this_0) funds_2_0)))) (and (and (>= (+ (select (|balances| state_1) this_0) funds_2_0) 0) (<= (+ (select (|balances| state_1) this_0) funds_2_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= funds_2_0 (|msg.value| tx_0)) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (and (and (and (and (and (= (|msg.value| tx_0) 0) (= (|msg.sig| tx_0) 3017696395)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 0) 179)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 1) 222)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 2) 100)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 3) 139)) (>= (|bytes_tuple_accessor_length| (|msg.data| tx_0)) 4))) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_3_1 x_3_0))) (and true (= y_25_1 y_25_0))) true))))))) true) (summary_5_function_f__35_36_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 y_25_0 state_3 x_3_2 y_25_2))))


(assert
(forall ( (a_5_1 Int) (abi_0 |abi_type|) (b_7_1 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_29_0 Int) (expr_30_0 Int) (expr_31_1 Bool) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (y_25_0 Int) (y_25_1 Int) (y_25_2 Int))
(=> (and (and (interface_0_C_36_0 this_0 abi_0 crypto_0 state_0 x_3_0) true) (and (summary_5_function_f__35_36_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 y_25_0 state_1 x_3_1 y_25_1) (= error_0 0))) (interface_0_C_36_0 this_0 abi_0 crypto_0 state_1 x_3_1))))


(declare-fun |block_11_constructor_23_36_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int Int |state_type| Int Int Int ) Bool)
(declare-fun |block_12__22_36_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int Int |state_type| Int Int Int ) Bool)
(assert
(forall ( (a_5_0 Int) (a_5_1 Int) (abi_0 |abi_type|) (b_7_0 Int) (b_7_1 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_29_0 Int) (expr_30_0 Int) (expr_31_1 Bool) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (y_25_0 Int) (y_25_1 Int) (y_25_2 Int))
(block_11_constructor_23_36_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 a_5_0 b_7_0 state_1 x_3_1 a_5_1 b_7_1)))


(assert
(forall ( (a_5_0 Int) (a_5_1 Int) (abi_0 |abi_type|) (b_7_0 Int) (b_7_1 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_29_0 Int) (expr_30_0 Int) (expr_31_1 Bool) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (y_25_0 Int) (y_25_1 Int) (y_25_2 Int))
(=> (and (and (block_11_constructor_23_36_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 a_5_0 b_7_0 state_1 x_3_1 a_5_1 b_7_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_3_1 x_3_0))) (and (and true (= a_5_1 a_5_0)) (= b_7_1 b_7_0))) true)) true) (block_12__22_36_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 a_5_0 b_7_0 state_1 x_3_1 a_5_1 b_7_1))))


(declare-fun |block_13_return_constructor_23_36_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int Int |state_type| Int Int Int ) Bool)
(declare-fun |block_14_constructor_23_36_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int Int |state_type| Int Int Int ) Bool)
(assert
(forall ( (a_5_0 Int) (a_5_1 Int) (abi_0 |abi_type|) (b_7_0 Int) (b_7_1 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_11_0 Int) (expr_12_0 Int) (expr_13_1 Bool) (expr_29_0 Int) (expr_30_0 Int) (expr_31_1 Bool) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (y_25_0 Int) (y_25_1 Int) (y_25_2 Int))
(=> (and (and (block_12__22_36_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 a_5_0 b_7_0 state_1 x_3_1 a_5_1 b_7_1) (and (= expr_13_1 (= expr_11_0 expr_12_0)) (and (=> true true) (and (= expr_12_0 5) (and (=> true (and (>= expr_11_0 0) (<= expr_11_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_11_0 x_3_1) (and (and (>= b_7_1 0) (<= b_7_1 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (and (>= a_5_1 0) (<= a_5_1 115792089237316195423570985008687907853269984665640564039457584007913129639935)) true)))))))) (and (not expr_13_1) (= error_1 3))) (block_14_constructor_23_36_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 a_5_0 b_7_0 state_1 x_3_1 a_5_1 b_7_1))))


(assert
(forall ( (a_5_0 Int) (a_5_1 Int) (abi_0 |abi_type|) (b_7_0 Int) (b_7_1 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_11_0 Int) (expr_12_0 Int) (expr_13_1 Bool) (expr_29_0 Int) (expr_30_0 Int) (expr_31_1 Bool) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (y_25_0 Int) (y_25_1 Int) (y_25_2 Int))
(=> (block_14_constructor_23_36_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 a_5_0 b_7_0 state_1 x_3_1 a_5_1 b_7_1) (summary_3_constructor_23_36_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 a_5_0 b_7_0 state_1 x_3_1 a_5_1 b_7_1))))


(assert
(forall ( (a_5_0 Int) (a_5_1 Int) (abi_0 |abi_type|) (b_7_0 Int) (b_7_1 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_11_0 Int) (expr_12_0 Int) (expr_13_1 Bool) (expr_16_0 Int) (expr_17_0 Int) (expr_18_0 Int) (expr_19_1 Int) (expr_20_1 Int) (expr_29_0 Int) (expr_30_0 Int) (expr_31_1 Bool) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (y_25_0 Int) (y_25_1 Int) (y_25_2 Int))
(=> (and (and (block_12__22_36_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 a_5_0 b_7_0 state_1 x_3_1 a_5_1 b_7_1) (and (= x_3_2 expr_20_1) (and (=> true (and (>= expr_20_1 0) (<= expr_20_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_20_1 expr_19_1) (and (=> true (and (>= expr_16_0 0) (<= expr_16_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_16_0 x_3_1) (and (=> true (and (>= expr_19_1 0) (<= expr_19_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_19_1 (+ expr_17_0 expr_18_0)) (and (=> true (and (>= expr_18_0 0) (<= expr_18_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_18_0 b_7_1) (and (=> true (and (>= expr_17_0 0) (<= expr_17_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_17_0 a_5_1) (and (= error_1 error_0) (and (= expr_13_1 (= expr_11_0 expr_12_0)) (and (=> true true) (and (= expr_12_0 5) (and (=> true (and (>= expr_11_0 0) (<= expr_11_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_11_0 x_3_1) (and (and (>= b_7_1 0) (<= b_7_1 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (and (>= a_5_1 0) (<= a_5_1 115792089237316195423570985008687907853269984665640564039457584007913129639935)) true)))))))))))))))))))) true) (block_13_return_constructor_23_36_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 a_5_0 b_7_0 state_1 x_3_2 a_5_1 b_7_1))))


(assert
(forall ( (a_5_0 Int) (a_5_1 Int) (abi_0 |abi_type|) (b_7_0 Int) (b_7_1 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_11_0 Int) (expr_12_0 Int) (expr_13_1 Bool) (expr_16_0 Int) (expr_17_0 Int) (expr_18_0 Int) (expr_19_1 Int) (expr_20_1 Int) (expr_29_0 Int) (expr_30_0 Int) (expr_31_1 Bool) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (y_25_0 Int) (y_25_1 Int) (y_25_2 Int))
(=> (and (and (block_13_return_constructor_23_36_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 a_5_0 b_7_0 state_1 x_3_1 a_5_1 b_7_1) true) true) (summary_3_constructor_23_36_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 a_5_0 b_7_0 state_1 x_3_1 a_5_1 b_7_1))))


(declare-fun |contract_initializer_15_C_36_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int Int |state_type| Int Int Int ) Bool)
(declare-fun |contract_initializer_entry_16_C_36_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int Int |state_type| Int Int Int ) Bool)
(assert
(forall ( (a_5_0 Int) (a_5_1 Int) (abi_0 |abi_type|) (b_7_0 Int) (b_7_1 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_11_0 Int) (expr_12_0 Int) (expr_13_1 Bool) (expr_16_0 Int) (expr_17_0 Int) (expr_18_0 Int) (expr_19_1 Int) (expr_20_1 Int) (expr_29_0 Int) (expr_30_0 Int) (expr_31_1 Bool) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (y_25_0 Int) (y_25_1 Int) (y_25_2 Int))
(=> (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_3_1 x_3_0))) (and (and true (= a_5_1 a_5_0)) (= b_7_1 b_7_0))) (contract_initializer_entry_16_C_36_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 a_5_0 b_7_0 state_1 x_3_1 a_5_1 b_7_1))))


(declare-fun |contract_initializer_after_init_17_C_36_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int Int |state_type| Int Int Int ) Bool)
(assert
(forall ( (a_5_0 Int) (a_5_1 Int) (abi_0 |abi_type|) (b_7_0 Int) (b_7_1 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_11_0 Int) (expr_12_0 Int) (expr_13_1 Bool) (expr_16_0 Int) (expr_17_0 Int) (expr_18_0 Int) (expr_19_1 Int) (expr_20_1 Int) (expr_29_0 Int) (expr_2_0 Int) (expr_30_0 Int) (expr_31_1 Bool) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (y_25_0 Int) (y_25_1 Int) (y_25_2 Int))
(=> (and (and (contract_initializer_entry_16_C_36_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 a_5_0 b_7_0 state_1 x_3_1 a_5_1 b_7_1) (and (= x_3_2 expr_2_0) (and (=> true true) (and (= expr_2_0 5) true)))) true) (contract_initializer_after_init_17_C_36_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 a_5_0 b_7_0 state_1 x_3_2 a_5_1 b_7_1))))


(assert
(forall ( (a_5_0 Int) (a_5_1 Int) (a_5_2 Int) (abi_0 |abi_type|) (b_7_0 Int) (b_7_1 Int) (b_7_2 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_11_0 Int) (expr_12_0 Int) (expr_13_1 Bool) (expr_16_0 Int) (expr_17_0 Int) (expr_18_0 Int) (expr_19_1 Int) (expr_20_1 Int) (expr_29_0 Int) (expr_2_0 Int) (expr_30_0 Int) (expr_31_1 Bool) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (y_25_0 Int) (y_25_1 Int) (y_25_2 Int))
(=> (and (and (contract_initializer_after_init_17_C_36_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 a_5_0 b_7_0 state_1 x_3_1 a_5_1 b_7_1) (and (summary_3_constructor_23_36_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_3_1 a_5_1 b_7_1 state_2 x_3_2 a_5_2 b_7_2) true)) (> error_1 0)) (contract_initializer_15_C_36_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 a_5_0 b_7_0 state_2 x_3_2 a_5_2 b_7_2))))


(assert
(forall ( (a_5_0 Int) (a_5_1 Int) (a_5_2 Int) (abi_0 |abi_type|) (b_7_0 Int) (b_7_1 Int) (b_7_2 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_11_0 Int) (expr_12_0 Int) (expr_13_1 Bool) (expr_16_0 Int) (expr_17_0 Int) (expr_18_0 Int) (expr_19_1 Int) (expr_20_1 Int) (expr_29_0 Int) (expr_2_0 Int) (expr_30_0 Int) (expr_31_1 Bool) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (y_25_0 Int) (y_25_1 Int) (y_25_2 Int))
(=> (and (and (contract_initializer_after_init_17_C_36_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 a_5_0 b_7_0 state_1 x_3_1 a_5_1 b_7_1) (and (= error_1 0) (and (summary_3_constructor_23_36_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_3_1 a_5_1 b_7_1 state_2 x_3_2 a_5_2 b_7_2) true))) true) (contract_initializer_15_C_36_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 a_5_0 b_7_0 state_2 x_3_2 a_5_2 b_7_2))))


(declare-fun |implicit_constructor_entry_18_C_36_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int Int |state_type| Int Int Int ) Bool)
(assert
(forall ( (a_5_0 Int) (a_5_1 Int) (a_5_2 Int) (abi_0 |abi_type|) (b_7_0 Int) (b_7_1 Int) (b_7_2 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_11_0 Int) (expr_12_0 Int) (expr_13_1 Bool) (expr_16_0 Int) (expr_17_0 Int) (expr_18_0 Int) (expr_19_1 Int) (expr_20_1 Int) (expr_29_0 Int) (expr_2_0 Int) (expr_30_0 Int) (expr_31_1 Bool) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (y_25_0 Int) (y_25_1 Int) (y_25_2 Int))
(=> (and (and (and (and (and (= state_2 state_0) (= error_1 0)) (and true (= x_3_2 x_3_0))) (and (and true (= a_5_2 a_5_0)) (= b_7_2 b_7_0))) (and true (= x_3_2 0))) (>= (select (|balances| state_2) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_18_C_36_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 a_5_0 b_7_0 state_2 x_3_2 a_5_2 b_7_2))))


(assert
(forall ( (a_5_0 Int) (a_5_1 Int) (a_5_2 Int) (a_5_3 Int) (abi_0 |abi_type|) (b_7_0 Int) (b_7_1 Int) (b_7_2 Int) (b_7_3 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_11_0 Int) (expr_12_0 Int) (expr_13_1 Bool) (expr_16_0 Int) (expr_17_0 Int) (expr_18_0 Int) (expr_19_1 Int) (expr_20_1 Int) (expr_29_0 Int) (expr_2_0 Int) (expr_30_0 Int) (expr_31_1 Bool) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (y_25_0 Int) (y_25_1 Int) (y_25_2 Int))
(=> (and (and (implicit_constructor_entry_18_C_36_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 a_5_0 b_7_0 state_1 x_3_1 a_5_2 b_7_2) (and (contract_initializer_15_C_36_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_3_1 a_5_2 b_7_2 state_2 x_3_2 a_5_3 b_7_3) true)) (> error_1 0)) (summary_constructor_2_C_36_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 a_5_0 b_7_0 state_2 x_3_2 a_5_3 b_7_3))))


(assert
(forall ( (a_5_0 Int) (a_5_1 Int) (a_5_2 Int) (a_5_3 Int) (abi_0 |abi_type|) (b_7_0 Int) (b_7_1 Int) (b_7_2 Int) (b_7_3 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_11_0 Int) (expr_12_0 Int) (expr_13_1 Bool) (expr_16_0 Int) (expr_17_0 Int) (expr_18_0 Int) (expr_19_1 Int) (expr_20_1 Int) (expr_29_0 Int) (expr_2_0 Int) (expr_30_0 Int) (expr_31_1 Bool) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (y_25_0 Int) (y_25_1 Int) (y_25_2 Int))
(=> (and (and (implicit_constructor_entry_18_C_36_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 a_5_0 b_7_0 state_1 x_3_1 a_5_2 b_7_2) (and (= error_1 0) (and (contract_initializer_15_C_36_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_3_1 a_5_2 b_7_2 state_2 x_3_2 a_5_3 b_7_3) true))) true) (summary_constructor_2_C_36_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 a_5_0 b_7_0 state_2 x_3_2 a_5_3 b_7_3))))


(assert
(forall ( (a_5_0 Int) (a_5_1 Int) (a_5_2 Int) (a_5_3 Int) (abi_0 |abi_type|) (b_7_0 Int) (b_7_1 Int) (b_7_2 Int) (b_7_3 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_11_0 Int) (expr_12_0 Int) (expr_13_1 Bool) (expr_16_0 Int) (expr_17_0 Int) (expr_18_0 Int) (expr_19_1 Int) (expr_20_1 Int) (expr_29_0 Int) (expr_2_0 Int) (expr_30_0 Int) (expr_31_1 Bool) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (y_25_0 Int) (y_25_1 Int) (y_25_2 Int))
(=> (and (and (summary_constructor_2_C_36_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 a_5_0 b_7_0 state_1 x_3_1 a_5_3 b_7_3) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 0))) (interface_0_C_36_0 this_0 abi_0 crypto_0 state_1 x_3_1))))


(declare-fun |error_target_4_0| () Bool)
(assert
(forall ( (a_5_0 Int) (a_5_1 Int) (a_5_2 Int) (a_5_3 Int) (a_5_4 Int) (abi_0 |abi_type|) (b_7_0 Int) (b_7_1 Int) (b_7_2 Int) (b_7_3 Int) (b_7_4 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_11_0 Int) (expr_12_0 Int) (expr_13_1 Bool) (expr_16_0 Int) (expr_17_0 Int) (expr_18_0 Int) (expr_19_1 Int) (expr_20_1 Int) (expr_29_0 Int) (expr_2_0 Int) (expr_30_0 Int) (expr_31_1 Bool) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (y_25_0 Int) (y_25_1 Int) (y_25_2 Int))
(=> (and (and (interface_0_C_36_0 this_0 abi_0 crypto_0 state_0 x_3_0) true) (and (summary_5_function_f__35_36_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 y_25_0 state_1 x_3_1 y_25_1) (= error_0 1))) error_target_4_0)))


(declare-fun |error_target_5_0| () Bool)
(assert
(forall ( (a_5_0 Int) (a_5_1 Int) (a_5_2 Int) (a_5_3 Int) (a_5_4 Int) (abi_0 |abi_type|) (b_7_0 Int) (b_7_1 Int) (b_7_2 Int) (b_7_3 Int) (b_7_4 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_11_0 Int) (expr_12_0 Int) (expr_13_1 Bool) (expr_16_0 Int) (expr_17_0 Int) (expr_18_0 Int) (expr_19_1 Int) (expr_20_1 Int) (expr_29_0 Int) (expr_2_0 Int) (expr_30_0 Int) (expr_31_1 Bool) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (y_25_0 Int) (y_25_1 Int) (y_25_2 Int))
(=> (and (and (summary_constructor_2_C_36_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 a_5_0 b_7_0 state_1 x_3_1 a_5_3 b_7_3) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 3))) error_target_5_0)))


(assert
(forall ( (a_5_0 Int) (a_5_1 Int) (a_5_2 Int) (a_5_3 Int) (a_5_4 Int) (abi_0 |abi_type|) (b_7_0 Int) (b_7_1 Int) (b_7_2 Int) (b_7_3 Int) (b_7_4 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_11_0 Int) (expr_12_0 Int) (expr_13_1 Bool) (expr_16_0 Int) (expr_17_0 Int) (expr_18_0 Int) (expr_19_1 Int) (expr_20_1 Int) (expr_29_0 Int) (expr_2_0 Int) (expr_30_0 Int) (expr_31_1 Bool) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (y_25_0 Int) (y_25_1 Int) (y_25_2 Int))
(=> error_target_5_0 false)))
(check-sat)