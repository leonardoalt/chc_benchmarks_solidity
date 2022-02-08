(set-logic HORN)

(declare-datatypes ((|state_type| 0)) (((|state_type| (|balances| (Array Int Int))))))
(declare-datatypes ((|bytes_tuple| 0)) (((|bytes_tuple| (|bytes_tuple_accessor_array| (Array Int Int)) (|bytes_tuple_accessor_length| Int)))))
(declare-datatypes ((|tx_type| 0)) (((|tx_type| (|block.basefee| Int) (|block.chainid| Int) (|block.coinbase| Int) (|block.difficulty| Int) (|block.gaslimit| Int) (|block.number| Int) (|block.timestamp| Int) (|blockhash| (Array Int Int)) (|msg.data| |bytes_tuple|) (|msg.sender| Int) (|msg.sig| Int) (|msg.value| Int) (|tx.gasprice| Int) (|tx.origin| Int)))))
(declare-datatypes ((|ecrecover_input_type| 0)) (((|ecrecover_input_type| (|hash| Int) (|v| Int) (|r| Int) (|s| Int)))))
(declare-datatypes ((|crypto_type| 0)) (((|crypto_type| (|ecrecover| (Array |ecrecover_input_type| Int)) (|keccak256| (Array |bytes_tuple| Int)) (|ripemd160| (Array |bytes_tuple| Int)) (|sha256| (Array |bytes_tuple| Int))))))
(declare-datatypes ((|abi_type| 0)) (((|abi_type|))))
(declare-datatypes ((|tuple()| 0)) (((|tuple()|))))
(declare-fun |interface_0_C_33_0| (Int |abi_type| |crypto_type| |state_type| Int ) Bool)
(declare-fun |nondet_interface_1_C_33_0| (Int Int |abi_type| |crypto_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_constructor_2_C_33_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (= error_0 0) (nondet_interface_1_C_33_0 error_0 this_0 abi_0 crypto_0 state_0 a_2_0 state_0 a_2_0))))


(declare-fun |summary_3_function_f__18_33_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |summary_4_function_f__18_33_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int))
(=> (and (and (nondet_interface_1_C_33_0 error_0 this_0 abi_0 crypto_0 state_0 a_2_0 state_1 a_2_1) true) (and (= error_0 0) (summary_4_function_f__18_33_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 x_4_0 state_2 a_2_2 x_4_1))) (nondet_interface_1_C_33_0 error_1 this_0 abi_0 crypto_0 state_0 a_2_0 state_2 a_2_2))))


(declare-fun |summary_5_function_g__32_33_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_6_function_g__32_33_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int))
(=> (and (and (nondet_interface_1_C_33_0 error_1 this_0 abi_0 crypto_0 state_0 a_2_0 state_1 a_2_1) true) (and (= error_1 0) (summary_6_function_g__32_33_0 error_2 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 state_2 a_2_2))) (nondet_interface_1_C_33_0 error_2 this_0 abi_0 crypto_0 state_0 a_2_0 state_2 a_2_2))))


(declare-fun |block_7_function_f__18_33_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int Int ) Bool)
(declare-fun |block_8_f_17_33_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (y_8_0 Int) (y_8_1 Int))
(block_7_function_f__18_33_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1 y_8_1)))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (y_8_0 Int) (y_8_1 Int))
(=> (and (and (block_7_function_f__18_33_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1 y_8_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= a_2_1 a_2_0))) (and true (= x_4_1 x_4_0))) true)) true) (block_8_f_17_33_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1 y_8_1))))


(declare-fun |block_9_return_function_f__18_33_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_0 Int) (expr_13_1 Int) (expr_14_1 Int) (expr_15_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (y_8_0 Int) (y_8_1 Int) (y_8_2 Int))
(=> (and (and (block_8_f_17_33_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1 y_8_1) (and (= a_2_2 expr_15_1) (and (=> true (and (>= expr_15_1 0) (<= expr_15_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_15_1 expr_14_1) (and (=> true (and (>= expr_10_0 0) (<= expr_10_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_10_0 a_2_1) (and (=> true (and (>= expr_14_1 0) (<= expr_14_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_14_1 expr_13_1) (and (= y_8_2 expr_13_1) (and (=> true (and (>= expr_13_1 0) (<= expr_13_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_13_1 expr_12_0) (and (=> true (and (>= expr_11_0 0) (<= expr_11_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_11_0 y_8_1) (and (=> true (and (>= expr_12_0 0) (<= expr_12_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_12_0 x_4_1) (and (and (>= x_4_1 0) (<= x_4_1 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (= y_8_1 0) true))))))))))))))))) true) (block_9_return_function_f__18_33_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_2 x_4_1 y_8_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_0 Int) (expr_13_1 Int) (expr_14_1 Int) (expr_15_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (y_8_0 Int) (y_8_1 Int) (y_8_2 Int))
(=> (and (and (block_9_return_function_f__18_33_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1 y_8_1) true) true) (summary_3_function_f__18_33_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1))))


(declare-fun |block_10_function_f__18_33_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_0 Int) (expr_13_1 Int) (expr_14_1 Int) (expr_15_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (y_8_0 Int) (y_8_1 Int) (y_8_2 Int))
(block_10_function_f__18_33_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1 y_8_1)))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_0 Int) (expr_13_1 Int) (expr_14_1 Int) (expr_15_1 Int) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (y_8_0 Int) (y_8_1 Int) (y_8_2 Int))
(=> (and (and (block_10_function_f__18_33_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1 y_8_1) (and (summary_3_function_f__18_33_0 error_1 this_0 abi_0 crypto_0 tx_0 state_2 a_2_1 x_4_1 state_3 a_2_2 x_4_2) (and (= state_2 (|state_type| (store (|balances| state_1) this_0 (+ (select (|balances| state_1) this_0) funds_0_0)))) (and (and (>= (+ (select (|balances| state_1) this_0) funds_0_0) 0) (<= (+ (select (|balances| state_1) this_0) funds_0_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= funds_0_0 (|msg.value| tx_0)) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (and (and (and (and (and (= (|msg.value| tx_0) 0) (= (|msg.sig| tx_0) 3017696395)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 0) 179)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 1) 222)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 2) 100)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 3) 139)) (>= (|bytes_tuple_accessor_length| (|msg.data| tx_0)) 4))) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= a_2_1 a_2_0))) (and true (= x_4_1 x_4_0))) true))))))) true) (summary_4_function_f__18_33_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_3 a_2_2 x_4_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_0 Int) (expr_13_1 Int) (expr_14_1 Int) (expr_15_1 Int) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (y_8_0 Int) (y_8_1 Int) (y_8_2 Int))
(=> (and (and (interface_0_C_33_0 this_0 abi_0 crypto_0 state_0 a_2_0) true) (and (summary_4_function_f__18_33_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1) (= error_0 0))) (interface_0_C_33_0 this_0 abi_0 crypto_0 state_1 a_2_1))))


(declare-fun |block_11_function_g__32_33_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_12_g_31_33_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_0 Int) (expr_13_1 Int) (expr_14_1 Int) (expr_15_1 Int) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (y_8_0 Int) (y_8_1 Int) (y_8_2 Int))
(block_11_function_g__32_33_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1)))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_0 Int) (expr_13_1 Int) (expr_14_1 Int) (expr_15_1 Int) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (y_8_0 Int) (y_8_1 Int) (y_8_2 Int))
(=> (and (and (block_11_function_g__32_33_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= a_2_1 a_2_0))) true) true)) true) (block_12_g_31_33_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(declare-fun |block_13_return_function_g__32_33_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_14_function_f__18_33_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_0 Int) (expr_13_1 Int) (expr_14_1 Int) (expr_15_1 Int) (expr_22_0 Int) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (y_8_0 Int) (y_8_1 Int) (y_8_2 Int))
(=> (summary_3_function_f__18_33_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_2 a_2_2 x_4_2) (summary_14_function_f__18_33_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_2 a_2_2 x_4_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_0 Int) (expr_13_1 Int) (expr_14_1 Int) (expr_15_1 Int) (expr_22_0 Int) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (y_8_0 Int) (y_8_1 Int) (y_8_2 Int))
(=> (and (and (block_12_g_31_33_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (summary_14_function_f__18_33_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 expr_22_0 state_2 a_2_2 x_4_2) (and (=> true true) (and (= expr_22_0 0) true)))) (> error_1 0)) (summary_5_function_g__32_33_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_2 a_2_2))))


(declare-fun |block_15_function_g__32_33_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_0 Int) (expr_13_1 Int) (expr_14_1 Int) (expr_15_1 Int) (expr_22_0 Int) (expr_23_1 |tuple()|) (expr_26_0 Int) (expr_27_0 Int) (expr_28_1 Bool) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (y_8_0 Int) (y_8_1 Int) (y_8_2 Int))
(=> (and (and (block_12_g_31_33_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (= expr_28_1 (> expr_26_0 expr_27_0)) (and (=> true true) (and (= expr_27_0 0) (and (=> true (and (>= expr_26_0 0) (<= expr_26_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_26_0 a_2_2) (and (= error_1 0) (and (summary_14_function_f__18_33_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 expr_22_0 state_2 a_2_2 x_4_2) (and (=> true true) (and (= expr_22_0 0) true)))))))))) (and (not expr_28_1) (= error_2 1))) (block_15_function_g__32_33_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_2 a_2_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_0 Int) (expr_13_1 Int) (expr_14_1 Int) (expr_15_1 Int) (expr_22_0 Int) (expr_23_1 |tuple()|) (expr_26_0 Int) (expr_27_0 Int) (expr_28_1 Bool) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (y_8_0 Int) (y_8_1 Int) (y_8_2 Int))
(=> (block_15_function_g__32_33_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_2 a_2_2) (summary_5_function_g__32_33_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_2 a_2_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_0 Int) (expr_13_1 Int) (expr_14_1 Int) (expr_15_1 Int) (expr_22_0 Int) (expr_23_1 |tuple()|) (expr_26_0 Int) (expr_27_0 Int) (expr_28_1 Bool) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (y_8_0 Int) (y_8_1 Int) (y_8_2 Int))
(=> (and (and (block_12_g_31_33_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (= error_2 error_1) (and (= expr_28_1 (> expr_26_0 expr_27_0)) (and (=> true true) (and (= expr_27_0 0) (and (=> true (and (>= expr_26_0 0) (<= expr_26_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_26_0 a_2_2) (and (= error_1 0) (and (summary_14_function_f__18_33_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 expr_22_0 state_2 a_2_2 x_4_2) (and (=> true true) (and (= expr_22_0 0) true))))))))))) true) (block_13_return_function_g__32_33_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_2 a_2_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_0 Int) (expr_13_1 Int) (expr_14_1 Int) (expr_15_1 Int) (expr_22_0 Int) (expr_23_1 |tuple()|) (expr_26_0 Int) (expr_27_0 Int) (expr_28_1 Bool) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (y_8_0 Int) (y_8_1 Int) (y_8_2 Int))
(=> (and (and (block_13_return_function_g__32_33_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) true) true) (summary_5_function_g__32_33_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(declare-fun |block_16_function_g__32_33_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_0 Int) (expr_13_1 Int) (expr_14_1 Int) (expr_15_1 Int) (expr_22_0 Int) (expr_23_1 |tuple()|) (expr_26_0 Int) (expr_27_0 Int) (expr_28_1 Bool) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (y_8_0 Int) (y_8_1 Int) (y_8_2 Int))
(block_16_function_g__32_33_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1)))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_0 Int) (expr_13_1 Int) (expr_14_1 Int) (expr_15_1 Int) (expr_22_0 Int) (expr_23_1 |tuple()|) (expr_26_0 Int) (expr_27_0 Int) (expr_28_1 Bool) (funds_0_0 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (y_8_0 Int) (y_8_1 Int) (y_8_2 Int))
(=> (and (and (block_16_function_g__32_33_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (summary_5_function_g__32_33_0 error_1 this_0 abi_0 crypto_0 tx_0 state_2 a_2_1 state_3 a_2_2) (and (= state_2 (|state_type| (store (|balances| state_1) this_0 (+ (select (|balances| state_1) this_0) funds_2_0)))) (and (and (>= (+ (select (|balances| state_1) this_0) funds_2_0) 0) (<= (+ (select (|balances| state_1) this_0) funds_2_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= funds_2_0 (|msg.value| tx_0)) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (and (and (and (and (and (= (|msg.value| tx_0) 0) (= (|msg.sig| tx_0) 3793197966)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 0) 226)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 1) 23)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 2) 155)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 3) 142)) (>= (|bytes_tuple_accessor_length| (|msg.data| tx_0)) 4))) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= a_2_1 a_2_0))) true) true))))))) true) (summary_6_function_g__32_33_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_3 a_2_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_0 Int) (expr_13_1 Int) (expr_14_1 Int) (expr_15_1 Int) (expr_22_0 Int) (expr_23_1 |tuple()|) (expr_26_0 Int) (expr_27_0 Int) (expr_28_1 Bool) (funds_0_0 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (y_8_0 Int) (y_8_1 Int) (y_8_2 Int))
(=> (and (and (interface_0_C_33_0 this_0 abi_0 crypto_0 state_0 a_2_0) true) (and (summary_6_function_g__32_33_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (= error_0 0))) (interface_0_C_33_0 this_0 abi_0 crypto_0 state_1 a_2_1))))


(declare-fun |contract_initializer_17_C_33_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(declare-fun |contract_initializer_entry_18_C_33_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_0 Int) (expr_13_1 Int) (expr_14_1 Int) (expr_15_1 Int) (expr_22_0 Int) (expr_23_1 |tuple()|) (expr_26_0 Int) (expr_27_0 Int) (expr_28_1 Bool) (funds_0_0 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (y_8_0 Int) (y_8_1 Int) (y_8_2 Int))
(=> (and (and (= state_1 state_0) (= error_0 0)) (and true (= a_2_1 a_2_0))) (contract_initializer_entry_18_C_33_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1))))


(declare-fun |contract_initializer_after_init_19_C_33_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_0 Int) (expr_13_1 Int) (expr_14_1 Int) (expr_15_1 Int) (expr_22_0 Int) (expr_23_1 |tuple()|) (expr_26_0 Int) (expr_27_0 Int) (expr_28_1 Bool) (funds_0_0 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (y_8_0 Int) (y_8_1 Int) (y_8_2 Int))
(=> (and (and (contract_initializer_entry_18_C_33_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1) true) true) (contract_initializer_after_init_19_C_33_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_0 Int) (expr_13_1 Int) (expr_14_1 Int) (expr_15_1 Int) (expr_22_0 Int) (expr_23_1 |tuple()|) (expr_26_0 Int) (expr_27_0 Int) (expr_28_1 Bool) (funds_0_0 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (y_8_0 Int) (y_8_1 Int) (y_8_2 Int))
(=> (and (and (contract_initializer_after_init_19_C_33_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1) true) true) (contract_initializer_17_C_33_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1))))


(declare-fun |implicit_constructor_entry_20_C_33_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_0 Int) (expr_13_1 Int) (expr_14_1 Int) (expr_15_1 Int) (expr_22_0 Int) (expr_23_1 |tuple()|) (expr_26_0 Int) (expr_27_0 Int) (expr_28_1 Bool) (funds_0_0 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (y_8_0 Int) (y_8_1 Int) (y_8_2 Int))
(=> (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= a_2_1 a_2_0))) (and true (= a_2_1 0))) (>= (select (|balances| state_1) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_20_C_33_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_0 Int) (expr_13_1 Int) (expr_14_1 Int) (expr_15_1 Int) (expr_22_0 Int) (expr_23_1 |tuple()|) (expr_26_0 Int) (expr_27_0 Int) (expr_28_1 Bool) (funds_0_0 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (y_8_0 Int) (y_8_1 Int) (y_8_2 Int))
(=> (and (and (implicit_constructor_entry_20_C_33_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1) (and (contract_initializer_17_C_33_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 a_2_1 a_2_2) true)) (> error_1 0)) (summary_constructor_2_C_33_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 a_2_0 a_2_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_0 Int) (expr_13_1 Int) (expr_14_1 Int) (expr_15_1 Int) (expr_22_0 Int) (expr_23_1 |tuple()|) (expr_26_0 Int) (expr_27_0 Int) (expr_28_1 Bool) (funds_0_0 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (y_8_0 Int) (y_8_1 Int) (y_8_2 Int))
(=> (and (and (implicit_constructor_entry_20_C_33_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1) (and (= error_1 0) (and (contract_initializer_17_C_33_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 a_2_1 a_2_2) true))) true) (summary_constructor_2_C_33_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 a_2_0 a_2_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_0 Int) (expr_13_1 Int) (expr_14_1 Int) (expr_15_1 Int) (expr_22_0 Int) (expr_23_1 |tuple()|) (expr_26_0 Int) (expr_27_0 Int) (expr_28_1 Bool) (funds_0_0 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (y_8_0 Int) (y_8_1 Int) (y_8_2 Int))
(=> (and (and (summary_constructor_2_C_33_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 0))) (interface_0_C_33_0 this_0 abi_0 crypto_0 state_1 a_2_1))))


(declare-fun |error_target_3_0| () Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_0 Int) (expr_13_1 Int) (expr_14_1 Int) (expr_15_1 Int) (expr_22_0 Int) (expr_23_1 |tuple()|) (expr_26_0 Int) (expr_27_0 Int) (expr_28_1 Bool) (funds_0_0 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (y_8_0 Int) (y_8_1 Int) (y_8_2 Int))
(=> (and (and (interface_0_C_33_0 this_0 abi_0 crypto_0 state_0 a_2_0) true) (and (summary_6_function_g__32_33_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (= error_0 1))) error_target_3_0)))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_0 Int) (expr_13_1 Int) (expr_14_1 Int) (expr_15_1 Int) (expr_22_0 Int) (expr_23_1 |tuple()|) (expr_26_0 Int) (expr_27_0 Int) (expr_28_1 Bool) (funds_0_0 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (y_8_0 Int) (y_8_1 Int) (y_8_2 Int))
(=> error_target_3_0 false)))
(check-sat)